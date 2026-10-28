(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_pkcs7_parse_A A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_seq_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P006af27cda7144b3 1 2 32 3 0 1 98 1 101 1 32 12 40 1 46 1 67 1 71 1 82 1 83 1 84 1 89 1 90 1 91 1 99 1 100 1 2 102 2 103 2P006bbfd43bca86f5 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P006c3401225d4d42 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P00920d3998c930bb 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P00adb357f57a4d91 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P00cb6a22794269e9 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P00f37f86fb3400aa 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P021a41d3053bfcd6 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P027a7f4e26e7d364 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P030e98a3622f1149 1 1 16 3 0 1 87 1 88 1 4 48 2 86 2 89 2 90 32P039c34d83945140c 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P03a085889d5aa7e4 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P03ead3c8bb105ff7 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P0427315c594eefe2 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P04838843ee55c9d4 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P04a317ecf6206951 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P0558f3ee0baff2e8 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P05a91b6f4383f233 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P05aa3f99c247b85e 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P05fcd1b17d48fdb2 0 5 0 1 31 1 57 1 74 1 75 1P0610d99aad39e030 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P072e53cbcdba1a05 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P0747c707be36dc5f 1 2 32 11 45 1 52 1 55 1 59 1 70 1 71 1 72 1 77 1 78 1 79 1 87 1 32 3 1 1 60 1 86 1 2 88 1 89 1P07ec5618d3e938a9 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P07fbca27a67ea3f3 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P08d86d4f2f1a9112 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P09699ed3ed1fd0dc 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P09ada84a7de7b46f 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P09babbdb049c4df7 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P09fc6d03864afc65 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P0a69719c450cdcdb 0 4 0 1 57 1 74 1 75 1P0a7185fb75eb1dcd 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P0a831e8b082b3e8e 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P0a8f2759326cabd4 0 5 0 1 31 1 57 1 74 1 75 1P0b21899f8293f3ed 1 1 16 3 0 1 100 1 101 1 12 47 4 68 4 72 4 83 4 84 4 85 4 90 4 91 4 92 4 99 4 102 4 103 64P0b2ac2e06a9c250a 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P0b48e5c6a441cf81 0 4 0 1 57 1 74 1 75 1P0bab843b54018eee 0 4 0 1 57 1 74 1 75 1P0bc7a3faafdda00c 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P0be4cdd49c012f82 1 1 8 3 1 1 86 1 89 1 10 45 1 55 1 70 1 75 1 77 1 78 1 79 1 87 1 88 1 90 8P0bf31cf3fbfd1dfc 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P0c26410f6be8462c 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P0c2e07bf2ccb9ce7 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P0ccf503633265bb1 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P0d0278d9994f02db 1 2 32 11 45 1 52 1 55 1 59 1 70 1 71 1 72 1 77 1 78 1 79 1 87 1 32 4 1 1 43 1 62 1 86 1 2 88 1 89 1P0d02a279392360e3 0 5 0 1 31 1 57 1 74 1 75 1P0d6fdff3d167c3d0 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P0d757cac5f30164e 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P0dcce7118f037508 0 5 0 1 31 1 57 1 74 1 75 1P0e5a1949b5e311c9 0 5 0 1 31 1 57 1 74 1 75 1P0f244ca361382730 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P0f2473650af4b718 0 4 0 1 57 1 74 1 75 1P0fe376c0a4236b1c 0 5 0 1 31 1 57 1 74 1 75 1P0ffe8428743d586c 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P103ed0b86a77fbee 0 4 0 1 57 1 74 1 75 1P10b7c9cf6f888c13 1 2 32 2 0 1 87 1 32 2 1 1 86 1 2 88 1 89 1P10cbd8d86f50eb74 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P10d732083fd3277e 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P110b44e54575d006 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P1169693838c6398b 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P11d3528bdf97ed6f 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P11d657a59c72ee52 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P122dd5c74df489b4 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P1231c25d9608fe5e 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P13118fb89859cf7c 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P141a77e7ecd9e3be 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P14865d003821217d 0 13 2 1 46 1 55 1 56 1 60 1 71 1 72 1 73 1 78 1 79 1 80 1 87 1 88 1P149b6228ce4942d4 1 1 16 2 0 1 74 1 3 7 1 75 1 76 16P149fc04fc29f3533 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P14ac96c2da5f0e07 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P14f6cbe63f806881 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P153aecd117782e1b 0 14 0 1 10 1 44 1 53 1 54 1 58 1 69 1 70 1 71 1 76 1 77 1 78 1 85 1 86 1P15d507a14b2499a4 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P163c65a999e10194 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P1698e81c6c539769 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P176b3d56990be0fc 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P177729757bab8aeb 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P1782f0203ac52313 0 5 0 1 31 1 57 1 74 1 75 1P17a0d27818534cca 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P17c5ed902456b585 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P183e97a2f92b1aab 1 1 64 2 0 1 98 1 3 14 1 99 1 100 64P18dc48e6ecc62d66 0 5 0 1 31 1 57 1 74 1 75 1P1960e1550514f29b 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P1970b32fb9f0c5b0 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P1b77dfe41ec30db2 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P1bcfb734eee50ffe 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P1c00b334e09d30bd 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P1c3b416fd0d85f39 0 9 0 1 40 1 67 1 82 1 89 1 90 1 91 1 98 1 99 1P1c7d811edd58fcdf 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P1cccd0be044595d1 1 1 16 3 0 1 99 1 100 1 4 60 1 98 1 101 1 102 16P1cf5a72d9db89eef 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P1d058d7e6c8cd35a 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P1d1fddddbf73a118 1 1 16 3 0 1 86 1 87 1 4 47 2 85 2 88 2 89 32P1d336aa553723667 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P1dcca2d638c3adf6 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P1df6f0a3a7788379 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P1e36c04ee7de69e7 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P1e5a2b4dab12f800 0 10 1 1 45 1 55 1 70 1 73 1 77 1 78 1 79 1 86 1 87 1P1f22a7e4842ce312 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P1f4b6eacec2a53cb 0 5 0 1 31 1 57 1 74 1 75 1P1f93e801b823a319 0 4 0 16 56 16 74 16 75 16P1fe585b8b1e04dd1 0 8 0 1 67 1 82 1 89 1 90 1 91 1 98 1 99 1P1fe5f49d994363f0 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P20012a31d4abbe6e 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P205bd31366b0d7e5 1 1 16 3 0 1 100 1 101 1 12 47 4 68 4 72 4 83 4 84 4 85 4 90 4 91 4 92 4 99 4 102 4 103 64P20730eeb49da9d1a 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P20b6aa25a80dee3e 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P20b85b693328051d 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P20c064902b643499 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P20ea7cf3d44b293d 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P210eaaf0774ed345 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P2176af9706087241 0 4 0 1 57 1 74 1 75 1P21a65214f8b8c790 0 9 0 1 40 1 67 1 82 1 89 1 90 1 91 1 98 1 99 1P2207e088c59701a2 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P222e1bb479a84e6a 0 3 0 1 43 1 64 1P22a61ccbea8b9d56 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P22ab8288cb7e020b 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P22c3cbb4aef76cd4 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P232ef56308d54bac 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P23593b7ce9c8e93b 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P23a56492f57431a3 1 1 16 3 0 1 99 1 100 1 12 46 4 67 4 71 4 82 4 83 4 84 4 89 4 90 4 91 4 98 4 101 4 102 64P24a405e86aa733bc 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P24b0f143c700106e 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P24bd5ea22d53dca1 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P24c73dea71121f68 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P24cb3134e3c8bea1 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P252e5f3786e47442 0 11 0 1 44 1 54 1 69 1 70 1 71 1 76 1 77 1 78 1 85 1 86 1P2574277312cfa008 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P25cf15b557436fba 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P25f043b46bca4fe9 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P26106a66b9e5c6ce 0 4 0 1 57 1 74 1 75 1P2677d080e7dca941 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P269bae60161376f1 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P274a3ddc9f4c102a 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P27fa7dde79c99032 0 5 0 1 31 1 57 1 74 1 75 1P28338c696f3d0aaa 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P28e11421069238b3 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P2927a31442a42702 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P2962e0f005764cf5 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P29f3133f6720b220 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P29fdbbd98b194db2 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P2a47257927f5d58d 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P2a4f6a0d6140dbdd 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P2a52fd11686f11d3 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P2b1c210d9b077b58 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P2b30890b72814040 1 1 16 3 0 1 100 1 101 1 12 47 4 68 4 72 4 83 4 84 4 85 4 90 4 91 4 92 4 99 4 102 4 103 64P2b405e4de3fe8826 0 4 0 1 57 1 74 1 75 1P2bc402ba735467af 1 2 32 3 0 1 99 1 102 1 32 12 41 1 47 1 68 1 72 1 83 1 84 1 85 1 90 1 91 1 92 1 100 1 101 1 2 103 2 104 2P2c2d4204752a14ab 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P2cce901ebc569805 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P2ceab06e0bd9c914 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P2d2701e9967d4d9e 0 6 0 1 36 1 47 1 68 1 85 1 86 1P2d3939cbbf6ae174 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P2d3c6edeac2ad6ef 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P2dd681cc5298b148 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P2e0802ca858f2952 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P2e143ccb25514665 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P2ef9b4191fef7a7a 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P2f04d4f45c668a95 0 4 0 1 57 1 74 1 75 1P2f1407f00ce843fa 0 10 0 1 44 1 54 1 69 1 72 1 76 1 77 1 78 1 85 1 86 1P2f2d6666248b27e9 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P2f553086a37b1607 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P2f5ea183599364ba 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P2f69476c8b4a3c25 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P2f82719ee533f5eb 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P2fa602b4d9e8b155 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P2fa706a49f280363 0 4 0 1 57 1 74 1 75 1P2fa91f60acf10776 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P301fd7e646aec644 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P305ea27abfc866cc 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P3095055005fac708 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P309f81aed392f68a 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P3179ff513c239e5c 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P31eb83225dac5613 0 5 0 1 31 1 57 1 74 1 75 1P320b40893eba684a 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P32373e447956f55f 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P326391c7fa80cc85 0 12 2 1 44 1 45 1 49 1 60 1 61 1 62 1 67 1 68 1 69 1 76 1 77 1P32a5e0c09cb12b53 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P32b47b6e139dcb9b 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P32bc4ab219b45406 1 2 16 3 1 1 49 1 75 1 16 3 0 1 50 1 76 1 2 77 1 78 1P33528c2cdbe5322b 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P33699bd60a3aa8c7 0 4 0 1 57 1 74 1 75 1P345c6e425eb21e29 0 4 0 1 57 1 74 1 75 1P34609ea48d5c80c3 1 1 16 3 1 1 49 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P34bc93aa41086da9 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P34c38256cd8eb5b9 0 5 0 1 31 1 57 1 74 1 75 1P34faad7d694b3d97 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P35ad4896ed70bab5 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P35d21b21ca86b194 0 5 0 1 31 1 57 1 74 1 75 1P360e3ffe4ea018ff 1 1 8 3 1 1 76 1 77 1 9 44 1 59 1 64 1 66 1 67 1 68 1 75 1 78 1 79 8P36c28ec8b29e6fd3 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P36cefb5f13490b14 1 1 16 3 0 1 99 1 100 1 4 60 1 98 1 101 1 102 16P3736d23639bcdf1f 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P3760c7de27b12506 0 5 0 1 31 1 57 1 74 1 75 1P3793791f4c9759a0 1 1 64 2 17 1 98 1 3 0 1 99 1 100 64P37aaf98cbf899258 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P37b09ffaa3e8fb07 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P384e9d91ea6eb4b3 0 4 0 1 57 1 74 1 75 1P399a0a4046f0754d 0 9 0 1 44 1 54 1 69 1 76 1 77 1 78 1 85 1 86 1P39f460c8e2b24632 0 4 0 1 57 1 74 1 75 1P3a99d43b87093565 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P3ace90080a6ce4a6 0 3 0 1 42 1 61 1P3b08faabf43741e2 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P3b7ab2b92928c7d2 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P3c7ecf7f8f66b6a5 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P3cc04fdd15f6bad9 1 2 32 3 0 1 98 1 101 1 32 12 40 1 46 1 67 1 71 1 82 1 83 1 84 1 89 1 90 1 91 1 99 1 100 1 2 102 2 103 2P3cccb1d23db4e642 0 5 0 1 47 1 68 1 85 1 86 1P3cff5d561f3cee1a 0 8 0 1 43 1 58 1 65 1 66 1 67 1 74 1 75 1P3d54ac31dab65171 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P3dcf47b73c430e6b 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P3deaeddcfb20f7ba 1 2 8 2 0 1 98 1 8 2 88 1 99 1 2 100 1 101 1P3df98e9078e4ae52 0 13 0 1 2 1 42 1 43 1 47 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P3e4ad719d3160f14 1 1 8 3 0 1 85 1 88 1 10 44 1 54 1 69 1 74 1 76 1 77 1 78 1 86 1 87 1 89 8P3e543231f5d698f2 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P3e6ba33d4a56e6ad 0 9 1 1 44 1 59 1 62 1 66 1 67 1 68 1 75 1 76 1P3e7481599b62e106 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P3e972a71856bf478 1 1 8 3 0 1 75 1 76 1 9 43 1 58 1 63 1 65 1 66 1 67 1 74 1 77 1 78 8P3edb7f4c21d58a4c 0 4 0 8 36 8 98 8 99 8P3f062aebc60e45cb 0 10 0 1 43 1 58 1 59 1 60 1 65 1 66 1 67 1 74 1 75 1P3f449696e5879e7b 1 1 16 2 1 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16P3fc4c1e0aadfdd0e 0 9 0 1 43 1 58 1 61 1 65 1 66 1 67 1 74 1 75 1P3fca8c6139665e7a 1 1 16 4 1 1 38 1 51 1 75 1 11 41 1 44 1 48 1 59 1 60 1 61 1 66 1 67 1 68 1 76 1 77 16N0086abe9a6c1f895N00a98fdf143837ffN012d93589f0cdc6eN0180a8aabcb54055N0285c69334d8bc53N029254c122297e8bN0298b3c497660793N03356020d03529c2N03c448c3b7b99f15N03fa32c402eedecbN052073f796db280cN05911600c4ba2c78N072c19d1dcf6c950N0791aff5c1b1f596N07962240f059fffeN079cec3c0993eab5N094e7a616caca303N096c6afafd692aa3N09a9eb560ea3bb99N0b54fd4541a4c152N0c0fcb49916d9615N0c6d936c542cba0bN0e7e1aea31a42378N0eba2e0d8f6db98eN0f37d025ac7dcdf5N0f96e040251e276cN0faa3aa5ca4bb8dfN11536da9adeee449N11b6e4d900ae557aN11dcf4cc0fbb90dfN12086dc9de20d97fN121e155cc6046ab0N12381ff6e3bc17feN12eb6e7a33c21f53N13498d38510f5e64N1371622301bb4bbeN13802f6580ac7889N13d8d9dbd520e348N148a1515348ef969N1492543b98683f30N14c6646bd50a9a97N15a731fe06f452b0N16110a7cb9b238cbN16873d4c3c94c45dN17dbddaac804dd7aN18299194b53b4037N1870a8351f3913e7N1945010fd4424249N1aa8c64e642fdf20N1aea580e1759e333N1e10c052c283e2a1N1e3ab43afafdaf9bN1e8d2c13a02ce33eN1ec871defcdeab62N1f561559dc114e2cN1f7a7d1ad6d902b5N1fb7e2853f757bdbN1fb9a85f76ad231dN20269b8a4c8a9637N20a5ec5a638f3afdN20d4e5f6f42f51f1N22cba96de00fc566N22e2670d35b1142fN232f8f886653c289N2346e1ce54e2c2f3N2375a3a5266226e5N2385c8f310a6a6caN23c772006ad3962bN2508c7f19bd144cdN25265747f18af8a0N25930c35911c24c4N25ccfa3e93d4cb3bN262375921473f61bN2688685df401bbd0N26b385eeebd38025N27dcc1d87be0b015N284e98dd4d51db95N289ef04acdeac4ecN28b791daa5b72a92N2972c3e2f264e237N2acf507a5ca83b3dN2b13bd9384511fccN2bd22f048c7ccd64N2c11046fa3347000N2c3232a3dd37100aN2cd7781023344130N2ded50a803dbdc9bN2ea8767fe2d01d46N3056f4adabe2b975N318603b9d23f4e67N333b6f5143433678N343c4720b0b51fc1N35136294ddb66eb1N35e48f22416fb78dN365a4a2ad2f9f3f4N36aa7d74ff30525cN36ffcdf89c32e089N37613c9497a2dd5fN396b79929317e04cN3a634cafa4ccd810N3b185246dd7f3403N3b4c4df20034fe45N3b92f8e2d8ee199bN3bc125bc7f79f6e8N3bfabadd4965bcd5N3c741d99db04dfaeN3cd39c0032f9a324N3d2350e711745bbbN3db608243e7b5e1aN3de07b5c07bcfdc1N3e2dd94c280a53ce"%lxh.
Import ListNotations.
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
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Definition A_X509_SAN_EXT : Z := 0xae500.       (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis AMS : arl_amemset R = 0x68258.
  Hypothesis AMC : arl_amemcpy R = 0x67dbc.
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z).
  Hypothesis STKp0 : 0 <= STKp.
  Hypothesis PSAN : x509_parse_san_stmtA asegs R HIA PHIp FFRp CNTp STKp (LFMAX_CRT + 6) A_X509_PARSE_SAN.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Hypothesis SEQFREE : asn1_sequence_free_stmtA asegs R HIA A_ASN1_SEQUENCE_FREE.
  (* [comment removed for export] *)
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.
  Hypothesis PHIp_add : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_add : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_add : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43150339301.25000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R /\ arl_need_amem R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition STKx : Z := 240 + 48 + STKp + arl_need_smalloc R + arl_need_rt R.
  (* [comment removed for export] *)
  Definition CNTx (n : Z) : Z := n.
  Definition PHIx (n : Z) : Z := PHIp n + CNTp n * AVOL_CALL + n * AVOL_CALL.
  Definition FFRx (n d : Z) : Z := FFRp n (d + 1) + CNTp n * fr_charge 0 + n * fr_charge (d + 1) + n * fr_charge 0.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP CUR P END BUF lo slo d : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 5)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HCUR : rw_cells asegs m CUR (seq_cells ct cpad 0 0 0).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  (* [comment removed for export] *)
  Definition FSHb (b : byte) : list cell :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 b; C1 b; C1 b; C1 b; C1 b; C1 b; C1 b; C1 b;
     C1 b; C1 b; C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Definition rsl (FB : Z) (k0 k8 k16 k24 k48 : word) (j64 : list byte) : list cell :=
    [C8 k0; C8 k8; C8 k16; C8 k24; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 CUR); C8 (Z_to_bv 64 FB); C8 k48; CB 24 j64; C8 (Z_to_bv 64 FB)].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := fun ms =>
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word)
           (w0 w1 w2 tl k0 k8 k16 k24 k48 : word) (j64 jt jn : list byte),
      ms = MS (mkR (Z_to_bv 64 0xae578) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 (Z_to_bv 64 FB) a5 a6 a7
                   s2 (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) s7 s8 s9 (Z_to_bv 64 P)
                   (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
              F (Z_to_bv 64 0xae674) fc None m1 (seg_rom asegs)
      /\ bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224 /\ sp1 mod 32 = 0
      /\ HM asegs R HIA h1 LB ((FB, 256) :: LF) m1 /\ hcs asegs R HIA h1 = CS /\ htop asegs R HIA h1 = htop asegs R HIA h
      /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\ hflag asegs R HIA h1 = hflag asegs R HIA h
      /\ havol asegs R HIA h1 = havol asegs R HIA h /\ hfr asegs R HIA h1 = hfr asegs R HIA h
      /\ (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
      /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 256
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (FB + 32) [C8 tl] /\ rw_cells asegs m1 (FB + 64) [CB 80 jn]
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) (FSHb (Z_to_bv 8 248))
      /\ rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL
      /\ rw_cells asegs m1 sp1 (rsl FB k0 k8 k16 k24 k48 j64) /\ rw_cells asegs m1 (sp1 + 96) [CB 24 jt]
      /\ stk asegs m1 (sp1 + 120) (bv_unsigned sp + -104) /\ stk asegs m1 lo sp1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 PP [C8 (Z_to_bv 64 P)] /\ rw_cells asegs m1 CUR (seq_cells ct cpad 0 0 0) /\ bytes_at asegs m1 BUF bs
      /\ aobj asegs AL CS m1 PP 8 /\ aobj asegs AL CS m1 CUR 32 /\ aobj asegs AL CS m1 BUF n
      /\ (FB + 256 <= PP \/ PP + 8 <= FB) /\ (FB + 256 <= CUR \/ CUR + 32 <= FB)
      /\ (n = 0 \/ FB + 256 <= BUF \/ BUF + n <= FB)
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m m1
      /\ sshad asegs AL m1 slo (bv_unsigned sp).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 D1; try lx_pin1 DCB; try lx_pin1 ALC; try lx_pin1 DPB; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 CNTp_add; try lx_pin1 FFRp_add; try lx_pin1 PHIp_add; try lx_pin1 CNTp_mono; try lx_pin1 FFRp_mono; try lx_pin1 PHIp_mono; try lx_pin1 SEQFREE; try lx_pin1 FREEL; try lx_pin1 PSAN; try lx_pin1 CNTp; try lx_pin1 FFRp; try lx_pin1 PHIp; try lx_pin1 HMND; try lx_pin1 CALLOC; try lx_pin1 AMC; try lx_pin1 AMS.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03b0@D10637083011.185D10651765667.113D10823604468.154D12551588724.183D12658639931.112D12660902694.154D14196765263.185D18607476203.155D18607476203.159D20553579080.156D20553579080.157D20553579080.158D22857195205.186D22857195213.114D2457697673.184 D29848042130.186D31526457809.112D31528243920.183D3162359820.185 D32458983506.184D32467519490.186D32467519498.114D3254889317.154 D32604263324.187D33194539134.112D33285689726.183D3375407252.183 D36106837473.185D39411162312.155D39411162312.159D39565106411.212D39565106411.213D45716867365.183D46795284838.185D46805773126.113D50254960491.156D50254960491.157D50254960491.158D52056129450.159D52459714199.186D52574013935.159D54559284595.183D560907437.115  D59053605550.183D60098777666.113D60109264994.185D60109264995.186D60109265003.114D60109460051.183D60189065437.212D60189065437.213D6192914196.159 D62011770183.187D62011770191.115D62184560052.186D66237105964.184D68407130839.183D6911781074.183 L10116530568.11 L10837002389.2  L12126572370.2  L12654381620.1  L1685717371.0   L18021517688.14 L18271036602.161L19548981078.164L19980016842.14 L2333530698.151 L2333531081.151 L2333536794.151 L26163319485.151L26163319614.151L26163329773.151L26892418956.1  L28631256731.2  L28987030758.135L29738741675.1  L31142782368.2  L32463525127.1  L32929385090.136L33472729358.120L33485826452.1  L33485826452.15 L34452444106.2  L35653441506.13 L38257675168.2  L38692635477.0  L39280637297.0  L39332637397.0  L40228640085.0  L41202929119.204L42196131762.11 L42402910215.1  L43055369633.133L43300649301.0  L44166924249.3  L45298099350.1  L48117620906.100L48119718058.158L48119718059.159L48132302231.114L48834180257.0  L49111522807.1  L5067997811.164 L50797055232.13 L5325812058.113 L56009798182.1  L56380991837.10 L57355539152.165L57355539152.166L57698627611.2  L58790154276.14 L59308634497.16 L59578101107.190L60098763854.6  L61437265048.2  L6302879940.151 L6302880071.151 L6302890132.151 L64850595401.0  L65278984344.158L68343892476.135L6910010095.158 L7040749983.114 L8252318361.14  L9356559645.18  P1056307012.159 P12115299733.212P12115299733.213P28627113325.212P28627113325.213P31146933846.212P31146933846.213P34450608397.212P34450608397.213P38261788758.212P38261788758.213P44164039966.212P44164039966.213P51023938008.159P57713046236.212P57713046236.213Q10533598597.117Q10594483355.191Q10636905305.208Q10649498890.210Q10651864147.209Q13345046842.117Q13345046842.142Q13349241863.192Q1357990380.209 Q13732992878.209Q15249212539.208Q1530342990.159 Q15513214246.154Q15889328230.208Q16180847038.191Q17701933584.210Q1897072239.154 Q23937998252.117Q23937998260.119Q28465177121.209Q28465177121.210Q29850139295.192Q31021924279.153Q31599749226.117Q31599749226.142Q31603944791.192Q32440833928.190Q33271078526.190Q3421936230.211 Q3421936230.212 Q34390149656.210Q36104740333.192Q37995699067.208Q38248895664.120Q39031378545.209Q39180574961.212Q39180574961.213Q39600066516.210Q40271359350.159Q42437284299.143Q42439168719.153Q42439382252.121Q42439443119.212Q42439443119.213Q42441479405.196Q43880146028.120Q45360159462.208Q47241206720.117Q47313632828.117Q47313632828.142Q47313632828.190Q48119718061.191Q48132302231.190Q49429114885.192Q49441699128.117Q49441699128.142Q50796826103.159Q5265442331.210 Q5265442331.211 Q55415036769.212Q55415036769.213Q56533317809.191Q57228775306.211Q57228775306.212Q59310664043.117Q59310664043.142Q59310664043.190Q59321350679.212Q59321350679.213Q59323247697.191Q59323247702.192Q59865321072.212Q59865321072.213Q59865520179.121Q59867617330.196Q59871812884.143Q61847600945.210Q62022254700.119Q62022254708.117Q64157425270.117Q64157425270.142Q64170007371.192Q64681502660.196Q64683599813.121Q64683667846.212Q64683667846.213Q64685695714.143Q65266402725.190Q65266402749.194Q65278984344.192Q66565742822.208Q67151971323.208Q67517027822.117Q67517027822.142Q67517027822.190Q6897428426.194 Q6897428434.190 Q6910010095.192 Q9350548487.139 Q9870526438.208 00000V01301Z01[02<02c02d02e02f02g02h02i03S04004104204304404504[05E05b05c06R07307407507607707808Q09j0:P0;60;S0;T0;U0;V0<=0<>0<a0<b0=G0=H0=n0>]0?L0@20@a0BJ0D30DV0E>0E]0E^0FD0FE0Fk0GX0G`0Ga0Gf0Gg0Gh0HU0IE0I]0I^0K30K40K50KY0KZ0K^0K_0L<0L@0LA0LE0ML0MM0MN0MO0MP0Mh0Mi0Mj0Mk0Ml0Mm0NS0O@0OD0PO0PP0PQ0PV0Q\0R]0S^0TZ0T[0T`0UT0V=0W30W80WQ0WR0XL0XM0Y60Y@0Yk0Z50Z=0Z>0Zb0Zc0Zd0[<0[Z0\20\X0\Y0]V0^:0_U0a00bN0cl0eD0f\0h90iV0k40lR0mo0oL10210d11V12512M12e13=13U13V13W13X14Y15115T16416517617N17f18?18m19O19o1:O1:P1;91;:1;;1;<1;=1;>1<31<h1<i1<j1=M1=j1>M1?h1AC1AD1Aa1B<1B\1CA1D71Dm1EM1Em1FE1Fe1Ff1Fg1Fh1Gi1Hj1Hk1Hl1Hm1Ij1JL1Jn1K`1LR1LS1Mf1O91O:1O;1O<1O=1O>1O?1O@1OA1OB1OC1OD1OE1P:1PV1Q21Q31Q41Q51Qb1RT1SW1TZ1UB1UZ1V21VJ1WK1Wn1Wo1X01X11XI1Xa1Y91YZ1Z[S2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP3CUR2bs3LFB3PPB3CUBS2LF2sp2PP3BUF2bs3LFB4lxHn3sp13H194LFB'FS2LF2sp2PP3CUR3BUF2bs3LFB3PPB3CUBS2LF2sp2PP3BUF2bs3LFB4lxHn3sp13H194LFB'FFFFFFS2LF2sp2PP3CUR2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP3CUR2bs3LFB3PPB3CUBFFFFFS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP3CUR2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS1R3HIA2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2h12FBS2LF2sp2PP3CUR3BUF2bs3LFB3PPB3CUBFFFFFS1R3HIA1h2LF2sp2PP2bs3LFB3PP03TOP3SPR4lxHn3sp13H193SP14LFB'2h15Ehtop2FB2F02HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2PP2bs3LFB3PP03TOP3SPR4lxHn3sp13H193SP14LFB'2h15Ehtop2FB2F02HB5Ha_st5Hl_stS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS2LF2sp2PP3CUR2bs3LFB3PPB3CUBFFFS2LF2sp2PP2bs3LFB4lxHn3sp13H173H194LFB'FS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'FS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS3PPB3CUBS1R2LF2sp2PP2lo2bs3LFB3LOS4lxHn3sp13H194LFB'2FBS1R2LF2sp2PP2lo2bs3LFB3LOS4lxHn3sp13H194LFB'2FBS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS3PPB3CUBS1R2LF2sp2PP2lo2bs3LFB3LOS4lxHn3sp13H194LFB'2FBS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB3PP03SLO3LOS4NRTa3SPR4lxHn3sp13H193SP14LFB'2FB2F02HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB3PP03SLO3LOS4NRTa3SPR4lxHn3sp13H193SP14LFB'2FB2F02HB5Ha_st5Hl_stS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'S1R2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBFS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS1R3NS13NA14STKp5STKp02sp2lo3SLO4NRTa3sp13SP1S3BUF2bsFS3BUFSSS1R2LF2sp3slo2bs3LFB4SLOS3ALO4lxHn4LFB'2FB2F1S2LF2sp2PP2bs3LFB3SPR4lxHn3sp13H194LFB'2FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1FS1R3HIA3NS13NA14STKp5STKp01h2LF2sp3BUF2lo2bs3LFB3SLO3TOP4NRTa5BUFLO4lxHn4LFB'1a2Ha2H0FFS2LF3BUF2bs3LFB4lxHn4LFB'2FB1a2Ha2H0FS2spFS2LF2sp2PP3CUR2bs3LFB3PPB3CUBS2FBFS2FBS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB3PP03SLO4NRTa3SPR4lxHn3sp13H19FFFFS1R3HIA1h2sp2lo3TOP4HTOPFSSSSS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FBS1R3NS13NA14STKp5STKp02sp2lo3SLO4NRTa3sp13SP1S2spS1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO4NRTa3SPR3PPB3CUBSFS3sp1S1R3NS13NA14STKp5STKp02LF2sp2PP3CUR2lo2bs3LFB3SLO3LOS3ALO4NRTa3PPB3CUBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn4LFB'S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn4LFB'S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnSS3sp1S2LF2sp2PP2bs3LFB3PP03SPR4lxHn3sp13H194LFB'2FB2F02F8S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaS2LF2sp2PP2bs3LFB3PP03SPA3SPR4lxHn3sp13H153H163H173H19S3sp1S1R3BUF2lo2bs3LOS3ALO3BCEFS1R2LF2sp2PP2bs3LFB3PP03ACV3SPR4lxHn3sp13H194LFB'2FB2F02F1FS1R3NA14STKp5STKp02sp2lo3SLO4NRTa3sp13SP1S2FB2F02KbS2LF2sp2PP2bs3LFB4lxHn3sp13H194LFB'2FB1c2HcS1R2lo3LOSS2LF3LFBFS2LF3BUF2bs3LFB4lxHn4LFB'2FB1a2Ha2H0FSS2LF2bs3LFB4lxHn4LFB'2FBS2LF2sp2PP2bs3LFB4lxHn3sp13H19S2LF2bs3LFB4lxHn4LFB'2FBS2LF2sp2PP2bs3LFB3SPR4lxHn3sp13H153H19SS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3ALO3ACV4NRTa3SPR3sp13SP1S2LF2PP2lo2bs3LFB4PPLO4lxHn3sp14LFB'S1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'2FB4FBLO2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'2FB4FBLO2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB5CURLO3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3CUR2lo2bs3LFB5CURLO3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2F12HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3BUF2lo2bs3LFB3SLO4NRTa5BUFLO4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp3BUF2lo2bs3LFB3SLO4NRTa5BUFLO4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS2LF3CUR2lo2bs3LFB5CURLO4lxHn3sp14LFB'S2LF2sp2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stS2LF2sp2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBS2LF2bs3LFB4lxHn4LFB'2FBS2LF2PP2bs3LFB4lxHn4LFB'S2LF2PP2bs3LFB4lxHn4LFB'S2LF2PP2bs3LFB4lxHn4LFB'FFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'S2LF2PP2bs3LFB4lxHn4LFB'S2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'S2LF2sp2bs3LFB4lxHn3sp13H174LFB'FS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'S2LF2bs3LFB4lxHn4LFB'2FBS2LF2PP2bs3LFB4lxHn4LFB'S2LF2bs3LFB4lxHn3sp14LFB'S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3TOP4HTOP3PPB3CUBS1R3HIA1h2LF2PP3CUR2bs3LFB3PPB3CUBS2LF2bs3LFB4lxHn3sp13H194LFB'2HBS2LF2bs3LFB4lxHn3sp13H194LFB'2HBFS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4lxHn4LFB'FFFFFS2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stS2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stFFS2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'S2LF2PP3CUR2lo2bs3LFB3PPB3CUBS2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stFS1R3HIA1h2LF2bs3LFB4lxHn4LFB'S1R2LF3slo2bs3LFB4SLOS4lxHnS1R2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R2LF2PP3CUR3slo2bs3LFB4SLOS3PPB3CUBS1R2LF3slo2bs3LFB4SLOS4lxHn3sp14LFB'2FB2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS4lxHn3sp14LFB'2FB2HB5Ha_st5Hl_stS1R2LF3slo2bs3LFB4SLOS4lxHn4LFB'S2LF2sp2PP3CUR2lo2bs3LFB3PPB3CUBS2LF2PP2bs3LFB4lxHn4LFB'S1R2LF2PP3CUR2bs3LFB3ALO3PPB3CUBFFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn4LFB'S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHn4LFB'FFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS4NRTa4lxHn4LFB'S2LF2bs3LFB4lxHn3sp14LFB'2HB5Ha_stS2LF2bs3LFB4lxHn3sp14LFB'2HB5Ha_stS2LF2sp2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stS2LF2sp2bs3LFB4lxHn3sp13H174LFB'2FB2HB5Ha_st5Hl_stFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'2FB2HB5Ha_st5Hl_stFFFFFFFFFFFFS2LF2sp2PP2bs3LFB3ALP3PP03SPR4lxHn3sp13H194LFB'2FB2F0S1R2LF2PP3CUR2bs3LFB3PPB3CUBS1R2LF2PP3CUR2bs3LFB3PPB3CUBFFFS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn4LFB'S1R3HIA1h2LF2sp2PP3CUR3slo2bs3LFB3TOP4HTOP3PPB3CUBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn3sp14LFB'2FB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn3sp14LFB'2FB2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHnS2LF2bs3LFB4lxHn4LFB'2FBS2LF2bs3LFB4lxHn4LFB'2FBS2LF2bs3LFB4lxHn4LFB'2FBS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'S2LF2sp2lo2bs3LFB4lxHn3sp13H174LFB'FFFS2LF2bs3LFB4lxHn4LFB'2FBS2LF2bs3LFB4lxHn4LFB'2FBS2LF2bs3LFB4lxHn4LFB'2FBS2LF2bs3LFB4lxHn3sp13H183H194LFB'S1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO4NRTa4lxHn3sp13SP14LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS CURLO CWC CUR0 HCUR BIN HBY PPLO CWP PP0 ALP HPP LFB NRT STKp0 STKp NA1 NS1 SM2 UARG IMG"]
  Lemma pro_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m CUR 32 -> aobj asegs AL CS m BUF n ->
    evtA asegs AL CS S1P
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 CUR) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_X509_SAN_EXT) fc None m (seg_rom asegs)).
  Proof.
  intros until t6.
  intros HH ST SS MI OPP OCUR OBUF.
  unfold A_X509_SAN_EXT.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia | lx_side_lia ]]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  assert (BUFLO : BUF + n <= lo) by (first [ clear - BCE ALO LOS; lia | lx_side_lia ]).
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(first [ clear - LOS SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add length] in PPB.
  pose proof (rw_cells_bound _ _ _ _ HCUR) as CUB.
  cbn [cells_size csize Nat.add length seq_cells] in CUB.
  (* [comment removed for export] *)
  pose proof (conj HBY (conj HPP (conj HCUR (conj OPP (conj OCUR (conj OBUF I)))))) as EBOX.
  clear OPP OCUR OBUF.
  carve_frame 224%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lx_hide1 EBOX.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xae544] [] 377%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).   (* [comment removed for export] *)
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia | lx_side_lia ]).
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
  lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -224) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
  replace (bv_unsigned sp + -224 + 120) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
  lazymatch goal with STx : stk _ m0 lo (bv_unsigned sp + -224) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
  destruct (stk_split asegs m0 lo (sp1 + 120) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1 SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ])) as [STlo SThi].
  destruct (stk_carve asegs m0 lo (sp1 + 120) 120 STlo ltac:(first [ clear - SP1 SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ])) as [ST1 [jrs RSL]].
  replace (sp1 + 120 - Z.of_nat 120) with sp1 in RSL, ST1 by (clear; lia).
  apply (rw_cells_split_CB asegs m0 sp1 [] 120 jrs [] [8; 8; 8; 8; 8; 8; 8; 8; 24; 8; 24]%nat) in RSL; [| reflexivity].
  cbn [mk_CB_cells app] in RSL.
  cb8_to_c8 RSL (@nil cell).
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 RSL [c1] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 RSL [c1; c2] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 RSL [c1; c2; c3] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7; c8; c9] end.
  chunk_split RSL 10%nat RSLa TSB.
  replace (sp1 + 96) with (sp1 + 96) in TSB by (clear; lia).
  idtac "END-SPILL".
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 377%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. lx_unhide.
  try clear STJ.
  try clear STlo.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  idtac "SMALLOC".
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 340476 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (unfold LFMAX_CRT in LFB; first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1, STc : stk _ m1 lo sp1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 192); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact STc
                  | first [ clear - SLO SP1 TOP NS1 NA1 NRTa STKp0; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 2)) with 32%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 2)) with 256%nat in FRM by reflexivity.
      replace (64 * 2 ^ 2) with 256 in FRSH, HH1 by reflexivity.
      (* [comment removed for export] *)
      zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). kland Kb.
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      idtac "FRAME".
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      assert (APB : n = 0 \/ FB + 256 <= BUF \/ BUF + n <= FB).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right]. apply F3. apply in_or_app. left. exact BIN. }
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [8; 8; 8; 8; 8; 24; 80; 112]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat GA FRM3. chunk_split FRM3 1%nat JMC FRM4. chunk_split FRM4 1%nat GN FREST.
      lazymatch type of GA with rw_cells _ _ ?a _ => replace a with (FB + 32) in GA by (clear; lia) end.
      lazymatch type of GN with rw_cells _ _ ?a _ => replace a with (FB + 64) in GN by (clear; lia) end.
      clear FLNK JMC FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      cb8_to_c8 GA (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  idtac "PP-CHK".
  try (lx_hide1 EBOX). lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xae668] [] 377%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. lx_unhide.
  (* [comment removed for export] *)
      destruct EBOX as (HBY' & HPP' & HCUR' & OPP & OCUR & OBUF & _).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HPF;
        assert (CRP : client_range L (LB ++ fdata LF) (bv_unsigned sp) PP 8) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWP)| exact PPLO]);
        assert (CRC : client_range L (LB ++ fdata LF) (bv_unsigned sp) CUR 32) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWC)| exact CURLO]);
        assert (CRB : client_range L (LB ++ fdata LF) (bv_unsigned sp) BUF n) by (eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]);
        assert (OPP1 : aobj asegs AL CS mx PP 8);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OPP | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRP| clear; lia] ] |];
        assert (OCUR1 : aobj asegs AL CS mx CUR 32);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OCUR | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRC| clear; lia] ] |];
        assert (OBUF1 : aobj asegs AL CS mx BUF n);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OBUF | intros xq Hxq; eapply hcs_below_top; exact Hxq
                              | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right; split; [exact CRB| clear; lia]] ] |];
        assert (HB1 : bytes_at asegs mx BUF bs);
        [ eapply presA_bytes_at0; [exact HPF| exact HBY'| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right; split; [exact CRB| exact I]]] |];
        assert (HPP1 : rw_cells asegs mx PP [C8 (Z_to_bv 64 P)]);
        [ eapply presA_rw_cells; [exact HPF| exact HPP'| exact CRP| exact I] |];
        assert (HCUR1 : rw_cells asegs mx CUR (seq_cells ct cpad 0 0 0));
        [ eapply presA_rw_cells; [exact HPF| exact HCUR'| cbn [cells_size csize Nat.add length seq_cells]; exact CRC| exact I] |];
        clear HPF end.
      unfold seq_cells in HCUR1.
      (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with HHx : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mx HHx) as ABg end end.
      zstep. zstep. zstep.
      clear ABg.
      idtac "S1P".
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      lazymatch goal with H : rw_cells _ m9 sp1 _ |- _ => rename H into RSLX end.
      lazymatch type of RSLX with rw_cells _ _ _ [C8 ?a0; C8 ?a8; C8 ?a16; C8 ?a24; _; _; _; C8 ?a48; CB 24 ?ja; _] =>
        assert (RSL9 : rw_cells asegs m9 sp1 (rsl FB a0 a8 a16 a24 a48 ja)) by (unfold rsl; exact RSLX) end.
      clear RSLX.
      lazymatch goal with H : rw_cells _ m9 CUR _ |- _ => change (rw_cells asegs m9 CUR (seq_cells ct cpad 0 0 0)) in H end.
  apply evtA_done. unfold S1P.
      exists FB, sp1, h1, m9.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      repeat match goal with |- _ /\ _ => split end;
        first [ exact RSL9 | eassumption | exact PRES
              | lazymatch goal with
                | |- _ \/ _ => first [exact APP | exact APC | exact APB]
                end
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
