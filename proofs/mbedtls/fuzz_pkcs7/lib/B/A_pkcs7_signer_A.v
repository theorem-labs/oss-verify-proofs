(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001490dcb0c83760 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P00fc6012696fee8a 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P0125a73af47f4fef 1 1 16 3 0 1 103 1 104 1 10 47 1 66 1 75 1 78 1 85 1 86 1 87 1 102 1 105 1 106 16P017692d540001912 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P0198a377d7d2c844 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P01c4cbcdf0dcf1d9 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P02c0d454bfc242cc 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P02f5caf4586f9e29 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P031f2c63a19c5de6 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P03a4d2f07d9ee02e 1 1 16 3 0 1 104 1 105 1 10 48 1 67 1 76 1 79 1 86 1 87 1 88 1 103 1 106 1 107 16P044ec7b0861d585e 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P048764f8a08f42a8 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P04b054d1d9500509 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P04da1b4e0bb7e9d5 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P0561a087596bb18f 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P05bee2c6eb2042b5 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P05e33a7e65475208 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P05f7a75a6e02501c 0 5 0 1 35 1 67 1 85 1 86 1P06e8a83bc186bb87 0 4 0 1 67 1 85 1 86 1P07529e483f97bc61 0 8 1 1 42 1 67 1 76 1 86 1 91 1 103 1 104 1P077eb57b8deff0f4 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P0780eb2e48b2189c 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P07b44b4c7a31784b 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P07d04108acf3b815 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P07ef03fbc00f733c 0 5 0 1 35 1 67 1 85 1 86 1P0857f3479227926e 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P08f57b55ff8e358c 1 1 64 2 5 1 102 1 3 0 1 103 1 104 64P08f9728815dd7686 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P09014e4b3c454279 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P091c16ee2d992529 1 2 32 3 0 1 103 1 106 1 32 10 42 1 48 1 67 1 76 1 79 1 86 1 87 1 88 1 104 1 105 1 2 107 2 108 2P0a37163b85041aad 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P0ac5f22cc70cc2a4 1 2 32 3 0 1 102 1 105 1 32 10 41 1 47 1 66 1 75 1 78 1 85 1 86 1 87 1 103 1 104 1 2 106 2 107 2P0acc18fe5a302ca6 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P0b0afeefc83793c7 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P0b727eec37c14c2b 0 6 0 1 49 1 58 1 68 1 85 1 86 1P0b80e8edfa440f6c 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P0bdf4a5bf915697d 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P0bea6c2a9b8f4cb1 0 6 0 1 49 1 58 1 68 1 85 1 86 1P0c40ec9167144001 0 5 0 1 35 1 67 1 85 1 86 1P0cfe40bff6b920f6 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P0d69527702633ed7 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P0d77fc02fd192ad0 0 5 0 1 35 1 67 1 85 1 86 1P0d8c10abfa006748 0 5 0 1 35 1 67 1 85 1 86 1P0dc645ead1140c9c 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P0dcec2a8f03ee2d8 0 8 0 1 41 1 66 1 75 1 85 1 90 1 102 1 103 1P0dd8f4cecdc52e9f 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P0dfe2909f62afe94 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P0eab5fec5e2c1697 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P0eb3b56111ec4dc5 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P0ec4a95f8441fe69 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P0f98e9a3b5298a2a 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P0fcebe8025b8af82 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P10b01e0588665a15 0 6 0 1 49 1 58 1 68 1 85 1 86 1P124a7d5167bd727a 0 5 0 1 35 1 67 1 85 1 86 1P1268095894c79d7a 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P126e4130e8f5e036 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P12b0372d87572fa3 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P1301f2c5d34a9a6d 0 6 0 1 58 1 61 1 84 1 102 1 103 1P13142500c473c2dd 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P1320c9be33746433 1 1 16 3 0 1 104 1 105 1 4 62 2 103 2 106 2 107 32P139a80fb4a0a97dd 0 9 0 1 41 1 66 1 75 1 85 1 86 1 87 1 102 1 103 1P13cafc67618f08cd 1 2 32 3 0 1 102 1 105 1 32 10 41 1 47 1 66 1 75 1 78 1 85 1 86 1 87 1 103 1 104 1 2 106 2 107 2P13da647a345bfced 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P13fa36207a022766 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P146788064845ee14 0 7 0 1 41 1 66 1 75 1 85 1 102 1 103 1P14927681b10aa5b8 1 2 32 3 0 1 103 1 106 1 32 10 42 1 48 1 67 1 76 1 79 1 86 1 87 1 88 1 104 1 105 1 2 107 2 108 2P14a6d871a23446e7 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P14d37172469232f4 0 6 0 1 49 1 58 1 68 1 85 1 86 1P1514fdf210b363e6 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P151de53aa340205b 1 2 32 3 1 1 103 1 106 1 32 10 42 1 48 1 67 1 76 1 79 1 86 1 87 1 88 1 104 1 105 1 2 107 2 108 2P15ee9fce72d5de94 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P167e5fc4a44beb2d 0 6 0 1 49 1 58 1 68 1 85 1 86 1P1680239a77b9c457 1 2 32 3 0 1 102 1 105 1 32 10 41 1 47 1 66 1 75 1 78 1 85 1 86 1 87 1 103 1 104 1 2 106 2 107 2P169d7086edd7af72 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P16c04e29febbde94 0 4 0 16 66 16 85 16 86 16P16df27db4a55956d 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P171f51fe879b59ea 0 8 1 1 42 1 67 1 76 1 86 1 89 1 103 1 104 1P1726419b03b94ea2 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P1755a31d986555b1 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P17705ced3fd00bda 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P17e90c59f5a88228 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P180d8e457da8ac7e 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P1859764aa3b860fe 1 2 32 3 0 1 103 1 106 1 32 10 42 1 48 1 67 1 76 1 79 1 86 1 87 1 88 1 104 1 105 1 2 107 2 108 2P1880c4c2e17c259c 0 4 0 1 67 1 85 1 86 1P18ada85dbc311e44 0 6 0 1 49 1 58 1 68 1 85 1 86 1P18eb290b72d4f16c 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P1921f1197e88207c 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P1959f5b19f55d6f7 0 6 0 1 31 1 61 1 84 1 102 1 103 1P195c85d213dc16cf 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P196afe2508c944af 0 5 0 1 35 1 67 1 85 1 86 1P19b21b5a030a3168 0 6 0 1 49 1 58 1 68 1 85 1 86 1P19d0870616ba8ad2 0 4 0 1 67 1 85 1 86 1P1a0b1c2d5cb78cf5 0 5 0 1 35 1 67 1 85 1 86 1P1a3e8fc4d56bd67e 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P1bb2df3d790987cf 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P1d001051fd1c62ae 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P1d9b399f8e8fccbb 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P1dae9bdb793222b4 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P1daf25a6e0d95cce 0 4 0 1 67 1 85 1 86 1P1dd3f195ce57fc52 0 4 0 1 67 1 85 1 86 1P1e428f38c73070a7 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P1e4a67a1990b17eb 0 5 0 1 35 1 67 1 85 1 86 1P1ea72f9d77c5eb68 0 6 0 1 49 1 58 1 68 1 85 1 86 1P1ef7e15684b4e17a 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P1f0132220ceba127 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P1f48ce2dc1886bbe 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P1f4e5647498005b9 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P1f96d586a1d9b005 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P1fc5b4d87402f54b 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P1ffcc278ffe68ccf 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P20de1930ec01d1e0 0 5 0 1 35 1 67 1 85 1 86 1P20e1cb4295af0d7d 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P2112b2470592a9ba 0 4 0 1 67 1 85 1 86 1P211a84dcba4f9c83 0 5 0 1 35 1 67 1 85 1 86 1P212aabc942547b94 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P212dabadb8d01cba 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P216ca9cf2b8b5280 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P21d4cbce305abdb5 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P2230398b7ed75416 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P223d1990d3e53d1b 0 4 0 1 67 1 85 1 86 1P2328f0a420808c3f 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P23305259993223db 0 8 1 1 42 1 67 1 76 1 86 1 93 1 103 1 104 1P23ebab8636b4e636 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P242af4da357e909a 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P242c272c967cce40 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P244b21d884176bd8 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P2510b93440cbb9aa 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P2604548b82863b74 0 4 0 1 67 1 85 1 86 1P26147ba695d4392b 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P262d98d57f0ff3ac 1 1 16 3 0 1 103 1 104 1 4 61 2 102 2 105 2 106 32P26c5d187b3734a7b 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P270356470c5ea3c8 0 8 0 1 41 1 66 1 75 1 85 1 92 1 102 1 103 1P2759f0d2c770be03 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P27621b821172cc61 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P279b478db19ec7ab 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P27b2126d49e57f22 0 4 0 1 67 1 85 1 86 1P27b902103da8a811 0 7 0 1 41 1 66 1 75 1 85 1 102 1 103 1P28c71ad8bc2546e4 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P28d2d1e19a6c14e0 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P28db42535a57c178 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P29239f64e9130823 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P293bcd95a8e47b27 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P295ea0cc109881f4 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P29830d49d6c0a3d0 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P29d1ca9f91588295 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P2a30a238038dfcd5 0 6 0 1 49 1 58 1 68 1 85 1 86 1P2a6df039d0ed74be 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P2beedf549fb6ed63 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P2c147c970081349e 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P2c3a1eb8e1b9846f 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P2c3a86fce1d5e6d7 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P2c46705621e35a7b 0 6 0 1 49 1 58 1 68 1 85 1 86 1P2ca89e51877d760d 0 4 0 1 67 1 85 1 86 1P2cf631576571ef44 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P2d28ddc44e0db169 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P2d3f378d865c1025 1 2 32 3 0 1 103 1 106 1 32 10 42 1 48 1 67 1 76 1 79 1 86 1 87 1 88 1 104 1 105 1 2 107 2 108 2P2e13823f03fde94f 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P2e7bfa895fc72feb 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P2e9f7ee09f07b466 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P2ed960905480156c 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P2ee92fa13b24078f 0 5 0 1 35 1 67 1 85 1 86 1P2f3752986cc653f5 1 2 32 3 0 1 104 1 105 1 32 3 1 1 103 1 106 1 2 107 2 108 2P2f58800c98aae70d 0 3 0 1 32 1 47 1P2f9f01929ced9887 0 5 0 1 35 1 67 1 85 1 86 1P30d6879049fbee00 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P30db1a847cf8f753 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P3179903dd15f46ec 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P323549664a75fe5b 0 6 0 1 49 1 58 1 68 1 85 1 86 1P3251936ff8e3ac8d 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P32663c9fdd6582c2 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P32f8a6ab9b049421 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P33551fafb761f81a 0 4 0 1 67 1 85 1 86 1P340185931c57bf9b 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P34120b538579a311 0 7 1 1 50 1 59 1 69 1 76 1 86 1 87 1P34d21e8a0ba6b320 1 1 16 3 1 1 27 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P34dd44f00549eab9 0 5 0 1 35 1 67 1 85 1 86 1P352686d38f94e686 0 4 0 1 67 1 85 1 86 1P355beeea2d9dd4c0 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P3570eb8d6b249621 1 1 16 3 0 1 104 1 105 1 10 48 1 67 1 76 1 79 1 86 1 87 1 88 1 103 1 106 1 107 16P3592f04385c73429 0 6 0 1 49 1 58 1 68 1 85 1 86 1P35be6e296ba202dd 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P35d00b43564b5e51 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P35eeb8c7de4f09a4 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P36dbedc0eb868b6b 1 1 16 3 0 1 104 1 105 1 10 48 1 67 1 76 1 79 1 86 1 87 1 88 1 103 1 106 1 107 16P36efcdbe46ec5eeb 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P375e0e43f2e2cdc0 0 4 0 1 67 1 85 1 86 1P379aaffb2a80dee4 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P37c04fbf31938cc3 1 2 16 2 0 1 87 1 16 2 1 1 86 1 2 88 1 89 1P37c6705da45f11bd 1 1 16 2 0 1 85 1 3 7 1 86 1 87 16P38171e7629ae68c4 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P387ddd3b8a2cf4ec 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P38fd3f4a84e9d97a 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P397da0e24e350130 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P39c5451510e3ac85 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P3a33515077bb2831 0 4 0 1 67 1 85 1 86 1P3a586ed6d6288800 0 3 0 1 48 1 67 1P3a8b2743cb272c1e 1 1 16 3 0 1 104 1 105 1 10 48 1 67 1 76 1 79 1 86 1 87 1 88 1 103 1 106 1 107 16P3abab7f3db358832 1 1 16 2 1 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P3b1e9a6ee47d913c 1 1 16 4 1 1 29 1 44 1 86 1 9 49 1 50 1 59 1 62 1 69 1 70 1 71 1 87 1 88 16P3b94d178f6afe901 0 6 0 1 49 1 58 1 68 1 85 1 86 1P3bb7786c0b3e72dc 1 1 64 2 0 1 102 1 3 6 1 103 1 104 64P3bc60113f3566ab8 0 7 1 1 50 1 59 1 69 1 74 1 86 1 87 1P3bd8e40f06eefaee 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P3c05fd26d9aa0cc7 0 7 0 1 49 1 58 1 68 1 73 1 85 1 86 1P3c7acdc98564031d 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P3cbcc50d57020ba0 0 6 0 1 66 1 75 1 85 1 102 1 103 1P3ce3c1ca17b2fb49 0 8 0 1 49 1 58 1 68 1 69 1 70 1 85 1 86 1P3d69bc9167306a7b 1 2 16 3 1 1 27 1 86 1 16 3 0 1 28 1 87 1 2 88 1 89 1P3d85f10dc43a1db5 0 7 0 1 49 1 58 1 68 1 75 1 85 1 86 1P3d9ec9dc77aa0245 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P3dceb535ef769fc7 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P3e0b69044f608430 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1P3e36f7eeff51f9c3 0 10 2 1 51 1 60 1 61 1 63 1 70 1 71 1 72 1 87 1 88 1P3ed101ef8f06e995 0 6 0 1 49 1 58 1 68 1 85 1 86 1P3faca2d41f4ae40d 0 7 1 1 50 1 59 1 69 1 72 1 86 1 87 1N0276a3202df3b5fcN02b12a9072dd576fN032efb7f78ede598N039eb01c3af0b03dN03fd1436f086524eN05e39c2e95149a20N05fe849beab41160N06a4c1189a24d05eN06a7a330a2df1feeN06af624b31a580cdN06e490d911d8f852N07726360d0155c2dN084a0f6b1b9074cbN089421ddaffd3743N09103d481901b089N09ad89aaa7139e35N0aa0382dbd2f39ffN0c8946411697d898N0cbcbd3408887107N0d6ea33070e3a756N0d894dd4cdae73c2N0e311f1a631f7b63N0eebc742bfaf5e6bN0ef06ebba9d67f0dN0fbf364a6eb0449bN1034a68fe9104e99N10de28ee33a14e33N10ed6aa2baac6bdcN10feff29aa178f01N1218165e07b8da7bN12ca204905880debN13610ecb87b4fae5N13e5c487a61beaa3N1476d36e36434882N14adf5049a0a199aN14e48a64194c0c3bN15f7ca3e297daaafN179030cbfd556374N186f128a2d72d267N1a0ee7a588f7fa55N1c3065d04b59e653N1d567c156b78f4eaN1f3c60b4202f987cN2152c2efd2a340feN21a8fd4519898e63N21e032d42be43778N22745528016265eaN22a4e49dbdf869bdN2308d93051bf4c83N231f0d5b80cc2668N23ed239c3f7fd1a3N23fb126aaf68c76bN241a181ab208e004N2539d69a2449b654N2659d8dfc6d07185N2731757df0f1ae78N27fbe49e18dafd8aN28f299066e183d7eN293516740cb94649N29ab2d467ef86c80N2a33de1c7a62276eN2a46399aef4da762N2ad8bc53adf50f59N2b6c5995a0679998N2deb22a951a7161cN2e314d785d0b296fN2f294b0ede8a3f61N2f29ba149a85fc77N2f68696310d78721N3015ab21e569a188N303cf94128342543N31c913216e2f6aafN330741be50df0992N33da838a0e5737b7N345492310dc1b67dN34a3b1b9e60de378N366ca7984ddba7edN3690da2e404485edN36c954e9a8ff739fN36dca0b350a4cef8N3707510bbbd9c3a3N37280a267bbd0445N37884062fffdbbf5N3828dc6abc9e4612N39996cf6452a46ddN39ab209cb352cbfeN39d0637be2193762N3a3cfd60c9b503d2N3c821f10af1bb2a5N3caedb9059a3ce60N3cc5c927910044f3N3d8b0913920a7747N3dd6b18d901c8110N3f463cceb81d4258N3fc03a54e3b0bc89"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_signer_A () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_bcmp"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_signer_stmt.A_PKCS7_SIGNER"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIn : Z -> Z) (FFRn : Z -> Z -> Z) (CNTn : Z -> Z) (STKn : Z).
  Hypothesis STKn0 : 0 <= STKn.
  Hypothesis NAM0 : 0 <= arl_need_amem R.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55857805827.17000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKsg : Z := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signer_A ()) "(0.+=0.(1.(1.VSTKn,+1070.)(1.(0.+130.(2.VR,))(1.(0.+70.(3.VR,))(1.(4.VR,)(5.VR,))))))")
(* [comment removed for export] *).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 2)%nat.
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
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKsg.
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
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold STKsg in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signer_A ()) "Lms,$6.(7.$8.LFB,$8.(7.$8.Lsp1,$8.(7.(9.$:.VR,VHIA,)Lh1,(9.$:.VR,VHIA,)(7.P,(;.&40.)(<.(;.&8.))Lm1,P,(;.&40.)(<.(;.&8.))(7.(;.&40.)Lx1,(;.&40.)(7.(;.&40.)Lt0,(;.&40.)(7.(;.&40.)Lt1,(;.&40.)(7.(;.&40.)Lt2,(;.&40.)(7.(;.&40.)La0,(;.&40.)(7.(;.&40.)La2,(;.&40.)(7.(;.&40.)La3,(;.&40.)(7.(;.&40.)La4,(;.&40.)(7.(;.&40.)La5,(;.&40.)(7.(;.&40.)La6,(;.&40.)(7.(;.&40.)La7,(;.&40.)(7.(;.&40.)Lt3,(;.&40.)(7.(;.&40.)Lt4,(;.&40.)(7.(;.&40.)Lt5,(;.&40.)(7.(;.&40.)Lt6,(;.&40.)(7.(;.&40.)Lw0,(;.&40.)(7.(;.&40.)Lw1,(;.&40.)(7.(;.&40.)Lw2,(;.&40.)(7.(;.&40.)Lk0,(;.&40.)(7.(;.&40.)Lk8,(;.&40.)(7.(;.&40.)LkE,(;.&40.)(7.(;.&40.)Lk16,(;.&40.)(7.(;.&40.)Lk24,(;.&40.)(7.(=.(;.&8.))LjA,(=.(;.&8.))(7.(=.(;.&8.))LjB,(=.(;.&8.))(>.(?.$6.R1>.(10.(11.R19.(12.&40.R1<.)Vgp,Vtp,R18.R17.R16.Vsp,(12.&40.R1<.)R15.(12.&40.VEND,)R14.R13.R12.R11.R10.R?.(12.&40.R1=.)(12.&40.VSIG,)(12.&40.VPP,)(12.&40.VDALG,)Vs6,(12.&40.(0.R1=.+20.))Vs8,(12.&40.(0.(13.R1=.+3.)(14.(15.VR,))))(12.&40.(14.(15.VR,)))(12.&40.R1=.)R>.R=.R<.R;.)VF,(12.&40.+98?9<.)Vfc,(16.(;.&40.))R1:.(17.$:.)))(>.(>.(18.(19.(1:.&40.Vsp,)+=0.)R1<.)(18.R1<.(19.(1:.&40.Vsp,)+<0.)))(>.(?.$8.(1;.R1<.+20.)=)(>.(1<.$:.VR,VHIA,R1;.VLB,(1=.(1>.$8.$8.)(1?.$8.$8.R1=.+40.)VLF,)R1:.)(>.(?.P,$8.Sp(20.$:.VR,VHIA,R1;.)(20.$:.VR,VHIA,Vh,))(>.(?.$8.(21.$:.VR,VHIA,R1;.)(21.$:.VR,VHIA,Vh,))(>.(?.$8.(22.$:.VR,VHIA,R1;.)(22.$:.VR,VHIA,Vh,))(>.(?.$8.(23.$:.VR,VHIA,R1;.)(23.$:.VR,VHIA,Vh,))(>.(?.$8.(24.$:.VR,VHIA,R1;.)(24.$:.VR,VHIA,Vh,))(>.(?.$8.(25.$:.VR,VHIA,R1;.)(25.$:.VR,VHIA,Vh,))(>.Pmo,$26.(27.(28.$:.VR,VHIA,R1<.R1.)(28.$:.VR,VHIA,Vh,R1.))(>.(?.$8.(1;.R1=.+40.)=)(>.(29.VR,VLB,VLF,R1=.+40.)(>.(2:.$:.R1:.R1=.(1=.$2;.(2<.R:.)(1=.$2;.(2<.R9.)(1=.$2;.(2<.R8.)(2=.$2;.)))))(>.(2:.$:.R1:.(0.R1=.+20.)(1=.$2;.(2<.(12.&40.=))(2=.$2;.)))(>.(2:.$:.R1:.(0.(13.R1=.+3.)(14.(15.VR,)))(1=.$2;.(2>.(12.&8.+?1.))(1=.$2;.(2>.(12.&8.+?1.))(1=.$2;.(2>.(12.&8.+?1.))(1=.$2;.(2>.(12.&8.+?1.))(1=.$2;.(2>.(12.&8.=))(1=.$2;.(2>.(12.&8.+?3.))(1=.$2;.(2>.(12.&8.+?3.))(1=.$2;.(2>.(12.&8.+?3.))(2=.$2;.))))))))))(>.(2:.$:.R1:.(0.(1:.&40.Vsp,)-68.)(1=.$2;.(2<.Vs11,)(1=.$2;.(2<.Vs10,)(1=.$2;.(2<.Vs9,)(1=.$2;.(2<.Vs8,)(1=.$2;.(2<.Vs7,)(1=.$2;.(2<.Vs6,)(1=.$2;.(2<.Vs5,)(1=.$2;.(2<.Vs4,)(1=.$2;.(2<.Vs3,)(1=.$2;.(2<.Vs2,)(1=.$2;.(2<.Vs1,)(1=.$2;.(2<.Vs0,)(1=.$2;.(2<.Vra,)(2=.$2;.)))))))))))))))(>.(2:.$:.R1:.R1<.(1=.$2;.(2?.#18.R2.)(1=.$2;.(2<.R6.)(1=.$2;.(2<.R7.)(1=.$2;.(2<.R5.)(1=.$2;.(2<.R4.)(1=.$2;.(2<.R3.)(1=.$2;.(2?.#10.R1.)(1=.$2;.(2<.(12.&40.R1=.))(2=.$2;.))))))))))(>.(30.$:.R1:.(0.R1<.+58.)(0.(1:.&40.Vsp,)-68.))(>.(30.$:.R1:.Vlo,R1<.)(>.(31.$:.R1:.)(>.(2:.$:.R1:.VPP,(1=.$2;.(2<.(12.&40.VP,))(2=.$2;.)))(>.(2:.$:.R1:.VSIG,(32.==Vsj,))(>.(2:.$:.R1:.VDALG,(33.Vdtg,Vdpad,Vdlen,Vdq,))(>.(34.$:.R1:.VBUF,Vbs,)(>.(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)R1:.VPP,+8.)(>.(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)R1:.VSIG,+<8.)(>.(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)R1:.VDALG,+18.)(>.(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)R1:.VBUF,(36.(37.(;.&8.)Vbs,)))(>.(38.(18.(0.R1=.+40.)VPP,)(18.(0.VPP,+8.)R1=.))(>.(38.(18.(0.R1=.+40.)VSIG,)(18.(0.VSIG,+<8.)R1=.))(>.(38.(18.(0.R1=.+40.)VDALG,)(18.(0.VDALG,+18.)R1=.))(>.(38.(?.$8.(36.(37.(;.&8.)Vbs,))=)(38.(18.(0.R1=.+40.)VBUF,)(18.(0.VBUF,(36.(37.(;.&8.)Vbs,)))R1=.)))(>.(39.$:.VR,VHIA,Vh,VLB,VLF,(1:.&40.Vsp,)(1:.&40.Vsp,)(2=.$3:.)Vm,R1:.)(3;.$:.(15.VR,)R1:.Vslo,(1:.&40.Vsp,)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 D3; try lx_pin1 D2; try lx_pin1 D1; try lx_pin1 Q3; try lx_pin1 Q2; try lx_pin1 Q1; try lx_pin1 ALD; try lx_pin1 DSB; try lx_pin1 ALS; try lx_pin1 DPB; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 B3; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 ALP; try lx_pin1 sj; try lx_pin1 dq; try lx_pin1 dlen; try lx_pin1 dpad; try lx_pin1 dtg; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 NRT; try lx_pin1 STKn0; try lx_pin1 CNTn; try lx_pin1 FFRn; try lx_pin1 PHIn; try lx_pin1 GETTAG; try lx_pin1 FREE; try lx_pin1 CALLOC; try lx_pin1 HMND; try lx_pin1 DIMG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0250@D10637083020.192D10639329459.112D14196765248.192D18512717141.193D18514816885.113D18607476203.160D2457697672.191 D3162359811.192 D32458983507.191D3254889317.159 D32604263327.194D3267764854.160 D3385912464.190 D36106837486.192D42574804762.193D43510757705.193D45254614292.193D45702202657.190D46793042006.112D46795284841.192D50254960491.161D51038213418.161D55346665922.161D55346665922.162D55346665922.163D560907438.114  D60098777666.113D60109264994.193D60109265005.192D60111245650.112D61005654077.193D61016138269.113D62011770180.194D62011770188.114D65008438061.191D68409210579.190D6897083606.190 L10775412921.169L10837002389.2  L12654381620.1  L15756354262.7  L17193996438.1  L17607390836.171L1832968857.11  L19548981073.171L19980016842.11 L21980071943.1  L24524441946.123L26892418956.1  L27729706458.187L29738741675.1  L31170831519.166L33483560980.12 L33485826452.1  L35653441506.10 L38308634325.0  L39076636629.0  L39280637297.0  L39332637397.0  L40226756952.1  L40228640085.0  L43055369633.134L45363093875.197L45703525153.0  L48117620909.98 L48119718058.167L48119718061.166L49130057368.11 L50790731766.10 L51038230838.188L53537894342.3  L54437681876.8  L57355539152.169L57355539152.171L58790154276.11 L59308634497.16 L60098763854.6  L61437265048.2  L67922604617.0  L6910010088.166 L7040749983.124 L7715476710.136 L9356559645.15  P1056307012.161 P28348577804.161P54301534716.161Q10533598597.116Q10594483354.198Q11276122434.199Q11288706168.116Q13345046842.116Q13349241856.199Q1530342990.161 Q23216651711.198Q23937998252.116Q23937998260.118Q31021924279.158Q31158247845.197Q31158247869.201Q31170831519.199Q31599749226.116Q31603944784.199Q32440833928.197Q36104740330.199Q38248895665.119Q40271359350.161Q41137788007.116Q41150370141.199Q42439168719.158Q42439382255.120Q42441479404.203Q43880146029.119Q45252517151.199Q47241206720.116Q48119718060.198Q48132302231.197Q50796826103.161Q56533317808.198Q59310664043.116Q59310664043.197Q59323247696.198Q59323247697.199Q59865520176.120Q59867617331.203Q6192914196.158 Q62022254700.118Q62022254708.116Q64681502661.203Q64683599814.120Q6897428426.201 Q6897428434.197 Q6910010088.199 Q9350548487.142 00000]01J01K02902f02g02h02i03S03T04E04F04G04H04I04J04K05505b06O06P07;07<07=08008c09W0:H0;90;m0<[0=H0>20>_0?I0?J0@40@f0@n0A30AA0AF0B:0BB0C60CS0CW0DM0DQ0E;0E?0E^0E_0E`0F=0F>0F?0F@0FA0FF0FG0GK0H:0H;0I70Ie0JS0J[0K?0Km0L90LS0LT0ML0Mf0N70NA0NI0NJ0Ni0OS0P@0Pn0QY0RE0S20S_0T>0T?0T@0TA0TB0Ti0UH0VD0W40Wb0XA0X`0Y?0Y@0YA0YB0YC0Z00ZR0ZS0ZT0[90[l0\Q0]A0]B0^00^^0_L0`60`70`80`90`:0`;0`<0`=0`]0aG0b10bc0cc0dB0da0e@0ehS1R4STKn2LF2sp2PP2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABFS1R4STKn2LF2sp3SIG2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABFFFS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBFS1R3HIA4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2h12FBFFFFFFS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2sp2PP2bs3LFB4lxHn3sp13H304LFB'2FBFS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H283H304LFB'FFS1R4STKn2LF2sp4DALG2bs3LFB4lxHn3sp13H304LFB'3x142HxS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS3PPB3SGB3DABS1R4STKn2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS3PPB3SGB3DABS1R4STKn2LF2sp3SIG2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBFS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBS1R4STKn2LF2sp3slo2bs3LFB4SLOS3ALO4lxHn4LFB'2FB2F1S3BUF2bsS3BUFS1R2lo3LOS3ALOS3sp1S1R4STKn2LF2sp2bs3LFB3SPR4lxHn3sp13H304LFB'2FB2F02F8S1R4STKnS1R4STKn2LF2sp2bs3LFB3SPR4lxHn3sp13H304LFB'2FB2F02F8S1R3HIA4STKn1h2sp3TOP3sp13SP1S2spS1R4STKn2LF2sp2bs3LFB3SPA3SPR4lxHn3sp13H263H273H283H30S2spS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FBS2FBS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBFFS1R3HIA4STKn1h2sp2lo3TOP4HTOPSSSSS3sp1SS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PP03SG03DA03SLO3SPR3PPB3SGB3DABS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H304LFB'2FB1c2HcSS1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3SLO3LOS3ALO3PPB3SGB3DABS1R4STKn2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R4STKn2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R4STKnS1R4STKn2sp2lo3slo4SLOS4SLOL3SLO3LOSS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H283H304LFB'2FBS2sp3sp13SP1S1R4STKn2sp2lo3SLO3sp13SP1FS1R4STKn2LF2sp2bs3LFB3ACV3SPR4lxHn3sp13H304LFB'2FB2F02F1S1R4STKn2sp2lo3SLO3sp13SP1S1R4STKn2FB2F02KbS1R2lo3LOSS2LF3LFBSS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2sp2bs3LFB3SPR4lxHn3sp13H263H30S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R3NS14STKn2sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R4STKn2LF2PP2lo2bs3LFB4PPLO4lxHn3sp14LFB'S1R4STKn2LF3SIG2lo2bs3LFB4SGLO4lxHn3sp14LFB'S1R4STKn2LF4DALG2lo2bs3LFB4DALO4lxHn3sp14LFB'S1R4STKn2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBFFFFS1R4STKn2LF2sp2bs3LFB4lxHn3sp13H284LFB'S1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R3HIA4STKn1h2LF2sp2PP3SIG4DALG2bs3LFB3TOP4HTOP3PPB3SGB3DABS1R3HIA4STKn1h2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R3HIA4STKn1h2LF2sp2bs3LFB3TOP4HTOP4lxHn4LFB'S1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBFFFFS1R4STKn2LF2PP3SIG4DALG2lo2bs3LFB3PPB3SGB3DABS1R3HIA4STKn1h2LF2bs3LFB4lxHn4LFB'FFS1R4STKn2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R4STKn2LF2PP3SIG4DALG3slo2bs3LFB4SLOS3PPB3SGB3DABS1R4STKn2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R4STKn2LF2sp2PP3SIG4DALG2lo2bs3LFB3PPB3SGB3DABFS1R4STKn2LF2PP3SIG4DALG2bs3LFB3ALO3PPB3SGB3DABS1R4STKn2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R4STKn2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R4STKn2LF2sp2lo2bs3LFB3SLO3LOS4lxHn4LFB'FFFFFFFS1R4STKn2LF2bs3LFB4lxHn3sp14LFB'S1R4STKn2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R4STKn2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R3HIA4STKn1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn4LFB'S1R3HIA4STKn1h2LF2sp2PP3SIG4DALG3slo2bs3LFB3TOP4HTOP3PPB3SGB3DABS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2bs3LFB4lxHn4LFB'2FBS1R4STKn2LF2bs3LFB4lxHn3sp13H293H304LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS DALO CRDA DA0 HDA SGLO CWS SG0 HSG BIN HBY PPLO CWP PP0 HPP LFB NAM0 STKn NS1 SM0 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signer_A ()) "Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)P,(1<.$:.VR,VHIA,Vh,VLB,VLF,Vm,)P,(30.$:.Vm,Vlo,(1:.&40.Vsp,))P,(3;.$:.(15.VR,)Vm,Vslo,(1:.&40.Vsp,))P,(31.$:.Vm,)P,(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)Vm,VPP,+8.)P,(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)Vm,VSIG,+<8.)P,(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)Vm,VDALG,+18.)P,(35.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)Vm,VBUF,(36.(37.(;.&8.)Vbs,)))(3<.$:.(15.VR,)(20.$:.VR,VHIA,Vh,)$3=.(10.(11.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(12.&40.VPP,)(12.&40.VEND,)(12.&40.VSIG,)(12.&40.VDALG,)R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(12.&40.$3>.)Vfc,(16.(;.&40.))Vm,(17.$:.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST SS MI OPP OSG ODA OBUF.
  unfold A_PKCS7_SIGNER.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 TOP HTOP; lia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(clear - LOS SLO NS1; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add length] in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSG) as SGB.
  cbn [cells_size csize Nat.add length signer_cells] in SGB.
  pose proof (rw_cells_bound _ _ _ _ HDA) as DAB.
  cbn [cells_size csize Nat.add length buf_cells] in DAB.
  destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _].
  rewrite Forall_forall in BR.
  destruct (BR _ ltac:(apply in_or_app; left; exact BIN)) as (_ & _ & BCE & BIMG).
  cbn [fst snd] in BCE, BIMG.
  clear BR.
  (* [comment removed for export] *)
  pose proof (conj HBY (conj HPP (conj HSG (conj HDA (conj OPP (conj OSG (conj ODA (conj OBUF I)))))))) as EBOX.
  clear OPP OSG ODA OBUF.
  carve_frame 192%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 365%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -192) ST ltac:(clear - SP1 SLO NS1; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (unfold LFMAX_CRT in LFB; clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | clear - SLO SP1 TOP NS1; lia
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
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). kland Kb.
          rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 0) with 64 in *. change (8 * 2 ^ 0) with 8 in FSH. change (Z.to_nat 64) with 64%nat in FRM. change (Z.to_nat 8) with 8%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 FB 64 FRSH CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APSG.
      assert (APD : FB + 64 <= DALG \/ DALG + 24 <= FB).
      { eapply (fresh_apart_client R LB LF lo DALG 24 FB 64 FRSH CRDA); [clear; lia| clear; lia| clear - ALO LOS; lia]. }
      assert (APB : n = 0 \/ FB + 64 <= BUF \/ BUF + n <= FB).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right]. destruct FRSH as (_ & _ & _ & F3'). apply F3'. apply in_or_app. left. exact BIN. }
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -192) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -192) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 88) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 88) 88 STlo ltac:(clear; lia)) as [_ [jrs RSL]]. clear STlo.
      replace (sp1 + 88 - Z.of_nat 88) with sp1 in RSL by (clear; lia).
      apply (rw_cells_split_CB asegs m3 sp1 [] 88 jrs [] [24; 8; 8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity]. cbn [mk_CB_cells app] in RSL.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: _) => cb8_to_c8 RSL [c0] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb8_to_c8 RSL [c0; c1] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb8_to_c8 RSL [c0; c1; c2] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 RSL [c0; c1; c2; c3] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => cb8_to_c8 RSL [c0; c1; c2; c3; c4] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: _) => cb8_to_c8 RSL [c0; c1; c2; c3; c4; c5; c6] end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 8; 16; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      chunk_split FREST 1%nat FLNK FRMb. chunk_split FRMb 1%nat G4 FRMc. clear FLNK FRMc.
      lazymatch type of G4 with rw_cells _ _ ?a _ => replace a with (FB + 32) in G4 by (clear; lia) end.
      cb8_to_c8 G4 (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_hide1 EBOX. lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x98f9c] [] 365%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  (* [comment removed for export] *)
      destruct EBOX as (HBY' & HPP' & HSG' & HDA' & OPP & OSG & ODA & OBUF & _).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HPF;
        assert (CRP : client_range L (LB ++ fdata LF) (bv_unsigned sp) PP 8) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWP)| exact PPLO]);
        assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) SIG 200) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWS)| exact SGLO]);
        assert (CRD' : client_range L (LB ++ fdata LF) (bv_unsigned sp) DALG 24) by (eapply client_range_lower; [exact CRDA| exact DALO]);
        assert (CRB : client_range L (LB ++ fdata LF) (bv_unsigned sp) BUF n) by (eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]);
        assert (OPP1 : aobj asegs AL CS mx PP 8);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OPP | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRP| clear; lia] ] |];
        assert (OSG1 : aobj asegs AL CS mx SIG 200);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OSG | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRS| clear; lia] ] |];
        assert (ODA1 : aobj asegs AL CS mx DALG 24);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact ODA | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRD'| clear; lia] ] |];
        assert (OBUF1 : aobj asegs AL CS mx BUF n);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OBUF | intros xq Hxq; eapply hcs_below_top; exact Hxq
                              | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right; split; [exact CRB| clear; lia]] ] |];
        assert (HB1 : bytes_at asegs mx BUF bs);
        [ eapply presA_bytes_at0; [exact HPF| exact HBY'| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right; split; [exact CRB| exact I]]] |];
        assert (HPP1 : rw_cells asegs mx PP [C8 (Z_to_bv 64 P)]);
        [ eapply presA_rw_cells; [exact HPF| exact HPP'| exact CRP| exact I] |];
        assert (HSG1 : rw_cells asegs mx SIG (signer_cells 0 0 sj));
        [ eapply presA_rw_cells; [exact HPF| exact HSG'| cbn [cells_size csize Nat.add length signer_cells]; exact CRS| exact I] |];
        assert (HDA1 : rw_cells asegs mx DALG (buf_cells dtg dpad dlen dq));
        [ eapply presA_rw_cells; [exact HPF| exact HDA'| cbn [cells_size csize Nat.add length buf_cells]; exact CRD'| exact I] |];
        clear HPF end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      repeat match goal with |- _ /\ _ => split end;
        first [ eassumption | exact PRES
              | lazymatch goal with
                | |- _ \/ _ => first [exact APP | exact APSG | exact APD | exact APB]
                end
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
