(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_x509_seq_stmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007e473fedd4043e 0 6 0 1 55 1 64 1 65 1 72 1 73 1P009ed63e69872591 0 6 0 1 59 1 60 1 82 1 86 1 91 1P00a926c75d5c39d7 0 6 0 1 55 1 64 1 65 1 72 1 73 1P0151d8f72f8610f1 0 7 0 1 36 1 75 1 84 1 85 1 92 1 93 1P015ab5b28fdc16d7 0 2 0 1 55 1P01e6242550a47193 0 6 0 1 55 1 64 1 65 1 72 1 73 1P022d58911ebf657d 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P024416d05b00d936 0 6 0 1 55 1 64 1 65 1 72 1 73 1P0262cad32113f860 0 5 0 1 35 1 54 1 72 1 73 1P028b5e1aa022e38a 0 6 0 1 55 1 64 1 65 1 72 1 73 1P02a43952c64d6848 1 1 16 3 0 1 93 1 94 1 4 56 2 92 2 95 2 96 32P02e4b73025052bc6 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P03090ef37f75ddf0 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0336d6fd637b502e 0 5 0 1 35 1 54 1 72 1 73 1P034a77e32b66a502 0 6 0 1 55 1 64 1 65 1 72 1 73 1P03d9de8d9e8c7e17 0 4 0 1 54 1 72 1 73 1P04276f1de6d6069f 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P0443bfa44e176698 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P0515a12f98512156 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P051f7bcd58c94e60 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P052f71039dcbbf56 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P068fbb0885803fce 1 2 32 3 0 1 92 1 95 1 32 10 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 93 1 94 1 2 96 1 97 1P0732c8fe8eaacaa9 0 5 0 1 35 1 54 1 72 1 73 1P074b48aa0b39136b 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P077b58775b399d44 0 6 0 1 75 1 84 1 85 1 92 1 93 1P07894fc140b7ab0e 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P07fc1858edefbfea 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P0898104bc00f47e8 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P08add556aadc8002 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P08b5a6c8bcb96e2c 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P08b7e9ecff657019 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P090c4e1316fe3918 0 3 0 1 41 1 50 1P09562aa35c22ce9f 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0997f22db4445abe 0 2 0 1 59 1P099f72620fa100fa 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P0a06caf85537eab6 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P0a2fe200a15ab560 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0a63edac1fb13a5d 0 5 0 1 35 1 54 1 72 1 73 1P0a7368414aace0fc 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P0aa2b8cd4e85916c 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P0accdd232632410c 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0acd2f2d3130bd64 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P0b267b651204abb5 0 6 0 1 59 1 60 1 82 1 86 1 91 1P0b60b9ddbfccb8b8 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0b91b1dcc20f0825 0 6 0 1 55 1 64 1 65 1 72 1 73 1P0c5299546d2d5f7f 1 1 16 3 0 1 94 1 95 1 4 57 2 93 2 96 2 97 32P0c567022a3ea2b20 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P0c576dfa2773bfdb 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P0c72e08cc603aa89 0 3 0 1 83 1 84 1P0c9f80cf1088d13b 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P0ca2b8b2da572615 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P0ccb8e5d2cbad7d3 0 6 0 1 55 1 64 1 65 1 72 1 73 1P0d163da9b524a02d 1 2 8 2 0 1 95 1 8 2 88 1 96 1 2 97 1 98 1P0d8d1ee75363c9af 0 4 0 1 54 1 72 1 73 1P0dcdefd3796456a9 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P0dd8b7d371ae59a1 0 5 0 1 35 1 54 1 72 1 73 1P0ebdeb65cfecb203 1 1 16 3 0 1 94 1 95 1 7 42 4 76 4 85 4 86 4 93 4 96 4 97 64P0eed40106c7a7cea 1 2 32 3 0 1 93 1 96 1 32 3 1 1 94 1 95 1 2 97 2 98 2P0f1f8ebbc85e97b3 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P0f51c59ce75937df 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P0f5f337596388b1f 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P0fe98d293bd6c851 0 5 0 1 60 1 82 1 86 1 93 1P10c034005a44b2aa 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P1138739371d6a075 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P115bb9a7d1eb4777 0 6 0 1 53 1 56 1 74 1 92 1 93 1P124c91ff5b6f7601 0 2 0 1 54 1P12919052cdbb963e 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P12ca0ddd3671ddd0 0 6 0 1 55 1 64 1 65 1 72 1 73 1P1364d7c7cb6ba564 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P1407a9ccdc7cad9b 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P144f6f02bab2ef2c 0 11 2 1 38 1 65 1 74 1 77 1 78 1 79 1 86 1 87 1 94 1 95 1P1452570b7245fe4a 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P14b2a530194f1355 0 6 0 1 55 1 64 1 65 1 72 1 73 1P1538a950541995d6 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P16105f367ed885e0 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P16ec35632e90e418 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P1722a985f6e1a9d1 0 8 0 1 36 1 75 1 82 1 84 1 85 1 92 1 93 1P174c67bd75b649a9 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P17b187baad1af80a 0 8 0 1 59 1 65 1 75 1 77 1 84 1 89 1 90 1P17d15bacebd4a833 1 1 64 2 12 1 92 1 3 0 1 93 1 94 64P17f9e87672f3a500 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P18534ffe947231d6 0 8 0 1 59 1 65 1 75 1 77 1 84 1 89 1 90 1P188e67df6cc546db 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P189124ff082057fa 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P189ec0a532b77875 0 4 0 16 53 16 72 16 73 16P19a6f15a78537875 0 3 0 1 83 1 84 1P1a2f63a7d5266757 0 5 0 1 35 1 54 1 72 1 73 1P1aa4bc21aaa9d1f9 0 6 0 1 34 1 56 1 74 1 92 1 93 1P1ac56bb6a2fa2760 0 2 0 1 59 1P1ad435f454daea44 0 3 0 1 42 1 53 1P1afa2213827dcb67 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P1b0cfdf81264e5f7 1 2 32 3 0 1 92 1 95 1 32 10 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 93 1 94 1 2 96 1 97 1P1b559247c331f261 1 2 32 3 1 1 93 1 96 1 32 10 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 94 1 95 1 2 97 1 98 1P1b69262064da4e68 0 4 0 1 54 1 72 1 73 1P1b7642c544171e37 0 5 0 1 35 1 54 1 72 1 73 1P1b9f7f74757af4db 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P1bbcd481d47ea5e5 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P1bc2d2a36c8187b3 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P1c2499aa0770d27e 0 5 0 1 35 1 54 1 72 1 73 1P1cd9140c1b0aec2d 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P1d0b999892e50ed0 0 4 0 1 54 1 72 1 73 1P1ef44b8955ad695f 0 2 0 1 56 1P1f10430b2e444e94 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P20649e2a4b6a38a3 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P2065dfba8e4abdd1 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P20f1e7175a5a9e8c 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P21008048bb03790a 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P215dda22112b4a24 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P2179fe4c138e50a7 1 1 16 2 0 1 72 1 3 11 1 73 1 74 16P21879ebef79890fc 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P22ec513edb34c8c0 0 4 0 8 16 8 95 8 96 8P23005a4f44ea788c 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P23005d1829f9ce3f 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P23339bbff72e5751 0 2 0 1 1 1P23dc1e4806468a7e 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P2431d777b2536a54 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P24d7eecf56186bdd 0 5 0 1 35 1 54 1 72 1 73 1P24f3a39325b7ef35 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P2508da11e2b728a0 0 6 0 1 55 1 64 1 65 1 72 1 73 1P25cffc5decf9f16c 1 2 32 3 0 1 93 1 96 1 32 10 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 94 1 95 1 2 97 1 98 1P2629bf7ec0277b76 0 12 0 1 4 1 36 1 63 1 72 1 75 1 76 1 77 1 84 1 85 1 92 1 93 1P263efc7ddd16a0d0 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P2644aac42a3395fe 0 5 0 1 60 1 82 1 86 1 93 1P285167d042968d0a 0 5 0 1 35 1 54 1 72 1 73 1P2869f2994ca912df 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P28aa15886d54a6a0 1 1 16 2 1 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P28e055d7348d21d4 0 8 1 1 37 1 76 1 83 1 85 1 86 1 93 1 94 1P29238dd46a43b83a 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P2937101a2b0ac415 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P298389f0cb9686c0 0 2 0 1 54 1P29fe2710a2b6160c 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P2aa980ffbda3702a 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P2b1025cf570be0ee 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P2b1a46adbf147109 0 4 0 1 54 1 72 1 73 1P2b78fac093ee6d84 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P2c2183f760671dbd 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P2c296f4d4ab523af 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P2c78ecaf79bfbaca 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P2cf8789d395de8ad 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P2ddaf47ac7f5a801 0 4 0 1 54 1 72 1 73 1P2de2f7fcae96db3a 0 4 0 1 54 1 72 1 73 1P2e8c2024d33236e9 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P2eb1ab8b58a68934 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P2ecae2d970e95ea0 0 4 0 1 54 1 72 1 73 1P2ee515f794384712 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P2f597c57d87aec2d 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P306d702b2f14240a 1 2 32 3 1 1 93 1 96 1 32 10 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 94 1 95 1 2 97 1 98 1P30770cc99c3fce8f 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P310b6e8e5d9f1fb2 0 7 0 1 55 1 62 1 64 1 65 1 72 1 73 1P31bbcacc042f4b88 1 2 32 3 0 1 93 1 96 1 32 3 1 1 94 1 95 1 2 97 2 98 2P3206f40baf250ece 0 2 0 1 54 1P324a7b863373eb15 0 8 1 1 37 1 76 1 79 1 85 1 86 1 93 1 94 1P324ccbac235b6e73 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P32753d4adb8c41ca 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P32809bdfb528bb2a 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P32bee4e24f75faab 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P32d802c88318cc45 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P336d38bf54a77cae 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P338003809b39908d 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P339511ecd5b74e16 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P349a24f68c5d2eb6 0 4 0 1 54 1 72 1 73 1P34cbf3f5edffb7a4 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P35345b6c72f26653 1 1 16 3 0 1 93 1 94 1 7 41 4 75 4 84 4 85 4 92 4 95 4 96 64P35c88ae40562526b 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P35ed87e1aa41c847 1 2 16 3 1 1 45 1 73 1 16 3 0 1 46 1 74 1 2 75 1 76 1P361cda6b38a438e1 0 4 0 1 54 1 72 1 73 1P3632eea8d27a6c34 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P36d83da58190c436 0 5 0 1 35 1 54 1 72 1 73 1P36e4587adcde8273 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1P36ed923966be055b 0 5 0 1 35 1 54 1 72 1 73 1P36fc335ede48d564 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P3731ac8171b76cb8 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P3737c1db719c7d30 1 1 16 3 0 1 94 1 95 1 7 42 4 76 4 85 4 86 4 93 4 96 4 97 64P37e2ce8383939604 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P383ebeaca073b067 0 6 0 1 55 1 64 1 65 1 72 1 73 1P3899dba0c2e6ecb5 0 2 0 1 1 1P39098f1063bd3e14 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P39271dd7928b9544 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3956d619265e7454 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3979cc7b23556007 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P3985a23da2f61860 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P39af8468323df095 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P3a05ac1b5c5ce03d 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P3a3b73d28b9a5e7f 1 2 16 2 0 1 74 1 16 2 1 1 73 1 2 75 1 76 1P3a5579b33230c332 0 8 0 1 36 1 75 1 78 1 84 1 85 1 92 1 93 1P3a6180c55f6975f8 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P3b096e72a5c9b600 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P3b25e1c1bcc5bbc8 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3b3aa450f03ebfea 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P3b3ea9652811dae5 0 4 0 1 54 1 72 1 73 1P3bea58f59c11218a 0 7 0 1 55 1 58 1 64 1 65 1 72 1 73 1P3c6faa5c5365616e 0 7 1 1 56 1 63 1 65 1 66 1 73 1 74 1P3c9493ea07b29a66 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3cc2aa76c7915989 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P3d1ca14c6fab174c 1 1 16 4 1 1 38 1 47 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3dfe716516a141b1 0 8 0 1 6 1 41 1 55 1 64 1 65 1 72 1 73 1P3e148fd92964ca8f 0 9 0 1 36 1 75 1 76 1 77 1 84 1 85 1 92 1 93 1P3e52210aeff458d7 1 1 16 3 1 1 45 1 73 1 9 41 1 44 1 56 1 57 1 58 1 65 1 66 1 74 1 75 16P3e6972a1e7315e15 1 1 16 3 0 1 94 1 95 1 7 42 4 76 4 85 4 86 4 93 4 96 4 97 64P3ecbeb490313da2c 1 1 64 2 0 1 92 1 3 13 1 93 1 94 64P3f07b458c611d8eb 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P3f25dbfa4b11ea9e 0 7 1 1 56 1 59 1 65 1 66 1 73 1 74 1P3f55f9e5e5af951f 0 4 0 1 54 1 72 1 73 1P3fa8ce51c8ebdb90 0 7 2 1 43 1 57 1 66 1 67 1 74 1 75 1P3fdf99540e0a91b5 0 8 0 1 55 1 56 1 57 1 64 1 65 1 72 1 73 1N000f218013d5338cN001d46dabc55bfb4N002061c6a5981a76N004d8533f0e07447N00659481f0290e0eN02154a7e0b593180N0274df4ebe1da6adN02dd20379258400eN037a347f725bdcb6N03d44d88f22c121dN0468662a1c5c77afN04b305247995ff0bN0586791c71dba4deN05c6ee057525548bN05df81c626614245N05e555b7c131f6cfN060a79db5bec8dd0N06ce50b89be8bdc1N06df42e0c8654ba2N072e994303d34475N0772aa01441a68dcN08a0bd2a7340b3fdN0a1f6484257ca35bN0a461b731ae7b745N0ac238b6c47c255bN0b4fdad31f41a73bN0bc34b2cb850609cN0bfa7b37f9751245N0c17776af125d8feN0c6e6338a729f7bbN0d5a64091c9a6c50N0d8fd6db66d4e4e8N0d949c0171936624N0dd1a7b229518d13N0e09d9b2bde6e370N0e51c4cd09003125N0eabf8cd4a01c1e5N0ec4177afedbb283N0f3b43363400213aN0f8c878832db8c8aN0fa54255f8cd5608N0fbf5653ad99ab4cN0fc4baa6dacafb5eN0fe37d1078c19c60N0ff9c5f1a56ec602N101aa6080c8776c6N112d14a7098e59a3N116936348b2ee8b2N1194cbd446c1a2a2N129bedda5b7d74b1N129f25d92235bff7N140eab906a301906N14c1c52d0b1f8659N14ef0b2b8202c036N1538ce13356f6a39N15f3f549e32260a8N15f5c9a20853827aN165581448ee73a36N166ee4c485a605ceN16c51b233e270c94N1726d98c596e689aN179ab2e9972316f5N184ca85f3c1690edN186682ae5f43a92eN18974df0f0d0a550N1a259a16ce2d2552N1b51e3fc025155c8N1bba3828be2b95e0N1c65c1baf7afbb0fN1c7ac98a35788a6bN1cf2f24d36003352N1d2344b8cc445a91N1d5e4aa292adc52dN1dc64c1385a64723N1ec59afde1256e32N1ed8b7c4f964ef78N1f04095111972007N1f0ec39a8115ee25N1f3870b3c2656c9cN1f853b06aa565ccdN1fa4f8cb14e02564N1facc2f1daf7efb9N203a746ca2e077e4N20777444443e13b8N208b36ddd23d19aeN211955d738b2bc5aN2151b8a79fa980c4N2193199d00fed7cfN21cac81c4a9fcf20N225a738db51f2b3eN228fa67e0969996aN233fc519a6433c55N234e303f2b70fd53N2360cdc27446461eN2404441b4e1a72f0N2507b893529082e4N254716c5bdd576d1N2568a7a1ad887e65N25cbf86ad88e97faN262be470feb6bbc3N26438f3e8c68ebd3N26487a24386587efN2653c66d4ee95fc2N2656cd23a2351388N269b73fa86df7e48N27664d54f2e22624N27ee6ecadebd4503N286992c872fec0bfN2925ba9de9d89e61N2a412244d2263908N2a98faac06cf7272N2b6c639465ecc64cN2cc7b5e1d1bc94bcN2d94f136dce905adN2dd4a17fc36fb494N2e08be5bb903bc11N2ec96e86e3dd6ca5N30b3753c6e1a2ebcN3201fae2f5ba259bN3203f95efa5266e6N32053efeccc23b31N32e820b0fd2a7598N3376d7f27313d235N347cac689a97efa6N34c4f60a89026132N34ee94c5fba5520aN34f700515c41e111N356781ae1b0a2aafN35986da0601aab94N35d5dc40a8334287N36b7c9946722c63eN36c1fc6a073054abN36ecf5a477bc98e3N370d5dbc4d231621N3720200a3bbf44c9N3730c0ce4d5cc2c5N384fce2d786c727cN38f00507ecf452faN3911d8499c8e5619N3ac1b998e4457275N3db03821a521f37bN3df0d8da10ca9d12N3e2c640eab303bddN3e62bea9e227b3b6N3e8217ea37ba3920N3ea89257cb247c76"%lxh.
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
Ltac2 gd_tbl_A_x509_get_san_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_X509_GET_SAN"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_swrap"; "Walk.Call.MIDP"].


Definition A_X509_GET_SAN : Z := 0xaf3ec.       (* [comment removed for export] *)
Definition A_SMALLOC_0G : Z := 0x52ef8.           (* [comment removed for export] *) (* [comment removed for export] *)

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
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Variable STKe : Z.
  Hypothesis STKe0 : 0 <= STKe.

  (* [comment removed for export] *)
  Definition STKg : Z := 112 + 48 + STKe + arl_need_smalloc R.

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
  Hypothesis SLO : lo <= bv_unsigned sp - STKg.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold STKg in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lx5,(5.&40.)(1.(5.&40.)Lx6,(5.&40.)(1.(5.&40.)Lx7,(5.&40.)(1.(5.&40.)Lx10,(5.&40.)(1.(5.&40.)Lx11,(5.&40.)(1.(5.&40.)Lx12,(5.&40.)(1.(5.&40.)Lx13,(5.&40.)(1.(5.&40.)Lx14,(5.&40.)(1.(5.&40.)Lx15,(5.&40.)(1.(5.&40.)Lx16,(5.&40.)(1.(5.&40.)Lx17,(5.&40.)(1.(5.&40.)Lx28,(5.&40.)(1.(5.&40.)Lx29,(5.&40.)(1.(5.&40.)Lx30,(5.&40.)(1.(5.&40.)Lx31,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)Llenj,(5.&40.)(7.(8.$0.R18.(9.(:.(;.&40.+:?45<.)(;.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(;.&40.R16.)R10.R?.R>.R=.R<.R;.R:.R9.(;.&40.R17.)(;.&40.VCUR,)(;.&40.VEND,)(;.&40.VPP,)(;.&40.(<.R17.+20.))(;.&40.R17.)(;.&40.(<.(=.R17.+3.)(>.(?.VR,))))(;.&40.(>.(?.VR,)))Vs10,Vs11,R8.R7.R6.R5.)VF,(;.&40.+:?4?0.)Vfc,(10.(5.&40.))R14.(11.$4.)))(7.(7.(12.(13.(14.&40.Vsp,)+70.)R16.)(12.R16.(13.(14.&40.Vsp,)+60.)))(7.(8.$2.(15.R16.+20.)=)(7.(16.$4.VR,VHIA,R15.VLB,(17.(18.$2.$2.)(19.$2.$2.R17.+40.)VLF,)R14.)(7.(8.P,$2.Sp(1:.$4.VR,VHIA,R15.)(1:.$4.VR,VHIA,Vh,))(7.(8.$2.(1;.$4.VR,VHIA,R15.)(1;.$4.VR,VHIA,Vh,))(7.(8.$2.(1<.$4.VR,VHIA,R15.)(1<.$4.VR,VHIA,Vh,))(7.(8.$2.(1=.$4.VR,VHIA,R15.)(1=.$4.VR,VHIA,Vh,))(7.(8.$2.(1>.$4.VR,VHIA,R15.)(1>.$4.VR,VHIA,Vh,))(7.(8.$2.(1?.$4.VR,VHIA,R15.)(1?.$4.VR,VHIA,Vh,))(7.Pmo,$20.(21.(22.$4.VR,VHIA,R16.R1.)(22.$4.VR,VHIA,Vh,R1.))(7.(8.$2.(15.R17.+40.)=)(7.(23.VR,VLB,VLF,R17.+40.)(7.(24.$4.R14.R17.(17.$25.(26.R4.)(17.$25.(26.R3.)(17.$25.(26.R2.)(27.$25.)))))(7.(24.$4.R14.(<.R17.+20.)(17.$25.(26.R1.)(27.$25.)))(7.(24.$4.R14.(<.(=.R17.+3.)(>.(?.VR,)))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.=))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(27.$25.))))))))))(7.(24.$4.R14.(<.(14.&40.Vsp,)-58.)(17.$25.(26.Vs9,)(17.$25.(26.Vs8,)(17.$25.(26.Vs7,)(17.$25.(26.Vs6,)(17.$25.(26.Vs5,)(17.$25.(26.Vs4,)(17.$25.(26.Vs3,)(17.$25.(26.Vs2,)(17.$25.(26.Vs1,)(17.$25.(26.Vs0,)(17.$25.(26.Vra,)(27.$25.)))))))))))))(7.(24.$4.R14.R16.(17.$25.(26.(;.&40.R17.))(27.$25.)))(7.(29.$4.R14.(<.R16.+8.)(<.(14.&40.Vsp,)-58.))(7.(29.$4.R14.Vlo,R16.)(7.(2:.$4.R14.)(7.(24.$4.R14.VPP,(17.$25.(26.(;.&40.VP,))(27.$25.)))(7.(24.$4.R14.VCUR,(2;.Vct,Vcpad,===))(7.(2<.$4.R14.VBUF,Vbs,)(7.(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R14.VPP,+8.)(7.(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R14.VCUR,+20.)(7.(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R14.VBUF,(2>.(2?.(5.&8.)Vbs,)))(7.(30.(12.(<.R17.+40.)VPP,)(12.(<.VPP,+8.)R17.))(7.(30.(12.(<.R17.+40.)VCUR,)(12.(<.VCUR,+20.)R17.))(7.(31.$4.VR,VHIA,Vh,VLB,VLF,(14.&40.Vsp,)(14.&40.Vsp,)(17.(18.$2.$2.)(19.$2.$2.VPP,(<.VPP,+8.))(17.(18.$2.$2.)(19.$2.$2.VCUR,(<.VCUR,+20.))(27.(18.$2.$2.))))Vm,R14.)(7.(32.$4.(?.VR,)R14.Vslo,R16.)(32.$4.(?.VR,)R14.R16.(14.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 D1; try lx_pin1 ALC; try lx_pin1 B5; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 ALP; try lx_pin1 GT.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02N0@D10639180168.185D10651765667.111D10823604468.151D12549489996.183D12658639931.110D12660902694.151D14194668100.185D18607476203.152D20553579080.153D22855098056.186D22857195213.112D2455600524.184 D29850139295.186D31526149352.183D31526457809.110D3160262663.185 D32456886359.184D32465422351.186D32467519498.112D3254889317.151 D32606360467.187D33194539134.110D33283596102.183D3373313708.183 D36104740330.185D39411162312.152D45714769693.183D46793187693.185D46805773126.111D50254960491.153D52461811354.186D54557184843.183D560907437.113  D58077997354.153D59055705238.183D60098777666.111D60109265003.112D60111362153.185D60111362158.186D60111559787.183D62009673032.187D62011770191.113D62182462905.186D65010535209.184D68405032175.183D6909683434.183 L17607390846.162L1832968857.12  L19548981083.162L19980016842.12 L2333530698.150 L2333536794.150 L26163319485.150L26163329773.150L29738741675.1  L31170831509.157L33483560980.13 L33485826452.1  L35228767239.1  L35653441506.11 L36180999398.111L38692635477.0  L3876079316.9   L39332637397.0  L39618635427.2  L40228640085.0  L43055154860.109L43202358967.160L4472687353.162 L45363093875.190L47663688086.1  L48117620904.97 L48119718052.158L48119718055.157L49130057368.12 L49658308257.0  L50204818630.3  L50388565080.1  L50790731766.11 L52255793882.181L56380976587.10 L56854270298.112L57355539152.161L57355539152.164L58071656716.182L58790154276.12 L59308634497.16 L60098763854.6  L61437265048.2  L6302879940.150 L6302890132.150 L67922604617.0  L6910010082.157 L7040749983.113 L9356559645.16  L9873114841.11  P1056307012.151 P1056307012.153 P51023938008.151P51023938008.153Q10523111609.117Q10594483344.191Q10651763882.119Q10651763890.115Q12660624651.121Q1530342990.153 Q22857195208.116Q22857195211.120Q23216651701.191Q23927511184.117Q23927511196.122Q26032252603.196Q31021924279.151Q31158247845.190Q31158247869.194Q31170831509.192Q32440833928.190Q32467519500.120Q32467519503.116Q32679790552.191Q32681887701.117Q33196749134.121Q33271078526.190Q34966725149.196Q38248895679.123Q40216052035.190Q40271359350.153Q42439168719.151Q42441479401.198Q42441479403.124Q43351262911.115Q43351262911.190Q43880146019.123Q46805771343.119Q46805771351.115Q47230721788.117Q47313632828.115Q47313632828.190Q48119718054.191Q48132302231.190Q50796826103.153Q56533317818.191Q59867617332.124Q59867617334.198Q60460432782.116Q60740903729.115Q6192914196.151 Q62011770180.122Q62011770184.117Q64681502658.124Q67038703949.151Q67517027822.115Q67517027822.190Q6897428426.194 Q6897428434.190 Q6910010082.192 Q8701272495.198 Q9350548487.134 00000Q00b01A01B01T02302402502602X02j02k02l02m02n02o03M03o04A04B04i05;05<05=05>05?05]06>06O06P06Q06R06h07G07H07_08608]09D09k0:K0:[0:\0;:0;;0;Y0<A0<B0<j0=B0=C0=D0=E0=F0=J0=]0=^0=_0=c0>;0>P0>Q0?50?60?@0?A0@;0A60A_0BB0BG0C50Ch0D[0D\0D]0Di0Dn0EN0El0FE0Fo0G00G^0H@0H`0Hj0I40I<0I=0I>0I?0IR0J00Jd0KQ0L00LO0M00MQ0Ma0N40NB0NP0N_0O:0OI0OX0Ok0PJ0P]0Q70Q[0Qn0RA0RT0RU0Rd0S30S40S50SD0SE0T80TF0TG0T_0U:0UU0Uk0Ul0Um0V>0VL0VZ0Vk0Vl0Vm0W`0XS0YB0YC0YD0YE0YW0Yi0Z=0ZJ0ZW0[:0\10\20\30\F0\Y0\l0]\0^8S2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H224LFB'FS2LF2sp3BUF2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H224LFB'FFFS2LF2sp3CUR2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFBFFFFFS2LF2sp2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFBFS1R3HIA2LF2sp2bs3LFB3sp13H224LFB'2h12FBS2LF2sp3BUF2bs3LFBFFFFS2LF2sp2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBFFFS1R3HIA1h2LF2sp2bs3LFBS2LF2sp2bs3LFB3sp13H203H224LFB'FS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2bs3LFB3sp13H224LFB'2FBS1R2LF2sp2bs3LFBFS2LF2sp2bs3LFB3sp13H224LFB'2FBFS2LF2sp2bs3LFB3sp13H224LFB'2FBS2LF2sp2bs3LFB3SPR3sp13H224LFB'2FB2F02F8SS2LF2sp2bs3LFB3SPR3sp13H224LFB'2FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1FFFFS2FBS2LF2bs3LFB4LFB'2FBFFS2spS1R3HIA1h2sp2lo3TOP4HTOPS2LF2sp2PP3CUR2bs3LFBSS1R3NS14STKe5STKe02sp2lo3SLO3sp13SP1SS3sp14SP1MSS1R3NS14STKe5STKe02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPRS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'2FB4FBLOS1R2LF3slo2bs3LFB4SLOS3ALO3sp14LFB'2FB2F1S2LF2sp2bs3LFB3sp13H224LFB'2FB1c2HcS3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'SSS2sp3sp13SP1S3sp1S1R3NS14STKe5STKe02sp2lo3SLO3LOSS2LF2sp2bs3LFB3sp13H224LFB'2FBS1R3BUF2lo2bs3LOS3BCE3ALOS2LF2sp2bs3LFB3SPA3SPR3sp13H183H193H203H22FS1R2LF2sp2bs3LFB3ACV3SPR3sp13H224LFB'2FB2F02F1S2LF2sp2bs3LFB3sp13H203H224LFB'2FBS1R4STKe5STKe02sp2lo3SLO3sp13SP1S2FB2F02KbS1R2lo3LOSS2LF3LFBFFSS2LF2bs3LFB4LFB'2FBS2LF2sp2bs3LFB3SPR3sp13H183H22S1R3NS14STKe5STKe02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R3NS14STKe5STKe02sp2lo3slo4SLOL3SLO3sp13SP1S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF3CUR2lo2bs3LFB5CURLO3sp14LFB'S2LF3CUR2lo2bs3LFB5CURLO3sp14LFB'S1R2LF2sp2bs3LFBS2LF2bs3LFB4LFB'2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H204LFB'S2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3LFB3sp14LFB'S1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4LFB'S2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBFS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBFFS2LF3BUF2bs3LFBFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'S2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFB4LFB'S1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOSFFS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS4LFB'FFFS2LF2PP3CUR2bs3LFBS2LF2PP3CUR2bs3LFBS2LF2bs3LFB3sp14LFB'S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'FFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP3sp13SP14LFB'S2LF2bs3LFB3sp13H213H224LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS DCB CURLO CWC CUR0 DPB B47 B3 BIN PPLO CWP PP0 LFB STKe0 STKe NS1 SM0 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(16.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(24.$4.Vm,VPP,(17.$25.(26.(;.&40.VP,))(27.$25.)))P,(24.$4.Vm,VCUR,(2;.Vct,Vcpad,===))P,(2<.$4.Vm,VBUF,Vbs,)P,(29.$4.Vm,Vlo,(14.&40.Vsp,))P,(32.$4.(?.VR,)Vm,Vslo,(14.&40.Vsp,))P,(2:.$4.Vm,)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)Vm,VCUR,+20.)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)Vm,VBUF,(2>.(2?.(5.&8.)Vbs,)))(33.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)$34.(9.(:.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(;.&40.VPP,)(;.&40.VEND,)(;.&40.VCUR,)R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(;.&40.$35.)Vfc,(10.(5.&40.))Vm,(11.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH HPP HCUR HBUF ST SS MI OPP OCUR OBUF.
  unfold A_X509_GET_SAN.
  unfold seq_cells in HCUR.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  rt_facts.
  assert (BUFLO : BUF + n <= lo) by (clear - BCE ALO LOS; lia).
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKe0 TOP HTOP; lia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO NS1 STKe0; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
  idtac "T-CARVED".
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 152%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO NS1 STKe0; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | clear - SLO SP1 TOP NS1 STKe0; lia
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
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL NS1 STKe0; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 1%nat FRa SAVE end.
      replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in SAVE by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -88); rename ST2x into STK2 end.
      destruct (stk_split asegs m3 sp1 (sp1 + 8) (bv_unsigned sp + -88) STK2 ltac:(clear - SP1; lia)) as [STs SThi]. clear STK2.
      destruct (stk_carve asegs m3 sp1 (sp1 + 8) 8 STs ltac:(clear; lia)) as [_ [jsp SLOT0]]. clear STs.
      replace (sp1 + 8 - Z.of_nat 8) with sp1 in SLOT0 by (clear; lia).
      cb8_to_c8 SLOT0 (@nil cell).
  (* [comment removed for export] *)
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaf4f0] [] 152%N). lx_tree.
  lxr_leaf. lx_carry.
  lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      idtac "S1P".
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition EXQ (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm2,P,(5.&40.)(6.(5.&8.))(1.$2.Lr,$2.(1.$2.Lp',$2.(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)Lxra,(5.&40.)(1.(5.&40.)Lx5,(5.&40.)(1.(5.&40.)Lx6,(5.&40.)(1.(5.&40.)Lx7,(5.&40.)(1.(5.&40.)Lx11,(5.&40.)(1.(5.&40.)Lx12,(5.&40.)(1.(5.&40.)Lx13,(5.&40.)(1.(5.&40.)Lx14,(5.&40.)(1.(5.&40.)Lx15,(5.&40.)(1.(5.&40.)Lx16,(5.&40.)(1.(5.&40.)Lx17,(5.&40.)(1.(5.&40.)Ls3v,(5.&40.)(1.(5.&40.)Ls4v,(5.&40.)(1.(5.&40.)Ls5v,(5.&40.)(1.(5.&40.)Ls6v,(5.&40.)(1.(5.&40.)Ls9v,(5.&40.)(1.(5.&40.)Lx28,(5.&40.)(1.(5.&40.)Lx29,(5.&40.)(1.(5.&40.)Lx30,(5.&40.)(1.(5.&40.)Lx31,(5.&40.)(7.(8.$0.R1;.(9.(:.R14.(;.&40.O2.)Vgp,Vtp,R13.R12.R11.Vsp,(;.&40.O2.)(;.&40.R19.)R10.R?.R>.R=.R<.R;.R:.(;.&40.O3.)R9.R8.R7.R6.(;.&40.O3.)(;.&40.(<.(=.O3.+3.)(>.(?.VR,))))R5.Vs10,Vs11,R4.R3.R2.R1.)VF,(;.&40.+:?57<.)Vfc,(10.(5.&40.))R1:.(11.$4.)))(7.(7.(36.-3000.R19.)(36.R19.=))(7.(7.(12.VP,R18.)(12.R18.VEND,))(7.(16.$4.VR,VHIA,O1.VLB,(17.(18.$2.$2.)(19.$2.$2.O3.+40.)VLF,)R1:.)(7.(2:.$4.R1:.)(7.(24.$4.R1:.O3.(17.$25.(26.R17.)(17.$25.(26.R16.)(17.$25.(26.R15.)(27.$25.)))))(7.(24.$4.R1:.(<.(=.O3.+3.)(>.(?.VR,)))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.=))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(27.$25.))))))))))(7.(24.$4.R1:.(<.(14.&40.Vsp,)-58.)(17.$25.(26.Vs9,)(17.$25.(26.Vs8,)(17.$25.(26.Vs7,)(17.$25.(26.Vs6,)(17.$25.(26.Vs5,)(17.$25.(26.Vs4,)(17.$25.(26.Vs3,)(17.$25.(26.Vs2,)(17.$25.(26.Vs1,)(17.$25.(26.Vs0,)(17.$25.(26.Vra,)(27.$25.)))))))))))))(7.(24.$4.R1:.O2.(17.$25.(26.(;.&40.O3.))(27.$25.)))(7.(29.$4.R1:.(<.O2.+8.)(<.(14.&40.Vsp,)-58.))(7.(29.$4.R1:.Vlo,O2.)(7.(24.$4.R1:.VPP,(17.$25.(26.(;.&40.R18.))(27.$25.)))(7.(24.$4.R1:.VCUR,(2;.Vct,Vcpad,===))(7.(31.$4.VR,VHIA,Vh,VLB,VLF,(14.&40.Vsp,)(14.&40.Vsp,)(17.(18.$2.$2.)(19.$2.$2.VPP,(<.VPP,+8.))(17.(18.$2.$2.)(19.$2.$2.VCUR,(<.VCUR,+20.))(27.(18.$2.$2.))))Vm,R1:.)(7.(32.$4.(?.VR,)R1:.Vslo,O2.)(32.$4.(?.VR,)R1:.O2.(14.&40.Vsp,)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition CALLQ (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm3,P,(5.&40.)(6.(5.&8.))(1.$2.Lq,$2.(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)LLw,(5.&40.)(1.(5.&40.)Lxra,(5.&40.)(1.(5.&40.)Lx5,(5.&40.)(1.(5.&40.)Lx6,(5.&40.)(1.(5.&40.)Lx7,(5.&40.)(1.(5.&40.)Lx13,(5.&40.)(1.(5.&40.)Lx14,(5.&40.)(1.(5.&40.)Lx15,(5.&40.)(1.(5.&40.)Lx16,(5.&40.)(1.(5.&40.)Lx17,(5.&40.)(1.(5.&40.)Lx28,(5.&40.)(1.(5.&40.)Lx29,(5.&40.)(1.(5.&40.)Lx30,(5.&40.)(1.(5.&40.)Lx31,(5.&40.)(7.(8.$0.R14.(9.(:.R=.(;.&40.O2.)Vgp,Vtp,R<.R;.R:.Vsp,(;.&40.O2.)(;.&40.VPP,)(;.&40.VEND,)(;.&40.VCUR,)R9.R8.R7.R6.R5.(;.&40.O3.)(;.&40.VCUR,)(;.&40.VEND,)(;.&40.VPP,)(;.&40.(<.O3.+20.))(;.&40.O3.)(;.&40.(<.(=.O3.+3.)(>.(?.VR,))))(;.&40.(>.(?.VR,)))Vs10,Vs11,R4.R3.R2.R1.)VF,(;.&40.+:?578.)Vfc,(10.(5.&40.))R13.(11.$4.)))(7.(7.(12.(<.VP,+2.)R12.)(12.R12.VEND,))(7.(16.$4.VR,VHIA,O1.VLB,(17.(18.$2.$2.)(19.$2.$2.O3.+40.)VLF,)R13.)(7.(2:.$4.R13.)(7.(24.$4.R13.O3.(17.$25.(26.R11.)(17.$25.(26.R10.)(17.$25.(26.R?.)(27.$25.)))))(7.(24.$4.R13.(<.O3.+20.)(17.$25.(26.R>.)(27.$25.)))(7.(24.$4.R13.(<.(=.O3.+3.)(>.(?.VR,)))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.=))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(27.$25.))))))))))(7.(24.$4.R13.(<.(14.&40.Vsp,)-58.)(17.$25.(26.Vs9,)(17.$25.(26.Vs8,)(17.$25.(26.Vs7,)(17.$25.(26.Vs6,)(17.$25.(26.Vs5,)(17.$25.(26.Vs4,)(17.$25.(26.Vs3,)(17.$25.(26.Vs2,)(17.$25.(26.Vs1,)(17.$25.(26.Vs0,)(17.$25.(26.Vra,)(27.$25.)))))))))))))(7.(24.$4.R13.O2.(17.$25.(26.(;.&40.O3.))(27.$25.)))(7.(29.$4.R13.(<.O2.+8.)(<.(14.&40.Vsp,)-58.))(7.(29.$4.R13.Vlo,O2.)(7.(24.$4.R13.VPP,(17.$25.(26.(;.&40.R12.))(27.$25.)))(7.(24.$4.R13.VCUR,(2;.Vct,Vcpad,===))(7.(2<.$4.R13.VBUF,Vbs,)(7.(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R13.VPP,+8.)(7.(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R13.VCUR,+20.)(7.(31.$4.VR,VHIA,Vh,VLB,VLF,(14.&40.Vsp,)(14.&40.Vsp,)(17.(18.$2.$2.)(19.$2.$2.VPP,(<.VPP,+8.))(17.(18.$2.$2.)(19.$2.$2.VCUR,(<.VCUR,+20.))(27.(18.$2.$2.))))Vm,R13.)(7.(32.$4.(?.VR,)R13.Vslo,O2.)(32.$4.(?.VR,)R13.O2.(14.&40.Vsp,)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition MIDP (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := fun ms => EXQ FB sp1 h1 ms \/ CALLQ FB sp1 h1 ms.

  (* [comment removed for export] *)
  Lemma swrap32_errsum'' : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "Pr,$2.Pc,$2.P,(7.(36.-10000.R2.)(12.R2.=))P,(7.(12.(13.(37.+2.+40.)+10000.)R2.)(36.R2.(37.+2.+40.)))(8.$2.(38.&20.(<.(15.R4.+10000000000000000.)R3.))(<.R4.(13.R3.(37.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DCB; try lx_pin1 CWC; try lx_pin1 ALC; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 SM0; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03Y0@C40858145355.200C60410007123.201D10636937134.201D10637083017.154D12660624642.153D14196765253.154D14197109858.201D16071854214.201D2457516971.201 D2459793318.152 D31528442088.153D3162115617.201 D3162359814.154 D32452690557.152D32458870384.201D32604263317.155D33196749127.153D3388366638.151 D35883165164.151D36106837483.154D36107017164.201D39243574473.201D39258595524.152D39604305264.201D39604616023.154D45704738463.151D46794843979.201D46795284844.154D60109265000.154D60109446735.201D62011770190.155D64997949699.152D65008160014.201D68221095944.201D68411655533.151D6899603304.151 K20981739667.201K29378133114.201K30993319891.201K32053909171.199K36557281826.199K65858155712.201L1136325469.2   L17605293694.128L18025444970.170L18489062900.25 L19546883931.128L19698471166.32 L2033615896.2   L20977711877.2  L21654730866.2  L22838518177.0  L25852964777.167L25852964777.170L2621559066.1   L27111942217.1  L27380263923.3  L27821999381.175L27938633021.32 L29391009772.3  L30997223346.3  L31168734357.124L32051500981.2  L33610110299.1  L3484572308.32  L35236225328.25 L35253537528.167L35653441506.11 L35903316071.25 L36544860596.2  L38235734261.1  L41110154015.25 L41251426164.1  L41589526666.167L41629762929.3  L43202358961.133L43305107741.25 L4472687353.135 L45363093875.158L45921596632.2  L47870616696.2  L48117620900.125L48117620903.124L48132302231.158L49233373885.2  L50059654756.3  L5021251703.1   L50678314462.3  L51674283543.167L51674283543.170L52225557330.2  L55195235631.25 L56380991837.10 L57387012359.32 L58972524609.3  L59308586248.2  L60098763854.6  L62275882349.3  L64179129035.1  L64220386483.2  L65862516566.2  L66812728480.3  L67070089790.2  L67922604617.0  L6912107234.124 L8680080987.1   L881835912.0    L9080220944.4   L9356559676.16  O14912726833.200O20099309002.200O20866770946.201O22525005962.201O25735317723.199O3041047083.199 O33542776439.199O3493317847.201 O37559489567.201O3821773283.201 O424351700.197  O44938202843.201O49701823576.200O4997777340.200 O50011839873.197O53687452546.199O55209884805.197O58922430686.197O59163721641.197O60925138987.198O61021385103.200P1129456122.200 P2044614335.199 P21647862485.197P33614305247.199P41636534230.197P47876372191.201P49230739482.200P50048623811.197P50671478649.197P52212974038.200P62260666314.197P64207511333.200P66818508295.201P67064334489.200P8684274911.198 Q10523111604.161Q10588139941.175Q10592386206.159Q10592533181.201Q10636937134.201Q10637083020.160Q10651763882.164Q11133374175.201Q11657053839.201Q11657494700.159Q12551782730.160Q12562269300.197Q12658527489.166Q14851060500.168Q14851060501.169Q17027695041.201Q17681074618.201Q19551029871.175Q21767670690.201Q22855098061.165Q23218748859.159Q23219026840.201Q23925414038.167Q23927511197.161Q26028057501.199Q26030071964.201Q26032252593.172Q27573751300.201Q27942454161.201Q2803826605.201 Q29775981542.201Q31158247845.158Q31168734357.162Q31170831514.170Q32440833928.158Q32465422346.165Q32681607669.201Q32681887702.159Q32681887704.161Q33194651972.166Q33271078526.197Q33285757760.160Q3477426724.201 Q34964382778.201Q34966725143.172Q34979309371.199Q38250992816.169Q38250992817.168Q40216052035.158Q40259924710.175Q42437284299.198Q42439168719.201Q42441479395.174Q43336582017.160Q43351262911.197Q43878048877.168Q46794843979.201Q46795284841.160Q46805771343.164Q47230721777.161Q47313632828.197Q47328312066.160Q48117620904.159Q48118064779.201Q48132302231.158Q49563371193.161Q49886471364.199Q49888159685.201Q49890664936.172Q56525516080.158Q56530976407.201Q56531220660.159Q59865603600.201Q59867617340.174Q59871812884.198Q62009673038.167Q62011770181.161Q67517027822.197Q67523317968.160Q6897428434.158 Q6910010093.170 Q6912107234.162 Q8697078925.198 Q8699324297.201 Q8701272485.174 Q9356559674.178 Q9640321936.175 Q9644583048.201 00000400800M00b01;01<01=02A02B02C02D02E02F02[03003N03g03h03i03j03k03l03m03n03o04D04Y04n05L05j06A06V06k07h07i08>0980:60:L0:a0;_0<Y0<Z0=>0=[0>J0>e0?m0?n0?o0@00@10@R0A30A80A<0AG0A\0Bf0Bg0Bh0C60C70C80D=0E60ER0Ej0F90F:0F>0FM0FQ0Fm0Fn0Gj0H80H\0I60I>0I?0Im0J[0KI0KJ0KK0KL0KM0Kn0LO0LP0M?0MX0Mi0N50N;0NE0NF0NG0NH0NI0NJ0NK0NL0NZ0N[0N\0Nk0O_0O`0Oa0Ob0Oc0Od0Oe0Of0Og0Oh0Oi0Oj0Ok0Ol0Om0On0Oo0P00P10P20P30P40PJ0QB0QC0QD0R:0S60T20Th0UB0V00VJ0W80X00Xf0Xg0Y70YE0YS0Ya0Yo0Z=0ZK0ZY0ZZ0Z[0Z\0Z]0Zl0Zm0[?0[M0\C0\^0]T0]c0^10^?0^R0_10_F0_[0`00`10`_0`n0aD0aR0a`0an0ao0b>0b?0b@0bA0bP0bQ0bR0bd0cR0d@0dn0e<0eJ0eK0eY0eo0fE0f[0f\0f]0fn0g<0gJ0gX0gi0gj0gk0hY0iG0j50j60j70j80j90j:0j;0j<0j=0j>0j?0jL0jY0jZ0j[0ji0k70kE0l00l[0mF0mZ0mk0n<S2PPS2FBS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP3BUF2bs3LFB2FB3sp1FFS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB3PP03SLO3LOS2FB3sp13SP14SP1R2F0FFFFFS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R3HIA2LF2PP2bs3LFB2FB3sp12h1S2LF2PP3BUF2bs3LFB2FB3sp1FFFFFFFFS2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R2LF2PP2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2lo2bs3LFB3LOS2FB3sp1S1R2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S2LF2PP2bs3LFB2FB3sp1S1R3HIA1h2LF2sp2PP2bs3LFB3PP03TOP2FB3sp12h13SP15Ehtop4SP1R2F0FS2LF2PP2bs3LFB2FB3sp1S2LF2PP1P3END2lo2bs3LFB2FB3sp13APP3x252x23x263x273x324POSTS2LF2PP1P3END3BUF2lo2bs3LFB2FB3sp13APB3x252x23x263x273x324POSTS2LF2PP3BUF2bs3LFB3DPBS2LF2PP3CUR2bs3LFB2D1S2LF2PP3CUR1P3END2lo2bs3LFB2FB3sp13APC3x252x23x263x273x324POSTS2LF2PP1P3END2lo2bs3LFB2FB3sp13APP3x252x23x263x273x324POSTFS2LF2PP2bs3LFB3PP02FB3sp14SP1R2F02F8S2LF2PP1P2bs3LFB2FB3sp11q3H27S1R3NS14STKe5STKe02sp2PP2lo2bs4PPLO3SLO3sp13SP1S2LF2PP2bs3LFB2FB3sp12F02F8S1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8FFFSS2LF2PP1P3END2bs3LFB2FB3sp11q3HqrS2LF2PP1P3END2bs3LFB2FB3sp11q3HqrS3sp1S2PPS2rg3RRg2NES2LF2PP2bs3LFB2FB3sp1S1R3NS14STKe5STKe02sp2PP2lo3slo2bs3PP04SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0FFS2LF2bs3LFB2FBFFS1R3NS14STKe5STKe02sp2PP2lo2bs3PP03SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R3NS14STKe5STKe02sp2PP3BUF2lo2bs4PPLO3SLO3sp13SP15BUFLOS2LF2PP2bs3LFB2FB3sp12rg3RRgS1R3HIA1h2sp2lo3TOP4HTOPS3BUF2bs2FB3APBFS2loS2PP3BUF2bs3DPBS2FBS2LF2PP2bs3LFB2FB3sp12rg3RRgFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S2PP2bs2FB3APPS1R2LF3slo2bs3LFB4SLOS2FB3sp13ALO2F1S2LF2PP2bs3LFB2FB3sp11c2HcS2sp3sp1FS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFFFFS2LF2PP1P3END2bs3LFB2FB3sp11q3HqrS2LF2PP1P3END2bs3LFB2FB3sp11q3HqrFS1R3NS14STKe5STKe02sp2lo2bs3SLO2FB3sp13SP14FBLOS1R3BUF2lo2bs3LOS3ALO3BCES2PP2bs2FB3sp12F0S3BUF2bs3B47S1i2HiS1R2lo3LOSFFFFFFSS2LF2bs3LFB2FBFSS2sp2lo3sp13SP1S1R3NS14STKe5STKe02sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFS2LF2sp2bs3LFB3sp13SP1S1R3NS14STKe5STKe02LF2sp3CUR2lo2bs3LFB5CURLO3SLO3sp13SP1FFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB3sp13SP14FBLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp13SP13ALO2F1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S2LF2PP2lo2bs3LFB4PPLO3sp1S1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLOS2LF2lo2bs3LFB2FB3sp14FBLOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO2FB4FBLOS1R3NS14STKe5STKe02LF2sp3BUF2lo2bs3LFB3SLO3sp13SP15BUFLOS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1FS1R2LF2sp2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2bs3LFB2FBFFFFS2LF3BUF2bs3LFBFS2LF2lo2bs3LFB3sp1S2LF2PP2bs3LFBS1R3NS14STKe5STKe02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp13SP1S2LF2PP2bs3LFB2FB3sp12F02F8S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP13ALOS2LF3CUR2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1S2LF2sp2lo2bs3LFB3sp1FS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2bs3LFB3sp1S2LF2sp2bs3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBFS2LF3CUR2bs3LFBFFFS2LF3BUF2bs3LFBFFS2LF2lo2bs3LFB3sp1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3sp13SP1S2LF2lo2bs3LFBS2LF2lo2bs3LFBFS2LF2bs3LFB2FBS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOSFFS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOFFS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKe5STKe02LF2sp2lo2bs3LFB3SLO3LOS3ALOFFFFFFFFFFS1R2LF2bs3LFBS1R2LF2bs3LFBFFS2LF2bs3LFB2FBS2LF2bs3LFB2FBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP3sp13SP14HTOPS2LF2bs3LFB3sp14SP1RS2LF2bs3LFB2FB2F0S2LF2bs3LFB2FB2F0". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS D1 CURLO CUR0 DPB B5 B47 B3 B2 B1 BIN PPLO CWP PP0 ALP LFB STKe0 STKe GT NS1 IMG"]
  Lemma mid_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_san_A ()) "PFB,$2.Psp1,$2.Ph1,(3.$4.VR,VHIA,)Pmm,P,(5.&40.)(6.(5.&8.))Px5,(5.&40.)Px6,(5.&40.)Px7,(5.&40.)Px10,(5.&40.)Px11,(5.&40.)Px12,(5.&40.)Px13,(5.&40.)Px14,(5.&40.)Px15,(5.&40.)Px16,(5.&40.)Px17,(5.&40.)Px28,(5.&40.)Px29,(5.&40.)Px30,(5.&40.)Px31,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Plenj,(5.&40.)P,(7.(12.(13.(14.&40.Vsp,)+70.)R16.)(12.R16.(13.(14.&40.Vsp,)+60.)))P,(8.$2.(15.R17.+20.)=)P,(16.$4.VR,VHIA,R17.VLB,(17.(18.$2.$2.)(19.$2.$2.R19.+40.)VLF,)R16.)P,(8.P,$2.Sp(1:.$4.VR,VHIA,R18.)(1:.$4.VR,VHIA,Vh,))P,(8.$2.(1;.$4.VR,VHIA,R19.)(1;.$4.VR,VHIA,Vh,))P,(8.$2.(1<.$4.VR,VHIA,R1:.)(1<.$4.VR,VHIA,Vh,))P,(8.$2.(15.R1=.+40.)=)P,(23.VR,VLB,VLF,R1>.+40.)P,(24.$4.R1<.R1?.(17.$25.(26.R<.)(17.$25.(26.R;.)(17.$25.(26.R:.)(27.$25.)))))P,(24.$4.R1=.(<.R20.+20.)(17.$25.(26.R:.)(27.$25.)))P,(24.$4.R1>.(<.(=.R21.+3.)(>.(?.VR,)))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.+?1.))(17.$25.(28.(;.&8.=))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(17.$25.(28.(;.&8.+?3.))(27.$25.))))))))))P,(24.$4.R1?.(<.(14.&40.Vsp,)-58.)(17.$25.(26.Vs9,)(17.$25.(26.Vs8,)(17.$25.(26.Vs7,)(17.$25.(26.Vs6,)(17.$25.(26.Vs5,)(17.$25.(26.Vs4,)(17.$25.(26.Vs3,)(17.$25.(26.Vs2,)(17.$25.(26.Vs1,)(17.$25.(26.Vs0,)(17.$25.(26.Vra,)(27.$25.)))))))))))))P,(24.$4.R20.R22.(17.$25.(26.(;.&40.R23.))(27.$25.)))P,(29.$4.R21.(<.R23.+8.)(<.(14.&40.Vsp,)-58.))P,(29.$4.R22.Vlo,R24.)P,(2:.$4.R23.)P,(24.$4.R24.VPP,(17.$25.(26.(;.&40.VP,))(27.$25.)))P,(24.$4.R25.VCUR,(2;.Vct,Vcpad,===))P,(2<.$4.R26.VBUF,Vbs,)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R27.VPP,+8.)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R28.VCUR,+20.)P,(2=.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)R29.VBUF,(2>.(2?.(5.&8.)Vbs,)))P,(30.(12.(<.R2=.+40.)VPP,)(12.(<.VPP,+8.)R2=.))P,(30.(12.(<.R2>.+40.)VCUR,)(12.(<.VCUR,+20.)R2>.))P,(31.$4.VR,VHIA,Vh,VLB,VLF,(14.&40.Vsp,)(14.&40.Vsp,)(17.(18.$2.$2.)(19.$2.$2.VPP,(<.VPP,+8.))(17.(18.$2.$2.)(19.$2.$2.VCUR,(<.VCUR,+20.))(27.(18.$2.$2.))))Vm,R2<.)P,(32.$4.(?.VR,)R2=.Vslo,R2?.)P,(32.$4.(?.VR,)R2>.R30.(14.&40.Vsp,))(33.$4.(?.VR,)(1:.$4.VR,VHIA,Vh,)(39.R32.R31.R30.)(9.(:.(;.&40.+:?45<.)(;.&40.R31.)Vgp,Vtp,R2>.R2=.R2<.Vsp,(;.&40.R31.)R2;.R2:.R29.R28.R27.R26.R25.R24.(;.&40.R32.)(;.&40.VCUR,)(;.&40.VEND,)(;.&40.VPP,)(;.&40.(<.R32.+20.))(;.&40.R32.)(;.&40.(<.(=.R32.+3.)(>.(?.VR,))))(;.&40.(>.(?.VR,)))Vs10,Vs11,R23.R22.R21.R20.)VF,(;.&40.+:?4?0.)Vfc,(10.(5.&40.))R2?.(11.$4.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until lenj.
  intros SP1 SP1M HH1 Ehcs Ehtop Estk F64 FRSH FHD HLEN FSH SAVE SLOT SThi STlo MI HPP HCUR HBUF OPP OCUR OBUF APP APC PRES SS1 SS2.
  rt_facts.
  unfold seq_cells in HCUR.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP.
  rewrite Ehtop, Estk in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKe0; lia).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKe0 TOP HTOP; lia]).
  assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
  destruct (frame_factsA R HIA CS h1 LB LF mm FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
  change (64 / 8) with 8 in SBND, APS.
  assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
  assert (BINA : In (BUF, n) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; left; exact BIN).
  assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA h1 LB _ mm LB HH1 ltac:(intros b Hb; exact Hb) _ BIN) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
  assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 64) :: LF)) lo (htop asegs R HIA h) PP 8)
    by (eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]).
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WCP : wcover R LB LF (bv_unsigned sp) W PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (munch_refl W mm) as MU. pose proof (wmono_refl asegs mm) as WM.   (* [comment removed for export] *)
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  lx_pre. lx_run_tac (PLAN [0x52ef8; 0x9990c; 0xae500; 0xaf3ec; 0xaf578; 0xaf57c] [] 152%N).
  lx_tree.
  all: lxr_leaf; lx_carry.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xaf504) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x9990c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename mg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH (FB + 32) 1%nat as OLEN | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mg HH1) as ABg | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => pose proof GT as SPT | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG in SPT | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "GT-CALL" | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply SPT with (CS := CS) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | lazymatch goal with | |- BUF + _ < 2 ^ 63 => clear - B47; lia | |- _ \/ _ => clear - APP APB DPB BUFLO PPLO SP1 SLO NS1 STKe0 F1 FBLO ALO LOS; lia | |- _ => clear - SP1 SP1M SLO NS1 STKe0 F0 F1 F8 F64 ALO LOS ACP B5 PP0 ALP B1 B2 B3; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try clear SPT; try clear OLEN| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 32) [C8 ?lq] |- _ => rename lq into Lw end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename q into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename qq into q end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename rg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rg end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HLg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HLg end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename RRg into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < rg <= 0 |- _ => rename H into RRg end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hqr into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ <= q <= _ |- _ => rename H into Hqr end | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x52ef8; 0x9990c; 0xae500; 0xaf3ec; 0xaf578; 0xaf57c] [] 152%N); lx_tree | |- _ => idtac end.
  all: (lxr_leaf; lx_carry).
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaf3ec) _ _ _ (seg_rom _)] => lx_apply pro_walk | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaf578) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaf57c) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: match goal with |- ?g => idtac "lxw mid_walk: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
