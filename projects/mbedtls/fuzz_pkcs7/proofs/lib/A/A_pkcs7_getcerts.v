(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepCrt CrtFacts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_alloc_lib A_asn1_get_tag_stmt A_asn1_get_tag A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_fuzz_entry.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_pkcs7_free.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00ba72fc544cc841 0 6 0 1 45 1 48 1 58 1 76 1 77 1P00cfc2f8c43fa216 0 7 0 1 72 1 73 1 74 1 103 1 107 1 110 1P00fcb9477562b954 1 2 32 3 0 1 103 1 106 1 32 10 45 1 71 1 74 1 77 1 80 1 87 1 88 1 89 1 104 1 105 1 2 107 2 108 2P0105664731de601f 0 6 0 1 61 1 64 1 77 1 78 1 79 1P02be25d84339b123 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P03125315d06cff2a 0 2 0 1 60 1P03392b33d2d518e3 0 7 0 1 72 1 73 1 74 1 103 1 107 1 110 1P0397134d4aee5619 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P03bd8db7802c8174 0 7 0 1 30 1 61 1 64 1 77 1 87 1 88 1P03d0626d6155532b 0 6 0 1 45 1 48 1 58 1 76 1 77 1P041924ead394e5f4 1 1 16 3 0 1 106 1 107 1 10 55 1 74 1 77 1 80 1 87 1 88 1 89 1 105 1 108 1 109 16P042d83639684b2e5 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P049d3adbb8fac5db 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P04ad9c1562cf57e5 0 6 0 1 45 1 48 1 58 1 76 1 77 1P04b01162168127a7 0 2 0 1 60 1P04f8ee8feda8c00b 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P050eb7249c409445 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P0592e541e9eb5729 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P05d682cd7264d306 0 2 0 1 60 1P05f7a31d8618e482 1 1 16 3 0 1 105 1 106 1 4 68 2 104 2 107 2 108 32P061b06edf3ced641 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P06201e8e2fd05fd1 1 2 32 3 0 1 106 1 107 1 32 3 1 1 105 1 108 1 2 109 2 110 2P062cb1483edc46c1 0 5 0 1 35 1 57 1 76 1 77 1P065736d844816f7a 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P066b8965fd336fed 1 1 16 3 0 1 106 1 107 1 4 69 2 105 2 108 2 109 32P067585a48737e0c9 0 7 0 1 45 1 71 1 74 1 87 1 103 1 104 1P067b55c6333f16af 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P06a1f89026f125b4 1 2 32 3 0 1 117 1 120 1 32 10 49 1 83 1 86 1 89 1 92 1 99 1 100 1 101 1 118 1 119 1 2 121 2 122 2P06c5a2b522bb0910 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P0720914feae79291 0 8 0 1 46 1 73 1 76 1 86 1 89 1 104 1 105 1P07318f0f026c1b7c 0 9 0 1 30 1 49 1 52 1 65 1 66 1 67 1 75 1 76 1P073674ce84028a5d 0 5 0 1 35 1 57 1 76 1 77 1P07532380b4a4802e 0 6 0 1 56 1 72 1 75 1 86 1 105 1P07dd78147c366ef9 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P07fe824eed864ba9 0 6 0 1 45 1 48 1 58 1 76 1 77 1P08202cce4de7c557 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P083e71e848bf773e 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P08b094083b3b27fc 0 5 0 1 35 1 57 1 76 1 77 1P08ebc10a3a4f7c5b 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P090409a693eb57cc 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P090b23e30606fb2e 0 3 0 1 46 1 57 1P090d108fe94f1905 0 5 0 1 35 1 57 1 76 1 77 1P09bd5deaf852937f 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P09d4fc6b3978efca 0 6 0 1 45 1 48 1 58 1 76 1 77 1P09f15f819cb4074e 0 4 0 1 57 1 76 1 77 1P0a066bd2030cd523 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P0a0b620517a1cb56 0 6 0 1 73 1 76 1 86 1 104 1 105 1P0a63850335278567 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P0ab5d15d7defaee3 0 6 0 1 73 1 74 1 103 1 107 1 114 1P0ac7269b0aaf8994 0 14 0 1 46 1 73 1 76 1 77 1 79 1 86 1 87 1 88 1 93 1 94 1 95 1 104 1 105 1P0afa7f569bffd8ec 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P0afff9dc1cfef16e 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P0b418fb7e954e9a5 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P0ba4e20fca69a945 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P0bc38f5e1f4adcde 0 7 0 1 45 1 71 1 74 1 87 1 103 1 104 1P0bf9646d43b46b02 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P0c77b349f5c048a4 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P0cd62ffafe5dcbd4 0 5 0 1 35 1 57 1 76 1 77 1P0cdf4bf1d18d325b 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P0d84068f054cf836 0 7 0 1 45 1 71 1 74 1 87 1 103 1 104 1P0dbcc3a0e9dc5959 0 4 0 1 45 1 104 1 105 1P0e286eacd8ece657 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P0e7a9319423d4be6 0 3 0 1 41 1 76 1P0e84376f805dd9a6 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P0e8e070053edd29c 0 3 0 1 41 1 76 1P0ead179a76dba003 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P0edb585ed3d39e77 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P0f045730bfa7f944 0 4 0 1 57 1 76 1 77 1P0f785c6b085fbf2a 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P0f8814d72681e92f 0 4 0 1 29 1 87 1 88 1P101ce64e89446649 0 6 0 1 45 1 48 1 58 1 76 1 77 1P10516b8f9f956306 0 6 0 1 45 1 48 1 58 1 76 1 77 1P10c0a54ffe839140 0 6 0 1 56 1 72 1 75 1 86 1 105 1P115ab8ce2c50a4d4 1 2 32 3 1 1 104 1 107 1 32 10 46 1 72 1 75 1 78 1 81 1 88 1 89 1 90 1 105 1 106 1 2 108 2 109 2P11c0213db7c1649c 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P11c2bfd04fa7dead 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P1238453a7686ba0f 0 4 0 64 9 64 104 64 105 64P1245af092cc4d8ae 0 6 0 1 61 1 64 1 77 1 78 1 79 1P125af4c07222aecb 1 1 16 3 0 1 106 1 107 1 10 55 1 74 1 77 1 80 1 87 1 88 1 89 1 105 1 108 1 109 16P12b5c1829dd389d1 0 6 0 1 49 1 52 1 65 1 66 1 67 1P12dd57f6dc81516a 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P13381e01d85423f0 0 2 0 1 60 1P139dcb9ca698d159 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P13aaeed3acba7ee3 0 4 0 1 57 1 76 1 77 1P13d4290c143ebd3c 1 2 32 3 0 1 103 1 106 1 32 10 45 1 71 1 74 1 77 1 80 1 87 1 88 1 89 1 104 1 105 1 2 107 2 108 2P1461270c9c657ff7 0 3 0 1 41 1 76 1P149a698210eb9d42 1 1 16 3 0 1 106 1 107 1 10 55 1 74 1 77 1 80 1 87 1 88 1 89 1 105 1 108 1 109 16P14dc51c8287cdab3 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P14e313839371b660 0 4 0 16 56 16 76 16 77 16P151112a8973d2cbe 0 5 0 1 35 1 57 1 76 1 77 1P1554a56e9199b120 0 6 0 1 61 1 64 1 77 1 78 1 79 1P1554f68a48fefed5 0 7 0 1 49 1 83 1 86 1 99 1 117 1 118 1P155ccc214371b01b 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P15793f0513649689 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P158a44247f7cfaaa 0 4 0 1 44 1 103 1 104 1P15b48ca266208fd3 0 6 0 1 61 1 64 1 77 1 78 1 79 1P15ca162ba890895e 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P15f3d4d889c4754b 0 2 0 1 1 1P1669b56e47a40202 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P16786b636781f5ff 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P16835d9326480160 0 4 0 1 29 1 87 1 88 1P1684af81899460e5 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P16d8b840f23d736e 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P16e9074aec18e350 0 6 0 1 45 1 48 1 58 1 76 1 77 1P178ff3f93a12d849 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P179bb04c7603fc57 0 11 2 1 47 1 73 1 76 1 77 1 82 1 89 1 90 1 91 1 105 1 106 1P180fafe8d45a6c55 0 13 0 1 73 1 76 1 77 1 79 1 86 1 87 1 88 1 93 1 94 1 95 1 104 1 105 1P18621391615dfce9 0 10 0 1 50 1 53 1 55 1 59 1 66 1 67 1 68 1 76 1 77 1P18656ec11611f3f6 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P1898020befc8aa56 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P18be70519fe66c61 0 5 0 1 35 1 57 1 76 1 77 1P191dc34af951d676 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P191f67959666de85 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P1960c676b7005ce6 0 2 0 1 67 1P19b159167831a7b0 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P1a0282567b377ae7 1 2 8 2 0 1 103 1 8 2 98 1 104 1 2 105 1 106 1P1a172e39ea0d53f4 0 2 0 1 61 1P1a308ed7331acef8 0 2 0 1 1 1P1a605dc1705e0e85 0 2 0 1 72 1P1a6a32924c1d3d0c 0 3 0 1 41 1 76 1P1a81c5e024b174a5 0 4 0 8 23 8 103 8 104 8P1a99a92c68803ff2 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P1ad470ffd726b69e 0 2 0 1 67 1P1ae1b6590b2ba01e 1 1 64 2 55 1 76 1 3 0 1 75 1 77 64P1af5839740df43dc 1 1 64 2 0 1 75 1 3 2 1 76 1 77 64P1b3585a80e02be05 0 4 0 1 57 1 76 1 77 1P1b4e353af849f12a 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P1b62d2fe05bd05a8 1 1 8 3 1 1 104 1 107 1 8 46 1 72 1 75 1 88 1 98 1 105 1 106 1 108 8P1b6b0b1e9e50d146 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P1b9bf5a78c60d6a5 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P1bc1b1d0ce59cd7f 0 5 0 1 35 1 57 1 76 1 77 1P1c42a835b72ad179 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P1c6c3230b352aa7f 0 6 0 1 45 1 48 1 58 1 76 1 77 1P1c7ebc36705fd97f 0 2 0 1 1 1P1c9acb0e96cae633 1 2 32 3 0 1 106 1 107 1 32 3 1 1 105 1 108 1 2 109 2 110 2P1cd0e468bf736282 0 6 0 1 29 1 41 1 64 1 75 1 76 1P1d8bd75324c6c262 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P1da058c43b640c09 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P1db074e5f531f8d8 0 6 0 1 45 1 48 1 58 1 76 1 77 1P1db96d95f6205c30 0 2 0 1 1 1P1e12df30049ae527 0 11 2 1 48 1 75 1 78 1 79 1 81 1 88 1 89 1 90 1 106 1 107 1P1e2141b1c5be3c3e 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P1e310ec705a5aeca 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P1e5db170e7ee311a 0 4 0 1 57 1 76 1 77 1P1eeb33c5152fe255 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P1eec99c79261bc4c 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P1f1b2fa0bc6ce5de 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P1fa0711812ac0524 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P1fa7158b8c0a4cc4 0 6 0 1 45 1 48 1 58 1 76 1 77 1P1fb1e88b0495d3b2 0 6 0 1 61 1 64 1 77 1 78 1 79 1P207de0143507c682 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P20a611a806cb6578 0 7 0 1 46 1 73 1 76 1 86 1 104 1 105 1P20b055c2e3f4e5ec 0 5 0 1 35 1 57 1 76 1 77 1P212696373ea4cd93 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P212936897690adf3 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P2142f2054079ae95 0 6 0 1 61 1 64 1 77 1 78 1 79 1P216e992683e6456d 0 2 0 1 69 1P219d8a0aba0b1662 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P21a9d7fa0ab76623 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P21b8bd2bc7bc91da 0 6 0 1 61 1 64 1 77 1 78 1 79 1P21ed71a9fa79b177 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P2226bb674e177c68 0 3 0 1 41 1 76 1P2259e9b1918e2db2 0 3 0 1 41 1 76 1P225e909297bc8e60 1 2 32 3 0 1 103 1 106 1 32 10 45 1 71 1 74 1 77 1 80 1 87 1 88 1 89 1 104 1 105 1 2 107 2 108 2P22e9ab63593ab551 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P230114f2cb3e54d0 0 3 0 1 41 1 76 1P2319034295daefd7 0 4 0 1 57 1 76 1 77 1P231ecc621dd2dfee 0 5 0 1 35 1 57 1 76 1 77 1P237f7698bab00e04 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P23bb642968be7d00 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P23bce81796db5fc4 0 2 0 1 72 1P23c37ecd4f992a6b 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P23da2480b0eab5d6 0 6 0 1 73 1 74 1 103 1 107 1 114 1P23e15757380c8bb1 0 6 0 1 61 1 64 1 77 1 78 1 79 1P23ec295072b6aeca 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P23f7e3282abb7c63 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P242b733fd591f9d8 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P246da65337f07bde 1 1 16 3 0 1 105 1 106 1 10 54 1 73 1 76 1 79 1 86 1 87 1 88 1 104 1 107 1 108 16P249944887a441f48 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P24cf9a3a6962dd89 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P2500f6b1ba604f89 0 6 0 1 61 1 64 1 77 1 78 1 79 1P25781251cb5f5faf 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P25f1204dc5dede23 0 2 0 1 61 1P2605811d9fc0813d 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P260d7fd9ec249567 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P265c9be1d20c549d 0 6 0 1 45 1 48 1 58 1 76 1 77 1P266d85367afe763f 0 6 0 1 61 1 64 1 77 1 78 1 79 1P26d4e26c7890a65e 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P26eed69888be87b0 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P271d1ab892da5aa6 0 4 0 1 57 1 76 1 77 1P276f876186e8f3fb 1 2 32 3 0 1 104 1 107 1 32 10 46 1 54 1 73 1 76 1 79 1 86 1 87 1 88 1 105 1 106 1 2 108 2 109 2P27fc6aa5d937cf39 0 6 0 1 65 1 68 1 85 1 104 1 105 1P282774bdaaa55311 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P28297e8a019a3739 0 6 0 1 45 1 48 1 58 1 76 1 77 1P2870effa0c545277 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P28827b9596e9223b 0 16 0 1 45 1 66 1 67 1 71 1 74 1 75 1 80 1 87 1 88 1 89 1 94 1 96 1 99 1 103 1 104 1P294b2f47fea04d49 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P295f6045bea47283 0 3 0 1 41 1 76 1P298beadbcc7cc22d 0 3 0 1 41 1 64 1P29bbdbed4b422263 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P29c54553a40fc48b 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P2a81fe98e1794d56 0 5 0 1 56 1 75 1 86 1 105 1P2aa281b7ae221c60 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P2acaf94b8f4a3602 0 3 0 1 41 1 76 1P2ad7c12f048a1ea5 1 1 16 2 0 1 76 1 3 7 1 77 1 78 16P2ae02a75216034e8 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P2aee83b5c482c3d8 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P2b2d8f8ace00a2e3 0 4 0 1 57 1 76 1 77 1P2bcae26c39f63252 0 4 0 1 57 1 76 1 77 1P2c1eef82ab13c8f3 0 8 1 1 46 1 72 1 75 1 88 1 91 1 104 1 105 1P2c29bfa111f50791 0 4 0 1 57 1 76 1 77 1P2c35406551a84147 0 8 0 1 46 1 73 1 76 1 86 1 96 1 104 1 105 1P2c4d92c59b7cf38e 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P2c56a15cd4dafb84 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P2c7b1e474b783dde 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P2c8a6905adbb4ca0 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P2cad4983a72606b2 0 6 0 1 44 1 56 1 86 1 103 1 104 1P2ce53915417398c6 0 6 0 1 61 1 64 1 77 1 78 1 79 1P2ce6c1cf7419783b 0 6 0 1 45 1 48 1 58 1 76 1 77 1P2d59f5f3f0ea2d10 0 4 0 1 57 1 76 1 77 1P2d8796daef76a34a 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P2d880b77c5e05f75 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P2ddf6b32370d63cd 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P2df6801cb8a49f64 1 2 64 2 0 1 104 1 64 2 55 1 105 1 2 106 1 107 1P2dfd7ebc1d34d31e 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P2e9ef8adba0b7826 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P2efe27c57e1110c5 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P2eff7da28f056476 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P2f030184e89556cd 0 3 0 1 32 1 45 1P2f3e9f8f69cb488b 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P2ff64d0e7f9cb727 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P305217e7bd70a4b8 0 6 0 1 40 1 68 1 85 1 104 1 105 1P306b6e8f5817249c 0 3 0 1 41 1 76 1P306d4fbc36890b20 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P308060686f482dc8 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P30a2569fd41a3c4a 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P30c785324a2a6d4d 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P30d2597bde8bc316 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P30e65a577c6faf5d 0 4 0 1 57 1 76 1 77 1P3128b44a3cb7ad88 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P31291a9fd8bcd7d7 0 6 0 1 44 1 84 1 86 1 103 1 104 1P314bfe63d50922af 1 2 32 3 0 1 105 1 106 1 32 3 1 1 104 1 107 1 2 108 2 109 2P3162867d91a70c79 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P31953b480bf3c6ab 0 5 0 1 35 1 57 1 76 1 77 1P31abcb60403f3ea0 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P31adc78d9f6e895f 0 8 0 1 45 1 71 1 74 1 87 1 90 1 103 1 104 1P3203e5b7dace2be2 0 2 0 1 67 1P32374837d7b36259 0 4 0 1 57 1 76 1 77 1P32812015827719d2 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P32997a4aeb30e766 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P32abb373768a3853 0 4 0 1 57 1 76 1 77 1P32b80bd4139cde51 0 4 0 1 29 1 87 1 88 1P32bf1545743588d5 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P32c84705ba8a9d09 0 4 0 1 48 1 117 1 118 1P32c8c88d5c020dea 0 9 0 1 46 1 73 1 76 1 86 1 87 1 88 1 104 1 105 1P32e8a8d98e8b2280 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P332e6fe6e650ad81 0 8 1 1 47 1 74 1 77 1 87 1 97 1 105 1 106 1P332f32756a718001 0 3 0 1 41 1 76 1P33531396680a6127 0 6 0 1 61 1 64 1 77 1 78 1 79 1P33566778d7345de1 1 2 32 3 0 1 105 1 106 1 32 3 1 1 104 1 107 1 2 108 2 109 2P337f349e4d88e490 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P33c8de3e53b99151 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P343e21c46efdda3e 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P343fe41cba558e19 1 2 32 3 1 1 105 1 108 1 32 10 47 1 55 1 74 1 77 1 80 1 87 1 88 1 89 1 106 1 107 1 2 109 2 110 2P344409cf5c9a084d 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P346ea2840db320b3 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P3477fb599c7a856d 0 2 0 1 68 1P35021e5c07e5383f 1 1 16 3 0 1 106 1 107 1 10 55 1 74 1 77 1 80 1 87 1 88 1 89 1 105 1 108 1 109 16P35273478475f0e26 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P35372d9efc5ab712 1 2 32 3 0 1 105 1 106 1 32 3 1 1 104 1 107 1 2 108 2 109 2P3549311a6f6237b1 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P354cf0bbab1a9851 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P356c3ca116f9409c 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P3576dbb17d876060 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P359228df84c94117 1 2 32 3 0 1 105 1 108 1 32 10 47 1 55 1 74 1 77 1 80 1 87 1 88 1 89 1 106 1 107 1 2 109 2 110 2P35b1caf7c0776605 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P35f428e4e68b8667 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P36b638be6688d9ed 1 2 32 3 0 1 104 1 107 1 32 10 46 1 54 1 73 1 76 1 79 1 86 1 87 1 88 1 105 1 106 1 2 108 2 109 2P36c8f3cfd698c803 0 8 1 1 47 1 74 1 77 1 87 1 90 1 105 1 106 1P36ccaa6c6cee60b2 0 5 0 1 56 1 75 1 86 1 105 1P37f6ef4c4bc10214 1 1 64 2 1 1 75 1 3 0 1 76 1 77 64P37fc55e8aa0bd6ac 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P3813e30062f71239 0 2 0 1 1 1P38b3e444cfef3a5b 0 7 0 1 45 1 48 1 58 1 68 1 76 1 77 1P38e48007ac045cf2 0 7 0 1 45 1 48 1 58 1 61 1 76 1 77 1P39098947e7bb5153 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P3975f3a14a5e1102 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P39a1752aa62b8596 0 9 0 1 45 1 71 1 74 1 87 1 88 1 89 1 103 1 104 1P39cf6683e282ddfe 0 5 0 1 35 1 57 1 76 1 77 1P39e104b569e08435 1 1 16 4 1 1 29 1 42 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P3a83a1f64946da05 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P3a86df2e4777e6cc 0 5 0 1 35 1 57 1 76 1 77 1P3b2ec3e2adf570b3 1 2 32 3 1 1 105 1 108 1 32 10 47 1 55 1 74 1 77 1 80 1 87 1 88 1 89 1 106 1 107 1 2 109 2 110 2P3b4a5ea425b78b6d 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P3b59fa9317c500db 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P3c11d7a98e657774 0 6 0 1 61 1 64 1 77 1 78 1 79 1P3c15981f77b66027 0 13 0 1 45 1 48 1 49 1 51 1 58 1 59 1 60 1 65 1 66 1 67 1 76 1 77 1P3c1da111d8f5edca 0 7 1 1 46 1 49 1 59 1 69 1 77 1 78 1P3c30460a1e8c1285 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P3c61d0d492882d4b 0 4 0 1 29 1 87 1 88 1P3cd157456d2f944a 0 7 1 1 46 1 49 1 59 1 62 1 77 1 78 1P3d66e7e0b9176670 0 10 2 1 47 1 50 1 51 1 53 1 60 1 61 1 62 1 78 1 79 1P3d6d09f148ba3ab9 1 1 16 3 1 1 27 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16P3d89bf547123fb9f 0 2 0 1 60 1P3da5ebe7694b8a7b 0 2 0 1 62 1P3ddcb8d0daa789ec 0 8 0 1 45 1 48 1 58 1 59 1 60 1 76 1 77 1P3e603aaa0ef54e56 0 3 0 1 41 1 76 1P3e9d419a306e3203 1 1 16 3 0 1 106 1 107 1 10 55 1 74 1 77 1 80 1 87 1 88 1 89 1 105 1 108 1 109 16P3eddad68497baaec 1 2 32 3 0 1 76 1 79 1 32 3 1 1 77 1 78 1 2 80 2 81 2P3ef7a471087a5f56 0 3 0 1 41 1 76 1P3f180c1c82736203 1 1 8 3 0 1 103 1 106 1 8 45 1 71 1 74 1 87 1 97 1 104 1 105 1 107 8P3f3eefe46ad68dc7 0 5 0 1 35 1 57 1 76 1 77 1P3fc326dda4600d9b 1 1 16 2 1 1 77 1 9 45 1 46 1 49 1 52 1 59 1 60 1 61 1 78 1 79 16N000c210e4f5c9e3fN00b8f0cf57298935N00c9ac9919e54b99N00d3b9925b093046N010ac2ac90f55e49N01266bd34937d298N025233dc3b5c1f16N02d3088446690a8bN0319a47215940a95N036293f6efdeef5aN050ae484feca2d2dN05237547bb792211N053ec18edcf3a415N0559cd5df63cbd39N056f65d926f22fe4N05705493b6c146a7N058e38af12d1e69bN068f1f7ca6ec0b15N069df2b34f816254N06e24ffda6a1b24bN07131fcad6bd3f8fN079aa265dad3a559N07dd62b7593825a8N07e5ebadc2e3f206N0812ab77addbb3a3N0824e32658018da4N08eb515c37b86969N090c634db6437a90N092e768052dcbba8N093c51550743e1c7N09c5886c0ebe8a94N09f59e74dcb31701N0aa4bfef710a2784N0af5bc3f8f631abbN0b1d3f3ff49d5ed4N0b3879189493c149N0beab4e920cbe3baN0c70e11ee483d5b7N0c80a95113995cb1N0cae7723fa8c6e3bN0ccf0f89509aea8dN0d1735c33b440228N0d58ee03ab46f898N0d6dfc97b8f02d1fN0d74d318f6253d50N0e449c2f4f9f9e5eN0ee7edd1ec932767N0f4c85f44acf15a7N0f80b8ef09e9b8b9N0f882cea621c67dcN0f9a138f9a65bd72N0fd2ad9bbbd78f13N0ff39b8b2fa726c6N105318e28d9b2793N107e81d5800b2234N10e3461e8f876d70N112c1d38c4da81edN113b7b2edb2d2446N114ae48a05cf215bN120d1be4bb096d20N1218bf8cfcec0136N122419fb2dc71e56N124383db47a1b31bN127853f40252b724N12e0869318bee935N12f00b938c65979aN12f71a692a31dd0eN1302dcbdc0a08bedN135fde5fd1933e7bN138f7a7dadcb4a41N1431f0e404bd44e2N143d8da586048513N14af9bf85ff0f27cN14b40a3ef33dcf94N14c63503feb55908N14caafd05f81577dN14dba5e0af11d5d7N152c495dd7b40910N1537ba7b7624b930N1545658c86995c8cN15a4987fc923d9b1N15b0288d0e5728feN15f94005b778504dN160e66a6870ec39bN165ec3a38f04b51bN1704835d7f64bc89N1784a5568325f600N17a2461320f009d9N17c6d2070e178199N17dfb29c9bdd19b5N17e0a629e904300dN17e2bb8513658c75N17e4a8b4f86922a4N180cf614c7b7d19dN184bf55835538c84N1887282b3b3475e4N18e0f539f7168d8fN18ed1af08f46461cN18f702ee6bb3ba8aN18fa394268f60dbcN18fcd13379f8d9ecN190844a0a65eeab8N194a6ce4e1715922N19616f4cade52bdbN1989481ad2db378cN19ddcf61435898b1N1a19a7390b59973fN1a33f386cf7f339eN1ad8b862731e75aaN1afc9a55535307d1N1b1899f86a70a7f5N1b1d0da6b2b29cd4N1b20c95d0f8c3320N1b3159459bb190ffN1b4802341483044dN1b70f664116cd7fbN1c0f4c6f9abfd0beN1c4192d2ae97b02aN1c5a1cb062cfc4b8N1c9330ea37b49e64N1cb17bdc89dc598aN1d068d00a6281526N1d203fd809ea4972N1d2f987958862cf1N1d35d472c087aa3dN1d552d4af42c9693N1da4a4bce27b43f8N1deb2ece5eff749bN1e5f24f6cb4f07f9N1e6aafe266e09746N1e74379723febd8dN1e9c441a3fc931cfN1ec53acbfad6577fN1fb3647b22083b90N2031b090a453ed6bN2038fc2e3618eaa8N20910c24947cedd1N20bcfa28203d6f82N20e1ccace9d4c93cN210a5e7db52e7293N2115a09b71794372N2154d006f9ffe1a3N2187c650a1819731N21f3471db59c7746N221144df740b9c12N221f2cd9cbfb233aN226701c689649878N227a9f4071fa61b9N2295b2b02459b44fN2305e7a35a37f28cN23393c968d9ffe35N233ee6ddb0131ae8N2345c477d2d97966N23a0f7ed30a48669N243c2146d5d627b7N2514e6f9ce4b9f47N2515e0a14f9fec8dN25195430337b2235N252ca316bf429324N256169e0896aa557N25adffd46a6a0aecN25fedbec65f8efc7N26149e27a3c5ed57N2622d3630f45e482N267be017e4f7ab07N2750aa7123af7ee9N275727ecd6e993f0N27607235025a20adN2789eb91eb4eed76N279da4cd78e527d8N27e1732b5940eb8aN2841d52d0f514efcN2847365921e11902N286d6b628b37d78eN288679fed60bb045N28bfc7faf3540b2aN28f9c3482bc1ef32N293c62558322ea82N295eb03518992cabN2a2d139f82038dcaN2a41c90d89291701N2a56d3fc64a9cbc3N2ad1da1964fc3ccbN2b0f9c3236370fb3N2b17f803f60dbe1aN2b6f1a52f8ce4612N2c1865e6c97f0469N2c4c18d5fc1e23bbN2c62e636a8e2ea82N2c64f1c0b79ce09dN2c6af656697f5eafN2c7ce5d868e1c06aN2c8640058b3ff587N2c93df4be8304552N2d024540d656a5c4N2d40850a679d671bN2d54c00384fdc3bbN2d6be373e61b3f49N2dd4a69286721b75N2ded97e8c9176abaN2e019fe98f1c5d8eN2ea0e0b0dab0ed14N2eab6b98f70b94a8N2f1582571036cba1N2f3471a16d0d8ee8N2f48ea766714707bN2fbb8b6bc289dbf2N2fc0d5d363bfcae1N302e0a4974dfbe5dN308a87946c9b8b3aN309ff18ace06642aN30a911f17ee1ce82N30afa60c6af145e6N30c32aae4c610f89N30d79e3db88cc60bN310014a924afdc2dN3114c39631e3e2f9N311d228ddcfc30a6N3194192f91ddb776N3194e5cf3c2831b9N31aeefeba1a82de1N31d6c17261753cd6N31ea780a5135bf1bN31ec80e399ab2ee7N31ef356ac87ebe5bN3226a507f989dcb8N32930b5171413dffN32e2e0a6f97c35a6N331bec861ff1e0f3N336ea5d87b1fc7f0N33e9fd573d8309feN33f5c950ab5b05f5N340bc98c761d10a2N3419e4e16a870864N344b2ca3f06add7fN344d7aab56737214N3462c107e33c98d5N348a57f9f746322dN3490267b5cba565bN34a9352c13c02f19N34ab3872a61febf4N351ea17d360f711eN3556cfd61b26ef1eN356069f127b6ea61N357055986773768aN359fb78f2712ec0bN35c163f9044512c6N3612f43537b8e2d8N3621f3e95f9f0621N363cc6234a43a629N363f16ccb5b8e8b1N36b4edc4e4318dfaN36e91e14342b380dN36f111d5d8bb6df3N3724ba6c95791306N3772fcfa8e6f2f38N37a183f032bd1d40N37aa4619f121dcefN37f7542ce5892651N39e484ab48c812f1N39f9404b411f1f75N3a2c15c5ee62a55eN3ac60f26b835d8d5N3ae9bbce2a3b839dN3b71c4c917485693N3c0e9dd78132c1a0N3c31cc7f58d7826bN3c3bb620c8be8ceeN3c5132155de89f0dN3c52f7664c6b2a20N3c8bab782459ebdbN3cdf7e04c57047a1N3ce49de9033b9840N3d40424f00846cf6N3d6fb8f1f2016d3bN3d9c43341120f673N3da47c2aab55ba7aN3dd2654217c3ee81N3dd7ad756bbcde2eN3e0b6ef90bb1cf44N3e3c7b4a59872b09N3e4f0e77f470738fN3e6810cc0fb29501N3e6d0488ee609c34N3ea014a7487d5f1eN3ea660215d35d1e0N3ec56c2d39fdd3eeN3ed5a1f055f37678N3edb9acbc5e9e248N3efe3681536beb89N3f043821eff4d050N3f0ec65ebcfafbf7N3f171b60b5752ad0N3f7557dfd29fb96aN3f8600c2707098a9N3fbd6e88d4da76f6"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_getcerts () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Spec.RepCrt.crt_zero"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Spec.RepCrt.CRT_SIZE"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_PKCS7_GETCERTS"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Walk.Call.LUI_FFFFB"; "A_X509_CRT_PARSE_DER"; "Walk.Call.MIDP"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Walk.Call.EPOST"; "OSSVerify.KrLib.Spec.SInv.si_P"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Walk.FFRg"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_pkcs7_getcerts_stmtC.pkcs7_get_certs_postA_c"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"].


Definition A_PKCS7_GETCERTS : Z := 0x098028.      (* [comment removed for export] *)
Definition A_SMALLOC_1 : Z := 0x52af8.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_X509_CRT_PARSE_DER : Z := 0x0a98d4.  (* [comment removed for export] *)
Definition A_ASN1_GET_TAG_G : Z := 0x0990e0.     (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variable PK : pk_class asegs.
  Variable SI : sinv (arl_L R).
  Variables (PHIc : Z -> Z) (FFRc : Z -> Z -> Z) (CNTc : Z -> Z) (STKc : Z).
  Hypothesis CRTPARSE : x509_crt_parse_der_stmtA asegs R HIA PK SI PHIc FFRc CNTc STKc A_X509_CRT_PARSE_DER.
  Hypothesis PHIc_mono : forall n n', 0 <= n <= n' -> 0 <= PHIc n <= PHIc n'.
  Hypothesis FFRc_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRc n d <= FFRc n' d.
  Hypothesis CNTc_mono : forall n n', 0 <= n <= n' -> 0 <= CNTc n <= CNTc n'.
  Hypothesis STKc0 : 0 <= STKc.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKg : Z := 176 + Z.max (Z.max STKc 16) (arl_need_smalloc R).

  Definition FFRg (n d : Z) : Z := FFRc n (d + 1).


  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF CRT lo slo d : Z) (bs : list byte).
  Hypothesis HPP0 : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis AL8 : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HB : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis W1 : BUF <= P. Hypothesis W2 : P <= END. Hypothesis W3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B47 : BUF + Z.of_nat (length bs) < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BSMALL : Z.of_nat (length bs) < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DPD : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis CZ : crt_zero asegs m CRT.
  Hypothesis CAL8 : CRT mod 8 = 0. Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CRT CRT_SIZE.
  Hypothesis CRTLO : CRT + CRT_SIZE <= lo.
  Hypothesis DCB : CRT + CRT_SIZE <= BUF \/ BUF + Z.of_nat (length bs) <= CRT.
  Hypothesis DCD : CRT + CRT_SIZE <= hl_data_lo L \/ hl_data_hi L <= CRT.
  Hypothesis DPC : PP + 8 <= CRT \/ CRT + CRT_SIZE <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKg.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_1 in SM1; unfold STKg in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Ltac kz K := first [ rewrite Z.mod_small in K by lia
                     | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by lia
                     | apply land64_zero in K; [| lia] | apply mod64_zero in K; [| lia]
                     | apply land64_nonzero in K; [| lia] | apply mod64_nonzero in K; [| lia] | idtac ].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lx1,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La0,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Ls11v,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(7.(5.&8.))Ljm,(7.(5.&8.))(8.(9.$0.R19.(:.(;.R14.(<.&40.R17.)Vgp,Vtp,R13.R12.R11.Vsp,(<.&40.R17.)R10.(<.&40.VEND,)R?.R>.R=.R<.R;.R:.(<.&40.R18.)(<.&40.VPP,)(<.&40.VCRT,)(<.&40.(=.R18.+20.))(<.&40.(>.(?.VR,)))Vs7,Vs8,(<.&40.(=.(10.R18.+3.)(>.(?.VR,))))(<.&40.R18.)R5.R9.R8.R7.R6.)VF,(<.&40.+9815<.)Vfc,(11.(5.&40.))R15.(12.$4.)))(8.(8.(13.(14.(15.&40.Vsp,)+;0.)R17.)(13.R17.(14.(15.&40.Vsp,)+:0.)))(8.(9.$2.(16.R17.+20.)=)(8.(17.$4.VR,VHIA,R16.VLB,(18.(19.$2.$2.)(1:.$2.$2.R18.+80.)VLF,)R15.)(8.(9.P,$2.Sp(1;.$4.VR,VHIA,R16.)(1;.$4.VR,VHIA,Vh,))(8.(9.$2.(1<.$4.VR,VHIA,R16.)(1<.$4.VR,VHIA,Vh,))(8.(9.$2.(1=.$4.VR,VHIA,R16.)(1=.$4.VR,VHIA,Vh,))(8.(9.$2.(1>.$4.VR,VHIA,R16.)(1>.$4.VR,VHIA,Vh,))(8.(9.$2.(1?.$4.VR,VHIA,R16.)(1?.$4.VR,VHIA,Vh,))(8.(9.$2.(20.$4.VR,VHIA,R16.)(20.$4.VR,VHIA,Vh,))(8.Pmo,$21.(22.(23.$4.VR,VHIA,R17.R1.)(23.$4.VR,VHIA,Vh,R1.))(8.(9.$2.(16.R18.+40.)=)(8.(24.VR,VLB,VLF,R18.+80.)(8.(25.$4.R15.R18.(18.$26.(27.R4.)(18.$26.(27.R3.)(18.$26.(27.R2.)(28.$26.)))))(8.(25.$4.R15.(=.R18.+20.)(18.$26.(27.(<.&40.=))(28.$26.)))(8.(25.$4.R15.(=.R18.+28.)(18.$26.(29.#18.R1.)(28.$26.)))(8.(25.$4.R15.(=.R18.+40.)(18.$26.(27.(<.&40.=))(28.$26.)))(8.(25.$4.R15.(=.(10.R18.+3.)(>.(?.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))(8.(25.$4.R15.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R15.(=.R17.+30.)(18.$26.(27.(<.&40.R18.))(28.$26.)))(8.(2;.$4.R15.R17.(=.R17.+30.))(8.(2;.$4.R15.(=.R17.+38.)(=.(15.&40.Vsp,)-68.))(8.(2;.$4.R15.Vlo,R17.)(8.(2<.$4.R15.)(8.(25.$4.R15.VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))(8.(2=.$4.R15.VCRT,)(8.(2>.$4.R15.VBUF,Vbs,)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R15.VPP,+8.)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R15.VCRT,$30.)(8.(31.(13.(=.R18.+80.)VPP,)(13.(=.VPP,+8.)R18.))(8.(31.(13.(=.R18.+80.)VCRT,)(13.(=.VCRT,$30.)R18.))(8.(32.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(28.$33.)Vm,R15.)(34.$4.(?.VR,)R15.Vslo,(15.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 DCD; try lx_pin1 CAL8; try lx_pin1 DPD; try lx_pin1 BUF0; try lx_pin1 AL8; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 BUF; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 DIMG; try lx_pin1 STKc0; try lx_pin1 CNTc_mono; try lx_pin1 FFRc_mono; try lx_pin1 PHIc_mono; try lx_pin1 CRTPARSE; try lx_pin1 CNTc; try lx_pin1 FFRc; try lx_pin1 PHIc; try lx_pin1 SI; try lx_pin1 PK; try lx_pin1 GETTAG; try lx_pin1 NS1.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02O0@D10639180170.190D10639329459.110D14194668102.190D1699716194.111 D1703908936.191 D18621761100.156D2457697668.189 D29569067336.189D31414394129.191D3160262661.190 D32458983519.189D32606360469.192D3267764854.155 D3267764854.156 D3269959874.154 D3269959874.155 D3375410824.188 D36104740328.190D40204540626.191D45716866873.188D46793042006.110D46793187695.190D50256927948.157D51052764813.157D560907438.112  D60098777666.111D60111245650.110D60111362152.191D60111362155.190D62009673038.192D62011770188.112D65213503937.191D65226085355.111D68407129291.188D6911780558.188 D9109149383.191 L10646859417.10 L10649519402.1  L10837002389.2  L12654381620.1  L13422353008.163L15629616632.10 L15756354262.7  L16772787627.1  L17701970480.1  L18546069956.115L18546069956.195L19548981077.163L19980016842.10 L21980071943.1  L24133462171.158L24524441946.113L27188209011.195L27729706458.182L29444833228.4  L29604608213.0  L29738741675.1  L32463525127.1  L32698691262.98 L33472729358.119L33483560980.11 L33485826452.1  L37156630869.0  L38385093968.1  L3839370119.1   L38948636245.0  L39188636933.0  L39332637397.0  L40226756952.1  L40228640085.0  L4065519265.0   L43055402687.123L43582648292.1  L48117620909.92 L48119718054.159L48119718057.158L50790731766.9  L51038230714.183L51609971893.161L53537894342.3  L53570331885.93 L53572429033.163L53582991471.93 L53582991979.163L54437681876.7  L56301984508.1  L57355539152.162L57355762177.15 L58790154276.10 L59308634497.16 L60558678699.1  L61437265048.2  L63405906047.1  L65225890918.1  L66151427842.16 L6910010092.158 L7040749983.114 L7715476710.125 L9356559645.14  P1041497315.153 P1041497315.157 P30285507275.153P30285507275.157Q10533598597.114Q10594483358.196Q10651763882.116Q12660624644.120Q13345046842.114Q13349241860.197Q1540433385.157 Q1706006094.117 Q23927511184.118Q23937998252.114Q24133462171.197Q24137657765.195Q24137657789.199Q30220990907.196Q31036470288.153Q31599749226.114Q31603944788.197Q32440833928.195Q33196749121.120Q35653441506.113Q36104740334.197Q38248895667.119Q40277518033.157Q42437204328.153Q42439382243.122Q42441479392.201Q43880146031.119Q46805771343.116Q47241206720.114Q48119718056.196Q48132302231.195Q50790663760.157Q56533317812.196Q59310664043.114Q59310664043.195Q59323247700.196Q59323247701.197Q59865520188.122Q59867617343.201Q60109315147.113Q62011770184.118Q62022254708.114Q6203790515.153 Q62144309170.114Q62156890764.197Q64681502665.201Q64683599818.122Q65215601095.117Q65901052544.197Q65913636798.114Q67028613866.153Q6897428426.199 Q6897428434.195 Q6910010092.197 Q9109149378.197 Q9350548487.138 00000]01=01>01[02I02J02K03503603703a04R04S04T04U04V04W04X04Y05C05c06P06Q07<07_08C08g09X0:I0;30;P0<>0<[0<\0=F0=G0=O0=S0=[0=`0>T0>\0>j0>n0?20?30?40?h0@E0@I0@h0A^0BM0C70CG0CH0CL0CP0DC0DD0DE0DF0DG0DK0DO0DP0DQ0DR0DW0DX0DY0El0F00F\0GN0H@0HV0ID0J90JE0JF0JG0JH0JI0Jc0Jh0Ji0K>0KX0Ki0Km0L50L:0L?0LY0M80Mb0NB0Nl0OW0PB0Po0Q\0R90RX0S50SS0ST0SU0T<0TV0U60Ub0VA0V`0W?0W^0XL0XM0XN0XO0Xm0YT0YU0Z20ZT0[90[\0\D0\d0]A0]_0^Q0_C0_m0_n0_o0`00`10`20`30`40`M0`g0aA0aa0ab0ac0b[0cK0ce0cf0cg0dY0e80eW0f60f70f_S1R4STKc2LF2sp2PP2bs3LFB4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp2PP3CRT2bs3LFB3CRBFS1R4STKc2LF2sp3CRT2bs3LFB3CRBS1R4STKc2LF2sp3CRT2bs3LFB4lxHn3sp13H264LFB'2FBFFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBFFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R3HIA4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2h12FBFFFFFFFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp2PP3CRT2bs3LFB3CRBS1R4STKc2LF2sp2PP2bs3LFB4lxHn3sp13H264LFB'2FBFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H243H264LFB'S1R3HIA4STKc1h2LF2sp3CRT2bs3LFB3CRBS1R4STKc2LF2sp3CRT2lo2bs3LFB3LOS3CRBS1R4STKc2LF2sp3CRT2lo2bs3LFB3LOS3CRBS1R4STKc2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp3CRT2bs3LFB3CRBS1R4STKc2LF2sp3CRT2bs3LFB4lxHn3sp13H264LFB'2FBS1R4STKc2LF2sp3CRT2bs3LFB3CRBFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBFS1R4STKcS2PPS3BUF2bsS3BUFS1R4STKc2LF2sp2bs3LFB3SPR4lxHn3sp13H264LFB'2FB2F02F8S1R4STKcS1R2lo3LOS3ALOS2FBS2PPFFS1R4STKc2LF2sp2bs3LFB3SPR4lxHn3sp13H264LFB'2FB2F02F8S1R3HIA4STKc1h2sp3TOP3sp13SP1S2spS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2sp2bs3SPA3LFB3SPR4lxHn3sp13H223H233H243H26S1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FB1c2HcS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R2FB4SBlo4SBhiSS2FBS2FBS1R4STKc2LF2sp3BUF3CRT3slo2bs4SLOS3LFB3ALO3CRB4BUFCFFFSS2FBS2FBSSSS3sp1SSS1R4STKc2LF2sp2PP1P3END3BUF3CRT2lo2bs3PP02W12W22W33DPB4CRT03DCB3DPC3SLO3LFB3SPR3CRBS2FBS1R4STKc2LF2sp3CRT2lo2bs3SLO3LFB3LOS3ALO3CRBS1R4STKc2LF2sp2lo2bs3SLO3LFB4lxHn4LFB'2FB2F05ACLloS1R4STKc2LF2sp2lo2bs3SLO3LFB4lxHn4LFB'2FB2F05ACLloS1R4STKc2sp2lo3SLO3LOSS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H243H264LFB'2FBS1R4STKc2LF2sp3slo2bs4SLOS3LFB3ALO4lxHn4LFB'2FB2F02F1S2sp3sp13SP1FFFFS1R4STKc2sp2lo3SLO3sp13SP1S3CRTFS1R4STKc3ACV2FB2F02F1S1R4STKc2sp2lo3SLO3sp13SP1S1R4STKc2FB2F02KbS2FBS2LF3LFBS3sp1S3CRTS2FB2r03F641q1r1H2H02q02H4S1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2sp2bs3LFB3SPR4lxHn3sp13H223H26S1R4STKc2LF2sp2PP3CRT2bs3LFB3CRBS1R4STKc2sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R4STKc2LF2PP2lo2bs4PPLO3LFB4lxHn3sp14LFB'S1R4STKc2LF2PP2lo2bs4PPLO3LFB4lxHn3sp14LFB'S1R4STKc2LF3CRT2lo2bs5CRTLO3LFB4lxHn3sp14LFB'S1R4STKc2LF3CRT2lo2bs5CRTLO3LFB4lxHn3sp14LFB'S1R4STKc2LF2sp3CRT2bs3LFB3CRBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2PP3CRT2bs3LFB3CRBS1R4STKc2LF3BUF3CRT2bs3LFB3CRBFFS1R4STKc2LF2sp2bs3LFB4lxHn3sp13H244LFB'S1R4STKc2LF3CRT2bs3LFB3CRBS1R3HIA4STKc1h2LF3CRT2bs3LFB3CRBS1R3HIA4STKc1h2LF2sp3CRT2bs3TOP3LFB4HTOP3CRBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R3HIA4STKc1h2LF2sp2bs3TOP3LFB4HTOP4lxHn4LFB'FFFS1R4STKc2LF3BUF3CRT2bs3LFB3CRBS1R3HIA4STKc1h2LF2sp2lo2bs3TOP3LFB4HTOPFS1R4STKc2LF3CRT2lo2bs3LFB3CRBS1R3HIA4STKc1h2LF2bs3LFB4lxHn4LFB'S1R4STKc2LF3slo2bs4SLOS3LFB4lxHn4LFB'S1R4STKc2LF3CRT3slo2bs4SLOS3LFB3CRBS1R4STKc2LF3slo2bs4SLOS3LFB4lxHn4LFB'2FBS1R4STKc2LF2sp3CRT2lo2bs3LFB3CRBS1R4STKc2LF2PP3CRT2bs3LFB3CRBS1R4STKc2LF3CRT2bs3LFB3ALO3CRBS1R4STKc2LF2sp2lo2bs3SLO3LFB4lxHn4LFB'2FB2F05ACLloS1R4STKc2LF2sp2lo2bs3SLO3LFB4lxHn4LFB'2FB2F05ACLloS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS4lxHn4LFB'FFFFFFFS1R4STKc2LF2lo2bs3LFB3LOSS1R4STKc2LF3CRT2bs3LFB3CRBS1R4STKc2LF3CRT2bs3LFB3CRBS1R4STKc2LF2bs3LFB4lxHn3sp14LFB'FFS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHn4LFB'2FB2F0S1R3HIA4STKc1h2LF2sp3CRT3slo2bs3TOP3LFB4HTOP3CRBS1R4STKc2LF3CRT2bs3LFB3CRBFFS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS4lxHn3sp13SP14LFB'S1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBS1R4STKc2LF2bs3LFB4lxHn4LFB'2FBFS1R4STKc2LF2bs3LFB4lxHn3sp13H253H264LFB'". (* [comment removed for export] *)
  #[using="LOS LFB TPV SPH SPA TOP SLO SLOL SLOS DPC DCB CRTLO CWC CRT0 CZ DPB BSMALL B47 W3 W2 W1 BIN HB PPLO CWP PP0 HPP0 STKc SM1 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(34.$4.(?.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VCRT,$30.)(35.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)$36.(:.(;.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VCRT,)R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(<.&40.$37.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST SS MI OPP OCRT.
  unfold A_PKCS7_GETCERTS.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(first [ clear - LOS SLO; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  pose proof (rw_cells_bound _ _ _ _ HPP0) as PPB.
  cbn [cells_size csize Nat.add] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  unfold crt_zero, CRT_SIZE in CZ.
  pose proof (rw_cells_bound _ _ _ _ CZ) as CRB.
  cbn [cells_size csize Nat.add length] in CRB.
  unfold CRT_SIZE in *.
  destruct (hm_apart asegs R HIA h LB LF m HH) as [HBR _].
  destruct (proj1 (Forall_forall _ _) HBR _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _).
  cbn [fst snd] in BUFC.
  clear HBR.
  pose proof HB as HBm.
  pose proof (hcs_block asegs R HIA h LB LF m BUF _ HH BIN) as CBUF.
  carve_frame 160%nat ST.
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
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52af8] [] 211%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. try (clear HBm). try (pose proof HB as HBm).
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -160) ST ltac:(first [ clear - SP1 SLO; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 338680) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (clear - LFB; unfold LFMAX_CRT in LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      pose proof (presA_bytes_at asegs R _ _ _ _ _ _ m1 m2' BUF bs HP1 HBm ltac:(eapply client_range_block; [apply in_app_iff; left; exact BIN| clear; lia| clear; lia]) I) as HB1. clear HBm.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _).
          (* [comment removed for export] *)
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      assert (INF : In (FB, 128) ((FB, 128) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 128 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 88) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
      pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m3 FB 128 HH1) as AP.
      assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      assert (ACLlo : alloc_ceiling <= lo) by (first [ clear - ALO LOS; lia | lx_side_lia ]).
      assert (APB : FB + 128 <= BUF \/ BUF + Z.of_nat (length bs) <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
      pose proof (fresh_apart_client R LB LF lo PP 8 FB 128 FRSH ltac:(eapply (client_range_inside L); [exact CWP| intros b Hb; exact Hb| clear; lia| clear; lia]) ltac:(clear; lia) ltac:(clear; lia) ACLlo) as APP.
      pose proof (fresh_apart_client R LB LF lo CRT 744 FB 128 FRSH ltac:(eapply (client_range_inside L); [exact CWC| intros b Hb; exact Hb| clear; lia| clear; lia]) ltac:(clear; lia) ltac:(clear; lia) ACLlo) as APC.
      pose proof (art_stk_high asegs R HIA) as STKH.
      assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
      pose proof (apart_shadow_client AL CS FB 128 FB (shadow_of AL FB) 16 CSOK CFB CFB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as APS.
      unfold shadow_of in APS. rewrite <- SHFB in APS.
      pose proof (hcs_shadow_band asegs R HIA h FB (CFB FB ltac:(clear; lia))) as SBlo. pose proof (hcs_shadow_band asegs R HIA h (FB + 8 * 15) (CFB (FB + 8 * 15) ltac:(clear; lia))) as SBhi.
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi.
      assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 16 <= alloc_ceiling) by (first [ clear - SBlo SBhi; lia | lx_side_lia ]). clear SBlo SBhi.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 56) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 56) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 56 - Z.of_nat 8) with (sp1 + 48) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 24; 8; 56]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat L1C FRM3. chunk_split FRM3 1%nat JMC FRM4. chunk_split FRM4 1%nat L2C FREST.
      lazymatch type of L1C with rw_cells _ _ ?a _ => replace a with (FB + 32) in L1C by (clear; lia) end.
      lazymatch type of JMC with rw_cells _ _ ?a _ => replace a with (FB + 40) in JMC by (clear; lia) end.
      lazymatch type of L2C with rw_cells _ _ ?a _ => replace a with (FB + 64) in L2C by (clear; lia) end.
      clear FLNK FREST.
      cb8_to_c8 FHD (@nil cell). cb8_to_c8 L1C (@nil cell). cb8_to_c8 L2C (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  idtac "HDR-STORES".
  idtac "SB-STORES".
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x9815c] [] 211%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. try (clear HBm). try (pose proof HB as HBm).
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  try (match goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb _) _ |- _ => rename H into FSHX end).
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 16 eexists. eexists _, _, _, _.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [eassumption|]. split; [exact STlo|]. split; [exact SThi|].
      split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [unfold crt_zero, CRT_SIZE; eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [unfold CRT_SIZE; eassumption|]. split; [exact APP|]. split; [unfold CRT_SIZE; exact APC|].
      split; [exact PRES|]. exact SS.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation X00 := [(PP, PP + 8); (CRT, CRT + 744)].
  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition LUI_FFFFB : Z := -20480.

  (* [comment removed for export] *)
  Definition EPIQ (FB sp1 : Z) (h1 : HST asegs R HIA) (s11v w0 w1 w2 : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.$2.Lr,$2.(1.$2.Lp',$2.(1.(5.&40.)Lx1,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Ls4v,(5.&40.)(1.(5.&40.)Ls5v,(5.&40.)(1.(5.&40.)Ls6v,(5.&40.)(1.(5.&40.)Ls7v,(5.&40.)(1.(5.&40.)Ls8v,(5.&40.)(8.(9.$0.R18.(:.(;.R14.(<.&40.O6.)Vgp,Vtp,R13.R12.R11.Vsp,(<.&40.O6.)(<.&40.R16.)R10.R?.R>.R=.R<.R;.R:.(<.&40.O7.)(<.&40.VPP,)R5.R4.R3.R2.R1.(<.&40.(=.(10.O7.+3.)(>.(?.VR,))))(<.&40.O7.)O4.R9.R8.R7.R6.)VF,(<.&40.+981=<.)Vfc,(11.(5.&40.))R17.(12.$4.)))(8.(8.(38.(39.(3:.+2.+1?.))R16.)(13.R16.+1.))(8.(17.$4.VR,VHIA,O5.VLB,(18.(19.$2.$2.)(1:.$2.$2.O7.+80.)VLF,)R17.)(8.(2<.$4.R17.)(8.(25.$4.R17.O7.(18.$26.(27.O3.)(18.$26.(27.O2.)(18.$26.(27.O1.)(28.$26.)))))(8.(25.$4.R17.(=.(10.O7.+3.)(>.(?.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))(8.(25.$4.R17.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R17.(=.O6.+30.)(18.$26.(27.(<.&40.O7.))(28.$26.)))(8.(2;.$4.R17.O6.(=.O6.+30.))(8.(2;.$4.R17.(=.O6.+38.)(=.(15.&40.Vsp,)-68.))(8.(2;.$4.R17.Vlo,O6.)(8.(25.$4.R17.VPP,(18.$26.(27.(<.&40.R15.))(28.$26.)))(8.(8.(13.VP,R15.)(13.R15.VEND,))(8.(2=.$4.R17.VCRT,)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R17.VPP,+8.)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R17.VCRT,$30.)(8.(32.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(18.(19.$2.$2.)(1:.$2.$2.VPP,(=.VPP,+8.))(18.(19.$2.$2.)(1:.$2.$2.VCRT,(=.VCRT,+2>8.))(28.(19.$2.$2.))))Vm,R17.)(34.$4.(?.VR,)R17.Vslo,(15.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition CALLQ (FB sp1 : Z) (h1 : HST asegs R HIA) (s11v w0 w1 w2 : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.$2.Lp1,$2.(1.$2.Lp2,$2.(1.(5.&40.)LLw,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(8.(9.$0.R11.(:.(;.(<.&40.+982><.)(<.&40.O6.)Vgp,Vtp,R<.R;.R:.Vsp,(<.&40.O6.)(<.&40.VCRT,)(<.&40.R?.)R=.R9.R8.R7.R6.R5.(<.&40.O7.)(<.&40.VPP,)(<.&40.(=.(10.VPP,+3.)(>.(?.VR,))))(<.&40.(=.O7.+20.))(<.&40.R?.)(<.&40.$3;.)(<.&40.(=.R?.(15.&40.R=.)))(<.&40.(=.(10.O7.+3.)(>.(?.VR,))))(<.&40.O7.)O4.R4.R3.R2.R1.)VF,(<.&40.$3<.)Vfc,(11.(5.&40.))R10.(12.$4.)))(8.(17.$4.VR,VHIA,O5.VLB,(18.(19.$2.$2.)(1:.$2.$2.O7.+80.)VLF,)R10.)(8.(2<.$4.R10.)(8.(25.$4.R10.O7.(18.$26.(27.O3.)(18.$26.(27.O2.)(18.$26.(27.O1.)(28.$26.)))))(8.(25.$4.R10.(=.(10.O7.+3.)(>.(?.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))(8.(25.$4.R10.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R10.(=.O6.+30.)(18.$26.(27.(<.&40.O7.))(28.$26.)))(8.(25.$4.R10.(=.O6.+18.)(18.$26.(27.(<.&40.VCRT,))(28.$26.)))(8.(2;.$4.R10.O6.(=.O6.+18.))(8.(2;.$4.R10.(=.O6.+20.)(=.O6.+30.))(8.(2;.$4.R10.(=.O6.+38.)(=.(15.&40.Vsp,)-68.))(8.(2;.$4.R10.Vlo,O6.)(8.(25.$4.R10.VPP,(18.$26.(27.(<.&40.R>.))(28.$26.)))(8.(13.(=.VP,+2.)R?.)(8.(13.(15.&40.R=.)(14.VEND,R?.))(8.(13.(=.R?.+2.)R>.)(8.(13.R>.(=.R?.(15.&40.R=.)))(8.(2=.$4.R10.VCRT,)(8.(2>.$4.R10.VBUF,Vbs,)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R10.VPP,+8.)(8.(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R10.VCRT,$30.)(8.(32.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(18.(19.$2.$2.)(1:.$2.$2.VPP,(=.VPP,+8.))(18.(19.$2.$2.)(1:.$2.$2.VCRT,(=.VCRT,+2>8.))(28.(19.$2.$2.))))Vm,R10.)(34.$4.(?.VR,)R10.Vslo,(15.&40.Vsp,))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition MIDP FB sp1 h1 s11v w0 w1 w2 : machine_state -> Prop := fun ms =>
    EPIQ FB sp1 h1 s11v w0 w1 w2 ms \/ CALLQ FB sp1 h1 s11v w0 w1 w2 ms.

  (* [comment removed for export] *)
  Ltac fin_epiq :=
    apply evtA_done; left; unfold EPIQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- HM _ _ _ _ _ _ _ => eassumption
    | |- _ => idtac
    end.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DCD; try lx_pin1 CAL8; try lx_pin1 CZ; try lx_pin1 DPD; try lx_pin1 BSMALL; try lx_pin1 HB; try lx_pin1 HPP0; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 DIMG; try lx_pin1 STKc0; try lx_pin1 CNTc_mono; try lx_pin1 FFRc_mono; try lx_pin1 PHIc_mono; try lx_pin1 CRTPARSE; try lx_pin1 CNTc; try lx_pin1 FFRc; try lx_pin1 PHIc; try lx_pin1 SI; try lx_pin1 PK; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "06k0@C23920765559.243C40858145355.207C40860242543.242C60410007123.206D10636937134.207D10637083018.158D10639034250.243D10777814275.157D10779914024.160D10780387598.207D14195012678.243D14196765254.158D14197109858.207D16069757090.243D16071854214.207D1706006088.159 D2457516971.207 D2457697677.160 D2459793318.157 D31412296977.159D3160018437.243 D3162115617.207 D3162359813.158 D32452690557.157D32458870384.207D32458983510.160D32604263315.162D3376374386.156 D36104920040.243D36106837480.158D36107017164.207D40202443474.159D45717900227.156D46113591599.161D46115477290.243D46792746863.243D46794843979.207D46795284847.158D56536282705.161D56538493012.243D5982099855.243 D5983723402.161 D60098777666.157D60108722357.156D60109265000.159D60109265001.160D60109265003.158D60109265006.161D60109446735.207D60111543915.243D62011770184.162D65215601089.159D68221095944.207D68223193132.243D68407932977.156D6911601204.156 D9107052231.159 K20981739667.205K20983836855.243K21300719342.242K2872222302.243 K29378133114.207K30993319891.207K30995417079.243K40598034112.206K40600131300.243K5000048842.207 K54996069696.206K54998166884.243K59233359335.207K59235456451.242K65856058596.241K65858155712.206L10478284791.1  L10912730231.1  L11328262410.177L1212436494.23  L13192677399.202L13422353011.136L13552329815.173L13552329815.174L13560199721.1  L13590130921.173L13590130921.174L13951498865.2  L14456249847.1  L14674883745.0  L14689590990.178L14693784767.177L17424931378.202L17424931378.205L17611537599.177L18023395959.1  L18501631719.23 L19548981078.136L19698471166.23 L20755335684.202L20763013818.6  L20763668924.215L20977711877.2  L21298324828.2  L21644325741.3  L21654730866.2  L21942557427.3  L2275137097.0   L24133462168.132L24206288344.1  L2621559066.1   L26262941337.2  L26773555495.215L26892418956.1  L27111942217.1  L27188209011.165L27791187266.1  L27832436138.173L27938633021.23 L27940753276.177L28332440793.1  L28344346468.2  L28374644209.2  L28636403844.1  L2883004908.3   L2902542614.3   L29391009772.3  L30084097556.173L30507144274.2  L3058445732.2   L30997223346.3  L31463340406.205L31471780558.206L32454903270.1  L32881708804.1  L33314451782.177L33610110299.1  L3482443989.177 L3484572308.23  L35248859683.23 L35653441506.9  L35915950964.23 L37330155926.5  L38072332913.3  L38235734261.1  L38733631817.173L3913523846.6   L3914178944.215 L3922500152.202 L39240359025.3  L40281191306.3  L40585223510.2  L41114394636.23 L41251426164.1  L42488948659.2  L42750710500.2  L43098546815.1  L43317676558.23 L45837883074.1  L47870616696.2  L48067811388.23 L48119718058.132L48119718059.133L48132302231.165L48132302231.192L48167983619.2  L48455046775.1  L48938572529.2  L49233373885.2  L4929595632.2   L49352172808.202L50089821425.2  L5012405084.2   L5021251703.1   L50404673919.1  L50567770348.2  L50678314462.3  L50925318027.2  L51609971903.142L53075310967.1  L53527181501.2  L53617080676.3  L55008356054.2  L55182671420.23 L55304482341.3  L55694610473.1  L56523586534.1  L56787311448.1  L56881351127.2  L57387012359.23 L58039649675.2  L58539234803.1  L58970213517.1  L58972524609.3  L59037624984.2  L59231016551.2  L59308586248.2  L60098763854.6  L60117804535.2  L60448817524.1  L61774255627.2  L62033268571.177L62275882349.3  L62873986039.1  L63066551159.1  L6331996272.2   L63734196100.1  L64179129035.1  L64422884493.1  L64482796004.2  L64526681523.2  L64862124172.246L65847135803.202L65847135803.205L65862516566.2  L66298372189.2  L66580933757.177L66812728480.3  L66815160302.205L66823001303.7  L66823607382.207L66823607382.215L66925259691.219L67070089790.2  L6747462914.174 L67653551064.2  L6910010095.132 L7156637175.1   L8190532385.0   L8403266288.2   L8680080987.1   L881835912.0    L9080220944.4   L9092660855.1   L9356559676.14  L9783143000.1   O10642145966.243O10644243082.206O11643029133.241O14568686558.204O14616224269.238O14787361786.241O14912726833.204O14914823957.238O16086026184.206O16088123372.243O17217116232.206O17431956130.207O18153340038.242O18988691132.206O18990788248.242O20866770946.207O21469769210.239O22525005962.206O22527103150.241O26768438569.206O26770535693.242O30010457231.206O3043144207.241 O3076189820.238 O33081188902.243O33428745566.206O3491220723.243 O3493317847.205 O37557392443.243O37559489567.207O3821773283.207 O3823870407.243 O40314064762.242O424351700.205  O44938202843.205O44940300031.243O45106606221.239O45108703401.204O45120147859.242O45122245047.207O49701823576.204O50009742757.239O50011839873.205O55209884805.205O55211981985.239O55516142064.239O60923041807.240O64249863214.243O64251960330.206O64471909102.242O64474006218.206O6509964875.207 O6512062063.242 O65963309676.241O67168963243.242O9266956922.238 P13947775218.241P21656429038.239P28349085159.241P28379342706.238P30511339222.206P30513436402.242P3062169383.242 P3064266499.207 P33616402427.241P38078079190.204P39227264754.239P42484919333.206P42761764931.206P42763862119.242P47874275067.243P47876372191.205P48924428374.206P49230739482.204P50086205042.242P50671478649.205P50673575773.239P50930023688.241P53531847230.238P53605002215.239P53607099331.204P58041177900.206P61786326152.243P61788423340.206P62260666314.205P64486486887.238P64541068801.242P66292560634.206P66294657758.242P66816411171.243P66818508295.207P67064334489.204P67066431677.238P8686372091.240 Q10521014463.171Q10592386192.166Q10592533181.207Q10594483344.177Q10594483353.169Q10598576410.173Q10636937134.207Q10637083010.167Q10639034250.243Q10651763882.174Q11133374175.207Q11657053839.207Q11657494690.166Q11659591851.169Q12658527492.176Q14851060497.180Q14851060506.179Q17025597925.243Q17027695041.207Q1703908940.175 Q1706006080.168 Q17681074618.207Q17683171742.243Q19561597648.173Q19561597649.219Q21140520597.168Q21765573510.243Q21767670690.207Q22481990270.168Q23925414038.171Q23925414044.178Q24133462168.172Q24133462174.181Q24137657765.165Q27573751300.207Q27575848480.243Q27942454161.207Q27944551349.243Q2803826605.207 Q2805923721.243 Q29775981542.207Q29778078658.243Q30220990901.177Q30220990908.169Q30222614424.207Q30223088053.166Q32435106995.243Q32435581616.170Q32440833928.165Q32679510481.243Q32679790545.169Q32679790546.170Q32679790547.171Q32681607669.207Q32681887704.166Q33194651969.176Q33228598873.173Q34667047578.170Q34667424921.243Q34671339291.219Q3477426724.207 Q3479523840.243 Q35333735512.219Q38250992820.180Q38250992831.179Q40216052035.165Q41412201211.243Q42437284299.207Q42437284299.240Q42439168719.207Q42441265899.243Q42441479406.183Q43878048867.179Q46792746863.243Q46794843979.207Q46795284839.167Q46805771343.174Q47228624634.171Q48117620902.166Q48118064779.207Q48119718060.170Q48119718063.169Q48120161967.243Q48132302231.165Q49561274034.171Q51220483007.170Q51220663740.243Q56525516080.165Q56530976407.207Q56531220666.166Q56533317811.169Q59865603600.207Q59867617329.183Q59867700788.243Q59871812884.207Q59871812884.240Q62009673028.178Q62009673038.171Q64681502663.183Q64681845186.243Q64683942374.207Q64685695714.207Q64685695714.240Q65213503941.175Q65215601097.168Q6897428434.165 Q6910010089.181 Q6910010095.172 Q8124604587.243 Q8124655272.170 Q9346354338.184 Q9356888860.220 Q9633850158.219 Q9633850159.173 Q9644583048.207 Q9646680236.243 00000400800<00@00a01B01c02D02e03F03G03H03I04H05G05l05m05n05o06006106206306T07507V08>08?08@08A08B08C08d09E09f0:G0:h0;I0;j0<K0<L0<M0=50=]0>E0>m0?U0@=0@e0AM0An0BS0CZ0Da0Db0EC0ED0FJ0GR0H^0Ij0K40KV0L80M>0NF0OP0PV0Q^0R@0Rb0Sj0U00U10U20V00VE0Vm0W]0XK0Y90Y=0Yk0ZY0ZZ0Z_0Z`0[I0[J0[k0\L0]<0]@0^@0^g0_[0`\0`]0b=0b>0b?0b@0bA0bB0bC0b]0bb0bg0bh0cV0cZ0c^0dD0dE0dh0e^0fY0f^0f_0f`0fa0fb0fm0fn0gV0gW0gX0gY0hE0i10i50i60iZ0i[0jM0k>0l>0l[0m10m20m30m70m_0m`0oN10P10Q10Z10[11111511611711811M11N11O12D12m13V14?14h14i14m14n14o15015X15Y15Z15[15`15a15b15c16P16Q16R16S16T17I17T17X17\17a17b18418518618;18G18H18I18O18Y18Z18^18_19a19b19f19g19h19i19j19o1:01:11:l1;M1;n1;o1<01<\1<]1<^1<_1<`1<a1=B1=C1=d1=l1>F1>J1>K1>L1>M1>N1>]1>^1?H1?M1?N1?O1?P1?Q1?R1?S1?T1?U1?V1?W1?X1?Y1?Z1?[1?\1?]1?^1?_1?`1?a1?b1?c1?d1?e1?f1?g1?h1?i1?j1?k1?l1?m1?n1?o1@01@11@21@31@41@51@61@71@81@R1@l1@m1@n1@o1A01A11A21A31A41A51A61A71B31BY1CJ1DF1Do1EX1FK1G>1G?1H;1I71Ik1J\1KM1LI1ME1NA1O=1P91P_1QE1RA1S=1Sn1T_1U[1VW1WS1X91Xj1Y^1Z@1Zb1[\1\V1]G1^81^91^S1^m1_G1_a1`;1`P1`j1aD1a^1b81bR1bS1bT1bU1c01cN1cO1ci1dC1d^1e91ej1f[1gH1go1h01ha1iR1j01jY1k61kP1kj1lD1lE1lF1lo1mX1n31nN1o01oR1ol20F20`21:21;21<21=21>21?21@21A21B21C21^22322M22g23A23_24=24W25125K25L25f26F26f27F27f28F28c29=29W2:12:K2:f2;O2<82<a2=J2>32>\2>]2?72?Q2?R2?S2?T2?U2?V2?W2?X2?Y2?Z2@12@H2A52Ab2BO2C<2Ci2DD2D_2E92ES2Em2En2Eo2FO2Fo2GL2Gd2HA2H^S2FBS2PPS2PPS2FBS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnFFFS1R4STKc2LF2sp2PP2lo2bs3PP03SLO3LFB3LOS2FB3sp13SP14SP1R2F04lxHnS1R4STKc2LF2sp2PP2lo2bs3PP03SLO3LFB3LOS2FB3sp13SP14SP1R2F04lxHnS1R4STKc2LF2PP3CRT2bs3LFB2FB3sp14lxHnFFFFFFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R3HIA4STKc2LF2PP2bs3LFB2FB3sp12h14lxHnFFFFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnFFS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2lo2bs3LFB3LOS2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP3CRT2bs3LFB2FB3sp14lxHnS1R3HIA4STKc1h2LF2sp2PP2bs3PP03TOP3LFB2FB3sp12h13SP15Ehtop4SP1R2F04lxHnS1R3HIA4STKc1h2LF2sp2PP2bs3PP03TOP3LFB2FB3sp12h13SP15Ehtop4SP1R2F04lxHnFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnFS1R4STKc2LF2PP1P3END2lo2bs3LFB2FB3sp13x153APP4lxHn2x33x163x173x184POSTS1R4STKc2LF2PP2lo2bs3LFB2FB3sp13APP4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP3CRT2lo2bs3LFB2FB3sp13APC4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP3BUF2lo2bs3LFB2FB3sp13APB4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP1P3END3BUF2lo2bs3LFB2FB3sp13x153APB4lxHn2x33x163x173x184POSTS1R4STKc2LF2PP3BUF2bs3DPB3LFB4lxHnS1R4STKc2LF2PP3BUF2bs3DPB3LFB4lxHnS1R4STKc2LF2PP1P3END2lo2bs3LFB2FB3sp13x153APP4lxHn2x33x163x173x184POSTS1R4STKc2LF2PP2lo2bs3LFB2FB3sp13APP4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP1P3END3CRT2lo2bs3LFB2FB3sp13x153APC4lxHn2x33x163x173x184POSTS1R4STKc2LF2PP1P3END2lo2bs3LFB2FB3sp13x153APP4lxHn2x33x163x173x184POSTS1R4STKc2LF2PP2lo2bs3LFB2FB3sp13APP4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP3CRT2bs3DPC3LFB4lxHnS1R4STKc2LF2PP3CRT2bs3DPC3LFB4lxHnS1R4STKc2LF2PP2lo2bs3LFB2FB3sp13APP4lxHn2p12Lw3x293x173x303x313x325POST0S1R4STKc2LF2PP1P3END2lo2bs3LFB2FB3sp13x153APP4lxHn2x33x163x173x184POSTFFS1R4STKc2LF2PP1P3BUF2bs3PP02W13LFB2FB3sp14SP1R2F04lxHn2p14Hp1aS1R4STKc2PP2bs2FB3APPS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r23RR2S1R4STKc2LF2PP2bs3PP03LFB2FB3sp14SP1R2F02F84lxHnS1R4STKc2LF2PP1P3END2bs3LFB2FB3sp14lxHn2p13Hp1S1R4STKc2LF2PP1P3END2bs3LFB2FB3sp14lxHn2p13Hp1S2FBS1R4STKc2LF2PP1P3END2bs3LFB2FB3sp14lxHn2p13Hp1S1R4STKc2LF2PP1P3END2bs3LFB2FB3sp14lxHn2p13Hp1FS3sp1SS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2p12Lw1HFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3PP03LFB2FB3sp14SP1R2F02F84lxHnS2FBS1R4STKc2sp2PP3BUF2lo3slo2bs4PPLO4SLOS4SLOL3SLO3sp13SP13ALO4BUFCS1R4STKc2LF2PP2bs3LFB2FB3sp12F02F84lxHnS1R4STKc2sp2lo3SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R4STKc2LF2PP1P2bs3PP03LFB2FB3sp14SP1R2F04lxHn2p12Lw4Hp1a2p23Hp2FS1R4STKc2LF2PP1P3END3BUF3CRT2bs3PP02W12W33DPB3DCB3DPC3LFB2FB3sp14SP1R2F04lxHn2p13Hp14Hp1a2p23H37FFFFFSS1R4STKc2LF2bs3LFB2FB4lxHnS3sp1S3sp1FS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2p12Lw2p23Hp2S2spS2PPS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn1c2HcFS1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp1S1R4STKc2sp2lo3slo4SLOS4SLOL3SLO2FB3sp13SP13ALO3ACP2F0S1R4STKc2LF2sp2PP2lo2bs3PP03SLO3LFB2FB3sp13SP14SP1R2F04lxHnS3sp1FFFFS2r23RR22NEFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r13RR1FFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r23RR23H35S1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r23RR23H35S2FBFS1R4STKc2LF2PP2bs3LFB2FB3sp12F04lxHnFS1R4STKc2LF2PP2bs3PP03LFB2FB3sp14SP1M4SP1R2F04lxHnS1R4STKc2sp2lo3SLO3LOS2FB3sp13SP14SP1M3ALO3ACP2F0S1R4STKc2sp2PP3BUF2lo3slo2bs4PPLO4SLOS4SLOL3SLO3sp13SP13ALO4BUFCS1R3HIA4STKc1h2sp2lo3TOP4HTOPS1R4STKc3BUF2bs2FB3APBSFS2loS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r13RR1FS1R4STKc2LF2PP1P3END3BUF3CRT2bs3PP02W12W33DPB3DCB3DPC3LFB2FB3sp14SP1R2F04lxHn2p12Lw3Hp14Hp1a3HLw2p23Lw23H342H4S1R4STKc2LF2PP3END2bs3PP03LFB2FB3sp14SP1R2F04lxHn2p12Lw3HLw2p23Hp2FS1R3HIA1hFS1R4STKc2PP3BUF2bs3DPBS2FBFFFS1R4STKc2PP2bs2FB3APPFFS1R4STKc2sp2lo3slo2bs4SLOS4SLOL3SLO2FB3sp13SP13ALO2F1S1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnFS2FBFFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r23RR2FFFS3sp1FFFS1R4STKc2LF2sp3slo2bs4SLOS3LFB2FB3ALO2F14lxHnFFFFS1R4STKc2sp2lo3slo2bs4SLOS4SLOL3SLO2FB3sp13SP13ALO2F1S2r13RR12NES2FBS2FBS3sp1FS1R4STKc2FB3sp12F0FFS3sp1S3BUF2bs3B47FFS1i2HiS1R2lo3LOSFS2FBFS1R4STKc2LF2PP3END3BUF2bs3PP02W33LFB2FB3sp14SP1R2F04lxHn2p12Lw3HLwFS2FBFFFFS3sp1FFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2p12Lw2p23Lw24LXKT3H343H36S1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHn2r13RR13H28FFFFFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnFS1R4STKc2LF2PP2bs3LFB2FB3sp14lxHnS2sp3sp1S1R4STKc2LF2bs3LFB2FB4lxHnS2FBSFFSS2sp2lo3sp13SP1FS1R4STKc2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS3sp1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R4STKc2sp2lo3SLO3sp13SP1S1R4STKc2sp2lo3SLO3sp13SP1FFFFFFFFFFFS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2lo2bs3LFB2FB3sp14FBLO4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB4lxHnS1R4STKc2LF2sp3CRT2lo2bs5CRTLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp3CRT2lo2bs5CRTLO3SLO3LFB3sp13SP14lxHnFS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3ALO2F14FBLO4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2PP2lo2bs4PPLO3LFB3sp14lxHnS1R4STKc2LF2PP2lo2bs4PPLO3LFB3sp14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3sp13SP13ALO2F14FBLO4lxHnS1R4STKc2LF2lo2bs3LFB2FB3sp14FBLO4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS2FB3ALO2F14FBLO4lxHnS1R4STKc2LF2sp2bs3LFB3sp13SP14lxHnS1R4STKc2LF2sp2bs3LFB3sp13SP14lxHnS1R4STKc2LF2sp3BUF2lo2bs3SLO3LFB3LOS3sp13SP13ALO4BUFC4lxHnS1R4STKc2LF2sp3BUF2lo2bs3SLO3LFB3LOS3sp13SP13ALO4BUFC4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnFS1R4STKc2LF2sp2bs3LFB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnFFFS1R4STKc2LF3BUF2bs3LFB4lxHnS1R4STKc2LF2lo2bs3LFB3sp14lxHnFS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF3CRT2bs3LFB4lxHnS1R4STKc2LF3CRT2bs3LFB4lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2PP2lo2bs4PPLO3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp13SPR2F02F8S1R4STKc2LF2PP2bs3LFB2FB3sp12F02F84lxHnFS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3sp13SP13ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3sp13SP13ALO4lxHnS1R4STKc2LF2PP3CRT2bs3LFB4lxHnS1R3HIA4STKc1h2LF2sp2bs3TOP3LFB4HTOP4lxHnS1R3HIA4STKc1h2LF2bs3LFB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnFFS1R4STKc2LF2sp2lo2bs3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3sp13SP14lxHnS1R4STKc2LF2bs3LFB3sp14lxHnS1R4STKc2LF2bs3LFB3sp14lxHnS1R4STKc2LF2sp2bs3LFB3sp13SP14lxHnS1R4STKc2LF2sp2bs3LFB3sp13SP14lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnFFFFFFFFFS1R4STKc2LF3BUF2bs3LFB4lxHnS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2lo2bs3LFB3sp14lxHnS1R4STKc2LF2lo2bs3LFB3sp14lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2lo2bs3LFB4lxHnS1R4STKc2LF2lo2bs3LFB4lxHnFS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF3slo2bs4SLOS3LFB4lxHnS1R4STKc2LF3slo2bs4SLOS3LFB4lxHnS1R4STKc2LF3slo2bs4SLOS3LFB4lxHnS1R4STKc2LF3slo2bs4SLOS3LFB4lxHnS1R4STKc2LF3slo2bs4SLOS3LFB4lxHnS1R4STKc2LF2sp2lo2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2PP2bs3LFB4lxHnS1R4STKc2LF2bs3LFB3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnS1R4STKc2LF2sp2lo2bs3SLO3LFB3LOS3ALO4lxHnFS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnFFFFFFFFFS1R4STKc2LF2bs3LFB4lxHnS1R4STKc2LF2bs3LFB4lxHnS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHnS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHnS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHnS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHnS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB4HTOP4lxHnS1R4STKc2LF3CRT2bs3LFB4lxHnS1R4STKc2LF3CRT2bs3LFB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnS1R4STKc2LF2bs3LFB2FB4lxHnFFS1R4STKc2LF2bs3LFB3sp14SP1R4lxHnS1R4STKc2LF2bs3LFB3sp14SP1R4lxHnS1R4STKc2LF2bs3LFB2FB2F04lxHnS1R4STKc2LF2bs3LFB2FB2F0S1R4STKc2LF2bs3LFB2FB2F04lxHnS1R4STKc2LF2bs3LFB2FB2F04lxHn". (* [comment removed for export] *)
  #[using="LOS LFB SPH TOP SLO SLOL SLOS DPC DCB CRTLO CWC CRT0 DPB BUF0 B47 W3 W2 W1 BIN PPLO CWP PP0 AL8 STKc GETTAG IMG"]
  Lemma mid_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Pms,$0.PFB,$2.Psp1,$2.Ph1,(3.$4.VR,VHIA,)Pm1,P,(5.&40.)(6.(5.&8.))Px1,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa0,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Ps11v,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Pjm,(7.(5.&8.))P,(9.$0.R19.(:.(;.R14.(<.&40.R17.)Vgp,Vtp,R13.R12.R11.Vsp,(<.&40.R17.)R10.(<.&40.VEND,)R?.R>.R=.R<.R;.R:.(<.&40.R18.)(<.&40.VPP,)(<.&40.VCRT,)(<.&40.(=.R18.+20.))(<.&40.(>.(?.VR,)))Vs7,Vs8,(<.&40.(=.(10.R18.+3.)(>.(?.VR,))))(<.&40.R18.)R5.R9.R8.R7.R6.)VF,(<.&40.+9815<.)Vfc,(11.(5.&40.))R15.(12.$4.)))P,(8.(13.(14.(15.&40.Vsp,)+;0.)R18.)(13.R18.(14.(15.&40.Vsp,)+:0.)))P,(9.$2.(16.R19.+20.)=)P,(17.$4.VR,VHIA,R19.VLB,(18.(19.$2.$2.)(1:.$2.$2.R1;.+80.)VLF,)R18.)P,(9.P,$2.Sp(1;.$4.VR,VHIA,R1:.)(1;.$4.VR,VHIA,Vh,))P,(9.$2.(1<.$4.VR,VHIA,R1;.)(1<.$4.VR,VHIA,Vh,))P,(9.$2.(1=.$4.VR,VHIA,R1<.)(1=.$4.VR,VHIA,Vh,))P,(9.$2.(16.R1?.+40.)=)P,(24.VR,VLB,VLF,R20.+80.)P,(25.$4.R1>.R21.(18.$26.(27.R=.)(18.$26.(27.R<.)(18.$26.(27.R;.)(28.$26.)))))P,(25.$4.R1?.(=.R22.+20.)(18.$26.(27.(<.&40.=))(28.$26.)))P,(25.$4.R20.(=.R23.+28.)(18.$26.(29.#18.R<.)(28.$26.)))P,(25.$4.R21.(=.R24.+40.)(18.$26.(27.(<.&40.=))(28.$26.)))P,(25.$4.R22.(=.(10.R25.+3.)(>.(?.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))P,(25.$4.R23.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))P,(25.$4.R24.(=.R26.+30.)(18.$26.(27.(<.&40.R27.))(28.$26.)))P,(2;.$4.R25.R27.(=.R27.+30.))P,(2;.$4.R26.(=.R28.+38.)(=.(15.&40.Vsp,)-68.))P,(2;.$4.R27.Vlo,R29.)P,(2<.$4.R28.)P,(25.$4.R29.VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))P,(2=.$4.R2:.VCRT,)P,(2>.$4.R2;.VBUF,Vbs,)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R2<.VPP,+8.)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)R2=.VCRT,$30.)P,(31.(13.(=.R31.+80.)VPP,)(13.(=.VPP,+8.)R31.))P,(31.(13.(=.R32.+80.)VCRT,)(13.(=.VCRT,$30.)R32.))P,(32.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(28.$33.)Vm,R30.)P,(34.$4.(?.VR,)R31.Vslo,(15.&40.Vsp,))(35.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)(3=.R35.R34.R33.R22.R21.R20.R1?.)R36.)")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until jm.
  intros -> SP1 SP1M HH1 Ehcs Ehtop Estk F64 FRSH FHD L1C JMC L2C FSHX SAVE SLOT ST48 SThi STlo MI1 HPP CZ1 HB1 OPP OCRT APP APC PRES0 SS.
  rt_facts.
  unfold CRT_SIZE in *.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP.
  rewrite Ehtop, Estk in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO TOP HTOP; lia | lx_side_lia ]]).
  assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  (* [comment removed for export] *)
    destruct (hm_apart asegs R HIA h1 LB _ m1 HH1) as [HBR _].
  destruct (proj1 (Forall_forall _ _) HBR _ ltac:(apply in_app_iff; left; exact BIN)) as (_ & _ & BUFC & _).
  cbn [fst snd] in BUFC.
  clear HBR.
  assert (APB : FB + 128 <= BUF \/ BUF + Z.of_nat (length bs) <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
  pose proof (hm_aobj_block asegs R HIA h1 LB _ m1 BUF _ HH1 BIN) as OBUF.
  rewrite Ehcs in OBUF.
  (* [comment removed for export] *)
    assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) PP 8).
    { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
  assert (CWC1 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) CRT 744).
    { eapply client_wrange_mono; [exact CWC| intros b Hb; apply fdata_cons_sub; exact Hb]. }
  assert (CWL1 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) (FB + 32) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
  assert (CWL2 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) (FB + 64) 8).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
  (* [comment removed for export] *)
    assert (PRES : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) X00 m m1).
    { destruct PRES0 as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]]. eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
  clear PRES0.
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WCPP : wcover R LB LF (bv_unsigned sp) X00 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  unfold crt_zero in CZ1.
  pose proof (hm_abase asegs R HIA h1 LB _ m1 HH1) as AB1.
  frame_aobj FSHX (FB + 32) 1%nat as OL1.
  pose proof GETTAG as GT'.
  unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_G in GT'.
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  try lxg_b8u. lx_pre. lx_run_tac (PLAN [0x052af8; 0x0981dc; 0x0990e0; 0x0a98d4] [] 211%N).
  lx_tree.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x9816c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x990e0) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GT' with (CS := CS) (PP := PP) (LENP := FB + 32) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 160) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | lazymatch goal with | |- BUF + _ < 2 ^ 63 => first [ clear - B47; lia | lx_side_lia ] | |- _ \/ _ => first [ clear - APP APB DPB BUFC ACP ALO LOS SLO SP1 F1 PPLO; lia | lx_side_lia ] | |- _ => clear - SP1 SP1M SLO F0 F1 F8 F64 ALO LOS ACP PP0 BUF0; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "TAG1-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "TAG1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear OL1; try clear AB1| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HL1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 32) [C8 ?lw] |- _ => rename H into HL1; rename lw into Lw end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HPP2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename p1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP2; rename qq into p1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename r1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HOK1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HOK1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename RR1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < r1 <= 0 |- _ => rename H into RR1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hp1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : P <= p1 <= END |- _ => rename H into Hp1 end | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0x98178: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052af8; 0x0981dc; 0x0990e0; 0x0a98d4] [] 211%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x981b0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x990e0) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try lx_r0 r1 | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => subst r1 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => destruct (HOK1 eq_refl) as [Hp1a HLw] | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HOK1| |- _ => idtac end.
  (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear ST48| |- _ => idtac end.
  (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear STa| |- _ => idtac end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => (* [comment removed for export] *) lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2 end end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m2b into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2b end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ m2b (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH2 (FB + 64) 1%nat as OL2 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GT' with (CS := CS) (PP := PP) (LENP := FB + 64) (P := p1) (END := p1 + bv_unsigned Lw) (BUF := BUF) (bs := bs) (tag := 48) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | lazymatch goal with | |- BUF + _ < 2 ^ 63 => first [ clear - B47; lia | lx_side_lia ] | |- _ = Z_to_bv 64 (p1 + bv_unsigned Lw) => apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow Z.of_N Pos.pow]; clear - LR Hp1 HLw W1 W3 B47 BUF0; Z.div_mod_to_equations; nia | |- _ \/ _ => first [ clear - APP APB DPB BUFC ACP ALO LOS SLO SP1 F1 PPLO; lia | lx_side_lia ] | |- _ => clear - SP1 SP1M SLO F0 F1 F8 F64 ALO LOS ACP PP0 BUF0 LR Hp1 HLw W1 W2 W3; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "TAG2-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "TAG2-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear OL2; try clear AB2| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HL2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 64) [C8 ?lw] |- _ => rename H into HL2; rename lw into Lw2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HPP3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename p2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP3; rename qq into p2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename r2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HOK2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HOK2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename RR2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < r2 <= 0 |- _ => rename H into RR2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hp2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : p1 <= p2 <= _ |- _ => rename H into Hp2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => assert (REL : forall mq, rw_cells asegs mq (sp1 + 24) [C8 (Z_to_bv 64 CRT)] -> stk asegs mq sp1 (sp1 + 24) -> stk asegs mq (sp1 + 32) (sp1 + 48) -> stk asegs mq sp1 (sp1 + 48)); [ intros mq A1 A2 A3; pose proof (stk_of_rw_cells asegs mq _ _ A1) as K; cbn [cells_size csize Nat.add] in K; replace (sp1 + 24 + Z.of_nat 8) with (sp1 + 32) in K by (clear; lia); eapply stk_merge; [eapply stk_merge; [exact A2| exact K| clear; lia]| exact A3| clear; lia] | .. ] | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0x981bc: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052af8; 0x0981dc; 0x0990e0; 0x0a98d4] [] 211%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x982ec) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xa98d4) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try lx_r0 r2 | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => subst r2 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => destruct (HOK2 eq_refl) as [Hp2a HLw2] | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HOK2| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => (* [comment removed for export] *) lazymatch goal with HHc : HM _ _ _ h1 _ _ m3 |- _ => pose proof (hm_abase asegs R HIA h1 LB _ m3 HHc) as AB3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear AB3| |- _ => idtac end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try match goal with |- context [Z_to_bv 64 (p2 + bv_unsigned Lw2)] => rewrite EQE end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => apply evtA_done | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => right | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => unfold CALLQ, A_X509_CRT_PARSE_DER, LUI_FFFFB | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => exists p1, p2, Lw | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => repeat (lazymatch goal with |- ex _ => eexists end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ] | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => repeat match goal with |- _ /\ _ => split end; first [ eassumption | exact PRES | first [ clear - Hp1a HLw Hp2a HLw2 EQE LR2; lia | lx_side_lia ] | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "CALLQ-LEFT:" g end ] | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0x982f8: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x052af8; 0x0981dc; 0x0990e0; 0x0a98d4] [] 211%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_epiq; first [ eassumption | first [ clear - Hp1 RR1; lia | lx_side_lia ] | exact PRES | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "EPIQ1-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0x981ec path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0x981ec path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] => replace (bv_swrap 32 e) with (r1 - 21248) by (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by (clear; lia); unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; change (4294967296 `div` 2) with 2147483648; clear - RR1; Z.div_mod_to_equations; lia) end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_epiq; first [ eassumption | first [ clear - Hp1 RR1; lia | lx_side_lia ] | exact PRES | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "EPIQ2-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0x981ec path 2: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0x981ec path 2: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (assert (R20 : r2 = 0) by (first [ clear - RR2; lia | lx_side_lia ])) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (subst r2) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (HOK2 eq_refl) as [Hp2a HLw2]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HOK2| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with HHc : HM _ _ _ h1 _ _ m3 |- _ => pose proof (hm_abase asegs R HIA h1 LB _ m3 HHc) as AB3 end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear AB3| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] => replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (-21376) : word) by (apply bv_eq; vm_compute; reflexivity) end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with A1 : rw_cells _ mx (sp1 + 24) _, A2 : stk _ mx sp1 (sp1 + 24), A3 : stk _ mx (sp1 + 32) (sp1 + 48) |- _ => pose proof (REL mx A1 A2 A3) as ST48; clear A1 A2 A3 end end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_epiq; first [ eassumption | clear; lia | first [ clear - Hp2 Hp1 HLw W2; lia | lx_side_lia ] | exact PRES | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "EPIQ4-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0x981ec path 3: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0x981ec path 3: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with A1 : rw_cells _ mx (sp1 + 24) _, A2 : stk _ mx sp1 (sp1 + 24), A3 : stk _ mx (sp1 + 32) (sp1 + 48) |- _ => pose proof (REL mx A1 A2 A3) as ST48; clear A1 A2 A3 end end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (fin_epiq; first [ eassumption | first [ clear - RR2; lia | lx_side_lia ] | first [ clear - Hp2 Hp1 HLw W2; lia | lx_side_lia ] | exact PRES | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "EPIQ3-LEFT:" g end ]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0x981ec path 4: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0x981ec path 4: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x981dc) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw mid_walk: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBc : list blk) (m0 m2x : mem) (WA WB : list ivl) (r p' : Z) (cb : list byte)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.(3.$4.VR,VHIA,)Lh4,(3.$4.VR,VHIA,)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(8.(9.$0.R11.(:.(;.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(<.&40.O3.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3>.Vra,)Vfc,(11.(5.&40.))R10.(12.$4.)))(8.(2<.$4.R10.)(8.(2;.$4.R10.Vlo,(15.&40.Vsp,))(8.(34.$4.(?.VR,)R10.Vslo,(15.&40.Vsp,))(8.(32.$4.VR,VHIA,O9.VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)O5.O7.R10.)(8.(32.$4.VR,VHIA,O9.(3?.$40.O8.VLB,)VLF,(15.&40.Vsp,)(15.&40.Vsp,)O4.O6.R10.)(8.(9.P,$2.Sp(1;.$4.VR,VHIA,R?.)(1;.$4.VR,VHIA,O9.))(8.(9.$2.(1<.$4.VR,VHIA,R?.)(1<.$4.VR,VHIA,O9.))(8.(9.$2.(1=.$4.VR,VHIA,R?.)(1=.$4.VR,VHIA,O9.))(8.(9.$2.(1>.$4.VR,VHIA,R?.)(1>.$4.VR,VHIA,O9.))(8.(9.$2.(1?.$4.VR,VHIA,R?.)(1?.$4.VR,VHIA,O9.))(8.(9.$2.(20.$4.VR,VHIA,R?.)(20.$4.VR,VHIA,O9.))(8.Pmo,$21.(22.(23.$4.VR,VHIA,R10.R1.)(23.$4.VR,VHIA,O9.R1.))(8.(17.$4.VR,VHIA,R?.(3?.$40.O8.VLB,)VLF,R10.)(8.(25.$4.R10.VPP,(18.$26.(27.(<.&40.O2.))(28.$26.)))(25.$4.R10.VCRT,(18.$26.(29.#2>8.O1.)(28.$26.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 DCD; try lx_pin1 CRTLO; try lx_pin1 CAL8; try lx_pin1 CZ; try lx_pin1 DPD; try lx_pin1 BSMALL; try lx_pin1 BUF0; try lx_pin1 B47; try lx_pin1 BIN; try lx_pin1 HB; try lx_pin1 PPLO; try lx_pin1 AL8; try lx_pin1 HPP0; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 DIMG; try lx_pin1 STKc0; try lx_pin1 CNTc_mono; try lx_pin1 FFRc_mono; try lx_pin1 PHIc_mono; try lx_pin1 CRTPARSE; try lx_pin1 CNTc; try lx_pin1 FFRc; try lx_pin1 PHIc; try lx_pin1 SI; try lx_pin1 PK; try lx_pin1 GETTAG; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01f0@D10777814275.149D14196765254.150D2459793318.149 D31412296978.150D3162359813.150 D32452690557.149D3374278032.148 D36106837480.150D40202443473.150D43016287773.150D45715803169.148D60109265003.150D62011770188.150D68405837779.148D6909504982.148 D9107052228.150 L13312155929.181L13424450162.122L13424450175.126L19546883927.122L19546883930.126L2275137097.0   L2333531081.118 L2333536794.116 L24131365012.123L24131365017.119L26163319614.118L26163329773.116L26966510855.201L27188209011.153L29604608213.0  L29789883986.200L30443668812.9  L35655538631.9  L38077847203.1  L39332637397.0  L39540652971.1  L39844638933.0  L42411609006.0  L48117620902.123L48117620903.124L48117620904.120L48117620907.119L50790731766.9  L51609971896.130L5162232212.2   L54924291872.199L60098763854.6  L60703343649.11 L61954813926.198L62018535662.1  L62406578796.195L6302880071.118 L6302890132.116 L6912107235.123 L6912107246.119 L9356559676.14  P5152549648.193 Q10592386204.154Q10592386207.158Q10637083009.162Q13347144710.155Q13347144715.159Q1703908939.163 Q21721340005.155Q21721340008.159Q22358563588.157Q22553469095.155Q23925414038.165Q24131365012.159Q24131365017.155Q24131365917.161Q24137657765.153Q24137657789.157Q24582661035.159Q30147450662.155Q30223088057.154Q30223088058.158Q30871588746.191Q31314676345.153Q34796740410.158Q36106837473.159Q36106837484.155Q38250992823.164Q4125667684.190 Q42439443119.192Q42441479407.167Q4279611329.192 Q43878048875.164Q46795284836.162Q48117620905.158Q48117620906.154Q48132302223.157Q48132302231.153Q52741535643.191Q5935758158.192 Q59668625896.159Q598502599.159  Q60382659730.159Q60382659743.155Q62009673038.165Q62158987907.159Q62158987918.155Q64133651577.191Q64681502662.167Q64683667846.192Q65213503938.163Q67397950268.154Q6897428426.157 Q6897428434.153 Q6912107235.159 Q6912107246.155 Q6912108138.161 Q7917062807.159 Q7917062810.155 Q7947405915.155 Q9107052224.155 Q9107052237.159 00000I00J00K00L00M00f00g00h00i01I01b02B02[02\03503603Y04=04a05@05_05`05a05b06706L06M06N07X08608709B09X0:60::0:;0:?0:@0:A0:o0;]0<K0=90=O0>70>80?C0?M0?k0A20A50AS0AT0AU0Aj0B?0Bi0Bj0C?0CT0Ci0Cj0Ck0DA0DB0DC0DD0DE0D]0E20EG0E\0F10FF0FG0FH0F]0G20GQ0GR0GS0GT0GU0Gj0HF0Hk0IF0Ib0J:0JO0K=0Kk0LY0MG0Mf0NB0NC0ND0NE0NF0NX0NY0NZ0O60O_0PR0Ph0Pi0Q>0QS0Qh0R=0RR0Rn0SJ0SK0SL0SMS1R4STKc2LF2bs3LFB2FB3sp1FFFFS1R4STKc2LF2bs3LFB2FB3sp1FFFS1R3HIA4STKc2LF2bs3LFB2h32FB3sp1S1R4STKc2LF2bs3LFB2FB3sp1S1R4STKc2LF2lo2bs3LFB3LOS2FB3sp1S1R4STKc2LF2bs3LFB2FB3sp1FS1R4STKc2LF2bs3LFB2FB3sp1FS1R4STKc2LF2bs3LFB2FB3sp14lxHn1p2PBS1R4STKc2LF2bs3LFB2FB3sp14SP1R2F82F0S1R4STKc2LF2bs3LFB2FB3sp14SP1R2F82F0S1R4STKc2LF2bs3LFB2FB3sp12F82F0S1R4STKc2LF2bs3LFB2FB3sp12F82F0SFFS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBFFS1R4STKc2LF2sp2PP3BUF3CRT2lo2bs3DPB3DCB3DPC3SLO3LFB2FB3sp13SP12F04lxHn3H13S1R4STKc2LF2bs3LFB2FB3sp11c2HcSS1R4STKc2LF2sp2PP3BUF3CRT2lo2bs3DPB3DCB3DPC3SLO3LFB2FB3sp13SP14SP1R2F04lxHnS1R4STKc2sp2lo3SLO3LOSS1R3HIA4STKc1h2sp2lo3TOP5HTOP3S2spSS2FBSSS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2sp2lo3SLO3LOSS1R4STKc2LF2sp3slo2bs4SLOS3LFB2FB3ALO2F1FS1R4STKc2LF2sp2PP3BUF3CRT2lo2bs3DPB3DCB3DPC3SLO3LFB2FB3sp13SP14SP1R2F04lxHnS1R2lo3LOSS1R4STKc2sp2lo3SLO3LOS3sp13SP1S1R4STKc2LF2sp2PP3BUF3CRT2lo2bs3DPB3DCB3DPC3SLO3LFB2FB3sp14SP1R2F04lxHnS1RS1R4STKc2LF2bs3LFB2FB3sp14lxHnFFS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRFS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2PP2bs3LFBFFS1R4STKc2LF3CRT2bs3LFBFFFFS1R3HIA4STKc1h2LF2bs3LFBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBFFS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FB4lxHn1p2PBFFFFS1R4STKc2LF2lo2bs3LFBS1R4STKc2LF2bs3LFB4lxHn1p2PBS1R4STKc2LF3slo2bs4SLOS3LFB4lxHn1p2PBS1R4STKc2LF3slo2bs4SLOS3LFBS1R4STKc2LF2bs3LFB4lxHn1p2PBS1R4STKc2LF2sp2lo2bs3LFBS1R4STKc2LF2PP2bs3LFBS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALOS1R4STKc2LF2bs3LFB2FB4lxHn1p2PBS1R4STKc2LF2bs3LFB4lxHn1p2PBFFFFS1R4STKc2LF2bs3LFBFFS1R4STKc2LF2bs3LFB4lxHn1p2PBS1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB5HTOP3S1R3HIA4STKc1h2LF2sp3slo2bs3TOP3LFB5HTOP34lxHn1p2PBS1R4STKc2LF3CRT2bs3LFBFS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FBS1R4STKc2LF2bs3LFB2FB3ALO2F1S1R4STKc2LF2bs3LFB2FB3ALO2F1FFF". (* [comment removed for export] *)
  #[using="LOS LFB SPH TOP SLO SLOL SLOS DPC DCB CWC CRT0 DPB W3 W2 W1 CWP PP0 bs BUF END P STKc IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Ph3,(3.$4.VR,VHIA,)PLBc,(7.$40.)Pm0,P,(5.&40.)(6.(5.&8.))Pm2x,P,(5.&40.)(6.(5.&8.))Pmm,P,(5.&40.)(6.(5.&8.))PWA,(7.$33.)PWB,(7.$33.)PFB,$2.Psp1,$2.Pxra,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Ps4v,(5.&40.)Ps5v,(5.&40.)Ps6v,(5.&40.)Ps7v,(5.&40.)Ps8v,(5.&40.)Ps11v,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Pr,$2.Pp',$2.Pcb,(7.(5.&8.))P,(17.$4.VR,VHIA,R24.(3?.$40.R23.VLB,)(18.(19.$2.$2.)(1:.$2.$2.R1=.+80.)VLF,)R20.)P,Px,$2.P,(1;.$4.VR,VHIA,Vh,R1.)(1;.$4.VR,VHIA,R27.R2.)P,(9.$2.(1<.$4.VR,VHIA,R26.)(1<.$4.VR,VHIA,Vh,))P,(9.$2.(1=.$4.VR,VHIA,R27.)(1=.$4.VR,VHIA,Vh,))P,(8.(13.(14.(15.&40.Vsp,)+;0.)R20.)(13.R20.(14.(15.&40.Vsp,)+:0.)))P,(9.$2.(16.R21.+20.)=)P,(9.$2.(16.R23.+40.)=)P,(24.VR,VLB,VLF,R24.+80.)P,(24.VR,(3?.$40.R2;.VLB,)VLF,R25.+80.)P,(41.(1;.$4.VR,VHIA,Vh,)R26.+80.)P,PB,$2.Pj,$2.P,(42.(19.$2.$2.)(1:.$2.$2.R2.R1.)VLF,)(31.(13.(=.R2:.+80.)R3.)(13.(=.R3.R2.)R2:.))P,(25.$4.R2;.R28.(18.$26.(27.R11.)(18.$26.(27.R10.)(18.$26.(27.R?.)(28.$26.)))))P,(25.$4.R2<.(=.(10.R29.+3.)(>.(?.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))P,(25.$4.R2=.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))P,(25.$4.R2>.(=.R2:.+30.)(18.$26.(27.(<.&40.R2;.))(28.$26.)))P,(2;.$4.R2?.R2;.(=.R2;.+30.))P,(2;.$4.R30.(=.R2<.+38.)(=.(15.&40.Vsp,)-68.))P,(2;.$4.R31.Vlo,R2=.)P,(2<.$4.R32.)P,(32.$4.VR,VHIA,R37.VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)R32.R35.R33.)P,(32.$4.VR,VHIA,R38.(3?.$40.R37.VLB,)VLF,(15.&40.Vsp,)(15.&40.Vsp,)R32.R35.R34.)P,(34.$4.(?.VR,)R35.Vslo,(15.&40.Vsp,))P,(25.$4.R36.VPP,(18.$26.(27.(<.&40.R18.))(28.$26.)))P,(25.$4.R37.VCRT,(18.$26.(29.#2>8.R18.)(28.$26.)))P,(41.(1;.$4.VR,VHIA,Vh,)VPP,+8.)P,(41.(1;.$4.VR,VHIA,Vh,)VCRT,+2>8.)P,(31.(13.(=.R37.+80.)VPP,)(13.(=.VPP,+8.)R37.))P,(31.(13.(=.R38.+80.)VCRT,)(13.(=.VCRT,+2>8.)R38.))(35.$4.(?.VR,)(1;.$4.VR,VHIA,R40.)(43.R40.R3?.R3>.R3=.R3;.R3:.R1?.R1>.R1=.)(:.(;.R37.(<.&40.R38.)Vgp,Vtp,R36.R35.R34.Vsp,(<.&40.R38.)(<.&40.R1?.)R33.R32.R31.R30.R2?.R2>.R2=.(<.&40.R39.)(<.&40.VPP,)R28.R27.R26.R25.R24.(<.&40.(=.(10.R39.+3.)(>.(?.VR,))))(<.&40.R39.)R23.R2<.R2;.R2:.R29.)VF,(<.&40.+981=<.)Vfc,(11.(5.&40.))R3<.(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until cb.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP FHD FSH SAVE SLOT ST48 SThi STlo MI PRES PRES2 SS HPP HCRT CRP CRC APP APC.
  rt_facts.
  unfold CRT_SIZE in *.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (CRP3 : crange (hcs asegs R HIA h3) PP 8) by (eapply crange_mono; [exact HCS3| exact CRP]).
  assert (CRC3 : crange (hcs asegs R HIA h3) CRT 744) by (eapply crange_mono; [exact HCS3| exact CRC]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 (LBc ++ LB) LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x98238] [] 211%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 (LBc ++ LB) ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b, In b (LB ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 128) :: LF))).
  { intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b, In b ((LBc ++ LB) ++ fdata LF) -> In b ((LBc ++ LB) ++ fdata ((FB, 128) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ lo (arl_stklo R) p PP 8 NCp (client_range_of_w L _ _ _ _ _ CWP) SUB1 LOS ltac:(clear; lia)) as NP1.
  pose proof (nc_apart _ _ _ lo (arl_stklo R) p CRT 744 NCp (client_range_of_w L _ _ _ _ _ CWC) SUB1 LOS ltac:(clear; lia)) as NP2.
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 48 + 8 <= p \/ p + 1 <= sp1 + 48).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1; lia | lx_side_lia ]| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LB LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SLOT.
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 48), STB : stk _ mf (sp1 + 56) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOT; stk_merge_into ST0 STB; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
  }
  split; [assumption|].
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  split; [exact HM4|].
  split; assumption.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@D25066864133.281D28498761192.281D4451634193.281 D60109196847.281K55782424244.281K9840090748.281 L10472354596.268L11338755728.5  L11455491570.10 L1263876072.7   L13982435139.7  L14226018324.3  L14924917537.0  L1540877545.3   L15756354262.7  L15843963615.7  L1685717371.0   L17925696804.4  L19391665270.2  L19980016842.7  L20128402598.3  L20763137444.4  L2275137097.0   L23069962499.7  L23182876091.2  L24128180555.1  L24579632058.7  L24836746166.10 L25852558868.3  L25985555144.1  L26892418956.1  L27111942217.1  L27188209011.3  L27470824284.2  L27667288301.4  L28390317327.1  L29820611332.3  L31021792691.6  L31474779520.268L31863022963.4  L31995967304.1  L35653326811.11 L36519722515.11 L38087549238.15 L38205559744.0  L39332637397.0  L40051937615.2  L40228640085.0  L40281191306.3  L41202929119.270L44032381512.1  L45938760768.0  L46506031415.14 L46881206513.10 L46888420773.9  L47205548646.4  L49493577844.3  L49799904432.3  L50059436232.1  L50404673919.1  L50796875722.11 L52045659405.3  L52118754430.17 L53035820241.9  L53075002650.8  L53271535775.270L53969727459.2  L54475214031.2  L55767739732.2  L56658999053.1  L57777299826.2  L58970213517.1  L59315137787.1  L59385437110.10 L60098763854.6  L60188359336.0  L6021324682.15  L62030920048.12 L62033268571.7  L6203936179.1   L64422884493.1  L66151427842.16 L6899380056.1   L696052593.2    L8827747003.8   L9356559645.16  L9631767084.2   L9835808138.2   L9873114841.11  P23170010975.281P40057967496.281P54460272136.281Q10649498890.278Q10649499535.277Q13734784178.277Q17701933584.278Q28496781288.280Q28498761192.281Q37216054521.278Q42439443119.281Q4451634193.281 Q4453582353.280 Q61556549392.279Q61847600945.278Q64683667846.28100000101<02G03Y04^05f05g06906M06f07@07I07J07V07d08?08@08J08S08k09509C09D09]09^09b0:30:V0:b0:g0:k0:o0;80;@0;N0;R0;^0<30<40<D0<I0<f0=L0>20>30>40>50>60>?0?40?90?:0?f0@I0@d0A10A;0AG0AL0AQ0Ah0B40Ba0C>0CY0DN0DU0DV0DW0D[0Db0Dg0Dj0EJ0ET0EU0F=0Fb0G;0G@0GE0Gh0Gl0H40HM0I80I?0I@0Id0K50LN0Mg0NR0O=0Oh0PS0QT0RU0SH0TR0US0VT0WI0XW0YnFS1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp12p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp12p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2sp2PP3CRT2lo2bs3LFB3LOS2FB3sp12p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3DPC3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2FB3APP2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stFS1P3BUF2W12p14Hp1aS2r33Hr31r2KR1q1H2H0S1P3END2p12Lw4Hp1a3HLw2LRS4CNTc1P2p12Lw3LBc5HCNT31HS1R2FB2F2SS2sp3sp13SP1S1R2lo3LOS3ALOS4CNTc1P3END2Lw3LBc5HCNT31HSS2PP1B1k1XS3CRT3CCBS1R3HIA1h2sp3TOP3sp13SP1S1R2PP3DPDS1P3END2p'3Hp'SS1R3HIA4PHIc1h1P3END1H2p'FS2FBS1P2p12Lw4Hp1a2LRS1R3HIA4PHIc1h1P3END2Lw2h33HV31H2p1S3CRT2FB3APCS3sp1S2spS2PPS2FB1c2HcS2LF3LFBS4CNTc1P3END1HS2FBS2PP3CRT3DPCS1R3HIA1h2sp3TOP4HTOPFS2sp3SPH3sp13SP1S3sp1S1R3HIA4STKc1h2sp2lo3TOP4HTOPS1R3HIA4FFRc1h1P3END1d2Lw2h34HFR31H2p1S1R3HIA4STKc1h2sp2PP2lo4PPLO4SLO'1a2HaSSFSS1R3HIA1hS1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp12f32j33LBc3SZC3CCBS3sp1SS1R4STKc2sp3CRT2lo5CRTLO4SLO'3sp13SP11A1k2HAS1P3END2p12p22Lw4Hp1a3HLw4Hp2a4Hp2bS1R4STKc2sp2lo4SLO'3sp13SP1S4CNTc1P2p'1HS1P3END2W2S2sp3sp13SP1S3sp1S3sp1S1R4STKc2sp2lo3LOS4SLO'S2sp3sp13SP1S1R4STKc2sp2lo3LOS3ALO4SLO'3sp13SP14DLOW1A2HAS1R3HIA4PHIc1h1P3END3BUD2Lw1HS1R3HIA4FFRc1h1P3END1d1H2p'S1R4STKc2LF2sp2PP3CRT2bs3LFB2FB3sp12f32j33LBc3SZC3CCBS1R3ACVFFS2spS2Lw2LRS3sp1S1XS1R3HIA4FFRc1h1P3END1d4BUDF2Lw1HS1R2lo3LOSSS1R3HIA4STKc1h2sp3CRT2lo5CRTLO4SLO'1a2HaS1R4STKc2sp2lo3slo4SLOS4SLOL3SPR4SLO'S3END3BUF2bs2W32p12Lw3HLwS3sp1S3sp1S2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS2FBS2sp3SPRS1P3END2p12Lw4Hp1a3HLw2LRS1R4STKc2sp2lo3LOS3ALO3ACV3SPR4SLO'3sp13SP1S2FB2F0FS1R4STKc2sp2lo3slo4SLOL4SLO'3sp13SP1S1R4STKc2LF2sp2PP3CRT2lo2bs4PPLO3LFB4SLO'2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2sp2PP3CRT2lo2bs4PPLO3LFB4SLO'3sp13SP12p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2sp2PP3CRT2lo2bs4PPLO3LFB4SLO'3sp13SP12p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2f32j33LBc3SZC3CCBS1R4STKc2LF2PP3CRT2bs3LFB2f32j33LBc3SZC3CCBS1R4STKc2LF2PP3CRT2bs3LFB2f32j33LBc3SZC3CCBS1R4STKc2LF2PP3CRT2bs3LFB2f32j33LBc3SZC3CCBS1R4STKc2LF2PP3CRT2bs3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3PP03LFB2f32j33LBc3SZC3CCB3HB0S1R4STKc2LF2PP3CRT3slo2bs4SLOS3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_stS1R4STKc2LF2PP3CRT2bs3LFB2f32j33LBc3SZC3CCB3HB05Ha_stS1R4STKc2LF2sp2PP3CRT2bs3AL83PP04CRT03LFB3SPR2FB3sp14SP1R2F02f32j33LBc3SZC3CCBS1R3HIA4STKc1h2LF2sp2PP3CRT3slo2bs3TOP3LFB4HTOP2p12Lw2f32j33LBc3SZC3CCB3HB05Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma main_call : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getcerts ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(23.$4.VR,VHIA,Vh,Vmo0,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(34.$4.(?.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(2?.$4.(?.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VCRT,$30.)P,(44.(45.VR,)VSI,Vm,)P,(13.(=.(1?.$4.VR,VHIA,Vh,)A1.VPHIc,(14.VEND,VP,))$46.)P,(47.$4.Vm,(48.VR,)(1=.$4.VR,VHIA,Vh,)(15.&40.Vs0,)(15.&40.Vsp,)Vd,)P,(13.(=.(20.$4.VR,VHIA,Vh,)(49.(14.VEND,VP,)Vd,))$4:.)(4;.$4.(4<.$4.VR,VHIA,VPK,VSI,VPHIc,$49.VCNTc,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VP,VEND,VCRT,(14.VEND,VP,)Vlo,Vslo,Vd,Vm,Vmo0,)(4=.(:.(;.Vra,Vsp,Vgp,Vtp,R17.R16.R15.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VCRT,)R14.R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(<.&40.$37.)Vfc,(11.(5.&40.))Vm,(12.$4.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST SS MI OPP OCRT SIP BUD UW BUDF.
    unfold A_PKCS7_GETCERTS. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof SLO as SLO'.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO' STKc0 NS1 TOP HTOP; lia]).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    unfold CRT_SIZE in *.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; unfold CRT_SIZE; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & x1 & y0 & y1 & y2 & z0 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & s11v & w0 & w1 & w2 & jm
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & L1C & JMC & L2C & FSHX
                   & SAVE & SLOT & ST48 & SThi & STlo & MI1 & HPP1 & CZ1 & HB1 & OPP1 & OCRT1 & APP & APC & PRES0 & SS1).
    unfold CRT_SIZE in APC, OCRT1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO' LOS ALO ACV NS1 STKc0; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & _ & _).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply mid_walk; unfold CRT_SIZE;
        first [ exact Ems | eassumption | match goal with |- ?g => idtac "MID-PRE-LEFT:" g end ]. }
    clear Ems FHD L1C JMC L2C FSHX SAVE SLOT ST48 SThi STlo MI1 HPP1 CZ1 HB1 OPP1 OCRT1 PRES0 SS1 HH1. intros ms2 P2.
    destruct P2 as [EQ | CQ].
    - (* [comment removed for export] *)
      destruct EQ as (m2 & r & p' & x1' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & s4v & s5v & s6v & s7v & s8v
                      & -> & Hr & HH2 & MI2 & FHD2 & FSH2 & SAVE2 & SLOT2 & ST482 & SThi2 & STlo2 & HPP2 & Hp' & CZ2 & OPP2 & OCRT2 & PRES & SS2).
      unfold CRT_SIZE in OCRT2.
      pose proof (presW_init_at R HIA h1 _ _ ([] ++ LB) LF m2 (bv_unsigned sp) (bv_unsigned sp) [(PP, PP + 8)] h HH2
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; rewrite Ehcs; exact Hx) Estk ltac:(clear - LOS SLO' NS1 STKc0; lia)) as PRES2.
      assert (HH2' : HM asegs R HIA h1 ([] ++ LB) ((FB, 128) :: LF) m2) by (cbn [app]; exact HH2).
      pose proof (presW_hmono R HIA h h1 LB LF _ _ _ m m2 PRES ltac:(intros x Hx; rewrite Ehcs; exact Hx) Estk) as PRESh1.
      pose proof OPP as CRP; apply aobj_crange in CRP. pose proof OCRT as CRC; apply aobj_crange in CRC.
      eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
      { unfold crt_zero in CZ2.
        eapply evtA_cs_mono.
        { eapply epi_walk with (h3 := h1) (LBc := []);
            unfold CRT_SIZE;
            first [ exact HH2' | exact PRESh1 | exact PRES2 | exact CRP | exact CRC | eassumption | reflexivity
                  | lazymatch goal with
                    | |- forall x, _ -> _ => intros x Hx; rewrite Ehcs; exact Hx
                    | |- fresh_apart _ ([] ++ LB) LF FB 128 => cbn [app]; exact FRSH
                    end
                  | match goal with |- ?g => idtac "EPI-A-PRE-LEFT:" g end ]. }
        intros x Hx; rewrite Ehcs in Hx; exact Hx. }
      cbv beta. intros ms9 EP.
      destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                      & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4 & HPP9 & HCRT9).
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold pkcs7_get_certs_postA_c.
      do 15 eexists. exists m9, mo9, h4, r, p', crt_own_zero, crt_junk_zero, (@nil blk).
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|].
      split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
      split.
      { pose proof (presW_presA asegs R HIA h1 LB LF _ _ _ _ _ PRES9) as HPF. rewrite Estk in HPF.
        eapply presA_weaken; [exact HPF| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside app] in Hx |- *. unfold CRT_SIZE in Hx. clear - Hx. tauto. }
      split; [rewrite E4top; exact Ehtop|]. split; [rewrite E4stk; exact Estk|]. split; [rewrite E4flag; exact Eflag|].
      split; [apply (proj2 (HKI4 mo9)); apply (proj2 (HKI mo9)); exact HK9|].
      split; [intros x Hx; rewrite E4cs, Ehcs; exact Hx|].
      split; [rewrite E4vol, Evol; pose proof (PHIc_mono 0 (END - P) ltac:(clear - W2; lia)); clear - H; lia|].
      split; [rewrite E4fr, Efr; unfold FFRg; pose proof (FFRc_mono 0 (END - P) (d + 1) ltac:(clear - W2; lia)); clear - H; lia|].
      split; [cbn [length]; pose proof (CNTc_mono 0 (END - P) ltac:(clear - W2; lia)); clear - H; lia|].
      split; [intros _; split; [rewrite E4vol, Evol; pose proof (PHIc_mono 0 (p' - P) ltac:(clear - Hp'; lia)) as H; clear - H; lia|];
              split; [rewrite E4fr, Efr; unfold FFRg; pose proof (FFRc_mono 0 (p' - P) (d + 1) ltac:(clear - Hp'; lia)) as H; clear - H; lia|];
              cbn [length]; pose proof (CNTc_mono 0 (p' - P) ltac:(clear - Hp'; lia)) as H; clear - H; lia|].
      split; [exact HPP9|]. split; [exact Hp'|].
      cbn [app].
      split; [apply crt_at_of_zero; [exact HCRT9| exact CAL8| exact CRT0]|].
      split; [rewrite crt_blocks_zero; apply Permutation_refl|].
      split; [exact NDL|].
      split; [cbn; clear; lia|].
      split; [exact HH4|].
      eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h1 LB LF _ _ _ _ _ PRES9))|].
      intros a Ha. exact (si_outside2 L SI PP 8 CRT 744 a DPD DCD Ha).
    - (* [comment removed for export] *)
      destruct CQ as (m3 & p1 & p2 & Lw & u0 & u1 & u2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6
                      & -> & HH3 & MI3 & FHD3 & FSH3 & SAVE3 & SLOT3 & SPILL3 & STa3 & STb3 & SThi3 & STlo3 & HPP3 & Hp1a & HLw & Hp2a & Hp2b & CZ3 & HB3 & OPP3 & OCRT3 & PRES & SS3).
      unfold CRT_SIZE in OCRT3.
      pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
      assert (CWC1 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) CRT 744).
      { eapply client_wrange_mono; [exact CWC| intros b Hb; apply fdata_cons_sub; exact Hb]. }
      assert (CWP1 : client_wrange L (LB ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) PP 8).
      { eapply client_wrange_mono; [exact CWP| intros b Hb; apply fdata_cons_sub; exact Hb]. }
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m3 PRES) as HP13.
      assert (SIP3 : si_P SI m3).
      { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP13)|].
        intros a Ha. exact (si_outside2 L SI PP 8 CRT 744 a DPD DCD Ha). }
      assert (UW3 : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
      { eapply uwc_presA; [exact HP13| exact UW| clear; lia| | clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO' SPR NS1 STKc0; lia].
        intros a Ha. cbn [outside]. split; [| split; [| exact I]]; clear - Ha PPLO CRTLO SLO' NS1 STKc0; lia. }
      assert (UWF : uwc asegs m3 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
      { pose proof SAVE3 as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
        replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
        eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW3| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
      clear HP13 UW3.
      destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SS3 ltac:(clear - SP1 SLO' SLOL NS1 STKc0; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply CRTPARSE with (h := h1) (LB := LB) (LF := (FB, 128) :: LF) (Q := p1) (blen := bv_unsigned Lw) (BUF := BUF) (bs := bs) (CRT := CRT) (lo := lo) (slo := slo) (d := d + 1);
          rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr; unfold CRT_SIZE;
          first [ exact HH3 | exact HB3 | exact BIN | exact CZ3 | exact CAL8 | exact CRT0 | exact OCRT3 | exact CWC1 | exact STlo3 | exact SSlo | exact SLOS | exact SLOL | exact MI3 | exact TPV | exact SIP3 | exact NDL | exact UWF | exact DCB | exact DCD | exact CRTLO | reflexivity
                | lazymatch goal with
                  | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                  | |- (length _ <= _)%nat => cbn [length]; clear - LFB; lia
                  | |- BUF <= p1 => clear - W1 Hp1a; lia
                  | |- 0 <= bv_unsigned Lw => clear - LR; lia
                  | |- p1 + _ <= BUF + _ => clear - HLw W3; lia
                  | |- BUF + _ < 2 ^ 47 => exact B47
                  | |- 0 < BUF => exact BUF0
                  | |- Z.of_nat (length bs) < 2 ^ 30 => exact BSMALL
                  | |- lo <= sp1 - STKc => clear - SLO' SP1 NS1 STKc0; lia
                  | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                  | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                  | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (PHIc_mono (bv_unsigned Lw) (END - P) ltac:(clear - LR HLw Hp1a; lia)); clear - BUD H; lia
                  | |- hfr _ _ _ _ + _ <= FR_MAX => pose proof (FFRc_mono (bv_unsigned Lw) (END - P) (d + 1) ltac:(clear - LR HLw Hp1a; lia)); unfold FFRg in BUDF; clear - BUDF H; lia
                  | |- _ = Z_to_bv 64 (bv_unsigned Lw) => symmetry; apply Z_to_bv_bv_unsigned
                  end
                | match goal with |- ?g => idtac "PARSE-PRE-LEFT:" g end ]. }
      cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
      destruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo4' & h3 & r3 & f3 & j3 & LBc
                      & E4 & Ea0 & Hr3 & MI4 & ST4 & SS4 & MF4 & HP4 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HCNT3 & CA4 & PERM4 & ND4 & RAW4 & HH4 & SIP4).
      injection E4 as Ems Emo. subst ms4 mo4 qa0.
      replace (ret_pc (Z_to_bv 64 0x982ec)) with (Z_to_bv 64 0x982ec : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      rewrite (unsigned_lit sp1) in ST4, SS4, HP4 by exact SP1R.
      rewrite Ehtop in HT3. rewrite Estk in HS3, HP4. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3. unfold CRT_SIZE in HP4.
      assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
      pose proof (hcs_ok asegs R HIA h3) as CSOK3.
      (* [comment removed for export] *)
      assert (HP4' : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) ([(CRT, CRT + 744)] ++ si_fp SI) m3 m4).
      { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
      (* [comment removed for export] *)
      assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (X00 ++ si_fp SI) m m4).
      { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
        eapply presA_trans; [eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| ]|].
        { intros x Hx. cbn [outside app] in Hx |- *. clear - Hx. tauto. }
        eapply presA_weaken; [exact HP4'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia|].
        intros x Hx. cbn [outside app] in Hx |- *. clear - Hx. tauto. }
      (* [comment removed for export] *)
      pose proof (fresh_apart_grow R HIA h3 LBc LB LF m4 FB 128 FRSH HH4) as FRSH3.
      pose proof (blocks_below_hm R HIA h3 _ _ m4 (LBc ++ LB) HH4 ltac:(intros b Hb; exact Hb)) as BB4.
      assert (OAP : forall b, In b (crt_blocks f3) -> 0 < snd b -> disjoint_from [(PP, PP + 8)] (fst b) (snd b)).
      { intros [B k] Hb Hk. cbn [fst snd] in Hk |- *. split; [| exact I].
        pose proof (obj_apart_new R HIA h3 LBc LB LF ((FB, 128) :: LF) m4 lo (htop asegs R HIA h) PP 8 B k DIMG HH4 ltac:(intros fb Hfb; right; exact Hfb) CWP ltac:(clear - ALO LOS; lia) ltac:(clear; lia)
                      ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERM4| exact Hb]) Hk) as X. clear - X. lia. }
      pose proof (presW_init_at R HIA h3 _ _ (LBc ++ LB) LF m4 (bv_unsigned sp) (bv_unsigned sp) [(PP, PP + 8)] h HH4
                    ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSh3 HS3 ltac:(clear - LOS SLO' NS1 STKc0; lia)) as PRES2.
      (* [comment removed for export] *)
      assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 128 -> cshd R LBq ((FB, 128) :: LF) SSPq TOPq c).
      { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
      apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 128) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(CRT, CRT + 744)] ++ si_fp SI) m3 m4 FB FSHXL CSOK) in FSH3;
        [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
      assert (DJF : disjoint_from ([(CRT, CRT + 744)] ++ si_fp SI) FB 24).
      { apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn [disjoint_from]; split; [clear - APC; lia| exact I] | apply si_disjoint_off; clear - F2; lia]. }
      apply (presA_rw_cells asegs R LB ((FB, 128) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(CRT, CRT + 744)] ++ si_fp SI) m3 m4 FB _ HP4) in FHD3;
        [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
         | exact DJF ].
      pose proof (art_data_lo asegs R HIA) as DLOW.
      assert (DJ : forall A k, sp1 <= A -> disjoint_from ([(CRT, CRT + 744)] ++ si_fp SI) A k).
      { intros A k HA. apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn [disjoint_from]; split; [clear - HA CRTLO SLO' NS1 STKc0 SP1; lia| exact I]|].
        apply si_disjoint_off. right. clear - HA DLOW ALO LOS SLO' NS1 STKc0 SP1. lia. }
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SAVE3; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SLOT3; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
      apply (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SPILL3; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
      apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in STa3; [| clear; lia| apply DJ; clear; lia].
      apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in STb3; [| clear; lia| apply DJ; clear; lia].
      apply (presA_stk asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SThi3; [| clear; lia| apply DJ; clear; lia].
      apply (presA_sshad asegs R _ _ _ _ _ _ m3 m4 _ _ HP4) in SShi; [| clear; lia| clear - HTOP TOP; lia].
      (* [comment removed for export] *)
      pose proof (client_range_lower L _ lo sp1 PP 8 (client_range_of_w L _ _ _ _ _ CWP1) PPLO) as CRPs.
      assert (DJP : disjoint_from ([(CRT, CRT + 744)] ++ si_fp SI) PP 8).
      { apply (proj2 (SInv.disjoint_from_app _ _ _ _)). split; [cbn [disjoint_from]; split; [clear - DPC; lia| exact I] | apply si_disjoint_off; clear - DPD; lia]. }
      apply (presA_rw_cells asegs R LB ((FB, 128) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(CRT, CRT + 744)] ++ si_fp SI) m3 m4 PP _ HP4) in HPP3;
        [| exact CRPs | exact DJP ].
      assert (OPP4 : aobj asegs AL (hcs asegs R HIA h3) m4 PP 8).
      { eapply aobj_cs_mono; [exact HCSh3|].
        eapply presA_aobj0; [exact CSOK| exact HP4| exact OPP3| intros x Hx; eapply hcs_below_top; exact Hx|].
        right. split; [exact CRPs| clear; lia]. }
      pose proof (sshad_merge asegs AL m4 slo sp1 (bv_unsigned sp) SS4 SShi ltac:(clear - SP1 SLOL SLO' NS1 STKc0; lia)) as SSm4. clear SS4 SShi.
      destruct CA4 as (CC4 & _ & _ & _ & OWN4).
      assert (SZC : cells_size (crt_cells f3 j3) = 744%nat) by reflexivity.
      pose proof (rw_cells_bound _ _ _ _ CC4) as CCB. rewrite SZC in CCB.
      pose proof (conj CC4 I) as CC4w (* [comment removed for export] *). apply rw_cells_blob in CC4. rewrite SZC in CC4.
      clear HP4 HP4' DJ OPP3 OCRT3 CZ3 HB3 MI3 STlo3 SSlo PRES HH3.
      (* [comment removed for export] *)
      apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF4))).
      clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
      clear HK1 MF1 MF4 mo1.
      assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCSh3| exact CFB]).
      assert (CRC3 : crange (hcs asegs R HIA h3) CRT 744) by (eapply crange_mono; [exact HCSh3| pose proof OCRT as X; apply aobj_crange in X; exact X]).
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSh3| exact SCS]).
      assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSh3| exact SCS0]).
      pose proof (hm_abase asegs R HIA h3 _ _ m4 HH4) as AB4.
      pose proof OPP as CRP; apply aobj_crange in CRP. pose proof OCRT as CRC; apply aobj_crange in CRC.
      assert (CRP3 : crange (hcs asegs R HIA h3) PP 8) by (eapply crange_mono; [exact HCSh3| exact CRP]).
      assert (CWP4 : client_wrange L ((LBc ++ LB) ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) PP 8).
      { eapply client_wrange_mono; [exact CWP1| intros b Hb; apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]]. }
      assert (WCPP : wcover R LB LF (bv_unsigned sp) (X00 ++ si_fp SI) PP 8) by (apply wcover_inside; cbn [inside app]; left; clear; lia).
      assert (WCPP2 : wcover R (LBc ++ LB) LF (bv_unsigned sp) [(PP, PP + 8)] PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
      (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        zstep.
        try match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
          replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (-21888) : word) by (apply bv_eq; vm_compute; reflexivity) end.
        zstep.
        pose proof (stk_of_rw_cells asegs m4 _ _ SPILL3) as K0. cbn [cells_size csize Nat.add] in K0.
        replace (sp1 + 24 + Z.of_nat 8) with (sp1 + 32) in K0 by (clear; lia).
        pose proof (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ STa3 K0 ltac:(clear; lia)) STb3 ltac:(clear; lia)) as ST48. clear K0 STa3 STb3 SPILL3.
        pose proof (presW_hmono R HIA h h3 LB LF _ _ _ m _ PRESb HCSh3 HS3) as PRESb3.
        eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
        { eapply epi_walk with (h3 := h3) (LBc := LBc);
            unfold CRT_SIZE;
            first [ exact HH4 | exact HCSh3 | exact PRESb3 | exact PRES2 | exact CC4 | exact CRP | exact CRC | eassumption | reflexivity
                  | match goal with |- ?g => idtac "EPI-B1-PRE-LEFT:" g end ]. }
        cbv beta. intros ms9 EP.
        destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                        & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH5 & HPP9 & HCRT9).
        apply aevtA_done. intros mo9 [HK9 MF9].
        unfold pkcs7_get_certs_postA_c.
        do 15 eexists. exists m9, mo9, h4, (-21888), p2, f3, j3, LBc.
        split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|].
        split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
        split; [pose proof (presW_presA asegs R HIA h3 LB LF _ _ _ _ _ PRES9) as HPF; rewrite HS3 in HPF; exact HPF|].
        split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
        split; [apply (proj2 (HKI4 mo9)); exact HK9|].
        split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
        split; [rewrite E4vol; pose proof (PHIc_mono (bv_unsigned Lw) (END - P) ltac:(clear - LR HLw Hp1a; lia)); clear - H HV3; lia|].
        split; [rewrite E4fr; unfold FFRg; pose proof (FFRc_mono (bv_unsigned Lw) (END - P) (d + 1) ltac:(clear - LR HLw Hp1a; lia)); clear - H HFR3; lia|].
        split; [pose proof (CNTc_mono (bv_unsigned Lw) (END - P) ltac:(clear - LR HLw Hp1a; lia)); clear - H HCNT3; lia|].
        split; [intros X; exfalso; clear - X; lia|].
        split; [exact HPP9|]. split; [clear - Hp2a Hp2b Hp1a HLw W2; lia|].
        split.
        { split; [exact (rw_cells_unblob _ _ _ _ _ _ (proj1 CC4w) SZC HCRT9)|]. split; [exact CAL8|]. split; [exact CRT0|]. split; [unfold CRT_SIZE; clear - CCB; lia|].
          eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := [(PP, PP + 8)]) (SP := bv_unsigned sp) (L2 := LBc ++ LB);
            [exact OWN4| intros b Hb; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PERM4| exact Hb] | | | clear - ACV; lia| exact MI9|].
          - eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
          - exact BB4.
          - exact OAP. }
        split; [exact PERM4|]. split; [exact ND4|]. split; [exact RAW4|]. split; [exact HH5|].
        eapply (si_heap_presx asegs L SI); [exact SIP4| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))|].
        intros a Ha. exact (si_outside1 L SI PP 8 a DPD Ha). }
      (* [comment removed for export] *)
      assert (R3 : 0 <= r3).
      { change 18446744073709551615 with (Z.ones 64) in KR. rewrite Z.land_ones in KR by (clear; lia). clear - KR Hr3. Z.div_mod_to_equations. lia. }
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into m5 end.
      lazymatch goal with A1 : rw_cells _ m5 (sp1 + 24) _, A2 : stk _ m5 sp1 (sp1 + 24), A3 : stk _ m5 (sp1 + 32) (sp1 + 48) |- _ =>
        pose proof (stk_of_rw_cells asegs m5 _ _ A1) as K0; cbn [cells_size csize Nat.add] in K0;
        replace (sp1 + 24 + Z.of_nat 8) with (sp1 + 32) in K0 by (clear; lia);
        pose proof (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ A2 K0 ltac:(clear; lia)) A3 ltac:(clear; lia)) as ST48; clear K0 A1 A2 A3 end.
      lazymatch goal with HHc : HM _ _ _ h3 _ _ m5, Pb : presW _ _ _ h LB LF _ _ _ m m5, P2 : presW _ _ _ h3 _ LF _ _ _ m4 m5, CCc : rw_cells _ m5 CRT _, MIc : mem_inv _ m5 |- _ =>
        rename HHc into HH6; rename Pb into PRESb6; rename P2 into PRES26; rename CCc into CC6; rename MIc into MI6 end.
      pose proof (presW_hmono R HIA h h3 LB LF _ _ _ m _ PRESb6 HCSh3 HS3) as PRESb3.
      eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
      { eapply epi_walk with (h3 := h3) (LBc := LBc);
          unfold CRT_SIZE;
          first [ exact HH6 | exact HCSh3 | exact PRESb3 | exact PRES26 | exact CC6 | exact CRP | exact CRC | eassumption | reflexivity
                | match goal with |- ?g => idtac "EPI-B2-PRE-LEFT:" g end ]. }
      cbv beta. intros ms9 EP.
      destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                      & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH5 & HPP9 & HCRT9).
      apply aevtA_done. intros mo9 [HK9 MF9].
      unfold pkcs7_get_certs_postA_c.
      do 15 eexists. exists m9, mo9, h4, 1, (p1 + bv_unsigned Lw), f3, j3, LBc.
      split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|].
      split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
      split; [pose proof (presW_presA asegs R HIA h3 LB LF _ _ _ _ _ PRES9) as HPF; rewrite HS3 in HPF; exact HPF|].
      split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
      split; [apply (proj2 (HKI4 mo9)); exact HK9|].
      split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
      split; [rewrite E4vol; pose proof (PHIc_mono (bv_unsigned Lw) (END - P) ltac:(clear - LR HLw Hp1a; lia)); clear - H HV3; lia|].
      split; [rewrite E4fr; unfold FFRg; pose proof (FFRc_mono (bv_unsigned Lw) (END - P) (d + 1) ltac:(clear - LR HLw Hp1a; lia)); clear - H HFR3; lia|].
      split; [pose proof (CNTc_mono (bv_unsigned Lw) (END - P) ltac:(clear - LR HLw Hp1a; lia)); clear - H HCNT3; lia|].
      split; [intros _; split; [rewrite E4vol; pose proof (PHIc_mono (bv_unsigned Lw) (p1 + bv_unsigned Lw - P) ltac:(clear - LR HLw Hp1a; lia)) as H; clear - H HV3; lia|];
              split; [rewrite E4fr; unfold FFRg; pose proof (FFRc_mono (bv_unsigned Lw) (p1 + bv_unsigned Lw - P) (d + 1) ltac:(clear - LR HLw Hp1a; lia)) as H; clear - H HFR3; lia|];
              pose proof (CNTc_mono (bv_unsigned Lw) (p1 + bv_unsigned Lw - P) ltac:(clear - LR HLw Hp1a; lia)) as H; clear - H HCNT3; lia|].
      split; [exact HPP9|]. split; [clear - Hp1a HLw W2 LR; lia|].
      split.
      { split; [exact (rw_cells_unblob _ _ _ _ _ _ (proj1 CC4w) SZC HCRT9)|]. split; [exact CAL8|]. split; [exact CRT0|]. split; [unfold CRT_SIZE; clear - CCB; lia|].
        eapply (crt_own_ok_presxD asegs L PK) with (CE := alloc_ceiling) (X := [(PP, PP + 8)]) (SP := bv_unsigned sp) (L2 := LBc ++ LB);
          [exact OWN4| intros b Hb; apply in_app_iff; left; eapply Permutation_in; [apply Permutation_sym; exact PERM4| exact Hb] | | | clear - ACV; lia| exact MI9|].
        - eapply heap_presx_weaken; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))| intros b Hb; apply in_app_iff; left; exact Hb| clear; lia| intros x Hx; exact Hx].
        - exact BB4.
        - exact OAP. }
      split; [exact PERM4|]. split; [exact ND4|]. split; [exact RAW4|]. split; [exact HH5|].
      eapply (si_heap_presx asegs L SI); [exact SIP4| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))|].
      intros a Ha. exact (si_outside1 L SI PP 8 a DPD Ha).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Theorem A_pkcs7_getcerts_spec_c : pkcs7_get_certs_stmtA_c asegs R HIA PK SI PHIc FFRg CNTc STKg A_PKCS7_GETCERTS.
  Proof.
    unfold pkcs7_get_certs_stmtA_c. intros until bs. intros; subst. eapply main_call; first [eassumption | reflexivity].
  Qed.
  (* [comment removed for export] *)
  Theorem A_pkcs7_getcerts_spec : pkcs7_get_certs_stmtA asegs R HIA PK SI PHIc FFRg CNTc STKg A_PKCS7_GETCERTS.
  Proof. apply get_certs_stmtA_of_c. exact A_pkcs7_getcerts_spec_c. Qed.
End Walk.

(* [comment removed for export] *)
