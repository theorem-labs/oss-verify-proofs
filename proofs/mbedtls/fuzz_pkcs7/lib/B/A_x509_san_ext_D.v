(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_len A_asn1_free_named_data_list_shallow A_asn1_sequence_free A_x509_get_name_stmt A_x509_seq_stmts A_x509_seq_stmtsE.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_parse_A A_x509_parse_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_bud A_x509_san_ext_B A_x509_san_ext_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_san_ext_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0017e3a7488845e5 0 2 0 1 1 1P0079e84ebfc25250 1 2 32 3 0 1 100 1 103 1 32 12 41 1 65 1 67 1 71 1 81 1 82 1 83 1 93 1 96 1 97 1 101 1 102 1 2 104 2 105 2P01a2a8dc84660150 1 1 8 3 1 1 117 1 120 1 10 43 1 82 1 88 1 96 1 108 1 111 1 112 1 118 1 119 1 121 8P025e3fe630f0a868 1 2 32 3 1 1 117 1 120 1 32 12 43 1 80 1 82 1 86 1 96 1 97 1 98 1 108 1 111 1 112 1 118 1 119 1 2 121 2 122 2P0294f3f61cbe882a 0 3 0 1 45 1 93 1P036af2d205ad5947 0 2 0 1 2 1P0429ebec09aba664 0 12 0 1 65 1 67 1 71 1 81 1 82 1 83 1 93 1 96 1 97 1 100 1 101 1P04506184f5a13efb 0 2 0 1 1 1P04567c4386661bc1 1 2 32 3 0 1 107 1 110 1 32 12 45 1 70 1 72 1 76 1 86 1 87 1 88 1 98 1 101 1 102 1 108 1 109 1 2 111 2 112 2P0500e9d1170188fe 0 6 0 1 40 1 54 1 80 1 100 1 101 1P05f9b43fa1d95d04 0 6 0 1 40 1 54 1 80 1 100 1 101 1P05ff476aebc76054 0 3 0 1 73 1 90 1P066c804af07534e9 0 6 0 1 41 1 55 1 94 1 116 1 117 1P0690ba7602467365 0 11 0 1 45 1 72 1 86 1 87 1 88 1 98 1 101 1 102 1 107 1 108 1P085ed06c1c3b108a 0 9 0 1 42 1 81 1 95 1 107 1 110 1 111 1 116 1 117 1P08790252e3b1ac37 0 6 0 1 41 1 92 1 94 1 116 1 117 1P087db20832226f33 0 11 0 1 42 1 81 1 95 1 96 1 97 1 107 1 110 1 111 1 116 1 117 1P08c89dfac1cff1b0 0 2 0 1 1 1P08fa142dbc080529 1 1 8 3 0 1 116 1 119 1 10 42 1 81 1 95 1 105 1 107 1 110 1 111 1 117 1 118 1 120 8P09155c03ad45fc8b 0 2 0 1 117 1P0a36560af37ea38a 1 2 32 3 0 1 107 1 110 1 32 12 45 1 70 1 72 1 76 1 86 1 87 1 88 1 98 1 101 1 102 1 108 1 109 1 2 111 2 112 2P0a73ee22c91e8ca1 0 4 0 1 46 1 91 1 94 1P0d8f67a824a1f07b 0 2 0 1 62 1P0db087a42371cf6f 1 1 8 3 0 1 116 1 119 1 10 42 1 81 1 87 1 95 1 107 1 110 1 111 1 117 1 118 1 120 8P0db9bfdce9e42f1f 0 4 0 1 42 1 117 1 118 1P0f204ad5677f2416 1 2 32 3 1 1 117 1 120 1 32 12 43 1 80 1 82 1 86 1 96 1 97 1 98 1 108 1 111 1 112 1 118 1 119 1 2 121 2 122 2P0f2ab3945121db95 1 2 32 3 0 1 107 1 110 1 32 12 45 1 70 1 72 1 76 1 86 1 87 1 88 1 98 1 101 1 102 1 108 1 109 1 2 111 2 112 2P0f66f113e8b1e351 1 2 32 3 0 1 100 1 103 1 32 12 41 1 65 1 67 1 71 1 81 1 82 1 83 1 93 1 96 1 97 1 101 1 102 1 2 104 2 105 2P0ffb5559eece5860 0 4 0 1 44 1 107 1 108 1P102c9974889ddc0c 0 3 0 1 75 1 92 1P1090fe3e3e3c9a11 0 3 0 1 75 1 92 1P10e667228f797f32 0 10 2 1 44 1 78 1 83 1 97 1 109 1 112 1 113 1 118 1 119 1P1255557662c4c995 1 1 8 3 0 1 116 1 119 1 10 42 1 81 1 87 1 95 1 107 1 110 1 111 1 117 1 118 1 120 8P12df192844f80bf8 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P1348c21c0c364b55 0 4 0 1 41 1 116 1 117 1P135f1007e64a0e59 0 4 0 1 41 1 116 1 117 1P1378f79ade50b7ff 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P137bb90928c85d93 0 6 0 1 41 1 55 1 94 1 116 1 117 1P139d7974348ff532 0 2 0 1 60 1P14e76cf3dca58bc6 0 2 0 1 2 1P15551c3a7d3d09d1 0 11 0 1 41 1 67 1 81 1 82 1 83 1 93 1 96 1 97 1 100 1 101 1P157d829e9af7280b 0 6 0 1 44 1 58 1 85 1 107 1 108 1P16167ef5e294edb8 1 2 32 3 0 1 118 1 119 1 32 3 1 1 117 1 120 1 2 121 2 122 2P16c62c989f5e6884 0 3 0 1 45 1 93 1P16daad129c12885e 0 2 0 1 116 1P18133a4c8d02f37d 0 2 0 1 1 1P1a419796c42f2335 1 2 32 3 0 1 118 1 119 1 32 3 1 1 117 1 120 1 2 121 2 122 2P1d0262c9a24d12bd 1 1 8 3 0 1 107 1 110 1 10 45 1 72 1 86 1 96 1 98 1 101 1 102 1 108 1 109 1 111 8P1d9bbf3b3dd0c2b3 1 2 32 3 0 1 107 1 110 1 32 12 45 1 70 1 72 1 76 1 86 1 87 1 88 1 98 1 101 1 102 1 108 1 109 1 2 111 2 112 2P1dc0b6de6cf28f8d 0 6 0 1 41 1 92 1 94 1 116 1 117 1P1f1b900dc3d4d990 0 3 0 1 43 1 91 1P208a2e2aaa9aa0ca 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P21b85e8a581a3b4c 0 6 0 1 44 1 58 1 85 1 107 1 108 1P224209713560144f 0 3 0 1 73 1 90 1P226b4d2a7f0c805b 0 11 0 1 45 1 72 1 86 1 87 1 88 1 98 1 101 1 102 1 107 1 108 1P230c492cd275af20 0 2 0 1 1 1P23b24284628701b7 0 11 0 1 42 1 81 1 95 1 96 1 97 1 107 1 110 1 111 1 116 1 117 1P24853f0b0c0c1bb6 0 4 0 1 45 1 108 1 109 1P24b02632d3fcf8fe 0 10 2 1 47 1 69 1 74 1 88 1 100 1 103 1 104 1 109 1 110 1P24e15c9ebbcaf86a 1 1 8 3 1 1 108 1 111 1 10 46 1 73 1 79 1 87 1 99 1 102 1 103 1 109 1 110 1 112 8P251f91e9fb64fc3d 1 1 8 3 1 1 108 1 111 1 10 46 1 73 1 87 1 97 1 99 1 102 1 103 1 109 1 110 1 112 8P25c0bd8cd4de9d34 0 2 0 1 2 1P266b1ae25e498f9c 0 14 0 1 45 1 47 1 67 1 72 1 77 1 86 1 94 1 95 1 98 1 101 1 102 1 107 1 108 1P26928ea1b1d816e7 0 9 0 1 42 1 81 1 95 1 107 1 110 1 111 1 116 1 117 1P26e87827f5867ca7 0 2 0 1 60 1P26f9385719e3b76a 0 9 0 1 45 1 72 1 86 1 98 1 101 1 102 1 107 1 108 1P27457c60fc394f66 1 1 8 3 1 1 117 1 120 1 10 43 1 82 1 88 1 96 1 108 1 111 1 112 1 118 1 119 1 121 8P2803f4063198846f 0 4 0 1 43 1 88 1 91 1P283319dba29d3e80 0 16 0 1 42 1 44 1 65 1 66 1 76 1 81 1 95 1 103 1 104 1 107 1 110 1 111 1 112 1 116 1 117 1P284a1a4a41add1ae 0 11 0 1 42 1 81 1 95 1 96 1 97 1 107 1 110 1 111 1 116 1 117 1P286bae47cb20a975 0 3 0 1 43 1 91 1P29dbaa708bd99ece 0 10 0 1 45 1 72 1 86 1 89 1 98 1 101 1 102 1 107 1 108 1P2a1bfd3f96cfc202 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P2a468c5fece043f0 0 8 0 1 67 1 81 1 82 1 83 1 93 1 96 1 97 1P2b5577c13dd9e378 0 10 0 1 42 1 81 1 95 1 98 1 107 1 110 1 111 1 116 1 117 1P2d3d23318c1f66c9 0 11 0 1 41 1 67 1 81 1 82 1 83 1 93 1 96 1 97 1 100 1 101 1P2df34684458626e5 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P30447619b575d05b 0 6 0 1 44 1 83 1 85 1 107 1 108 1P30ee7f622926b98d 0 3 0 1 54 1 80 1P313757a4be29c586 1 1 8 3 0 1 116 1 119 1 10 42 1 81 1 95 1 105 1 107 1 110 1 111 1 117 1 118 1 120 8P31be0e3a102bbf25 0 10 0 1 42 1 81 1 95 1 98 1 107 1 110 1 111 1 116 1 117 1P32d33f528997aa71 1 1 8 3 0 1 108 1 111 1 10 46 1 73 1 87 1 97 1 99 1 102 1 103 1 109 1 110 1 112 8P333c5d0dd645a3dc 0 16 0 1 42 1 44 1 65 1 66 1 76 1 81 1 95 1 103 1 104 1 107 1 110 1 111 1 112 1 116 1 117 1P33413319c77a3a96 0 9 0 1 73 1 87 1 97 1 99 1 102 1 103 1 108 1 109 1P339bd8068f3b7517 0 2 0 1 116 1P33ae6d802e950499 1 2 32 3 1 1 117 1 120 1 32 12 43 1 80 1 82 1 86 1 96 1 97 1 98 1 108 1 111 1 112 1 118 1 119 1 2 121 2 122 2P34e28fdbd61d8491 1 1 8 3 0 1 107 1 110 1 10 45 1 72 1 78 1 86 1 98 1 101 1 102 1 108 1 109 1 111 8P36336c13cdeef196 1 2 32 3 1 1 108 1 111 1 32 12 46 1 71 1 73 1 77 1 87 1 88 1 89 1 99 1 102 1 103 1 109 1 110 1 2 112 2 113 2P36dfe3fc9b07c01d 0 10 0 1 63 1 68 1 73 1 80 1 82 1 90 1 94 1 97 1 98 1P37671edac8e2993b 0 6 0 1 41 1 55 1 94 1 116 1 117 1P3776b9b9b1a991ff 0 2 0 1 60 1P377e8a80e966916d 0 2 0 1 61 1P37984f78b873b492 1 2 32 3 1 1 108 1 111 1 32 12 46 1 71 1 73 1 77 1 87 1 88 1 89 1 99 1 102 1 103 1 109 1 110 1 2 112 2 113 2P3887966a6038b472 0 4 0 1 42 1 117 1 118 1P392082f0ccbf36e7 1 2 32 3 1 1 117 1 120 1 32 12 43 1 80 1 82 1 86 1 96 1 97 1 98 1 108 1 111 1 112 1 118 1 119 1 2 121 2 122 2P3a382e631da66d71 0 3 0 1 46 1 94 1P3a4feb5c443fde02 1 1 8 3 1 1 117 1 120 1 10 43 1 82 1 96 1 106 1 108 1 111 1 112 1 118 1 119 1 121 8P3a8440f5625a5a18 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P3b5ed2171eb13331 1 2 32 3 1 1 108 1 111 1 32 12 46 1 71 1 73 1 77 1 87 1 88 1 89 1 99 1 102 1 103 1 109 1 110 1 2 112 2 113 2P3d4b168ffddaf9a3 0 3 0 1 76 1 93 1P3d7c38b9d164a1db 1 1 8 3 1 1 117 1 120 1 10 43 1 82 1 96 1 106 1 108 1 111 1 112 1 118 1 119 1 121 8P3eab9f028a03052d 1 2 32 3 0 1 116 1 119 1 32 12 42 1 79 1 81 1 85 1 95 1 96 1 97 1 107 1 110 1 111 1 117 1 118 1 2 120 2 121 2P3f2cf7ae4aedda0b 0 10 2 1 44 1 78 1 83 1 97 1 109 1 112 1 113 1 118 1 119 1P3fae4c611d818d3b 0 2 0 1 117 1N001a74ad50c3d155N001b94e736c763c1N005034bfd6edc27cN0060ab2a14d50874N009f1ec4eb605d4dN013087351479824cN013660e56a43ee44N01ba79620771547bN01e4472dc9f986baN01e5446dbbb384ceN02436dad6ebd9080N0260134fbda6909fN027f6a62cf0439aeN02f1c811666c313aN03018df8f9e12146N04a1f14e4af28b5bN057f1fd67f55b847N077ea52c33094687N0846b878078711d5N09957639787fb4baN0a029a98682a2b87N0a17eb71129c2c87N0ab412e2671314d7N0ac3d0efe680392fN0b38a1ecb5a1b424N0cd3e4ef2a358445N0cf2b2fc652e6208N0de88a10e70a9ffbN0e5d7eed3a721c40N0ee57b357cd4e347N0ef3bf146e515dbdN0f2bbb792283836bN0f6069afb7c852b7N0f7a27906c652431N0f7cc8502339d1f0N0f88cb0af58f898fN0fd4cc1c6bba96cbN100d3a7ada403fccN1033b2a2013b0dbeN111a4cc45bca19b2N134783663ce31c53N1418764789573b49N141c112cd004cfe9N1478e4643c2d8c0fN14a39758e41b0248N15998182daab3e18N15ce0232d2552172N15de95b38e78cac8N1605b17e0b6850ccN161bb5dba3490548N1651a734e0e62f0eN1689b44b7350dbf3N168c636087bc6201N16be381984bc15cbN16c37abc1b250eb4N16f87e6420e699faN170248f944971014N17bea3691397f603N1847f74a8c631f83N185ac2291f384489N1860241471f3cb46N18902bf25de8a10fN1898e652a7c97717N198d2868c96c371bN19a8eb5f5ce79e56N1a868597bb6a689bN1affd5a29e023cf2N1b3dc3dd13e8ffc8N1b9d126618fe066fN1be7c587b251bf47N1c179fd49b5a98f4N1c463be8743fbb50N1c786c915b3b7528N1c78d0fcc134b4eeN1c8634a30f396f82N1cb909159c0e910aN1d9eba29d9fa0a00N1daa4c04b5b0b2a5N1dd984a3555d4822N1de24c5da7218713N1deb4710e8c1a38fN1dfdb754844473fbN1e2da21d41a7e00dN1eabe067a2931557N1ecb3fbd1b29b3b2N1f136eb5075e2ec6N1f48921cc8cd32baN1f4d7f0f2f9db842N1fe1a8fe396803eeN200d0b9a453cb294N2028449c0bcc5658N203989271a05210cN20aa877ae12fe6d4N20c73686c454dac3N21f2122307a07612N2231353be09e3828N22b8da22c0a8fd2dN22d404320aab8ab2N22e9fa7c11cf787cN238072d42fb441d2N238db77aaa85a4bcN2394310c2a2c067eN23eb2f4e80137bceN23f3dcbc919bcff1N243a6c86d11fd3c0N25209435d9fc2663N25778dd30b4f223eN25920971aef7726bN25ae068ae195ecf7N25c7192bcf567c77N2604fab3cd0d6567N26c3544f46a24d55N270b1b809e7687c6N27421c1f583865d0N2815651509fbdc6eN282b3130bd3c56e0N288795e773ab529fN293f353fbe3cfb36N2961f41dc3ce7aa3N29ef69e320526f43N2a6de01c7370fbf0N2abb0e7e93c86856N2ad1c18745b24e57N2adde2a613ae0fc5N2b9709dd80e8c7cdN2bda6d37333301b7N2bdf917ab54d47f7N2d8bede310d20cffN2d8ff4a6bc65611aN2db40c4976fba67cN2deb6525ed18f5a6N2e31f2aa804891caN2e72b9abe35727f7N2f764d788a710b96N2f8a280e30ab444aN3024c7ef047b811bN307c4868c81e24d3N30bc8e247e10afabN30cb3b0cf3f590b6N30e47bdfa79e32e7N30ff1a04809be81bN32229fb7fd85b2bbN325aa6fe7907a3d0N326d8e6450363d92N334efc4fcbb319c9N336f6f13f06730a0N338fd74c08a58098N34000a7a581d7ce8N34011a3cdd5106d9N3447291a8551c4ddN3447755fa762c0a6N347b10f2cd55dbbfN34984a63ea31b0a3N359c9cacf18f4185N36075eaaa3962dc1N368fa254c0ac46ceN36fcbb8d91349ae2N37459592514b75bbN374a71679f096c1aN376f67cd14bdee5fN37b36aab361e5beaN37dc8bf898e21dfaN381fb376dec14f60N386fc1cfbe80fee4N387d16475477c839N388e524dc6b7c9c0N38adbc748cbfdec9N3975bef95beaf84aN3996cf8540ef8fcaN3a07ca64f3394caaN3a22c986b25d4c62N3abe5e29fbc86a9eN3aca9f32f92d467fN3b3e599876d8ce52N3b8c491426232e53N3bc21a461f25e946N3be5110ce01ad33dN3d21ac9cb44bb3e9N3d97abab0553c1e7N3dadb19a972bb4e6N3dcc196ebfc8e344N3ed31bf432740c62N3f1593a4874f620fN3f194a1fb0988872N3fa212f0aa0b0268"%lxh.
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
  Local Notation STKx := (A_x509_san_ext_A.STKx R STKp).
  Local Notation CNTx := A_x509_san_ext_bud.CNTx.
  Local Notation PHIx := (A_x509_san_ext_bud.PHIx PHIp CNTp).
  Local Notation FFRx := (A_x509_san_ext_bud.FFRx FFRp CNTp).

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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2S in SM2; unfold A_x509_san_ext_A.STKx in SLO; unfold SEQ_SIZE in *;
    pose proof NRT as (NRTm & NRTf & NRTa);
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation NB := (END - P).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHb := A_x509_san_ext_A.FSHb.
  Local Notation rsl := (A_x509_san_ext_A.rsl CUR).
  Local Notation LF' FB := ((FB, 256) :: LF).
  Local Notation POST := (seq_parser_postE asegs R HIA PHIx FFRx CNTx (fun r => r = 0) h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                            PP CUR P END BUF NB lo slo d m mo0).
  Local Notation sfr := (A_x509_san_ext_C.sfr R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m PP CUR P END BUF lo slo bs).
  Local Notation svA := (A_x509_san_ext_C.svA R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo0 PP CUR P END BUF lo slo bs).
  Local Notation Wc := (A_x509_san_ext_C.Wc PP).
  Local Notation nLB := (A_x509_san_ext_C.nLB LB).
  Local Notation nfreshA := (A_x509_san_ext_C.nfreshA R LB LF PP CUR).
  Local Notation curFA := (A_x509_san_ext_C.curFA CUR).
  Local Notation headrep := (A_x509_san_ext_C.headrep CUR END BUF).
  Ltac sfr_open D :=
    destruct D as (HHc & HTc & HSc & HCSc & SUBL & SP1 & SP1M & F64 & FRSH & CFB & PRES
                   & FHD & TLc & TSN & FSH & SAVE & RSL & TSB & STb & STlo & PPc & Hpc & BYc & OPP & OBUF & OCUR & CURc & OCc & CURF & MIc & SSc).
  Ltac svA_open D :=
    let S := fresh "SFR" in
    destruct D as (S & HKc & MFc & HFc & HVc & HFRc & SUBN & HND & HFR & HCF & HHD & HLS & CBUF).
  (* [comment removed for export] *)
  Ltac fin_sfr t :=
    unfold A_x509_san_ext_C.sfr;
    spine; first [ eassumption | (unfold A_x509_san_ext_A.FSHb; eassumption) | (unfold A_x509_san_ext_A.rsl; eassumption)
                 | (repeat split; eassumption) | reflexivity | solve [t] | match goal with |- ?g => idtac "SFR-LEFT:" g end ].

  (* [comment removed for export] *)
  Lemma swrap32_errsum' : forall r c, -0x10000 < r <= 0 -> 2^64 - 0x10000 <= c < 2^64 ->
    bv_swrap 32 (r mod 18446744073709551616 + c) = r + (c - 2^64).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  (* [comment removed for export] *)
  Definition ERRQ (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (k0 k8 k16 k24 k48 : word) (cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (m0 : mem)
      : machine_state -> Prop := fun ms =>
    exists (mm : mem) (r p' : Z) (w0 w1 w2 tl tg pd ln pv : word) (j64 jn : list byte)
           (xra t0 t1 t2 a0 a3 a4 a5 a6 a7 s3v s4v s5v s6v s7v s8v s9v s10v t3 t4 t5 t6 : word),
      ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 (Z_to_bv 64 FB) (Z_to_bv 64 FB) a3 a4 a5 a6 a7
                   (Z_to_bv 64 r) s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
              F (Z_to_bv 64 0xae940) fc None mm (seg_rom asegs)
      /\ -0x3000 < r < 0
      /\ sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd ln pv jn p' cur ctc cpc clc cpp cnx mm
      /\ presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc cur) m0 mm.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18993184566.1900000<S2FB1k1B1j1X". (* [comment removed for export] *)
  Lemma fresh_apart_relist : forall (h3 : HST asegs R HIA) LBa LBq m3 FB k,
    fresh_apart R LBa LF FB k -> HM asegs R HIA h3 LBq ((FB, k) :: LF) m3 -> fresh_apart R LBq LF FB k.
  Proof.
    clear. intros h3 LBa LBq m3 FB k (F0 & F1 & F2 & F3) HH. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
    destruct (hm_apart asegs R HIA h3 _ _ _ HH) as [_ BA].
    pose proof (blocks_apart_app2 LBq ((FB, k) :: LF) (B, j) (FB, k) BA Hb ltac:(left; reflexivity)) as X. cbn [fst snd] in X. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition CALLQ1 (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (k0 k8 k16 k24 k48 : word) (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (m0 : mem)
      : machine_state -> Prop := fun ms =>
    exists (mm : mem) (p1 : Z) (w0 w1 w2 tg pd Lw : word) (j64 : list byte)
           (xra t0 t1 t2 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word),
      ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 (sp1 + 96)) (Z_to_bv 64 (FB + 64)) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
                   (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) s10v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
              F (Z_to_bv 64 0xae760) fc None mm (seg_rom asegs)
      /\ p + 2 <= p1 /\ p1 + bv_unsigned Lw <= END
      /\ sfr hc Lh FB sp1 w0 w1 w2 Lw (Z_to_bv 8 0) k0 k8 k16 k24 k48 j64 tg pd Lw (Z_to_bv 64 p1) (repeat (Z_to_bv 8 0) 80) p1 cur ctc cpc clc cpp cnx mm
      /\ presW asegs R HIA hc Lh LF (bv_unsigned sp) (bv_unsigned sp) (Wc cur) m0 mm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D1; try lx_pin1 ALC; try lx_pin1 HCUR; try lx_pin1 B2; try lx_pin1 HPP; try lx_pin1 cpad; try lx_pin1 ct; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 slo; try lx_pin1 lo; try lx_pin1 BUF; try lx_pin1 P; try lx_pin1 CUR; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LF; try lx_pin1 LB; try lx_pin1 h; try lx_pin1 CNTp_add; try lx_pin1 FFRp_add; try lx_pin1 PHIp_add; try lx_pin1 CNTp_mono; try lx_pin1 FFRp_mono; try lx_pin1 PHIp_mono; try lx_pin1 SEQFREE; try lx_pin1 FREEL; try lx_pin1 PSAN; try lx_pin1 CNTp; try lx_pin1 FFRp; try lx_pin1 PHIp; try lx_pin1 HMND; try lx_pin1 CALLOC; try lx_pin1 AMC; try lx_pin1 SM2; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "07E0@C17025492443.253C23922862675.254C40860242543.286C60407910007.287D10637083023.204D10639034250.287D12660624642.201D16069757090.287D16899842714.287D21827169904.246D21827169904.256D22857195214.202D2455419791.287 D2459793318.200 D24982003465.205D26145662235.202D26272582909.202D27847976046.256D29848042137.202D31528442088.201D32452690557.200D32456773204.287D32467519497.202D33196749127.201D3388366767.199 D35883165037.199D38372681352.203D39245671661.287D39258595524.200D45704738334.199D45904138324.287D46792746863.287D46795284842.204D52459714204.202D60109265000.202D60109265001.203D60109265006.204D60109446735.246D60109446735.256D60111543915.287D62011770184.205D62184560063.202D63108280425.202D63203098543.203D66239447338.287D66251787523.200D68411655660.199D6899603433.199 D8210892007.246 D8210892007.256 K12369550074.256K20983836855.286K29380230238.287K30995417079.287K3357422114.256 K40600131300.286K44909611826.256K49539617926.287K65856058596.287K67300144087.287K6883718497.254 L10607040861.2  L11435711538.14 L11903015084.7  L12252132089.3  L12374102380.3  L13176305223.2  L13552329815.244L13590130921.244L13609633268.1  L13921201636.2  L15479883060.4  L16507621472.3  L18271036603.182L19548981075.169L19548981082.177L19914454641.3  L19980016842.7  L20977711877.2  L21218866939.2  L21472756189.3  L21654730866.2  L21870408481.0  L23904852552.244L24109380644.6  L2621559066.1   L26347244049.255L27111942217.1  L27832436140.262L27942945638.11 L28303713233.13 L29391009772.3  L29480742978.3  L30471084548.1  L30507144274.2  L3055355236.3   L3097940137.1   L30997223346.3  L32164962551.1  L33706827952.255L3371361092.2   L34673485611.1  L34881116657.3  L35524160859.1  L35653441506.13 L36463206329.4  L37515311624.244L38235734261.1  L38692635477.0  L39332637397.0  L40585223510.2  L4111429939.7   L41251426164.1  L41409160545.3  L41930984765.2  L42203879684.1  L42488948659.2  L43300649301.0  L43317676572.3  L44897386660.2  L45746831473.2  L45767744563.2  L47870616696.2  L48119718052.202L48119718054.172L48119718055.173L48119718060.165L48119718063.164L48119718063.204L48132302223.233L48132302231.232L48455046775.1  L48878812414.12 L49111522807.1  L49233373885.2  L49478371288.2  L49526752708.2  L5021251703.1   L50678314462.3  L5067997814.169 L5067997823.177 L50797055232.13 L52941874306.3  L55085943702.3  L5630415447.3   L56380991837.10 L56523586534.1  L57387013391.2  L57401527990.6  L58039649675.2  L5856141729.0   L58800853620.11 L58972524609.3  L59308586248.2  L59308586248.202L59578101107.208L60050824855.2  L60098763854.6  L60344741464.1  L60806163856.13 L62275882349.3  L63514960365.3  L64179129035.1  L6456363088.3   L64850595401.0  L65278984340.172L65278984349.164L65862516566.2  L66151427842.16 L66298372189.2  L66812728480.3  L66927438747.1  L67070089790.2  L67304579733.2  L6887286939.2   L6910010083.172 L6910010090.164 L7755672680.1   L8265267294.0   L8680080987.1   L881835912.0    L9048215537.2   L9080220944.4   L9356559676.18  L9631767084.2   L9748633241.2   O10642145966.286O10869052557.283O1256822778.283 O1478916974.256 O14914823957.286O17025492443.253O17215019116.286O18664807618.256O18990788248.287O20868868134.287O22527103150.287O23922862675.254O24491819535.285O24745514321.256O30012554411.287O3078286936.256 O33083286018.256O33451744063.287O3491220723.286 O37557392443.287O3823870407.287 O426448880.283  O43849271089.256O44940300031.286O49699726460.286O50009742757.283O50689527441.256O54122075603.287O55211981985.283O55518239188.253O56414299794.256O56949683218.256O57033538278.287O57796590714.286O58199495442.255O59625529265.256O60923041807.284O62217770509.286O64471909102.287O64660938334.256O66812877810.256O67171060367.256O8121201118.253 P12257878110.256P13909131111.286P16492167430.256P19901359346.283P21212095580.253P21649959665.283P30483304850.255P30513436402.287P3067467751.283 P34896300886.253P35526258683.285P36465839390.256P41419110342.256P41936805786.256P42199519890.256P42487016449.287P45740036822.256P45755520933.256P47874275067.286P49228642366.286P50673575773.283P52940256805.256P55088519473.256P58043275016.286P62262763502.283P63503971146.253P66294657758.287P66816411171.287P67066431677.286P6883718497.254 P8686372091.284 P9052888434.286 P9762015195.287 Q10521014459.219Q10523111606.211Q10592386192.209Q10594483355.215Q10594630297.287Q10598576412.262Q10637083010.210Q10637083914.222Q10639034250.287Q10639180173.218Q11135471355.287Q11657494690.209Q11659151019.287Q11659591849.215Q12549685577.216Q12551782724.210Q12562269292.250Q12562269292.283Q12562269300.248Q12562269300.282Q12658527497.223Q14851060499.226Q14851060500.227Q15223151242.210Q15229444002.250Q15229444026.282Q15766564435.256Q16069757090.287Q16178749877.209Q16180832188.287Q16180847038.215Q16431624348.287Q16663101329.256Q17025597925.287Q17580821928.219Q17683171742.287Q19561597654.262Q20827837006.248Q20827837014.283Q20832032627.216Q21765573510.287Q22855098056.216Q22855098061.224Q23613318552.256Q23615071876.248Q23615071900.250Q23704213803.215Q23704526633.287Q23925414032.228Q23925414034.219Q23927511199.211Q24112763840.282Q24112763864.250Q24123250416.210Q24125347580.217Q24132301258.208Q25167323776.250Q25167323800.282Q25182005160.210Q26143565085.216Q26145662224.210Q26147758112.282Q26147758136.250Q26716641902.250Q26716641910.282Q26718740294.210Q26868043871.256Q27100788706.256Q27575848480.287Q2805923721.287 Q29778078658.287Q29848042130.210Q29862723490.282Q29862723514.250Q31124869336.256Q31697440514.282Q31697440538.250Q31703730738.210Q32437204119.256Q32439777163.248Q32439777171.250Q32440833928.208Q32440833936.214Q32465422346.224Q32465422351.216Q32667206377.248Q32679510481.287Q32679790547.215Q32679790551.219Q32681607669.256Q33194651980.223Q33271078502.250Q33271078502.283Q33271078526.248Q33271078526.282Q33283660611.216Q33285757774.210Q34363165844.256Q34669522109.256Q34671243169.248Q34671243193.250Q34964382778.256Q35655619520.226Q38250992817.227Q38250992822.226Q38370584201.225Q38370584206.217Q40216052059.214Q40478267464.287Q42439168719.256Q42439381099.252Q42439381099.284Q42441265899.287Q42441479394.231Q43338679170.216Q43351262887.283Q43351262911.248Q44185591100.211Q45052365066.256Q45058574862.250Q45642374826.210Q45644471170.250Q45644471194.282Q46792746863.287Q46793187688.218Q46795284839.210Q46795285999.222Q47228624638.219Q47230721779.211Q47313632804.250Q47313632804.283Q47313632828.248Q47313632828.282Q47326214913.216Q47328312076.210Q47766815249.248Q47780987149.256Q48117620902.209Q48118064779.256Q48119718061.215Q48120161967.287Q48132302223.214Q48132302223.250Q48132302231.208Q48132302231.248Q48360113622.256Q49427017736.210Q49441699104.250Q49441699128.282Q49561274038.219Q49563371195.211Q50958212280.256Q52068366394.214Q54578303540.210Q54592984836.282Q54592984860.250Q54962373294.287Q5638002271.262 Q56525516072.214Q56525516080.208Q56531220666.209Q56533073587.287Q56533317809.215Q57129507055.209Q57830202365.287Q60111362153.226Q60458335630.216Q62009673032.228Q62009673034.219Q62011770183.211Q62380812747.256Q63110377583.216Q63201001385.217Q63201001390.225Q64157425262.250Q64157425270.282Q64172104518.210Q64681502667.231Q64681845186.287Q64683598658.252Q64683598658.284Q64683942374.256Q65266402725.208Q65266402749.214Q65278984340.220Q65278984346.229Q65278984349.212Q67517027822.248Q67517027822.282Q67517027830.250Q67517027830.283Q67521220819.216Q67523317982.210Q6897428426.214 Q6897428434.208 Q6910010083.220 Q6910010090.212 Q6910010093.229 Q7121519350.287 Q8126701711.256 Q8128848779.250 Q8128848787.248 Q9356559649.236 Q9356757767.264 Q9633850153.262 Q9644583048.256 Q9646680236.287 00000100200600:00X01=01_03A04Q05605[06=06>06?06f06g06h08;08<08=08[09@09b0:D0:E0:F0:d0:e0:f0;D0;E0;j0<H0<I0=00=W0>>0>l0?Z0@H0@h0@i0@j0AH0Am0BK0BL0Bj0CO0D40DV0E^0Fj0GL0Go0I70IX0Je0Km0M90M:0MB0N<0NU0NV0NW0N_0OQ0PZ0P^0P_0Pn0Po0QW0R;0R_0R`0S80S90S:0SE0SF0SG0T30TG0TL0U?0UC0Uh0VU0WJ0WK0WV0WW0WX0WY0W]0W^0Wb0XP0XQ0XU0XV0XW0Xo0Y00Y\0Y`0Ya0Yb0Yc0Z:0Z>0Z?0Z@0ZA0ZB0ZC0ZN0ZO0ZP0ZQ0ZR0[U0\Q0]M0^I0_E0`H0aK0bN0bR0cC0cH0cI0cQ0cR0cS0cT0dF0e80ea0eb0ec0en0fG0fK0fR0ff0fg0fh0gQ0g]0gc0gd0hG0hO0hY0h^0iS0iT0iU0iV0ib0ic0j60jI0jJ0jl0jm0jn0k20k30k40k50kH0k[0k_0k`0ka0kb0kc0l20lo0m60m70m80m90m:0m;0m<0m=0m>0m?0m@0mA0mB0mC0mD0mE0mF0mG0mH0mI0mJ0mK0mL0mM0mN0mO0mP0mQ0mR0mS0mT0mU0mV0mW0mX0mY0mZ0m[0m\0m]0m^0m_0m`0ma0mb0nH0oS10911D11E11F11G12J13U14f14g15O16517F17G18J19[1:^1;o1=@1=f1>L1?11@B1@h1AN1B01C=1DH1DI1DJ1EU1F`1G51GJ1G]1H01HJ1Hd1I71IJ1Id1J71JQ1JR1JS1JT1JU1JV1JW1JX1JY1JZ1Jn1Jo1KF1KG1KH1KI1Km1M41MG1Ma1N41O?1Oa1P;1P<1QG1R21R31R41R51S@1ST1Sh1TB1T\1U61U71U81UP1V41VX1VY1VZ1V[1V\1V]1V^1V_1V`1Va1Vb1Vc1Vd1Ve1Vf1Vg1WA1WB1WC1W^1X@1XA1XB1XC1XD1XE1XF1XG1XH1XI1XJ1XK1XL1X`1Y41Y51Y61Y71Y81Y91YM1YN1YO1YP1YQ1YR1YS1YT1Yn1ZH1Zb1[e1\L1\_1]21]F1]Z1][1]\1^>1^`1_B1_d1`?1`@1`A1`B1`C1`D1`E1`F1`G1`H1`b1a51aH1a[1b11bG1bH1bI1bJ1bK1bL1bM1bN1bO1cK1dN1eJ1fM1gI1hL1iH1jK1k01k11k21k31k41k51k61k71k81k91k:1k;1kU1kV1kW1kX1kY1kZ1k[1lN1lg1m>1mP1mb1n41nV1nW1nk1o?1o@1oA1oB1oj20Y21H22722f23923L23_24224E24F24G24H24I24J24K24^25125D25W25j25k25l25m25n26N26n27K27h28EFFS2PPS2FBS2LF2PP2bs3LFB2FB3sp13cur4lxHnS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP3BUF2bs3LFB2FB3sp13cur4lxHnS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB3PP03SLO3LOS2FB3sp12jn3cur3SP14CPOS4NRTa4SP1R2F04lxHn3LJNS1R3HIA1h2LF2sp2PP2bs3LFB3PP03TOP2hc2FB3sp12jn3cur3HTc3SP14CPOS4SP1R2F04lxHn3LJNS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP3CUR2bs3LFB2FB3sp13cur4lxHnFFS1R3HIA2LF2PP2bs3LFB2hc2FB3sp13cur4lxHnFFS1R3HIA1h2LF2sp2PP2lo2bs3LFB3PP03TOP2hc2FB3sp12jn3cur3HTc3SP14CPOS4SP1R2F04lxHn3LJNFFS2LF2PP2bs3LFB2FB3sp13cur4lxHnS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP3CUR2bs3LFB2FB3sp13cur4lxHnS2LF2PP3BUF2bs3LFB2FB3sp13cur4lxHnFFS2LF2PP2bs3LFB2FB3sp13cur4lxHnFFS2LF2PP2bs3LFB2FB3sp13cur4lxHnFS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP2bs3LFB2FB3sp13cur4lxHnFS1R2LF2PP2lo2bs3LFB3LOS2FB3sp13cur4lxHnS1R2LF2PP2lo2bs3LFB3LOS2FB3sp13cur4lxHnS1R2LF2PP2lo2bs3LFB3LOS2FB3sp13cur4lxHnS1R2LF2PP2lo2bs3LFB3LOS2FB3sp12jn3cur4lxHn3LJNS1R2LF2PP2lo2bs3LFB3LOS2FB3sp12jn3cur4lxHn3LJNS1R2LF2PP2lo2bs3LFB3LOS2FB3sp12jn3cur4lxHn3LJNS1R2LF2PP2bs3LFB2FB3sp13cur4lxHnFFS2LF2PP2bs3LFB2FB3sp13cur4lxHnS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP2bs3LFB2FB3sp13cur4lxHnFS2LF2PP2bs3LFB2FB3sp13cur4lxHnS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS2LF3BUF2bs3LFB2FB2jn3APB4lxHn3LJNS2LF2PP3END2lo2bs3LFB2FB3sp12jn1p3APP4lxHn3LJN3x293x173x303x313x325POST0S2LF2PP3END3BUF2lo2bs3LFB2FB3sp12jn1p3APB4lxHn3LJN3x293x173x303x313x325POST0S2LF2PP3BUF2bs3LFB3DPB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn3cur4CFBa4lxHn3LJNS2LF2PP3END2lo2bs3LFB2FB3sp12jn1p3APP4lxHn3LJN3x293x173x303x313x325POST0S2LF2PP2bs3LFB2FB2jn3APP4lxHn3LJNS2LF2PP3END2lo2bs3LFB2FB3sp12jn1p3cur4CFBa4lxHn3LJN3x293x173x303x313x325POST0S2LF2PP3END2lo2bs3LFB2FB3sp12jn1p3APP4lxHn3LJN3x293x173x303x313x325POST0S2LF2PP3END2lo2bs3LFB2FB3sp12jn1p3cur3CPP4lxHn3LJN3x293x173x303x313x325POST0FS2lo3sp1S1R3NS13NA14STKp5STKp02sp3BUF2lo2bs3SLO3sp13SP14NRTa5BUFLOS3END3BUF2bs2B33B471p3PLTFFS2lo3sp1S2LF2PP3END2bs3LFB2FB3sp12jn1p3cur4lxHn3LJN2p13Hp1S2LF2PP1P3END2bs3LFB3PP02FB3sp12jn1p3cur3Hpc4CPOS4SP1R2F04lxHn3LJN2p13H31S2FBFS3BUF2bs2FB3APBFS1R2LF2sp3slo2bs3LFB4SLOS2FB3ALO2F14lxHnS2LF2PP2bs3LFB2FB3sp13cur2F02F84lxHnS2LF2PP2bs3LFB2FB3sp13cur2F02F84lxHnFS1R3HIA1h2sp3TOP3sp13SP1FFS2sp2lo3sp1FSS2LF2sp2PP2bs3LFB2FB3sp12jn3cur3SP14lxHn3LJNS1P3END1p3Hpc2p13Hp1S3sp1S2LF2PP3END2bs3LFB2FB3sp12jn3cur4lxHn3LJN2p12Lw3H31S2PPS2LF2PP2bs3LFB2FB3sp12jn3cur4lxHn3LJNS1R3NS13NA14STKp5STKp02sp2lo3SLO3sp13SP14NRTaS1R3NS13NA14STKp5STKp02sp2lo3SLO2FB3sp13SP14NRTa4FBLOFS2rv3Hrv2NEFFFS2FBFS2FBS2LF2PP2bs3LFB2FB3sp12jn1p3cur4lxHn3LJN2p13H32FS2FBFFS1R3HIA1h2sp2lo3TOP4HTOPFS2LF2sp2PP2bs3LFB2FB3sp12jn3cur3SP14lxHn3LJNS2loSSFS1P3END3BUF2B12B51p3HpcS2FBFFFFSS2PP2FB3APPFFFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS2FBS1R3NS13NA14STKp5STKp02sp2lo3SLO3SPH2FB4NRTa4FBLOS3sp1FS2sp3sp1FFFS2LF2PP2bs3LFB3PP02FB3sp13cur4CPOS4SP1R2F02F84lxHnS2LF2PP2bs3LFB3PP02FB3sp13cur4CPOS4SP1R2F02F84lxHnS1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS4NRTaFFS3END1p3PLTS1R3BUF2lo2bs3LOS3ALO3BCES2FBS2FB2F0S1P3END3BUF2B11p3HpcFSS1R3NS14STKp5STKp02sp2lo3SLO3sp13SP14NRTaS3BUF2bs3B47S1i2HiFS2LF2PP2bs3LFB2FB3sp13cur4lxHn1c2HcS2rv3HrvS1R2lo3LOSS3sp1S1R3NS13NA14STKp5STKp02sp2PP2lo4PPLO3SLO3sp13SP14NRTaFFFS2lo2FB4FBLOSS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnFS2FB2r02F81q1r1H2H02q02H43sp14SP1MFFS2FBFFFS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2FBSFSFS2sp2lo3sp13SP1S1R3NS13NA14STKp5STKp02sp2lo3SLO3LOS3sp13SP13ALO3ACV4NRTa3SPRS2FB2F0FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF2PP2lo2bs3LFB4PPLO3sp12jn4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12jn3SP14NRTa4lxHn3LJNS2LF2lo2bs3LFB3sp12jn3cur3CLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB3sp12jn3SP14NRTa4FBLO4lxHn3LJNFFFS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO2jn4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12jn3SP14NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNFS2LF3BUF2lo2bs3LFB3sp12jn5BUFLO4lxHn3LJNS2LF2lo2bs3LFB2FB3sp12jn4FBLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB2jn4NRTa4FBLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB2jn4NRTa4FBLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNS2LF2PP2lo2bs3LFB4PPLO3sp12jn4lxHn3LJNS2LF2lo2bs3LFB2FB3sp12jn4FBLO4lxHn3LJNS2LF2sp2lo2bs3LFB3sp12jn3SP14lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2FB3sp12jn3SP13ALO4NRTa2F14lxHn3LJNS2LF2lo2bs3LFB2FB3sp12jn4FBLO4lxHn3LJNS2LF2lo2bs3LFB2FB3sp12jn4FBLO4lxHn3LJNS2LF2sp2bs3LFB3sp12jn3SP14lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp3BUF2lo2bs3LFB3SLO3sp12jn3SP14NRTa5BUFLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12jn3SP14NRTa4lxHn3LJNFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO2FB3sp12jn3SP14NRTa4FBLO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp12jn3cur3SP13CLO4NRTa4lxHn3LJNS1R2LF2sp2bs3LFB4lxHnS1R2LF2sp2bs3LFB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2PP2bs3LFB4lxHnS2LF2PP2bs3LFB4lxHnS2LF2PP2bs3LFB2jn4lxHn3LJNS2LF2PP2bs3LFB4lxHnS2LF2bs3LFB2FB2jn4lxHn3LJNFFFFFFFFFS2LF3BUF2bs3LFB4lxHnFS2LF2lo2bs3LFB3sp14lxHnFFFS1R2LF2lo2bs3LFB3LOS2jn3ALO4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp12jn3SP14NRTa4lxHn3LJNS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp12jn3cur3SP13CLO4NRTa4lxHn3LJNS2LF2lo2bs3LFB2jn3cur3CLO4lxHn3LJNS2LF2PP2bs3LFB2jn4lxHn3LJNFS1R3NS13NA14STKp5STKp02LF2sp2PP2lo2bs3LFB4PPLO3SLO3sp12jn3SP14NRTa4lxHn3LJNS2LF2PP2bs3LFB2FB3sp12jn3cur2F02F84lxHn3LJNFFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3sp12jn3SP13ALO4NRTa4lxHn3LJNS2LF3CUR2bs3LFB4lxHnS2LF3CUR2bs3LFB4lxHnS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn4lxHn3LJNFFS1R3HIA1h2LF2bs3LFB4lxHnS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4lxHnS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4lxHnFFFFFFFFFFFFFFFS2LF2bs3LFB2FB2jn4lxHn3LJNFFS2LF2bs3LFB3sp12jn4lxHn3LJNS2LF2sp2bs3LFB3sp12jn3SP14lxHn3LJNFFFFFFFFFFFFS2LF3CUR2bs3LFB4lxHnS2LF3CUR2bs3LFB4lxHnFFFFFS2LF3BUF2bs3LFB4lxHnFFFFFFFS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn4lxHn3LJNS2LF2bs3LFB2FB2jn4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3sp12jn3SP14NRTa4lxHn3LJNS1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOP4lxHnS2LF2lo2bs3LFB4lxHnS2LF2lo2bs3LFB4lxHnS2LF2bs3LFB3cur4lxHnS2LF2bs3LFB3cur4lxHnFFS1R2LF3slo2bs3LFB4SLOS2jn4lxHn3LJNS1R2LF3slo2bs3LFB4SLOS2jn4lxHn3LJNS1R2LF3slo2bs3LFB4SLOS2jn4lxHn3LJNS1R2LF3slo2bs3LFB4SLOS2jn4lxHn3LJNS1R2LF3slo2bs3LFB4SLOS4lxHnFFFFFFFFFS2LF2PP2bs3LFB2jn4lxHn3LJNS2LF2PP2bs3LFB4lxHnS2LF2PP2bs3LFB4lxHnS2LF2PP2bs3LFB4lxHnS1R2LF2bs3LFB3ALO4lxHnS1R2LF2bs3LFB3ALO4lxHnFFFFFFFFS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS3ALO4NRTa4lxHnS1R3NS13NA14STKp5STKp02LF2sp2lo2bs3LFB3SLO3LOS2jn3ALO4NRTa4lxHn3LJNS2LF2sp2lo2bs3LFB3sp12jn3SP14lxHn3LJNFFFFFFFFFFFS2LF2bs3LFB2FB2jn4lxHn3LJNFFFFFFS1R3HIA1h2LF2sp2bs3LFB3TOP3sp12jn3SP14HTOP4lxHn3LJNS1R2LF2lo2bs3LFB3LOS4lxHnS2LF2PP3CUR2bs3LFB4lxHnS1R2LF2bs3LFB4lxHnS1R2LF2bs3LFB4lxHnS1R2LF2bs3LFB4lxHnS2LF2PP2lo2bs3LFB4PPLO2jn4lxHn3LJNFS2LF2bs3LFB3cur4lxHnS2LF2bs3LFB3cur4lxHnFFFS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHnS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2jn4HTOP4lxHn3LJNS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2jn4HTOP4lxHn3LJNS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2jn4HTOP4lxHn3LJNS1R3HIA1h2LF2sp3slo2bs3LFB3TOP2jn4HTOP4lxHn3LJNS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnFFFFFFS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnS2LF2bs3LFB2FB4lxHnFFFFS2LF2bs3LFB3sp12jn4SP1R4lxHn3LJNS2LF2bs3LFB3sp12jn4SP1R4lxHn3LJNS2LF2bs3LFB2FB2jn2F04lxHn3LJNS2LF2bs3LFB2FB2jn2F04lxHn3LJNS2LF2bs3LFB2FB2jn2F04lxHn3LJN". (* [comment removed for export] *)
  #[using="LOS SPH TOP SLO SLOL SLOS DCB CURLO CWC CUR0 DPB B30 B5 B47 B3 B1 BIN HBY PPLO CWP PP0 ALP LFB NRT STKp0 STKp AMS NA1 NS1 IMG"]
  Lemma seg1 : forall (hc : HST asegs R HIA) (Lh : list blk) (FB sp1 : Z) (w0 w1 w2 tl k0 k8 k16 k48 : word) (j64 : list byte) (tg pd ln pv : word) (jn : list byte)
      (p cur : Z) (ctc cpc : word) (clc cpp cnx : Z) (mm : mem)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    sfr hc Lh FB sp1 w0 w1 w2 tl (Z_to_bv 8 248) k0 k8 k16 (Z_to_bv 64 (-9570)) k48 j64 tg pd ln pv jn p cur ctc cpc clc cpp cnx mm ->
    p < END ->
    evtA asegs AL (hcs asegs R HIA hc)
      (fun ms => CALLQ1 hc Lh FB sp1 k0 k8 k16 (Z_to_bv 64 (-9570)) k48 p cur ctc cpc clc cpp cnx mm ms
                 \/ ERRQ hc Lh FB sp1 k0 k8 k16 (Z_to_bv 64 (-9570)) k48 cur ctc cpc clc cpp cnx mm ms)
      (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (-8)) (Z_to_bv 64 END) (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (Z.shiftr PP 3 + al_sb AL)) (Z_to_bv 64 PP) (Z_to_bv 64 (FB + 32))
               (Z_to_bv 64 (FB + 64)) (Z_to_bv 64 cur) (Z_to_bv 64 p) (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) t3 t4 t5 t6)
          F (Z_to_bv 64 0xae6b0) fc None mm (seg_rom asegs)).
  Proof.
  (* [comment removed for export] *)
  intros until t6.
  intros D PLT.
  sfr_open D.
  rt_facts.
  pose proof (hcs_ok asegs R HIA hc) as CSOKc.
  pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HTOP.
  rewrite HTc, HSc in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NRTa STKp0; lia | lx_side_lia ]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 NA1 NRTa STKp0 TOP HTOP; lia | lx_side_lia ]]).
  assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
  assert (SCS1 : crange (hcs asegs R HIA hc) lo (sp1 - lo)) by (eapply crange_sub; [exact SCSc| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  assert (SCS03 : crange (hcs asegs R HIA hc) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCSc| exact SCS0]).
  assert (CFBc : crange (hcs asegs R HIA hc) FB 256) by (eapply crange_mono; [exact HCSc| exact CFB]).
  pose proof (fresh_apart_relist hc LB Lh mm FB 256 FRSH HHc) as FRSHc.
  destruct (frame_factsA R HIA (hcs asegs R HIA hc) hc Lh LF mm FB 256 lo HHc eq_refl FRSHc F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (_ & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
  change (256 / 8) with 32 in SBND, APS.
  pose proof (art_stk_high asegs R HIA) as STKH.
  assert (BINh : In (BUF, n) Lh) by (apply SUBL; exact BIN).
  assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BINh).
  assert (BINA : In (BUF, n) (Lh ++ fdata (LF' FB))) by (apply in_app_iff; left; exact BINh).
  assert (BUFLO : BUF + n <= lo).
    { destruct (blocks_below_hm R HIA hc Lh _ mm Lh HHc ltac:(intros b' Hb; exact Hb) _ BINh) as [_ BCE]. cbn [fst snd] in BCE. clear - BCE ALO LOS. lia. }
  pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
  pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 256 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
  destruct CURF as (CAL & CPOS & CLO & CPP & CBF & CFBa & CWcur & WCC0).
  pose proof CWcur as CWcurc.
  rewrite <- HTc in CWcurc.
  assert (SUBq : forall b', In b' (LB ++ fdata LF) -> In b' (Lh ++ fdata (LF' FB))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBL b' Hb)| right; apply (fdata_cons_sub b' [] FB 256 LF); exact Hb]. }
  assert (CWP1 : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA h) PP 8) by (eapply client_wrange_mono; [exact CWP| exact SUBq]).
  pose proof CWP1 as CWP1c.
  rewrite <- HTc in CWP1c.
  
    pose proof (presW_init_at R HIA hc _ _ Lh LF mm (bv_unsigned sp) (bv_unsigned sp) (Wc cur) hc HHc
    ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(first [ clear - LOS SLO NS1 NA1 NRTa STKp0; lia | lx_side_lia ])) as PRESw.
  assert (WL0 : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  assert (WLw : wlow R Lh LF) by (split; [exact (proj2 (proj2 (proj2 PRESw)))| apply (art_data_lo asegs R HIA)]).
  assert (WCP0 : wcover R LB LF (bv_unsigned sp) X0 PP 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
  assert (WCPw : wcover R Lh LF (bv_unsigned sp) (Wc cur) PP 8) by (apply wcover_inside; cbn [inside A_x509_san_ext_C.Wc]; left; clear; lia).
  unfold A_x509_san_ext_A.FSHb in FSH.
  unfold A_x509_san_ext_A.rsl in RSL.
  assert (P0p : 0 < p) by (clear - Hpc B1 B5; lia). assert (Pp47 : p + 1 < 2^47) by (clear - PLT B3 B47; lia).
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  try lxg_b8u. lx_pre. lx_run_tac (PLAN [0x531fc; 0x67dbc; 0x68258; 0x69484; 0x99724; 0x9a5ec; 0x9afa4; 0xae6b0; 0xae760; 0xae940; 0xaeb08] [(0xae6f8, DJoin); (0xae8a4, DSplit)] 377%N).
  lx_tree.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xae6e8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x68258) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH0 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH0 end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "S1-UNPOISONED" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename TSN2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 64) _ |- _ => rename H into TSN2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => assert (LJN : length jn = 80%nat) by (destruct TSN2 as [[WF _] _]; cbn in WF; exact (proj1 WF)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => apply (u8arr_of_rw_cells asegs) in TSN2 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => assert (OTSN : aobj asegs AL (hcs asegs R HIA hc) m2 (FB + 64) 80); [ change 80 with (8 * Z.of_nat 10); eapply (aobj_of_zero_shadow_sh asegs AL (hcs asegs R HIA hc) m2 FB _ (FB + 64) 8 10 CSOKc FSH0); [ eapply crange_sub; [exact CFBc| clear; lia| clear; lia] | exact F8 | first [ clear - F0; lia | lx_side_lia ] | clear; lia | intros i Hi; do 10 (destruct i as [|i]; [reflexivity| try (exfalso; first [ clear - Hi; lia | lx_side_lia ])]); exfalso; first [ clear - Hi; lia | lx_side_lia ] ] | .. ] | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => assert (CWN : client_wrange L (Lh ++ fdata (LF' FB)) lo (htop asegs R HIA hc) (FB + 64) 80) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => pose proof (artA_amemset asegs R HIA 0x68258) as SPM | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => specialize SPM with (h := hc) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply SPM with (LB := Lh) (LF := LF' FB) (DST := FB + 64) (v := 0) (n := 80) (lo := lo) (ds := jn); rewrite ?(unsigned_lit sp1) by exact SP1R; first [ eassumption | reflexivity | exact OTSN | exact LOS | lazymatch goal with | |- _ = arl_amemset R \/ _ => left; rewrite AMS; reflexivity | |- Z.of_nat (length _) = 80 => rewrite LJN; reflexivity | |- 0 <= 0 < 256 => clear; lia | |- lo <= _ - _ => first [ clear - SLO SP1 NS1 NA1 NRTa STKp0; lia | lx_side_lia ] | |- crange _ lo _ => exact SCS1 | |- FB + 64 + 80 <= lo \/ _ => left; first [ clear - FBLO; lia | lx_side_lia ] | |- 80 = 0 \/ _ => right; first [ clear - FBLO SLO SPH NS1 NA1 NRTa STKp0; lia | lx_side_lia ] | |- 80 < _ => clear; lia | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_sp_mono; [exact LOS| exact CWN] | |- _ <= htop _ _ _ _ => rewrite HTc; first [ clear - SP1 TOP; lia | lx_side_lia ] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1-MS-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "S1-MS-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear SPM; try clear OTSN| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename TSN3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : u8arr _ _ (FB + 64) _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; change (Z.to_nat 80) with 80%nat in H; rename H into TSN3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 (FB + 64) |- _ => subst x end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "S1-MEMSET-DONE" | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xad860: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x531fc; 0x67dbc; 0x68258; 0x69484; 0x99724; 0x9a5ec; 0x9afa4; 0xae6b0; 0xae760; 0xae940; 0xaeb08] [(0xae6f8, DJoin); (0xae8a4, DSplit)] 377%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xae72c) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x99724) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with HHx : HM _ _ _ hc _ _ m3 |- _ => pose proof (hm_abase asegs R HIA hc _ _ m3 HHx) as AB3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "S1-TAGCHK" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename BY3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with B : bytes_at _ ?mx BUF bs |- _ (MS _ _ _ _ _ ?mx _) => rename B into BY3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear RDt| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => idtac "S1-GETLEN-CALL" | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m4 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH4 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH4 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH4 (FB + 32) 1%nat as OTL | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => first [ lazymatch goal with ABx : abase _ _ m4 |- _ => idtac end | lazymatch goal with HHx : HM _ _ _ hc _ _ m4 |- _ => pose proof (hm_abase asegs R HIA hc _ _ m4 HHx) as AB4 end ] | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => pose proof (A_asn1_get_len_spec AL IMG) as GL' | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in GL' | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GL' with (CS := hcs asegs R HIA hc) (PP := PP) (LENP := FB + 32) (P := p + 1) (END := END) (BUF := BUF) (bs := bs) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; first [ eassumption | exact CSOKc | exact (art_alwf asegs R HIA) | exact ALP | exact PP0 | exact B5 | reflexivity | lazymatch goal with | |- BUF <= _ => first [ clear - B1 Hpc; lia | lx_side_lia ] | |- _ <= END => first [ clear - PLT; lia | lx_side_lia ] | |- END <= BUF + _ => exact B3 | |- BUF + _ < 2 ^ 63 => first [ clear - B47; lia | lx_side_lia ] | |- PP + 8 <= FB + 32 \/ _ => first [ clear - APP; lia | lx_side_lia ] | |- _ = 0 \/ PP + 8 <= BUF \/ _ => right; exact DPB | |- _ = 0 \/ FB + 32 + 8 <= BUF \/ _ => right; first [ clear - APB; lia | lx_side_lia ] | |- (FB + 32) mod 8 = 0 => clear - F8; Z.div_mod_to_equations; lia | |- 0 < FB + 32 => first [ clear - F0; lia | lx_side_lia ] | |- lo <= sp1 - 16 => first [ clear - SLO SP1 NS1 NA1 NRTa STKp0; lia | lx_side_lia ] | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia | |- crange _ lo _ => exact SCS1 | |- PP + 8 <= sp1 - 16 \/ _ => left; first [ clear - PPLO SLO SP1 NS1 NA1 NRTa STKp0; lia | lx_side_lia ] | |- FB + 32 + 8 <= sp1 - 16 \/ _ => left; first [ clear - FBLO SLO SP1 NS1 NA1 NRTa STKp0; lia | lx_side_lia ] | |- _ = 0 \/ BUF + _ <= sp1 - 16 \/ _ => right; left; first [ clear - BUFLO SLO SP1 NS1 NA1 NRTa STKp0; lia | lx_side_lia ] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1-GL-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "S1-GL-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear GL'; try clear OTL| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename rv into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hrv into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ < rv <= 0 |- _ => rename H into Hrv end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HL0 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : ?lx_rv = 0 -> _ |- _ => rename H into HL0 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename PP5 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename p1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ PP [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into PP5; rename qq into p1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename TL5 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Lw into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : rw_cells _ _ (FB + 32) [C8 ?lw] |- _ => rename H into TL5; rename lw into Lw end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename Hp1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : _ <= p1 <= END |- _ => rename H into Hp1 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => idtac "S1-GETLEN-DONE" | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xad898: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x531fc; 0x67dbc; 0x68258; 0x69484; 0x99724; 0x9a5ec; 0x9afa4; 0xae6b0; 0xae760; 0xae940; 0xaeb08] [(0xae6f8, DJoin); (0xae8a4, DSplit)] 377%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  all: (cut True; [ intros _ | ]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xae760) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (subst rv) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (HL0 eq_refl) as [Hp1a HLw]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HL0; try clear Krv; try clear Hrv| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "S1-CALLQ") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (left) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold CALLQ1) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists p1) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (do 5 eexists) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists Lw) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hp1a; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - HLw; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [fin_sfr ltac:(first [ clear - Hpc Hp1; lia | lx_side_lia ]) | eassumption]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xad8cc path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xae760) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xad8cc path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xae940) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "S1-GL-ERR") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (right) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold ERRQ) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [first [ clear - Hrv; lia | lx_side_lia ]|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [fin_sfr ltac:(first [ clear - Hpc Hp1; lia | lx_side_lia ]) | eassumption]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xada18 path 1: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xae940) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xada18 path 1: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xae940) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_unpin; idtac | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (subst rv) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (destruct (HL0 eq_refl) as [Hp1a HLw]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HL0; try clear Krv; try clear Hrv| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (idtac "S1-CLASS-ERR") | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (apply evtA_done) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (right) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (unfold ERRQ) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (exists (-9570)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (repeat (lazymatch goal with |- ex _ => eexists end)) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [clear; lia|]) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (split; [fin_sfr ltac:(first [ clear - Hpc Hp1; lia | lx_side_lia ]) | eassumption]) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ _ _ _ _ (seg_rom _)] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: post 0xada18 path 2: side goal left:" g; clear LXM] | |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [MS _ _ (Z_to_bv 64 0xae940) _ _ _ (seg_rom _)] => first [ solve [ lx_leaf ] | idtac "lxw: post 0xada18 path 2: neither the original finishing script nor lx_leaf closed the leaf" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xae760) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xae940) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- True => exact I | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw seg1: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
