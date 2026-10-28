(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0030821bd9a0ddd5 2 95 1 1 8 3 1 1 102 1 103 1 5 0 1 93 1 101 1 104 1 105 8 1 1 8 3 2 1 101 1 104 1 4 0 1 102 1 103 1 105 8P00333c57b394484e 0 2 0 1 5 1P0045b63a0ca4e8ef 1 1 8 2 0 1 99 1 3 30 1 100 1 101 8P0074b5e7f1ac5bb1 1 1 16 3 0 1 92 1 93 1 5 45 1 65 1 91 1 94 1 95 16P01401bffafb394ac 0 2 2 1 4 1P018083776217ce34 2 95 1 1 8 3 1 1 102 1 103 1 5 0 1 93 1 101 1 104 1 105 8 1 1 8 3 2 1 101 1 104 1 4 0 1 102 1 103 1 105 8P02121470ae54ce69 0 2 0 1 5 1P028c38ed212916e5 1 1 16 3 0 1 91 1 92 1 4 44 2 90 2 93 2 94 32P04b2f3025cbf49d0 0 4 0 1 89 1 97 1 98 1P04dcf2b746f484be 1 1 32 3 0 1 90 1 93 1 4 64 1 91 1 92 1 94 32P04f8ff7c5f32afc4 0 5 1 1 3 1 66 1 93 1 94 1P0739a76e43f0b9b2 0 2 0 1 2 1P0799c40c5441d7e2 1 1 32 3 0 1 90 1 93 1 4 64 1 91 1 92 1 94 32P0982704fc8bfa8ff 1 1 32 3 0 1 90 1 93 1 4 64 1 91 1 92 1 94 32P09dac947b6109ca7 1 1 16 3 0 1 83 1 84 1 4 32 2 82 2 85 2 86 32P0b9da8532074c13c 0 4 0 8 51 8 99 8 100 8P0ba411d611750f53 1 1 16 3 0 1 91 1 92 1 5 44 1 64 1 90 1 93 1 94 16P0c33163ea5ac8f7e 0 4 0 64 9 64 90 64 91 64P0d0440102b4ed6ef 0 2 0 1 1 1P0d0ca7a4f075b745 1 2 64 2 0 1 90 1 64 2 65 1 91 1 2 92 1 93 1P0d8ad44ca21a4c60 1 1 8 3 1 1 93 1 94 1 5 2 1 46 1 92 1 95 1 96 8P0db264d8eb90abf8 1 2 64 2 0 1 90 1 64 2 65 1 91 1 2 92 1 93 1P0dcfd7d4e4d5cef9 2 110 2 96 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8 2 96 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8P0dea76d1157d8694 0 4 0 1 89 1 97 1 98 1P0e09a71df87a9fd6 0 5 0 1 1 1 45 1 91 1 92 1P0eafff6c40671f00 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P0f0e41dcdc17dffa 1 1 16 3 0 1 91 1 92 1 4 44 2 90 2 93 2 94 32P10628f104bf155d5 0 6 0 1 63 1 78 1 79 1 90 1 91 1P11496123423150a8 1 1 32 2 16 1 90 1 3 0 1 91 1 92 32P11820b5e0ab39776 0 4 0 1 89 1 97 1 98 1P127587ba72755232 1 1 32 3 0 1 90 1 93 1 4 64 1 91 1 92 1 94 32P149320d5fafc953e 2 96 1 1 8 3 1 1 102 1 103 1 5 0 1 93 1 101 1 104 1 105 8 1 1 8 3 2 1 101 1 104 1 4 0 1 102 1 103 1 105 8P15103d3d7ad89845 2 110 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8P152c398c4fc412b9 0 5 0 1 33 1 74 1 82 1 83 1P153c320592aed818 0 2 0 1 6 1P1555269dda5c58dc 1 1 16 3 0 1 92 1 93 1 4 45 2 91 2 94 2 95 32P1635df200343d680 0 4 1 1 3 1 93 1 94 1P172647ca9da616c5 0 2 2 1 4 1P17f035f690e6aa33 0 2 0 1 5 1P180db98fb7fa8b5e 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P193f812a2e1ab555 1 1 16 3 0 1 92 1 93 1 5 45 1 65 1 91 1 94 1 95 16P19c78b6078e47f3d 1 1 16 3 0 1 92 1 93 1 5 45 1 65 1 91 1 94 1 95 16P19d030208b48c837 1 2 32 3 1 1 91 1 94 1 32 8 46 1 60 1 62 1 79 1 80 1 83 1 92 1 93 1 2 95 2 96 2P1ae77be07350b997 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P1c0b2955b418728b 0 4 0 1 89 1 97 1 98 1P1c30a6275adddbfd 1 1 8 2 0 1 99 1 3 29 1 100 1 101 8P1c3b03c9d80b707b 0 2 0 1 86 1P1c5f239ff2a5bb3f 0 5 0 1 45 1 82 1 90 1 91 1P1da6d2c053f4dd01 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P1dab659c3d3a0d4d 0 6 0 1 63 1 78 1 79 1 90 1 91 1P1e91535d4b939734 0 4 0 1 1 1 91 1 92 1P1f6518f02fa60513 0 5 0 1 45 1 82 1 90 1 91 1P1fcd2d0819e43943 1 1 8 3 1 1 92 1 95 1 4 2 1 93 1 94 1 96 8P1ff383e4a23be375 1 2 64 2 0 1 82 1 64 2 57 1 83 1 2 84 1 85 1P2001594d81cd7b6a 3 100 0 2 1 1 2 1 3 85 0 2 1 1 3 1 0 6 0 1 4 1 49 1 86 1 94 1 95 1 0 5 0 1 3 1 48 1 94 1 95 1 3 85 0 2 1 1 3 1 0 6 0 1 4 1 49 1 86 1 94 1 95 1 0 5 0 1 3 1 48 1 94 1 95 1P206c8be3c4c8e8d4 1 1 8 3 1 1 93 1 94 1 5 2 1 46 1 92 1 95 1 96 8P207edbfb766f2d10 0 4 0 1 89 1 97 1 98 1P20d9c0830e826d58 0 4 1 1 3 1 93 1 94 1P21483eccbb65d59a 2 95 1 1 8 3 1 1 102 1 103 1 5 0 1 93 1 101 1 104 1 105 8 1 1 8 3 2 1 101 1 104 1 4 0 1 102 1 103 1 105 8P2211cd3444b5b9c1 1 1 8 3 0 1 93 1 94 1 5 2 1 84 1 92 1 95 1 96 8P221e319cbd16172e 1 1 32 3 0 1 90 1 93 1 4 64 1 91 1 92 1 94 32P22457fc5fe0a427c 0 2 0 1 1 1P2272c642ff01dcf2 0 2 0 1 83 1P229bbcdc8178e57b 1 1 64 2 57 1 83 1 3 0 1 82 1 84 64P22a71effdb5247df 0 4 0 1 74 1 82 1 83 1P22c2363aae592f0c 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P22fac433ce635d14 0 6 0 1 44 1 75 1 77 1 90 1 91 1P233640b7d8d6c495 0 4 0 1 89 1 97 1 98 1P23e598da4e8015f1 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P245ade5261814cbf 1 1 8 3 1 1 93 1 94 1 4 2 1 92 1 95 1 96 8P246696eba0b8c086 0 4 0 8 51 8 99 8 100 8P256728ee5bf1f41d 0 2 2 1 4 1P25c04438c27ecc85 1 1 16 3 0 1 92 1 93 1 4 45 2 91 2 94 2 95 32P26009e02277516c8 0 4 0 1 89 1 97 1 98 1P267c9643e2f53a50 0 5 0 1 45 1 82 1 90 1 91 1P26dcca663b5830e3 1 1 16 3 0 1 92 1 93 1 5 45 1 65 1 91 1 94 1 95 16P27545b120122e3ba 1 1 64 2 1 1 82 1 3 0 1 83 1 84 64P279da22cd9ce8236 0 6 0 1 44 1 56 1 77 1 90 1 91 1P27bc7cb5abb54f78 0 2 0 1 1 1P28ecc6aa6849a987 0 6 0 32 44 32 90 32 91 32 92 32 93 32P29310bcf918479ec 1 1 8 3 0 1 92 1 95 1 4 2 1 93 1 94 1 96 8P29a7a8c067a749d1 1 1 32 3 0 1 83 1 86 1 4 57 1 84 1 85 1 87 32P29f4d8412fa04352 0 4 0 1 3 1 93 1 94 1P2a1c1908dda0340d 1 1 32 2 0 1 90 1 3 17 1 91 1 92 32P2ad44da755fae267 1 1 8 2 0 1 99 1 3 30 1 100 1 101 8P2af28e9b5dcbd5e9 0 5 0 1 3 1 47 1 93 1 94 1P2b46850a1dcc4782 1 1 8 3 0 1 92 1 95 1 5 2 1 65 1 93 1 94 1 96 8P2bb8d9475dbc535c 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P2bc53ad17bb7d879 0 4 0 1 2 1 94 1 95 1P2c03c8b324329dce 0 4 0 1 89 1 97 1 98 1P2d045926f30c1d2e 1 1 8 3 1 1 93 1 94 1 5 2 1 46 1 92 1 95 1 96 8P2d145b2c76b82ddf 0 5 0 1 45 1 82 1 90 1 91 1P2d89b632f01eaa2a 2 110 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8P2dbfd5c7841d91d7 0 6 0 1 44 1 75 1 77 1 90 1 91 1P2e1a1b235ecbc0b7 0 4 0 1 89 1 97 1 98 1P2e2d5ac74faa5e9b 2 101 2 86 1 1 8 3 3 1 93 1 96 1 6 0 1 48 1 85 1 94 1 95 1 97 8 1 1 8 3 2 1 94 1 95 1 5 0 1 47 1 93 1 96 1 97 8 2 86 1 1 8 3 3 1 93 1 96 1 6 0 1 48 1 85 1 94 1 95 1 97 8 1 1 8 3 2 1 94 1 95 1 5 0 1 47 1 93 1 96 1 97 8P2e3bf00fbcc37d26 1 1 8 3 0 1 94 1 97 1 5 2 4 65 4 95 4 96 4 98 32P2e42d46b797296c2 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P2e47bef52ca7aa6f 0 5 0 1 35 1 89 1 97 1 98 1P2ea2d5662cfe5730 0 4 0 8 51 8 99 8 100 8P2f69891e2de5af60 0 4 0 1 89 1 97 1 98 1P2fe266612b2a9806 2 101 2 87 1 1 8 3 3 1 93 1 96 1 6 0 1 48 1 85 1 94 1 95 1 97 8 1 1 8 3 2 1 94 1 95 1 5 0 1 47 1 93 1 96 1 97 8 2 87 1 1 8 3 3 1 93 1 96 1 6 0 1 48 1 85 1 94 1 95 1 97 8 1 1 8 3 2 1 94 1 95 1 5 0 1 47 1 93 1 96 1 97 8P303f18bcd9c0b2f8 0 2 0 1 85 1P31b302baac7c91e8 1 1 8 2 41 1 91 1 3 0 1 90 1 92 8P31ef79c713985032 0 2 0 1 84 1P3248e454cb10f9aa 0 4 0 1 1 1 91 1 92 1P32bd2e793c1e6c09 0 6 0 1 44 1 56 1 77 1 90 1 91 1P32fd316bcc86ee1a 1 1 8 3 0 1 92 1 95 1 5 2 1 65 1 93 1 94 1 96 8P3347f9815a49ba58 1 1 8 3 1 1 92 1 95 1 5 2 1 65 1 93 1 94 1 96 8P336848f84e7456d2 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P33ab4849ceaaef9c 0 6 0 32 64 32 90 32 91 32 92 32 93 32P3469fb6c589b5949 1 1 8 2 0 1 99 1 3 30 1 100 1 101 8P353cc1527165385b 0 4 0 8 49 8 99 8 100 8P35629c0fa97f9c75 2 110 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8 2 95 1 1 8 3 2 1 102 1 105 1 6 0 1 57 1 94 1 103 1 104 1 106 8 1 1 8 3 3 1 103 1 104 1 5 0 1 56 1 102 1 105 1 106 8P35d3ee1b19fe824e 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P35ea62b256b91295 0 2 0 1 7 1P369de288b0260482 1 1 32 3 0 1 93 1 96 1 4 65 1 94 1 95 1 97 32P372128d749a13d0d 0 2 0 1 87 1P373edd26a9c05633 1 1 16 3 0 1 98 1 99 1 4 34 2 97 2 100 2 101 32P379a9c1eed6b718d 0 7 0 1 60 1 62 1 79 1 80 1 93 1 94 1P37f5648ce8c08368 1 1 16 3 0 1 84 1 85 1 5 33 4 57 4 83 4 86 4 87 64P38aec3121b54a9dd 1 1 8 3 0 1 93 1 94 1 5 2 1 46 1 92 1 95 1 96 8P3b6cfe1e320a7d7e 0 7 0 16 44 16 64 16 90 16 91 16 92 16 93 16P3b84f06c152b6c81 0 5 0 1 1 1 64 1 91 1 92 1P3bb6a0f2ae65ceb8 1 1 32 3 1 1 91 1 94 1 4 65 1 92 1 93 1 95 32P3c3e985de4cafc0c 0 4 0 1 89 1 97 1 98 1P3c96e1fe20b7a39c 1 1 32 3 0 1 91 1 94 1 4 65 1 92 1 93 1 95 32P3ca0066afa68257b 0 4 0 1 3 1 93 1 94 1P3d5f8bebfacf7bcf 1 1 16 3 0 1 92 1 93 1 5 45 1 65 1 91 1 94 1 95 16P3da7aac1d4f5ec52 1 1 16 3 0 1 91 1 92 1 4 44 2 90 2 93 2 94 32P3f1241d42fa4639a 1 1 8 3 1 1 93 1 96 1 4 2 1 92 1 97 1 98 8P3f33d34295739627 0 4 0 1 89 1 97 1 98 1P3fb13447c9de4eb5 0 4 0 1 82 1 90 1 91 1N001d1ff56e02aa15N004848af8960b4c6N005eb74a06649d83N00ad21ae3e6268c3N00de7a741ed43e97N00e9947bc30412ebN011b871475199760N013843c6441d7d2cN01f0bca917c957a5N01fa88ef9da34ea5N021d9bb55e129f6eN02684a8b1326bad8N02b7578ada950666N02c2623e8666314cN034fc22fd96b247fN03cd9bb35321d3d6N03de61182ac4d19eN04324790d7bf7b2bN0530fc202663ea80N05616655f8789923N05e02e8a102ece2bN05ef1a89a51943bfN060465b3e46da27eN061353f2a5aab0ebN0635e630d0a83035N06b56b038672773fN06b849b071806271N06f1f94544cb08b7N074aea09bc64407eN0793252780330d3bN0798c512c48dd67eN079e8a08a4749f67N07e444c0a1c84a15N083fc8895060d772N089141883d2e4a9aN090c985786adb401N091bc7f194daf009N091e359ad18e9334N0a113034e627aa5aN0a628e958dead99fN0a9156d7889b7dd1N0aad0ae7598050edN0ab367b81225dbc4N0acb8bc0d3018827N0b3bb34ce4d83005N0b9e90112f553488N0bb5365e5e516767N0bc633a1c30f4bf8N0c4a8e06471bb4a7N0cb434ef5b4b2981N0cdf574742722ae2N0ce00dc8de576a4eN0d0544374f32ab08N0df482dcb8c4742cN0ee7df7d82aaaf9bN0f7bac5efe051886N0fa8952b2b556a52N0fe3aa0d83502e3bN1044962ceff1c7b2N106b0c22f49d89a0N118d3d9ccba97dbdN120078237146bd15N127cffe4d547bf31N12b67918cd0d7f13N12bc6602723f57e0N12f0363322c9dff8N130b108d47238a92N130f5267ce46a3cfN1351a7ebd64bfedeN144efc9d26242e95N14870719e14695e1N14b6fc4948fe5120N154bb3f7819959d7N157af460047ebceaN158c5a2b5bc04428N15f5589a71a07d3cN16756abd7bace7e0N16921339a6c950cdN173027d510930d19N17f681594de237edN18289ee24fdb0f29N186e509a6f8800f4N190b624893a3c328N1917cee23a2255a7N19b3631b1393d029N1a0178a84676fdcaN1a1e46ee806285afN1a56032fc1a4a537N1a7f92784548a014N1b067bb3bdc97abdN1c032f34e4cf9f71N1c776e4c2c994a20N1c9cc843f8ae3adaN1cc78b9710b4dcb0N1cdfd507006cf178N1d2e9370bc30f543N1db6aa449bd71a2dN1dc359ffaf9d8a8eN1f0cfdfae3116d2aN1f204a75ba3f93caN204399b537824c70N20c74e9bf5524fbeN21281cae39a9fb41N2128e70f246aca09N214227ededca157bN214c3c2f59fe09abN221140f06fc881b4N23a79e4c32424d1fN23cb67200c5be12dN24b6712133c6b5b5N24f18f805b639931N250bb3897c5794e3N2520b13e1ecc2ba3N25371aed8fb15f3aN256662abc285c4d1N25c5886db62ddf3fN2672ae967bda2382N267d725913d60576N26f85232ba3c3eb3N281670327ee08684N289b592954fc2123N293b4e82a01b040dN2972d05240809ec1N29734302ad478225N2a479041be83f819N2a602e69dc3a7c1cN2a7e83f2b97e2f10N2b70f37156817a3eN2bcbad0ac2c3de7dN2be5f3d21017c7faN2be9cb3161a0b02fN2c827b0d3ac7ee94N2d26c0fd668fb0c0N2d4007d20cff3898N2ead071a66c22250N2ec1e82f612356d7N2f092aad74b710d4N2f2fb13ce8970033N2f48214c249547a1N2f862478dc97113bN30b538f6c912cd16N31bc6384af2062a9N3348c84426c66848N3427669e36a94243N3457f277ff156077N345a86f28998c0dbN348001e97b533b93N3538bdc1d70530c1N35820a28b96ac691N35f2fbafe8e2668aN35fac72bfe4709f4N3604a8e615f6fd67N362f7906b7524941N36a89adece2d5843N36f11ee00b0ede56N379671c08fe90611N37d9ee4fa57215ffN383c85d75fb4cc67N39616f1829574d2aN3976560d4e3b0da5N39ae4813c2f99b63N3a2eeadc57fa6999N3a6317e9ee01c8f6N3b162cd09f7e80abN3b2822399ebc29ceN3b6c0f97883e95b9N3c29b89d8509de54N3c9b64aae1dfb3f3N3ce5ed6b7b94737aN3d225d3244c88edeN3d79fe4e32002efcN3f6ecce5b8c8a31fN3fcf0b3e954e1c34N3fdb3e5c8a24138f"%lxh.
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
Ltac2 gd_tbl_A_x509_skid_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "X509_SKID_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "x509_skid_postA"; "stdpp.bitvector.definitions.bv_swrap"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wlow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Walk.fctx"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"].


Definition A_X509_SKID : Z := 0xab2b4.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition X509_SKID_STACK_A : Z := 128.

Definition x509_skid_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SK P END lo slo : Z) (pad : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.O20.O1?.O1>.)Lh',(4.O20.O1?.O1>.)(1.$5.Lr,$5.(1.$5.Lp',$5.(1.(2.&40.)Ltg,(2.&40.)(1.(2.&40.)Lln,(2.&40.)(1.(2.&40.)Lq,(2.&40.)(6.(7.$0.R17.(8.(9.O1:.O19.O18.O17.R16.R15.R14.O16.O15.R13.R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(:.O1:.)O9.(;.(2.&40.))R7.(<.O20.)))(6.(=.O20.O1?.O1>.R6.O1<.O1;.R7.)(6.(7.P,$5.Sp(>.O20.O1?.O1>.R6.)(>.O20.O1?.O1>.O1=.))(6.(7.$5.(?.O20.O1?.O1>.R6.)(?.O20.O1?.O1>.O1=.))(6.(7.$5.(10.O20.O1?.O1>.R6.)(10.O20.O1?.O1>.O1=.))(6.(7.$5.(11.O20.O1?.O1>.R6.)(11.O20.O1?.O1>.O1=.))(6.(7.$5.(12.O20.O1?.O1>.R6.)(12.O20.O1?.O1>.O1=.))(6.(7.$5.(13.O20.O1?.O1>.R6.)(13.O20.O1?.O1>.O1=.))(6.Pmo,$14.(15.(16.O20.O1?.O1>.R7.R1.)(16.O20.O1?.O1>.O1=.R1.))(6.(17.O20.O1?.O1<.O1;.(18.&40.O19.)(18.&40.O19.)(10.O20.O1?.O1>.O1=.)(19.(1:.$5.$5.)(1;.$5.$5.O8.(1<.O8.+8.))(19.(1:.$5.$5.)(1;.$5.$5.O7.(1<.O7.+18.))(1=.(1:.$5.$5.))))O1.R7.)(6.(1>.O20.R7.)(6.(1?.O20.R7.O4.(18.&40.O19.))(6.(20.O20.(21.O1?.)R7.O3.(18.&40.O19.))(6.(7.(2.&40.)R13.(22.&40.R5.))(6.(6.(23.-3000.R5.)(24.R5.=))(6.(25.O20.R7.O8.(19.$26.(27.(22.&40.R4.))(1=.$26.)))(6.(25.O20.R7.O7.(19.$26.(28.R3.)(19.$26.(28.O2.)(19.$26.(27.R2.)(19.$26.(27.R1.)(1=.$26.))))))(6.(24.O6.R4.)(24.R4.O5.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_skid_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "Ph,(4.O4.O3.O2.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$5.PSK,$5.PP,$5.PEND,$5.PBUF,$5.Plo,$5.Pslo,$5.Pbs,(29.(2.&8.))Ptg0,(2.&40.)Ppad,(2.&40.)Pln0,(2.&40.)Pq0,(2.&40.)P,(=.O4.O3.O2.R31.R30.R2?.R=.)P,(2<.(2=.$2:.R30.)#200.)P,(25.O4.R?.R>.(19.$26.(27.(22.&40.R<.))(1=.$26.)))P,(25.O4.R10.R>.(19.$26.(28.R7.)(19.$26.(28.R6.)(19.$26.(27.R5.)(19.$26.(27.R4.)(1=.$26.))))))P,(2>.O4.R11.R<.R9.)P,(24.R=.R?.)P,(24.R10.R?.)P,(24.R10.(1<.R?.(2?.(2=.(2.&8.)R<.))))P,(23.(1<.R10.(2?.(2=.(2.&8.)R=.)))(30.+2.+3?.))P,(31.(24.(1<.R15.+8.)R14.)(24.(1<.R14.+18.)R15.))P,(31.(7.$5.(2?.(2=.(2.&8.)R?.))=)(31.(24.(1<.R16.+8.)R12.)(24.(1<.R12.(2?.(2=.(2.&8.)R?.)))R16.)))P,(31.(7.$5.(2?.(2=.(2.&8.)R10.))=)(31.(24.(1<.R16.+18.)R13.)(24.(1<.R13.(2?.(2=.(2.&8.)R10.)))R16.)))P,(7.$5.(32.R18.+8.)=)P,(7.$5.(32.R18.+8.)=)P,(6.(23.=R1:.)(24.(1<.R1:.+8.)(30.+2.+40.)))P,(6.(23.=R1:.)(24.(1<.R1:.+18.)(30.+2.+40.)))P,(23.=R18.)P,(1?.O4.R1>.R18.(18.&40.R3>.))P,(20.O4.(21.O3.)R1?.R18.(18.&40.R3?.))P,(24.R1:.(33.(18.&40.R40.)$34.))P,(24.R1;.(33.(33.(18.&40.R41.)+70.)(35.O3.)))P,(24.=(35.O3.))P,(24.(36.O3.)R1<.)P,(24.R1=.R1>.)P,(7.$5.(32.(18.&40.R45.)+10.)=)P,(24.(18.&40.R46.)(?.O4.O3.O2.R4:.))P,(24.(18.&40.R47.)(30.+2.+2?.))P,(31.(24.(1<.R27.+8.)R22.)(24.(18.&40.R48.)R27.))P,(31.(24.(1<.R27.+18.)R23.)(24.(18.&40.R49.)R27.))P,(31.(7.$5.(2?.(2=.(2.&8.)R22.))=)(31.(24.(1<.R25.(2?.(2=.(2.&8.)R22.)))R24.)(24.(18.&40.R4:.)R25.)))P,(37.(38.O3.)(39.$2:.R4>.(3:.R4=.))R25.R2:.+8.)P,(37.(38.O3.)(39.$2:.R4?.(3:.R4>.))R26.R2:.+18.)P,(37.(38.O3.)(39.$2:.R50.(3:.R4?.))R27.R28.(2?.(2=.(2.&8.)R25.)))P,(3;.(38.O3.)(39.$2:.R51.(3:.R50.))R28.(?.O4.O3.O2.R52.)R2=.+8.)P,(3;.(38.O3.)(39.$2:.R52.(3:.R51.))R29.(?.O4.O3.O2.R53.)R2=.+18.)P,(1>.O4.R30.)P,(7.(2.&40.)R4?.(22.&40.(3<.O3.)))P,(3=.O4.(21.O3.)(>.O4.O3.O2.R56.)R32.R31.+8.)P,(3=.O4.(21.O3.)(>.O4.O3.O2.R57.)R33.R31.+18.)P,(3=.O4.(21.O3.)(>.O4.O3.O2.R58.)R34.R2?.(2?.(2=.(2.&8.)R2<.)))P,(7.(2.&40.)R4=.(22.&40.R34.))P,(7.(2.&40.)R4=.(22.&40.R32.))P,(7.(2.&40.)R4=.(22.&40.R35.))(3>.O4.(21.O3.)(>.O4.O3.O2.R5<.)(3?.O4.O3.O2.R5<.R5;.R5:.R59.R58.R57.R56.R52.R51.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3:.R39.R37.R36.R35.R34.R32.R31.R2>.R38.)(8.(9.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.)R3:.(22.&40.O1.)R39.(;.(2.&40.))R38.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP SK P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SK \/ SK + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ SK + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SK.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SK mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SKB : 0 < SK /\ SK + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_SKID_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SK + 24 <= lo \/ bv_unsigned sp <= SK.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo SK 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SK 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_SKID_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_skid_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SK P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (SK, SK + 24)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation FSHL := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

  (* [comment removed for export] *)
  Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "Pr,$5.Pc,$5.P,(6.(23.-10000.R2.)(24.R2.=))P,(6.(24.(33.(30.+2.+40.)+10000.)R2.)(23.R2.(30.+2.+40.)))(7.$5.(40.&20.(1<.(32.R4.+10000000000000000.)R3.))(1<.R4.(33.R3.(30.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  (* [comment removed for export] *)
  Definition fctx (FB sp1 : Z) (h1 : HST asegs R HIA) (m0 mm : mem) (w0 w1 w2 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "(6.(=.$41.VR,VHIA,O6.VLB,(19.(1:.$5.$5.)(1;.$5.$5.O8.+40.)VLF,)O4.)(6.(7.P,$5.Sp(>.$41.VR,VHIA,O6.)(>.$41.VR,VHIA,Vh,))(6.(7.$5.(?.$41.VR,VHIA,O6.)(?.$41.VR,VHIA,Vh,))(6.(7.$5.(10.$41.VR,VHIA,O6.)(10.$41.VR,VHIA,Vh,))(6.Pmo,$14.(15.(16.$41.VR,VHIA,O6.R1.)(16.$41.VR,VHIA,Vh,R1.))(6.(7.$5.(11.$41.VR,VHIA,O6.)(11.$41.VR,VHIA,Vh,))(6.(7.$5.(12.$41.VR,VHIA,O6.)(12.$41.VR,VHIA,Vh,))(6.(7.$5.(13.$41.VR,VHIA,O6.)(13.$41.VR,VHIA,Vh,))(6.(6.(24.(33.(18.&40.Vsp,)+70.)O7.)(24.O7.(33.(18.&40.Vsp,)+60.)))(6.(7.$5.(32.O7.+20.)=)(6.(25.$41.O4.O8.(19.$26.(27.O3.)(19.$26.(27.O2.)(19.$26.(27.O1.)(1=.$26.)))))(6.(25.$41.O4.(1<.(42.O8.+3.)(43.(21.VR,)))(19.$26.(44.(22.&8.+?1.))(19.$26.(44.(22.&8.+?1.))(19.$26.(44.(22.&8.+?1.))(19.$26.(44.(22.&8.+?1.))(19.$26.(44.(22.&8.=))(19.$26.(44.(22.&8.+?3.))(19.$26.(44.(22.&8.+?3.))(19.$26.(44.(22.&8.+?3.))(1=.$26.))))))))))(6.(45.(>.$41.VR,VHIA,Vh,)O8.+40.)(6.(7.$5.(32.O8.+20.)=)(6.(23.=O8.)(6.(24.(1<.O8.+40.)O7.)(6.(3;.(38.VR,)(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.O8.+40.)VLF,)))(36.VR,)(?.$41.VR,VHIA,Vh,)O8.+18.)(6.(3;.(38.VR,)(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.O8.+40.)VLF,)))(36.VR,)(?.$41.VR,VHIA,Vh,)(1<.O8.+20.)+18.)(6.Px,$5.P,(6.(24.O8.R1.)(23.R1.(1<.O8.+40.)))(31.(6.(24.(36.VR,)R2.)(23.R2.(?.$41.VR,VHIA,Vh,)))(46.(19.(1:.$5.$5.)(1;.$5.$5.O8.+40.)VLF,)R2.))(6.Pb,$2:.P,(47.$2:.R1.(39.$2:.VLB,(3:.VLF,)))(47.$2:.R2.(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.O8.+40.)VLF,))))(6.(31.(24.(1<.O8.+40.)VPP,)(24.(1<.VPP,+8.)O8.))(6.(31.(24.(1<.O8.+40.)VSK,)(24.(1<.VSK,+18.)O8.))(6.(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.O8.+40.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))O8.)))(6.(1?.$41.O4.Vlo,O7.)(6.(24.Vlo,(33.O7.+10.))(6.(24.(1<.O8.+40.)(36.VR,))(6.(1?.$41.O4.O7.(1<.(18.&40.Vsp,)-58.))(6.(25.$41.O4.(1<.(18.&40.Vsp,)-58.)(19.$26.(27.Vs9,)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.)))))))))))))(6.(2>.$41.O4.VBUF,Vbs,)(6.(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)O4.VPP,+8.)(6.(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)O4.VSK,+18.)(6.(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)O4.VBUF,(2?.(2=.(2.&8.)Vbs,)))(6.(1>.$41.O4.)(6.(48.$41.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSK,(1<.VSK,+18.))(1=.(1:.$5.$5.))))O5.O4.)(6.(49.VR,VLB,VLF,)(6.(4:.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSK,(1<.VSK,+18.))(1=.(1:.$5.$5.))))O8.+40.)(6.(4;.VR,VLB,VLF,(18.&40.Vsp,)(10.$41.VR,VHIA,Vh,)O8.+40.)(6.(20.$41.(21.VR,)O4.Vslo,O7.)(6.(20.$41.(21.VR,)O4.O7.(18.&40.Vsp,))(6.(4<.VR,VLB,VLF,O8.+40.)(7.$5.(32.O8.+40.)=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac fctx_open D :=
    destruct D as (HH & ECS & ETOP & ESTK & HKI & EFLAG & EVOL & EFR & SP1 & SP1M & FH & FSH & CFB & FBAL & FB0 & FBS1
                   & FWH & FWD & FWS & SUBLF & AP1 & AP2 & AP4 & ST1 & SLO16 & SEPF & STK2 & SPILL & HBUF & OPP & OSK & OBUF & MI & PRES & WL & WCF & SFF
                   & SS1 & SS2 & FRSH & F64).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  (* [comment removed for export] *)
  Ltac fctx_build :=
    lazymatch goal with |- fctx _ _ _ _ _ _ _ _ => idtac end;
    unfold fctx; spine; first [ eassumption | match goal with |- ?g => idtac "FCTX-LEFT:" g end ].

  Ltac fin_postA PRES :=
    apply evtA_done; unfold x509_skid_postA;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    [ lazymatch goal with |- HM _ _ _ _ _ _ _ => eassumption end | ..];
    (lazymatch goal with
     | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
     | _ => idtac end);
    (lazymatch goal with
     | |- presA _ _ _ _ _ _ _ _ _ _ => eapply presW_presA; exact PRES
     | |- rw_cells _ _ _ _ => idtac
     | |- forall mo, HK _ _ _ _ mo <-> _ =>
         first [ assumption
               | let mo' := fresh "mo" in intros mo';
                 repeat (eapply iff_trans; [ match goal with H : forall mo, HK _ _ _ _ mo <-> _ |- _ => apply H end | ]);
                 apply iff_refl ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01_0@D10592386202.167D10651570095.164D14207581283.164D19504369718.165D2457697676.167 D32458983511.167D32604263317.168D3375868588.166 D37713024309.165D45717324573.166D46805315402.164D50132923712.167D52070850065.165D53314967871.167D60098777666.165D60098975310.164D60109265000.167D60109265003.166D62011770188.166D62011770190.168D62011770191.167D62022258533.165D62022716265.164D6912107242.166 L16277805103.2  L16578761643.1  L1685717371.0   L17605293693.148L18376345509.223L19546883928.148L20630677035.202L21224591641.198L22372406257.202L28641830579.2  L30218446521.222L30469992692.202L31168734358.142L39076636629.0  L39332637397.0  L40027115473.5  L40100639701.0  L42411609006.0  L43202358961.150L4472687353.152 L48119718063.143L50542531495.2  L50790731766.8  L51878069071.2  L52511154273.3  L55715474836.2  L57570196295.2  L61490559858.202L62018535662.1  L66232301891.3  L66571867724.8  L67028235242.10 L6912107233.142 L9877309020.8   P55705235216.213P57577290179.214Q10523111605.175Q10592386192.174Q10651763882.178Q10651763890.171Q12658527488.180Q14681873513.175Q23218748853.174Q23925414032.182Q23927511196.175Q26030354684.212Q26032252593.185Q31168734358.176Q31168734363.173Q31170831512.181Q32681887705.175Q33194651973.180Q33423269192.212Q34964698202.212Q34966725143.185Q35653441506.163Q36117321936.171Q37700443935.179Q37702541083.172Q38250992819.183Q4110986150.211 Q42439443119.212Q42441479395.187Q4279611329.212 Q43878048879.183Q4587995481.212 Q46805771343.178Q46805771351.171Q47230721776.175Q50165000279.172Q52064556095.172Q52066653243.179Q5935758158.212 Q59865321072.212Q59867617340.187Q60109315147.163Q60740903729.171Q62009673032.182Q62011770180.175Q64133651577.212Q65169306126.172Q6910010095.181 Q6912107233.176 Q6912107244.173 Q7917062806.175 Q8699115497.212 Q8701272485.187 00000D00X00Y00Z00[00o01L01M01a02502I02]03103203O03l04I04f05<05R05h06>06T06h06i06m06n08308N09S09d0:=0:N0:O0:c0:l0;30;40;50;J0;K0;L0;_0<:0<R0<S0<d0<e0<f0<g0<h0=10=40=50=F0=_0=f0>B0>C0>D0>M0>T0>[0>b0>j0>k0?20?>0?V0?i0@70@>0@E0@L0@M0@U0@a0A70AH0Ac0Ad0Ak0B20B90BB0BV0Be0Bn0C80CD0CK0CR0C\0Cf0Cm0D40D=0D>0D?0DL0DV0D\0Db0Dk0Dl0E30E:0EA0EO0F80F\S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1FFFS2sp2PP2SK2bs2FB3sp1S1R3HIA2sp2PP2SK2bs2FB3sp12h1FS2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1FS1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1FS2FBSS1R2sp2PP2SK2lo2bs3PPB3SKB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRS2sp2PP2SK2lo2bs3SLO2FB3sp1S1R2sp2PP2SK2lo2bs3PPB3SKB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRS1P3END2bs2p'3PPES2sp2PP2SK2bs2FB3sp11p2PBS1P3END2bs2p'3PPEFS2sp2PP2SK2bs2FB3sp1S2bs1r2RRS2bs2FBSSS2sp2lo3sp13SP15SLO16SSS2sp2bs2FB3sp14FBS1S1R3slo2bs4SLOS2FB3sp14SEPFS1R2sp2lo2bs3SLO3LOS3ALOFS1R2sp2lo3SLO3LOSFFFFS2bs1r2RRS1RFS1R2sp2lo3SLO3LOSS1R2sp2lo3SLO3LOS3sp13SP1S2bs2FBS2sp2lo3slo3SLO4SLOL3sp13SP1FFS1R2sp2bsS2bs2FBS2PP2bsS2PP2bsS3BUF2bsFS2bs2FBS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2sp2lo2bs3sp11p2PBS2sp2lo2bs3sp1S2bs2FBS2bs2FBS2bs2FBFS3BUF2bsS2bs2FB1p2PBS2lo2bs3sp15SLO161p2PBS2lo2bs3sp15SLO16S1R3HIA1h2sp2lo2bs3TOP4HTOPFS2SK2bsS2SK2bsS2lo2bsS2bs1p2PBS1R3slo2bs4SLOS1p2PBS1R3slo2bs4SLOSS2bs1p2PBS2sp2lo2bsS2bs2FB1p2PBS2PP2bsS2PP2bsS1R2bs3ALOS2PP2SK2bsS2SK2bsS2SK2bsS2bs1p2PBFFS1R2lo2bs3LOSS2PP2SK2bsS1R2bsS1R2bsS2bs1p2PBFS2bs2FBS2bs2FBS2bs2FBS1R2bs2FB4SEPFS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP1p2PBS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$41.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps9v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pj0,(2.&40.)Pr,$5.Pp',$5.Ptg,(2.&40.)Pln,(2.&40.)Pq,(2.&40.)Pxq24,(2.&40.)P,(7.(2.&40.)R1.(22.&40.(1<.(42.R23.+3.)(43.(21.VR,)))))P,(4=.R24.R23.R22.R21.R20.R1?.R1>.R1=.)P,(25.$41.R21.R24.(19.$26.(27.R9.)(1=.$26.)))P,(25.$41.R22.VPP,(19.$26.(27.(22.&40.R8.))(1=.$26.)))P,(25.$41.R23.VSK,(19.$26.(28.R8.)(19.$26.(28.Vpad,)(19.$26.(27.R7.)(19.$26.(27.R6.)(1=.$26.))))))P,(6.(24.VP,R:.)(24.R:.VEND,))P,(6.(23.-3000.R<.)(24.R<.=))(3>.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)(3?.$41.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSK,VP,VEND,Vlo,Vslo,Vpad,R27.)(8.(9.R22.(22.&40.R29.)Vgp,Vtp,R21.R20.R1?.Vsp,(22.&40.R29.)(22.&40.R=.)R1>.R1=.R1<.R1;.R1:.R19.R18.(22.&40.R2:.)R17.R16.R15.R14.(22.&40.R2:.)R8.R13.Vs10,Vs11,R12.R11.R10.R?.)VF,(22.&40.+:;498.)Vfc,(;.(2.&40.))R26.(<.$41.)))")
(* [comment removed for export] *).
  Proof.
  intros until q. intros xq24 ->.
  intros D SLOT0 HPP HSK PPE RR.
  fctx_open D.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xab4d4] [] 177%N). lx_tree.
  lxr_leaf. lx_carry.
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH5 end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h1 LB _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h1 LB ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
  as (p & h2 & ROp & [old Hold] & CRp & NCp & NSp & HM2 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff2).
  replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ _ _ p PP 8 NCp CR1 SUB' LOS ltac:(clear; lia)) as NP1.
  pose proof (nc_apart _ _ _ _ _ p SK 24 NCp CR2 SUB' LOS ltac:(clear; lia)) as NP2.
  pose proof (nc_apart0 _ _ _ _ _ p BUF _ NCp CR4 SUB' LOS) as NP4.
  assert (NP5 : bv_unsigned sp + -88 + 88 <= p \/ p + 1 <= bv_unsigned sp + -88).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 8 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp : wcover R LB LF (bv_unsigned sp) W p 1)
  by (eapply wcover_nc; [exact NCp| exact SUB'| clear - LOS SLO; lia]).
  rewrite ECS in CRp.
  clear HHe NCp NSp.
  (* [comment removed for export] *)
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM2.
  rewrite Z.eqb_refl in HM2.
  try (match goal with H : stk _ mf sp1 (bv_unsigned sp + -88) |- _ =>
        pose proof (stk_merge asegs mf lo sp1 _ ST1 H ltac:(clear - SP1 SLO16; lia)) as ST3; clear ST1 H end).
  try (match goal with H : rw_cells _ mf (bv_unsigned sp + -88) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
  assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)) by (eapply sshad_merge; [exact SS1| exact SS2| clear - SP1 SLOL SLO SLO16; lia]).
  lxr_stk_join. fin_postA PRES.
  all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@D10592386202.168D10647554354.165D14203009790.165D19504369718.166D2457697676.168 D32458983511.168D32604263317.169D3375868588.167 D37713024309.166D45717324573.167D46801529303.165D50132923712.168D52070850065.166D53314967871.168D60098777666.166D60103020755.165D60109265000.168D60109265003.167D62011770188.167D62011770190.169D62011770191.168D62018113012.165D62022258533.166D6912107242.167 L17605293693.144L19546883928.144L23685514925.182L27244818784.184L31168734358.138L31567655465.182L34866092019.237L34866092019.239L37660087412.184L38812005576.182L42606203780.184L43202358961.146L4472687353.148 L48119718063.139L66556016456.182L6912107233.138 Q10523111605.176Q10592386192.175Q10651763882.179Q10651763890.172Q12658527488.181Q14681873513.176Q23218748853.175Q23925414032.183Q23927511196.176Q26032252593.186Q31168734358.177Q31168734363.174Q31170831512.182Q32681887705.176Q33194651973.181Q34966725143.186Q35653441506.162Q36117321936.172Q37700443935.180Q37702541083.173Q38250992819.184Q42441479395.188Q43878048879.184Q46805771343.179Q46805771351.172Q47230721776.176Q50165000279.173Q52064556095.173Q52066653243.180Q59867617340.188Q60109315147.162Q60740903729.172Q62009673032.183Q62011770180.176Q65169306126.173Q6910010095.182 Q6912107233.177 Q6912107244.174 Q7917062806.176 Q8701272485.188 00000D00X00Y00Z00[00o01L01M01a02502I02]03103203O03l04I04f05<05R05h06>06T06h07m09209S0:a0:h0;G0;[0;o0<U0=10=E0=X0>30>K0>g0>n0?70?>0?E0?L0?T0?U0?\0?h0@@0@N0@U0@\0@c0@d0@l0A=0AX0AY0A`0Ag0An0B=0BG0BN0BU0B_0Bi0C00C70C80CE0CO0CU0C[0C\0Cc0Cj0D10D?0DcS2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1FFFS2sp2PP2SK2bs2FB3sp1S1R3HIA2sp2PP2SK2bs2FB3sp12h1FS2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1FS1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2lo2bs3LOS2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S1R2sp2PP2SK2lo2bs3PPB3SKB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRS1R2sp2PP2SK2lo2bs3PPB3SKB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRS2sp2PP2SK3END2bs2FB3sp14lxv03H27S1R2sp2PP2SK1P2lo2bs3PPB3SKB3LOS2FB3sp13FB05SLO163ALO3SPR2H04lxv04lxv13H253H27S2bs2FBS2sp2PP2SK1P2bs2FB3sp14lxv03H28S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK2bs2FB3sp1S2sp2PP2SK3END2bs2FB3sp14lxv04lxv13H26S2sp2PP2SK2bs2FB3sp13lxv3H30S2sp2PP2SK2bs2FB3sp1S2sp2bs2FB3sp14FBS1S1R3slo2bs4SLOS2FB3sp14SEPFS1R2sp2lo2bs3SLO3LOS3ALOS2sp2PP2SK2bs2FB3sp13lxv3H22S2bs2FBS1R2sp2bsS2bs2FBS2PP2bsS2PP2bsS3BUF2bsFS2bs2FBS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2sp2lo2bs3sp1S2bs2FBS2bs2FBS2bs2FBFS3BUF2bsS2lo2bs3sp15SLO16S1R3HIA1h2sp2lo2bs3TOP4HTOPFS2SK2bsS2SK2bsS2lo2bsS1R3slo2bs4SLOSS2sp2lo2bsS2PP2bsS2PP2bsS1R2bs3ALOS2PP2SK2bsS2SK2bsS2SK2bsFS1R2lo2bs3LOSS2PP2SK2bsS1R2bsS1R2bsFS2bs2FBS2bs2FBS2bs2FBS1R2bs2FB4SEPFS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP". (* [comment removed for export] *)
  Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_skid_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$41.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Ps6v,(2.&40.)Ps8v,(2.&40.)Pjunk1,(29.(2.&8.))Pjunk2,(29.(2.&8.))Pj3,(29.(2.&8.))Pj4,(29.(2.&8.))Plw0,(2.&40.)Pj0,(2.&40.)Ptg0,(2.&40.)Pln0,(2.&40.)Pq0,(2.&40.)P,(=.$41.VR,VHIA,R1=.VLB,(19.(1:.$5.$5.)(1;.$5.$5.R1?.+40.)VLF,)R1;.)P,(7.P,$5.Sp(>.$41.VR,VHIA,R1>.)(>.$41.VR,VHIA,Vh,))P,(7.$5.(?.$41.VR,VHIA,R1?.)(?.$41.VR,VHIA,Vh,))P,(7.$5.(10.$41.VR,VHIA,R20.)(10.$41.VR,VHIA,Vh,))P,Pmo,$14.(15.(16.$41.VR,VHIA,R22.R1.)(16.$41.VR,VHIA,Vh,R1.))P,(7.$5.(11.$41.VR,VHIA,R22.)(11.$41.VR,VHIA,Vh,))P,(7.$5.(12.$41.VR,VHIA,R23.)(12.$41.VR,VHIA,Vh,))P,(7.$5.(13.$41.VR,VHIA,R24.)(13.$41.VR,VHIA,Vh,))P,(6.(24.(33.(18.&40.Vsp,)+70.)R26.)(24.R26.(33.(18.&40.Vsp,)+60.)))P,(7.$5.(32.R27.+20.)=)P,(25.$41.R25.R29.(19.$26.(4>.#18.R13.)(1=.$26.)))P,(25.$41.R26.(1<.R2:.+18.)(19.$26.(4>.#8.R12.)(1=.$26.)))P,(25.$41.R27.(1<.R2;.+20.)(19.$26.(27.R11.)(1=.$26.)))P,(25.$41.R28.(1<.R2<.+28.)(19.$26.(4>.#10.R15.)(1=.$26.)))P,(25.$41.R29.(1<.R2=.+38.)(19.$26.(4>.#8.R14.)(1=.$26.)))P,(25.$41.R2:.(1<.(42.R2>.+3.)(43.(21.VR,)))(4?.#8.))P,(45.(>.$41.VR,VHIA,Vh,)R2?.+40.)P,(7.$5.(32.R30.+20.)=)P,(23.=R31.)P,(24.(1<.R32.+40.)R31.)P,(3;.(38.VR,)(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.R33.+40.)VLF,)))(36.VR,)(?.$41.VR,VHIA,Vh,)R33.+18.)P,(3;.(38.VR,)(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.R34.+40.)VLF,)))(36.VR,)(?.$41.VR,VHIA,Vh,)(1<.R34.+20.)+18.)P,Px,$5.P,(6.(24.R36.R1.)(23.R1.(1<.R36.+40.)))(31.(6.(24.(36.VR,)R2.)(23.R2.(?.$41.VR,VHIA,Vh,)))(46.(19.(1:.$5.$5.)(1;.$5.$5.R37.+40.)VLF,)R2.))P,Pb,$2:.P,(47.$2:.R1.(39.$2:.VLB,(3:.VLF,)))(47.$2:.R2.(39.$2:.VLB,(3:.(19.(1:.$5.$5.)(1;.$5.$5.R38.+40.)VLF,))))P,(31.(24.(1<.R37.+40.)VPP,)(24.(1<.VPP,+8.)R37.))P,(31.(24.(1<.R38.+40.)VSK,)(24.(1<.VSK,+18.)R38.))P,(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.R39.+40.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))R39.)))P,(1?.$41.R36.Vlo,R39.)P,(24.Vlo,(33.R3:.+10.))P,(24.(1<.R3<.+40.)(36.VR,))P,(1?.$41.R39.R3<.(1<.(18.&40.Vsp,)-58.))P,(25.$41.R3:.R3=.(19.$26.(27.R23.)(1=.$26.)))P,(25.$41.R3;.(1<.(18.&40.Vsp,)-58.)(19.$26.(27.Vs9,)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.)))))))))))))P,(25.$41.R3<.VPP,(19.$26.(27.(22.&40.VP,))(1=.$26.)))P,(25.$41.R3=.VSK,(19.$26.(28.R25.)(19.$26.(28.Vpad,)(19.$26.(27.R24.)(19.$26.(27.R23.)(1=.$26.))))))P,(2>.$41.R3>.VBUF,Vbs,)P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R3?.VPP,+8.)P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R40.VSK,+18.)P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R41.VBUF,(2?.(2=.(2.&8.)Vbs,)))P,(1>.$41.R42.)P,(48.$41.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSK,(1<.VSK,+18.))(1=.(1:.$5.$5.))))R44.R43.)P,(49.VR,VLB,VLF,)P,(4:.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSK,(1<.VSK,+18.))(1=.(1:.$5.$5.))))R49.+40.)P,(4;.VR,VLB,VLF,(18.&40.Vsp,)(10.$41.VR,VHIA,Vh,)R4:.+40.)P,(20.$41.(21.VR,)R47.Vslo,R4:.)P,(20.$41.(21.VR,)R48.R4;.(18.&40.Vsp,))P,(4<.VR,VLB,VLF,R4=.+40.)P,(7.$5.(32.R4>.+40.)=)(3>.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)(3?.$41.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSK,VP,VEND,Vlo,Vslo,Vpad,R4<.)(8.(9.(22.&40.+:;324.)(22.&40.R4>.)Vgp,Vtp,R4:.R49.R48.Vsp,(22.&40.R4>.)R47.R46.R45.R44.R43.R42.R41.R40.(22.&40.R4?.)(22.&40.VEND,)(22.&40.VPP,)(22.&40.VSK,)R3;.(22.&40.R4?.)R3:.(22.&40.(43.(21.VR,)))Vs10,Vs11,R3?.R3>.R3=.R3<.)VF,(22.&40.+:;35<.)Vfc,(;.(2.&40.))R4;.(<.$41.)))")
(* [comment removed for export] *).
  Proof.
  intros until q0.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 HL FD2 G2 FSH CFB FBAL FB0 FBS1 FWH FWD FWS SUBLF AP1 AP2 AP4
  ST1 SLO16 SEPF STK2 SLOT0 SPILL HPP HSK HBUF OPP OSK OBUF MI PRES WL WCF SFF SS1 SS2 FRSH F64.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  cbn [zcells] in FSH.
  pose proof (sums_asn1G_ok AL IMG) as LXSUMS.
  (* [comment removed for export] *)
  lxr_path. lxr_abase. lxr_pose.
  lx_pre. lx_run_tac (PLANS [0xab498] [(0xab41c, DJoin); (0xab488, DSplit)] 177%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA]). lx_tree.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xab498) _ _ _ (seg_rom _)] => lxr_leaf; lx_apply epi_walk | |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx BODY: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
