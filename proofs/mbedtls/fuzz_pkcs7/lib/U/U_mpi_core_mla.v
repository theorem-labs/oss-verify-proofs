(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0027979f03a87ee4 0 3 0 1 62 1 66 1P004257bc7c40c3a6 0 2 0 1 76 1P0058d319bb777504 0 5 0 4 5 4 13 16 20 16 32 16P005ac0c83ce5517f 1 1 8 1 0 1 2 60 1 78 1P00736c52c081e230 0 3 0 1 2 1 38 1P00e1ca1b9f1162cf 0 2 0 1 2 1P0113f26c473af303 2 69 0 4 0 1 3 1 67 32 79 4 0 6 0 1 2 1 52 4 59 4 66 32 77 4P01148a895aec9bb3 0 2 0 1 88 1P011eddbd082fea98 0 3 0 1 11 1 12 1P015e1326e2a1ebfa 2 38 0 6 0 1 1 1 15 4 22 4 29 4 39 1 0 3 0 1 2 1 30 4P0161bcbd9652cb35 0 3 0 1 15 1 38 1P018f245f49032915 0 2 0 1 42 1P01ac1ab5288a4662 0 6 0 8 53 8 60 8 67 64 72 8 78 8P01b913cf43337cde 1 1 4 1 0 1 2 26 1 42 1P01db9462ea77e2ee 0 2 0 1 54 1P01dba3dc8e058377 0 6 0 32 54 32 58 128 65 128 84 128 87 128P022117a4f2a062fb 2 32 0 6 0 4 3 4 30 4 31 4 34 4 37 16 0 4 0 1 2 1 30 1 31 1P0226569a2bc9b228 0 3 0 8 83 8 85 8P022d54349a1129ab 1 1 32 1 0 1 2 56 1 74 1P0245f835133f4650 0 3 0 1 2 1 62 1P024d2ae1ae609823 0 3 0 1 2 1 82 1P025590bf77291cc4 0 2 0 1 46 1P028b51e4a66380a3 0 2 0 1 1 1P02c5ca8563fb1902 0 2 0 1 86 1P02d1ae60b86543dd 0 2 0 1 82 1P02dbb50b071fa9a2 1 1 4 1 0 1 6 10 8 17 8 25 64 36 8 39 8 44 8P02ecdbc47e2863dc 0 2 0 1 40 1P02fa5e0b9c8cb11d 0 2 0 1 5 1P034923f3fc9c9df0 0 2 0 1 54 1P034e19ea04545c04 0 2 0 1 1 1P035922aadda886b9 0 2 0 1 28 1P035f108a5ee96b60 1 1 4 1 0 1 6 47 8 54 8 61 64 66 8 72 8 80 8P039eba233c98aaf6 0 3 0 1 4 1 18 1P03a3e78287daf103 0 2 0 1 45 1P03eab0c2d57878ed 1 1 4 1 0 1 4 25 8 39 64 50 8 58 8P03f3cf687498777d 0 2 0 1 13 1P043190a2d760b5dd 1 1 32 1 0 1 2 60 1 78 1P044a367f2716ba0a 0 6 0 8 33 8 40 8 47 64 52 8 58 8P045268e42fae9ea6 1 1 4 1 0 1 6 52 8 59 8 67 64 78 8 81 8 86 8P0459b7b7892e856f 1 1 4 1 0 1 2 25 1 38 1P04898511709b4523 1 1 4 1 0 1 6 19 8 26 8 33 64 38 8 44 8 52 8P0489f705921e909a 1 1 32 1 0 1 2 71 1 90 1P048b29c8083b92a6 0 2 0 1 60 1P048ea593f2fcd793 0 2 0 1 4 1P04c91a3b31bedaae 0 2 0 1 90 1P0521b3d3c4404431 0 3 0 8 81 8 83 8P0524e723d4e13223 1 1 4 1 0 1 4 49 8 63 64 74 8 82 8P0526791b98624f80 0 6 0 8 47 8 54 8 61 64 66 8 72 8P059137852564f147 0 2 0 1 88 1P05935df7d72976dc 0 2 0 1 84 1P05b57b8436fe7378 1 1 32 1 0 1 2 46 1 64 1P05c3c5e5ee5dbaec 0 3 0 1 2 1 10 1P0604ae7b13701635 1 1 4 1 0 1 4 53 8 67 64 78 8 86 8P061f9af0635d6ec1 0 2 0 1 53 1P065f586724cf4b54 0 2 0 1 15 1P066b0947c926bd7e 0 6 0 4 10 4 14 16 21 16 29 16 41 16P069227a76c92142c 0 3 0 1 9 1 10 1P06a14b7d7cc6f2d2 0 3 0 1 14 1 26 1P06cd7ae058ac80ef 1 1 4 1 0 1 6 28 8 35 8 43 64 54 8 57 8 62 8P078aaed85f196c00 1 1 4 1 0 1 3 16 1 26 1 38 1P078dc66c20a621c2 1 1 4 1 0 1 6 35 8 42 8 49 64 54 8 60 8 68 8P07a59c57068a4b1d 0 2 0 1 41 1P07b764212f213fbb 1 1 4 1 0 1 2 29 1 46 1P07d09a746121d61e 1 1 32 1 0 1 2 54 1 72 1P07f0dc9f820853b0 0 3 0 1 2 1 92 1P07fd8f534b5421ce 0 2 0 1 5 1P0869c1d0ed064f0c 0 2 0 1 61 1P087c3287c8e7f11e 0 2 0 1 2 1P089190096523609d 1 1 4 1 0 1 6 9 8 16 8 23 64 28 8 34 8 42 8P08bd1174f44bf326 0 3 0 8 83 8 85 8P08c18ffee3a30098 2 51 0 7 0 32 1 32 25 128 32 128 39 1024 50 128 51 32 0 3 0 1 2 1 40 32P091516a704bb6954 0 2 0 1 88 1P091d67f6881e6e43 0 2 0 1 78 1P09a0400d3d3f8607 1 1 8 2 24 1 41 1 2 0 1 42 1P0a0736aa6b878a07 0 4 0 1 18 1 22 1 39 1P0a2646716683bfb8 1 1 4 1 0 1 2 24 1 40 1P0a26def05efeda99 1 1 4 1 0 1 3 14 1 24 1 36 1P0a36fcb3eb3f8f61 1 1 4294967296 1 0 1 2 43 1 45 1P0b115a4d6fabb09a 2 46 0 7 0 32 1 32 21 128 28 128 35 1024 46 128 47 32 0 3 0 1 2 1 36 32P0b24f68f2918e175 0 3 0 1 17 1 40 1P0b5ff82f9a8ae1f8 1 1 4 1 0 1 5 9 1 16 1 23 1 28 1 40 1P0bae5b320a65e2c8 1 1 32 1 0 1 2 48 1 66 1P0bcbbe04dd3afa97 1 1 4 1 0 1 6 31 8 38 8 45 64 50 8 56 8 64 8P0bf595f9a403f529 0 2 0 1 6 1P0bfdbd59d90b8c51 0 4 0 1 3 1 18 4 28 4P0c580db177b6792f 1 1 32 1 0 1 2 58 1 76 1P0cb71771e7d87502 0 2 0 1 86 1P0ce4c3ec83f3e67c 0 2 0 1 90 1P0d302f495e9e90d7 0 2 0 1 76 1P0d9202a7780f0bbe 0 2 0 1 40 1P0de598baa6a13c52 0 2 0 1 80 1P0e6212976f9c38ba 1 1 32 1 0 1 2 34 1 52 1P0e6d29234ac43be3 2 41 0 4 0 1 3 1 43 32 55 4 0 6 0 1 2 1 28 4 35 4 42 32 53 4P0e8c6fa3520a8a18 1 1 4 1 0 1 5 11 1 18 1 25 1 30 1 42 1P0e960e9767cad65a 0 2 0 1 2 1P0f4e0073054679fb 0 2 0 1 56 1P0fc65279cea353fc 2 95 0 7 0 32 1 32 61 128 68 128 75 1024 86 128 87 32 0 3 0 1 2 1 76 32P0ff68533e3e83435 0 2 0 1 80 1P100510b4932a8e84 0 3 0 8 82 8 84 8P100af5ad201c053f 0 6 0 8 25 8 32 8 39 64 44 8 50 8P10126092f66c377a 0 2 0 1 5 1P103c4cbce9982059 2 54 0 7 0 32 1 32 27 128 34 128 41 1024 52 128 53 32 0 3 0 1 2 1 42 32P10774ea4c827ff38 1 1 32 1 0 1 2 36 1 54 1P10c108250b3a714f 1 1 32 1 0 1 2 30 1 48 1P10f62157c825efec 0 2 0 1 93 1P10f638e1497cf670 0 2 0 1 42 1P114bec5e41877a1a 0 2 0 1 92 1P11869922ece74a0f 1 1 4 1 0 1 4 31 8 45 64 56 8 64 8P119353b43809ea8f 0 4 0 1 18 1 22 1 39 1P119e60cc6b411bd2 0 4 0 8 11 1 12 1 40 1P11a7122c982264fb 1 1 32 1 0 1 2 71 1 90 1P11a8f2c97b3075d8 0 2 0 1 7 1P11a9da01ace13eb9 0 2 0 1 24 1P12209d1336042bf4 0 6 0 8 27 8 34 8 41 64 46 8 52 8P122e20cb0f966fd8 0 2 0 1 44 1P12636e211c60a586 1 1 8 2 22 1 39 1 2 0 1 40 1P12664f8b9ff07c67 0 2 0 1 2 1P12719a55634e8bee 1 1 32 1 0 1 2 36 1 54 1P128089ef2f175d82 0 6 0 4 5 4 13 16 20 16 27 16 32 16P12c596ec06a592d4 0 3 0 1 15 1 38 1P12f6e6d884810588 0 2 0 1 64 1P136885f470a7805c 0 2 0 1 22 1P136b5e096c17d2b6 0 3 0 1 70 1 74 32P138387550cacfcec 0 2 0 1 43 1P13bf38c4402a6942 1 1 32 1 0 1 2 48 1 66 1P13f49caf3bdcc9eb 0 2 0 1 84 1P143a8010738ebdbe 1 1 8 2 22 1 39 1 2 0 1 40 1P1485c53c5fc98718 0 2 0 1 6 1P14c922204686619d 1 1 32 1 0 1 2 62 1 80 1P14df9b65683b645a 1 1 4 1 0 1 4 16 1 23 1 26 1 36 1P14f231cff88dacf1 0 2 0 1 38 1P152c2428f3b565ec 0 3 0 1 16 1 28 1P1542587969cae5e5 0 2 0 1 86 1P15a998f549f0ce48 1 1 8 2 24 1 41 1 2 0 1 42 1P15b29789c7143408 1 1 4 3 0 1 10 1 41 4 3 14 1 21 1 46 1P1609947bd5f5f7db 1 1 4 4 0 1 54 1 73 32 87 4 4 58 8 65 8 84 8 92 8P166d332a9a0a08ef 2 74 0 7 0 32 1 32 45 128 52 128 59 1024 70 128 71 32 0 3 0 1 2 1 60 32P16aa8f04d74b9b54 1 1 32 1 0 1 2 34 1 52 1P16cc163ec943705a 1 1 4 1 0 1 6 20 8 27 8 35 64 46 8 49 8 54 8P16d863fc77969d88 0 2 0 1 52 1P171b094adc613f9d 0 2 0 1 5 1P177b0eb6be2917a1 0 2 0 1 96 1P177fcedb19d7bfdc 0 2 0 1 2 1P17d557819be3c9f5 1 1 4 1 0 1 6 17 8 24 8 31 64 36 8 42 8 50 8P17e709cfe13d41b2 0 4 0 8 8 1 12 1 38 1P1853e950f6e10f60 0 2 0 1 52 1P18630b0d6d8c30a1 2 87 0 7 0 32 1 32 55 128 62 128 69 1024 80 128 81 32 0 3 0 1 2 1 70 32P1864b8557d9b771f 0 3 0 8 84 8 86 8P187589477bc64638 0 2 0 1 43 1P187dc52db5c98adb 1 1 32 1 0 1 2 68 1 86 1P1902f82d2b4c0a86 1 1 4 1 0 1 2 28 1 44 1P191514e54dbfe330 1 1 32 1 0 1 2 52 1 70 1P1923bc72512bd19f 0 2 0 1 46 1P195b4c3493a0c235 0 2 0 1 60 1P197957fd1eca2065 0 6 0 8 57 8 64 8 71 64 76 8 82 8P1988acd5fc70c420 0 5 0 1 15 1 22 1 29 1 34 1P1a0dda413dd1ff22 1 1 8 1 0 1 2 62 1 80 1P1a72b7c23d97e46d 1 1 32 1 0 1 2 58 1 76 1P1a9022e05489587b 1 1 4294967296 1 0 1 2 45 1 47 1P1ac04c3bdad34858 0 2 0 1 30 1P1af4445e8d813a7f 1 1 4 1 0 1 4 57 8 71 64 82 8 90 8P1b283cdd6c39a36d 0 3 0 1 64 1 68 1P1b576188d853457a 0 3 0 1 2 1 10 1P1b6a06eddba778ee 0 6 0 8 29 8 36 8 43 64 48 8 54 8P1ba0f3c7fce9974e 2 51 0 4 0 1 3 1 51 32 63 4 0 6 0 1 2 1 36 4 43 4 50 32 61 4P1ba168f968646359 1 1 4 1 0 1 6 37 8 44 8 51 64 56 8 62 8 70 8P1bae3e327bdd5970 0 2 0 1 74 1P1bfa4bf29f3004ba 0 2 0 1 54 1P1c34f9880bef8781 0 3 0 1 22 1 28 4P1c835e60e5b920af 0 3 0 1 62 1 66 1P1c9cb3b6f8bd539b 0 3 0 1 70 1 74 32P1ccfe517cb33f9c9 1 1 4 1 0 1 6 37 8 44 8 51 64 56 8 62 8 70 8P1d04323fd880f228 1 1 4 1 0 1 4 21 8 35 64 46 8 54 8P1d417040669a022e 2 64 0 7 0 32 1 32 35 128 42 128 49 1024 60 128 61 32 0 3 0 1 2 1 50 32P1d50873dc247e5cc 0 3 0 1 17 1 40 1P1d61702799a74961 0 2 0 1 54 1P1d71591b64398eba 0 3 0 1 66 1 72 32P1de2c78ceff48723 0 2 0 1 46 1P1e0cb4880dee055c 0 2 0 1 62 1P1e0fc5ad64c04d35 1 1 4 1 0 1 2 25 1 38 1P1e65c1fef54d07d8 1 1 4 1 0 1 6 39 8 46 8 53 64 58 8 64 8 72 8P1eb5579bfb745b3b 0 3 0 1 18 4 22 1P1edb534fc2c2dac0 2 59 0 7 0 32 1 32 31 128 38 128 45 1024 56 128 57 32 0 3 0 1 2 1 46 32P1f024c1064de4378 1 1 32 1 0 1 2 72 1 90 1P1f3d2e75cf2098d5 1 1 4 1 0 1 6 11 8 18 8 25 64 30 8 36 8 44 8P1f5dde25acb93ed0 1 1 4 1 0 1 6 43 8 50 8 57 64 62 8 68 8 76 8P1f6b752515736882 0 2 0 1 3 1P1f88e5c7384fb17d 0 2 0 1 60 1P1facfaddfa869dba 1 1 4294967296 1 0 1 2 41 1 43 1P1fafd9b39faa78b5 0 4 0 1 26 1 29 4 30 4P1fd082ca1646f9b4 1 1 32 1 0 1 2 48 1 66 1P1fd705f78fc8e7e4 0 6 0 8 21 8 28 8 35 64 40 8 46 8P1ff79c956c7ff3cf 1 1 32 1 0 1 2 73 1 92 1P2056153f8781477b 0 2 0 1 61 1P206ecf7c4f6819ba 0 2 0 1 54 1P20b8275cc44806da 0 2 0 1 1 1P20ce5e601b38ac7c 1 1 4 2 0 1 20 1 2 13 1 38 1P20e690231bbbd26b 0 2 0 1 74 8P211de8e9b2c2e693 0 2 0 1 40 1P21aae56100ff08ba 0 2 0 1 1 1P21b6d15234c65999 0 3 0 1 2 1 90 1P21d2b0fdbdc3d9a5 0 2 0 1 64 1P21f534b42bace7e3 0 3 0 1 22 1 28 4P2266d37fe5c033ff 0 3 0 8 82 8 84 8P228e66a804e1f65f 2 84 0 7 0 32 1 32 53 128 60 128 67 1024 78 128 79 32 0 3 0 1 2 1 68 32P229f2ced611f2f34 0 6 0 8 43 8 50 8 57 64 62 8 68 8P22a3e45fde175bc8 1 1 32 1 0 1 2 62 1 80 1P22b4b7e3589c7761 1 1 8 1 0 1 2 64 1 82 1P22c9f6a498960de8 1 1 8 1 0 1 2 48 1 66 1P22d64b1c91ee69c3 1 1 32 1 0 1 2 38 1 56 1P2325053f2f1995d3 2 34 0 4 0 4 3 4 36 4 37 16 0 2 0 1 2 1P23316ec592d8a2ae 1 1 4 1 0 1 5 10 1 17 1 25 1 37 1 42 1P239cb388275b8efa 1 1 32 1 0 1 2 40 1 58 1P23b40dab6ef545c9 0 2 0 1 66 1P23db63437cc7efd6 1 1 32 1 0 1 2 52 1 70 1P2419c3b57c04ffc3 0 2 0 1 6 1P241e8a18e87eb410 0 3 0 1 16 1 26 1P2428c917dfd7b97d 0 2 0 1 6 1P2429aa7b72058d39 1 1 4 1 0 1 6 33 8 40 8 47 64 52 8 58 8 66 8P242a1a15c1197c53 0 3 0 1 2 1 92 1P24a2141d82fe2799 0 2 0 1 43 1P24b32fd0b29f2250 1 1 8 1 0 1 2 42 1 60 1P254f84f39e860f56 0 2 0 1 62 1P256264561d294df5 0 2 0 1 1 1P25685d5f195805bd 0 6 0 8 23 8 30 8 37 64 42 8 48 8P257bd7677314db9d 1 1 4 1 0 1 6 13 8 20 8 27 64 32 8 38 8 46 8P259ab318d4a478e1 2 41 0 6 0 4 1 4 17 16 24 16 31 16 41 4 0 3 0 1 2 1 32 4P25d3961d3477e6e5 0 2 0 1 2 1P25f3f9ea3fc2c8e6 0 6 0 32 49 32 57 128 64 128 76 128 82 128P2600cec6b14e827a 0 2 0 1 82 1P267d7257b9e54909 0 2 0 1 76 1P268f3f7d7402d6f7 1 1 8 2 24 1 41 1 2 0 1 42 1P269c0f65420c97d1 0 3 0 8 82 8 84 8P26a6d2767a8da24b 1 1 4 1 0 1 4 23 8 37 64 48 8 56 8P26c9f64979fe2925 1 1 32 2 0 1 66 1 3 71 1 72 1 90 1P26ce877be745991c 1 1 4 1 0 1 2 27 1 44 1P26ec4ba046ce9bd5 1 1 32 1 0 1 2 44 1 62 1P26f5b0b5e3f05310 1 1 4 1 0 1 4 27 8 41 64 52 8 60 8P273d296912ec4663 1 1 32 1 0 1 2 30 1 48 1P277b9f90a2be4874 1 1 32 1 0 1 2 26 1 44 1P2790c66f45e72ee2 1 1 4 1 0 1 4 47 8 61 64 72 8 80 8P27bd001854349703 1 1 4 1 0 1 4 43 8 57 64 68 8 76 8P27c07352e26bdb31 0 2 0 1 44 1P27c34a4ef79d0c46 1 1 32 1 0 1 2 28 1 46 1P27c89e32ae4142c0 1 1 32 1 0 1 2 54 1 72 1P27f199f3046b08b6 1 1 4 1 0 1 2 27 1 44 1P28239622c8d9adff 1 1 4 1 0 1 4 51 8 65 64 76 8 84 8P28bf37673decdd42 1 1 8 1 0 1 2 40 1 58 1P28e942d7160326f8 1 1 8 1 0 1 2 58 1 76 1P28f9b9c43f8f7138 1 1 4 1 0 1 4 59 8 73 64 84 8 92 8P291fa7d1e7e5eafa 1 1 8 2 22 1 39 1 2 0 1 40 1P2925330cb847c99b 1 1 32 1 0 1 2 38 1 56 1P293dea84eda4490e 1 1 32 1 0 1 2 74 1 92 1P29912b9735edf778 1 1 32 1 0 1 2 28 1 46 1P29e7649fd8b7dffd 0 2 0 1 2 1P2a096338560b59c3 1 1 32 1 0 1 2 66 1 84 1P2a6c7662e46777dd 0 2 0 1 66 1P2b0ec7e65c16433b 0 6 0 8 51 8 58 8 65 64 70 8 76 8P2b1e628c51cd6467 0 3 0 1 16 1 28 1P2b3188a2e7e7cfe9 0 2 0 1 44 1P2b3c4510c92dd6fc 0 2 0 1 61 1P2b40c4cbabbfd1d0 1 1 4 1 0 1 2 25 1 38 1P2b418c69d745ce13 1 1 8 1 0 1 2 44 1 62 1P2b5068c4f35488c1 2 30 0 4 0 1 3 1 33 4 43 4 0 5 0 4 2 4 18 16 25 16 32 16P2bbf558bd471c56e 0 6 0 8 31 8 38 8 45 64 50 8 56 8P2bd4440b9c054930 0 2 0 1 33 1P2c3227487e6d730b 1 1 4 1 0 1 6 41 8 48 8 55 64 60 8 66 8 74 8P2c333000456a290b 1 1 4 1 0 1 6 15 8 22 8 29 64 34 8 40 8 48 8P2c642d9a53c5656c 0 2 0 1 80 1P2c6d2f34283b8f9d 2 82 0 4 0 1 3 1 77 32 89 4 0 6 0 1 2 1 62 4 69 4 76 32 87 4P2c8f91dc0be42017 0 3 0 1 66 1 72 32P2ca9c5ea66a9a967 1 1 32 1 0 1 2 68 1 86 1P2caf6960e4445f99 0 2 0 1 4 1P2cb4fe2f7c707115 2 46 0 4 0 1 3 1 47 32 59 4 0 6 0 1 2 1 32 4 39 4 46 32 57 4P2cce331ffcdb19bb 1 1 8 1 0 1 2 68 1 86 1P2d73b755c70573f6 0 2 0 1 64 1P2d7dbcac369f0f75 1 1 4 1 0 1 3 13 1 27 1 44 1P2d885b82a139de5f 1 1 4 1 0 1 2 29 1 46 1P2dc9e831ea5e27d6 1 1 4 1 0 1 6 39 8 46 8 53 64 58 8 64 8 72 8P2e4fc6e934345d8b 0 3 0 1 64 1 68 1P2e8ab5a44cac7d45 1 1 4 1 0 1 6 32 8 39 8 47 64 58 8 61 8 66 8P2ea334c9d258f72d 0 2 0 1 44 1P2eb41ee899ee771a 0 2 0 1 72 8P2ebe0227de7c6829 0 2 0 1 13 1P2eeddf88e122c89c 0 2 0 1 86 1P2ef6764605411237 0 2 0 1 63 1P2f1d7a3b5f64d25e 1 1 32 1 0 1 2 66 1 84 1P2f3bc6f89530c490 0 3 0 1 26 1 30 4P2f6f54662359aad1 0 4 0 1 16 1 20 1 37 1P2f7e948c933c0f26 0 3 0 1 2 1 10 1P2f84fa23f809d7c8 0 2 0 1 74 1P2f8d858a4086c3d0 0 2 0 1 42 1P2f97118b90f8c236 0 5 0 1 13 1 20 1 27 1 32 1P2f9ecf121c11df33 0 7 0 32 49 32 57 128 64 128 71 1024 76 128 82 128P2fb16ebb96e9f769 0 2 0 1 62 1P2fbf16ed0a5aa1e8 0 2 0 1 56 1P2feaa4e8bc102d62 0 6 0 8 19 8 26 8 33 64 38 8 44 8P2ff7d5ae4952848e 1 1 8 1 0 1 2 34 1 52 1P30cbf0e947e59d1b 0 2 0 1 47 1P30ccf5380ccdf3d1 0 4 0 1 16 4 20 1 26 4P30cd88e0f4974299 1 1 4 1 0 1 4 33 8 47 64 58 8 66 8P30de1f24b1b5dd06 1 1 8 1 0 1 2 36 1 54 1P30ee27a1621bb7d0 1 1 4 1 0 1 4 29 8 43 64 54 8 62 8P31463eb3672ee1c4 2 74 0 4 0 1 3 1 71 32 83 4 0 6 0 1 2 1 56 4 63 4 70 32 81 4P3155d45b80915986 2 82 0 7 0 32 1 32 51 128 58 128 65 1024 76 128 77 32 0 3 0 1 2 1 66 32P316d4f78c5e6a56b 1 1 32 1 0 1 2 42 1 60 1P31735f24ea765c2c 1 1 32 1 0 1 2 32 1 50 1P31970b1ae77900da 0 3 0 1 2 1 60 1P319f860e33a339e9 0 3 0 1 2 1 80 1P31b52301f3e0e9b8 2 49 0 7 0 32 1 32 23 128 30 128 37 1024 48 128 49 32 0 3 0 1 2 1 38 32P31b877a51034e81d 0 4 0 1 16 4 20 1 26 4P31d891609677929b 1 1 32 1 0 1 2 32 1 50 1P31fe8c8da69383d5 1 1 4 4 0 1 3 1 25 4 28 4 2 18 1 38 1P321412e82c1efa5f 0 4 0 1 16 1 20 1 37 1P321fdaf046c681ab 1 1 32 1 0 1 2 42 1 60 1P3224aa82429fb27b 2 32 0 5 0 1 1 1 20 4 27 4 33 1 0 4 0 1 2 1 18 4 28 4P32559ffe3b967d7c 2 61 0 7 0 32 1 32 33 128 40 128 47 1024 58 128 59 32 0 3 0 1 2 1 48 32P32613ea2f96bed6f 1 1 4 1 0 1 2 30 1 46 1P32ef3b9c6c070afc 0 2 0 1 1 1P3357e7bc25afbb8d 0 2 0 1 92 1P336b0c1d82b60180 0 3 0 1 2 1 90 1P33775e0fa24f394c 0 2 0 1 41 1P3378a9b03f950467 0 4 0 1 70 1 73 32 74 32P337dde6371f15459 0 2 0 1 55 1P33dc003d95eba91a 1 1 4 1 0 1 6 51 8 58 8 65 64 70 8 76 8 84 8P33dcaaa16b154249 1 1 4 1 0 1 4 19 8 33 64 44 8 52 8P341ed75913311b9b 0 3 0 1 70 1 74 32P3421ff5f3d8d865c 0 2 0 1 95 1P34f265ce4c31a5df 0 2 0 1 63 1P351444e74500fadd 0 2 0 1 56 1P351d7a4dc8ed60b7 0 2 0 1 90 1P357d6433b1833a25 1 1 4 1 0 1 6 44 8 51 8 59 64 70 8 73 8 78 8P358885a21ccaea5c 1 1 32 1 0 1 2 60 1 78 1P35ac722a2d091385 0 3 0 1 2 1 80 1P35ed11190b92e5b6 1 1 4 1 0 1 6 48 8 55 8 63 64 74 8 77 8 82 8P362eca529bafc55e 2 56 0 7 0 32 1 32 29 128 36 128 43 1024 54 128 55 32 0 3 0 1 2 1 44 32P363bb60b48ff1014 1 1 4 1 0 1 5 13 1 20 1 27 1 32 1 44 1P3657d9c60442904f 0 2 0 1 82 1P365f1ce3f72a105b 0 6 0 8 49 8 56 8 63 64 68 8 74 8P3662b49771df5ee1 1 1 4 1 0 1 6 35 8 42 8 49 64 54 8 60 8 68 8P366bc7d24e8a2c74 0 3 0 1 17 1 40 1P369dc654e57f2846 0 3 0 1 2 1 62 1P36a59894532ca587 0 4 0 1 18 1 25 1 28 1P36aa82a652018ee0 0 2 0 1 63 1P36b5e9fa93489cf0 0 2 0 1 2 1P370296609f823157 1 1 8 1 0 1 2 38 1 56 1P3707eeba7d9c65bc 1 1 4 1 0 1 6 15 8 22 8 29 64 34 8 40 8 48 8P3743510e71bd89f1 0 2 0 1 41 1P3748eb459a2f0218 0 3 0 8 84 8 86 8P377533d3281b1b08 1 1 32 1 0 1 2 34 1 52 1P37a772cd19b62301 0 6 0 8 45 8 52 8 59 64 64 8 70 8P3819245abd0f4758 0 2 0 1 38 1P383695e221022554 1 1 4 1 0 1 3 15 1 29 1 46 1P385cb1b2916e7c6c 0 2 0 1 2 1P3861b7c7738e9327 0 4 0 8 11 1 12 1 40 1P38b994f178e09dda 1 1 32 1 0 1 2 50 1 68 1P38c62f160099a90b 0 2 0 1 82 1P3905858deb4b501e 1 1 4 1 0 1 2 26 1 42 1P390a98c68a0dac09 1 1 4 1 0 1 6 17 8 24 8 31 64 36 8 42 8 50 8P390ef92fa7ce5041 0 2 0 1 84 1P39173e3b65627194 0 3 0 1 22 1 28 4P398e782734227579 2 77 0 7 0 32 1 32 47 128 54 128 61 1024 72 128 73 32 0 3 0 1 2 1 62 32P39936b4b350cdaad 1 1 4 1 0 1 2 28 1 44 1P399817c4ce994b2a 0 2 0 1 8 1P39b62b9767495c49 0 2 0 1 1 1P39d16af0489cd1e5 0 2 0 1 6 1P39daf79a6a79006b 2 64 0 4 0 1 3 1 63 32 75 4 0 6 0 1 2 1 48 4 55 4 62 32 73 4P3a0a519094dd226a 1 1 32 1 0 1 2 46 1 64 1P3a20012e3c473b23 2 36 0 4 0 1 3 1 39 32 51 4 0 6 0 1 2 1 24 4 31 4 38 32 49 4P3a351ab09f35acff 0 3 0 8 84 8 86 8P3a4582bb0086f6c2 1 1 32 1 0 1 2 44 1 62 1P3aa3b2c086b914c1 0 3 0 1 26 1 30 4P3ac916e488fcd2b8 0 3 0 1 2 1 60 1P3ac9338a066acc49 0 2 0 1 15 1P3ae866e93bf97cc3 0 2 0 1 2 1P3af93f2007602080 0 3 0 1 4 1 18 1P3afe3027a5c15c39 0 2 0 1 1 1P3b080a34094bdd57 1 1 32 1 0 1 2 40 1 58 1P3b0c620361454bde 1 1 4 1 0 1 6 27 8 34 8 41 64 46 8 52 8 60 8P3b26ea32e59c33ec 0 3 0 1 14 1 26 1P3b2ef92701f85aef 1 1 4 1 0 1 6 24 8 31 8 39 64 50 8 53 8 58 8P3b5d726a7d5e7944 1 1 32 1 0 1 2 64 1 82 1P3b73e2511ad0768c 0 2 0 1 3 1P3ba05200ef735a35 0 2 0 1 94 1P3bc5902cb3d32bdf 2 92 0 7 0 32 1 32 59 128 66 128 73 1024 84 128 85 32 0 3 0 1 2 1 74 32P3c03e42a0c14b348 0 2 0 1 13 1P3c6aa3e90a6825d2 0 2 0 1 15 1P3c80adc4468fecf3 0 2 0 1 1 1P3caa264ad8a8a31a 1 1 32 1 0 1 2 26 1 44 1P3d2a145540b6ea0b 1 1 4 1 0 1 6 23 8 30 8 37 64 42 8 48 8 56 8P3d3173622682546b 0 3 0 1 26 1 30 4P3d455b1cdcb9eb21 1 1 32 1 0 1 2 73 1 92 1P3d5526f4f3d66bee 1 1 8 1 0 1 2 66 1 84 1P3d64d9baf6de9eac 2 79 0 7 0 32 1 32 49 128 56 128 63 1024 74 128 75 32 0 3 0 1 2 1 64 32P3d9720f6eb52f93e 1 1 32 1 0 1 2 64 1 82 1P3db2840595e0a691 1 1 8 1 0 1 2 46 1 64 1P3df6b4c983d34172 1 1 32 1 0 1 2 24 1 42 1P3e309cc7a35fd0c4 1 1 32 1 0 1 2 50 1 68 1P3e3b73bc6490d751 0 3 0 1 15 1 38 1P3e4901e0a2574df8 0 2 0 1 36 1P3e50a797b56d2815 0 3 0 8 81 8 83 8P3e6bc431ba95ef42 0 3 0 1 2 1 10 1P3e9bf8e50e58e202 0 2 0 1 58 1P3ea286f73dc57eb0 0 4 0 8 8 1 12 1 38 1P3ec22d5abc189e28 0 3 0 1 66 1 72 32P3ed3940752242830 0 2 0 1 62 1P3eec4d8e2c4e9028 1 1 4 1 0 1 6 13 8 20 8 27 64 32 8 38 8 46 8P3f1214dcf3ee434b 0 2 0 1 1 1P3f21d8e32bcf4083 1 1 4 1 0 1 6 19 8 26 8 33 64 38 8 44 8 52 8P3f43007c30c402be 0 2 0 1 46 1P3f580c6c07c5bb0c 0 3 0 1 2 1 82 1P3f66f4a59d7c0dc5 1 1 4 1 0 1 4 45 8 59 64 70 8 78 8P3f75a352b2d20b5d 1 1 4294967296 1 0 1 2 39 1 41 1P3f8b3b75d198ac80 2 35 0 4 0 4 3 4 36 4 39 16 0 2 0 1 2 1P3f90d591e503ade1 0 4 0 1 16 4 20 1 26 4P3fb36cdc3a77f8e8 0 2 0 1 5 1P3fd8f25f5bbac631 0 2 0 1 52 1P3fede6b59283b89b 0 6 0 8 59 8 66 8 73 64 78 8 84 8N00310577d1d9a47bN0031e07d75d5eb5bN00483c439e1a462eN004fb6f5bdfeaabfN00558ba814049bd7N005b888962251657N00716c02ec4aefe7N00aeaaa584e2bf4bN00b48b521c9bbdfbN00da87c39857f605N00de85141dd5da73N0109092fd4a72741N0130717619fa1e2aN0177c119c1284ba0N018fd8016dec8963N01cd23dc42fbac27N0201a64d242ff626N02485c147d1d519dN02997bf26fe6b9e2N02aa1404c557506aN02b93a6e751284f2N02d92a7d08ea8c32N02ede904020a3530N030b202e8890bc1aN034753119580953bN03571b054b4a4497N03595c70c0f9afbdN038aa6ed0b08e65fN039350946be17cffN03bd1334b53782a4N03c9a92658254d83N03fd18a08f1cff92N0420b3368bf8a1b4N042c434932dbc2d6N0430b69c39252352N0438c1d2c8ff049dN0441652b883d209dN0479511a7019f23dN049e6527f6106b83N04c798d7210dfe33N04d06349eb53c256N04f45a56193239d0N0518e48537753a1fN055275e0a52d7734N05730b020a71b5fdN05799b6af4432464N05a7bae0f655017aN05bb4f734b99de4fN05cb418e254bc918N05d0bd339d1b9387N05f87aca28e5d820N05fd038ed0b6a329N06081a48339a62a2N061d3715d415fb01N063237eeee2c50e8N066987674a63374eN06892068c8705d8fN068ed73229438aa7N06c1dfe36dffc5fdN06e68c294f4c2371N06f129a2eac656d4N07110b362fa1a90aN072368283749a4d6N073c4b4ff9ec232eN07407a91525438dcN0799219abad0c43cN07a550494ac389d3N07c39055c7e30bf3N07cf9ec0730de69dN07d32b8fe6c79a23N07e423649b79dd30N080b4ecac6c513dfN085863adf276cb7eN08a52c8e410afdadN08bb04a086eacb9fN08bf121e29e7ba3eN08d6efece089c05fN08fb80c2f195fb63N08fbb19241b9c320N0909ff59be43df52N09124dd2b0a74b06N09510cbb9380a402N097f84251335a95cN099b5b764dd717fdN09a977fb79c9f4f2N09d76fec6896fd94N09e376137a95f66bN0a3466956a7dc3acN0a4ab21ded8d49efN0aac283ec719e582N0b185186e8f8c6dcN0b49279d7c7804a2N0b4f1cd9b03bceacN0b59e7ab5f207d25N0b7db20c9ba6cf28N0bb1a31b7dad77cdN0bb9ec9a461b8349N0bc394f8020287ddN0bd7fcd2f7f3cc7eN0bdf23a11d2d3028N0c1d9aa2e458e460N0ccc01618942d04cN0ce3ae2cf05e8facN0cf42fa0f769445fN0d01414fd0a63075N0d017a0cc181ab5eN0d07cff28704ae80N0d168862427076f8N0d4da98f5aab283dN0d5c23aa5cf362f1N0d5f9d46216df73dN0d882a849ec4f259N0dc6a51541297088N0dc73d37d747bce5N0dcc0d08a56faf74N0e2d92b211654790N0e4f4053bd903309N0e9b0c3aedf95aafN0eab8dce5155567aN0eb71df534a3eed0N0ecfadbc52efc812N0ecfbb1deafa1de4N0ef48a7c79eb5d6aN0f0a0888d4fad517N0f0da2b1a07c55cbN0f22b00f9cfbb41cN0f361a5661ee164aN0f489a717e95ce29N0f5be0e9e218cd27N0f623c98ef5e7f0aN0fb2f50a6a6849f6N0fb8d3c03d60d144N107f1ca58eae00c6N10b7a85cf07251a0N10f17ae85d87cb91N10fa897522ad77f1N11129ae2d0be5a92N111327293179ea95N11240f80f15ef007N113812cf7d3e8029N1161e7a47a7f8fa7N1161f5140a6c8bc3N116dc2ab5f45ac57N1182ccb1a145409cN11a22adc8419fe15N11bb45e0574a6faaN120dd723e3e2fcecN1210468475063a53N12166c866ae479cbN121aadd9c174e57bN1224b612645ce669N1236858ef77ea95aN123ae9c1bbd2bef6N123d6ae9401f9ea8N125a92286ee0f7c1N12678ea937ee20cbN12aa5f1bbdbb12d7N12e217b8882a4fa0N1302d1fd1d7d9ebfN1331a28b470df684N134b0c4c3ec15168N1359888779aef4f3N13608660c554261eN1375c74439adcf4aN13825edce37f79b3N13903b1593dcfbc7N13e302fd7eb12540N1421be5b2bd0a599N14401f9cdd07d237N14403c0e369d20efN144ab5f52e457111N144add4e64f33c0dN144c0be23a82c499N145552b147625c17N145cb2e30c085ac7N146201fcac563813N14674c988bee2d41N14808a61718241dbN14c1ef29a9597334N14c3683e690db7ffN14d861daaf16ebf1N14e4f5cb5658f13dN1533a86ea84811cbN1542c7559a6467c6N154aec14cfc406b2N1560463cf7b32741N156cc5739a22fb67N159d3eb130262474N15a4f3be848a8407N15cc5ed90930cae3N15d40ff2e343dfc4N15dace048d7608b2N15dc86108456f8f4N160abd461fab98f0N163161249b78f88bN16aaf839a7ee6f19N16da854a7099c03eN16e06aa5a8569685N173f9812ff8cf6a2N1742dfa2a3f608a3N174d74199498f273N17ef38ab3a1c2242N17fc04ee4c50c787N181a9463e938988cN185386d1e3cfcd91N186143cb2d3fe54cN18664b369eb6fb87N187f46e56e4ee393N188096fd15f11b88N188ba11b33882da7N189aca939387fe5fN189c552dfdcf4eb7N18c6e715ecfe22e3N18c8f38ca3354718N1931d8317648e715N1934687698584dd9N193983fa813739f6N1957fbfe5ca9b143N19598c6949a6a9acN197b5c5078a73283N19813cfbf63df93cN199fecc2bfebc91bN19b6818d0da0d9c6N19c654b33be46d27N19d9e7352c837bc9N19dabae1b7f55f8eN19fd98a3244bf279N1a01f7d936f8876eN1a394c756944aa34N1a91a30585b9970cN1aaac48205051eb9N1abe20f6bbc5b200N1ae0f0515ff4d660N1ae9c9dfc649bda2N1b09ac6eab2bb9c0N1b1209a6dc8f1e4fN1b56e63de476201fN1b5b80418cbff3e8N1be68961b9b5a7bbN1bf5de381dd51a4bN1c030715f4529087N1c3483565b68f794N1c4798a59dc1f606N1c4f85d1ae2cd802N1c6efbec90bfc738N1c72ac9378c779c8N1c75bdd5e3dae960N1c8cdf5400d93db4N1c9ad29aca3c7075N1cb278b2c9b811eeN1cec27d8c5c68ad6N1cf9e8269d8dff7cN1d3b6f44ad8173f9N1d4c77cd93c77af3N1d6ceb6900c534efN1d8682a0c7920fc1N1d89e8a172f57d2bN1d8c072ecb9d49c5N1da152ab349f1cd9N1db33b2484ee9bfeN1ddb85c49db8c141N1df592b1a11e8973N1e2a147155abf897N1e3bff9e28f54f70N1e9409f7e4fde28dN1eabd12969e62c72N1eff8ddfa275b158N1f04c864bf35b48cN1f21aab77201c4eaN1f22aa11fa506895N1f3797c002c100a3N1f48dbbf4d627c9dN1f5bfb819c0b60feN1f5fc89ec70c9894N1f65c61e6ec67a4fN1f6fd052592f12d6N1f7ab3853d9c1c28N1f937a163319bedaN1ff0bd974701189fN20139adcde7e276cN20209a85d090a67aN203ccefbf1be2a20N20979bf619eb693bN20a7242ad8ce3642N20f75b71cf3ed4bcN20fa8869eb93bdb6N20fec9a4a50696beN213688a71f678b64N21397cab8d199218N2172054579fdaa83N21823fa34f6492bdN21cf69b396e9b14cN21dd44c935691168N22062f470b37bf5dN2251d89ba91b8103N2268fb47ef5bc552N22a2286435c84502N22c5af51611b5963N22cc842f2d442f57N22e1ab165057bea2N22e3fa24fff098d9N22edd3de91ca021eN22f31d40dcd3aebdN2305ba2d36eff40dN23098e5f84dfcca9N233d5bf84cb512abN236b94f7b6918c77N23993eaf4f0664aeN239d6ba2219831dcN23ab50d27e45fdaeN23e0b6c61fb0fa1aN24769b3f57b22242N247958ffb7c885f1N2499b36055118932N24a0b0fe1dd3b014N24a54bfc32f75fd2N24a7109382738251N24a97c928055355cN24aed7d561efca33N24f343e1fd763685N25180c87f009f5ecN25411f8b60c0d1f8N259501bbee8b2da2N25c6d1c62056bf2bN26330c54adb8a140N26403811d8ff10cbN2676c73a30eed5edN26bd627168ced320N26ca6888f2445819N26cc416cf4116f55N271b1250605518a5N272600b90a44cb40N2744e31307fec38aN276e8f42eb90d8d1N2774ca071b4d2e27N277516eafa755764N277960339c1fbcc0N27c0703cf661bd27N27d0e0d8bd926420N27d856accd2fc89cN27db396a037b1041N28218b9073c3e7bbN283115566cf424f1N28501bb7a9171c83N285e480c29932fc7N286b354832cb2127N2875988b349fcca6N288b956e3629992bN28c1c1ce662bded8N28f8d66595f063c5N291af2497bbc1862N2954406e72a9cc2fN295c0bb149e602a4N29841c3d18252cfbN299d02fc72da24e1N29b3dd74519319f3N29b716c568ef5e28N29c3d71a83e01132N2a0b3f0ea2966fa9N2a2895aff1773bb9N2a51d634df41299bN2a6a6128b10eb7e9N2a7ee293ed058014N2a8d7c20ec03ec77N2ab55b5b5b8ef1e5N2b1366b80c741ce3N2b30d26332f5be73N2b3de6fc9f565b5aN2b8c074ff103ae78N2b8e7987bb0cd0cfN2bb0af3aa96cdefdN2bc919085bf6aac3N2bd39f7233198d24N2be1c9323ae965d1N2bf3e801ecdd39f2N2c00b112a2032411N2c384bf594c449f2N2cd7e5c11763f92eN2ce40e443a3e6f8fN2d10a6e784437febN2d14cf0ca7d9754eN2d41bd5e7f2edcbeN2d831a329ae1e280N2da85e59a117131cN2db30adc9cd333c8N2dbaaa89a314035fN2dbd8144a745776fN2dce5e3465f618aeN2e2c846c2b314882N2e52e37f6f00bdbdN2e8a1a7645a5c8f9N2ed509f12277e6c6N2eebabc455e98e74N2f11820d77b1462bN2f1e6aefea301175N2f2de870a7e58853N2f45d644bc51c6c7N2fa8ebf5d7bbc00eN2faa995e95a4336aN302a476d4151e03dN3053b9ce3aca84c4N3078b37d1bc6e772N3096b5713cd2ea1cN3097c8862a226409N30c5373b7080b03aN30cf387a4cf2e6c4N30e1f8a7b371c394N310a7ba42aed9649N31221eff0fb488dcN3142cfe2ecbbd508N31473e4d01a782e3N315162356bebbc8eN3169ffca92038faeN317b09da6d1c5e88N317b8f99773aebf8N317b9095b3a4dc1cN321385aa2e9ef773N322674f6ec19c623N3273033397b807a6N328559eaf9e4f7cfN32dd98dd39d16986N32e9fdff2e07a4cbN331015e51b64e67bN33180861ca29074dN3359111441a808ceN337f9dd268b8f0e5N3392e346bbf5ea16N33a2cdfda7a2c25aN33a9785305ca9d80N33bdc58db3236fa5N33f6ee8b1c31e7cdN34579dc9d0057e1aN345ffe99476f342bN3484aa13279f827aN34b0979b6d552c0fN34bbf7f47cd582f7N34c17fffe5063e91N34dc969791b98ae4N34df75bf28410892N34fc2ecd3b9ff29dN351a2e078270c984N3538278ae38d9982N353c91fbea6cc403N3543a0c02c0179d7N355e1c84da9c27f9N3565e4ed0d3a5a30N356e497507711352N35a9c12b51ad4050N35aae8e842b37c3eN35ac51be5f1a612eN35c54f91d0cce6ecN35fd79efe7c5ec42N3601452adf9da946N3617b2e656cc8a75N3630fb2c2282c160N3638632d71dac3ceN3646de5e446b21a2N365751062fe3a7bdN365cffdf3326785cN367a70fb66846f0fN369689d699d4e757N36d1c4fc5f9ecb8bN36e95cc98e39145aN36ebed5bd6ef7334N3752b0c63f4f20e3N377eafa9996d27c8N3797f2aced4ec514N37ccaa89cb96dea2N37d154d24167a34bN37d55af0e2714712N37d731af6286ca7bN37e5ecc370e0861bN37ed8c7ac950f685N37f23996b2bbcaafN3813ca8cb447da6dN38156203a74aaab4N385f4fb69cc861fbN38648a93159bbfceN3871f0660061a537N3882e2075d8cdf0cN388bbab95b8ebe48N388e05012f7522beN389e05ecb48a3610N389ec9ea2ecc4179N38a0456717ba4eefN38b301ee4e5e8e96N38b3ef794b2358a0N3948337bcb13d870N395102023031e1bdN39624fd0308a6362N39aa55b555386980N39b45315cac3b801N39d481903b95d874N3a3e93d3a3aef26eN3a97694acc89e28fN3ab11c08d3aeda11N3ab165aff7ac405aN3ac238bbce0acc81N3ad603629db3398fN3af91ce621df2cb5N3b174c481826bc6cN3b1f114648ac5880N3b770448a750d321N3baaa80e8f812a99N3bac331f147c860dN3be0032d6ce2bdbeN3be909551b6ac7afN3bef00ab341a3fc3N3bfb1e4b0abfbe69N3c0193545e7dc809N3c33da8c0b3ced21N3c912cf42747296cN3cac74ef762f6a96N3ce8b92e8d4c0850N3d3537acd9dc4057N3d3ca74efe1af272N3d4c95944272d977N3d4ecfd93a1443c8N3d52e164229b7365N3d58cba701cdea48N3df0ff289b5285e6N3e00e987b2b9d9e6N3e2bd97936349fadN3e3c188d6068036fN3e5382bbb520a1d2N3e599173daf3a5e4N3e5e61d72b79386aN3e86c14e3f01fe93N3e8e7a2fd1f7cd43N3eba9813097c3b3bN3ecbfbf47d65c6beN3effb2d1631923dcN3f5151eefbcbe49dN3f5be94abe40e465N3f7b882ffa29e67bN3fc12c6024560e24N3febae708411a92cN3fff460a65c88692"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mla () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_MLA_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_mla_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Lists.ListDef.firstn"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "mpi_core_mla_stmt"; "mla_window_post"].


Definition U_MPI_CORE_MLA : Z := 0x239a8.
Definition MPI_CORE_MLA_STACK : Z := 48.

Definition mpi_core_mla_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D dl : Z) (ds : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lds',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O17.O16.O15.O14.R11.R10.R?.O13.O12.R>.R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(9.O17.)O6.(:.(2.&40.))R2.(;.O18.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O16.)$15.)(14.&40.O16.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O18.O1.R2.)(5.(18.O18.R2.)(5.(19.O18.R2.O5.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O4.)R1.)(1<.(2.&40.)(1=.O4.)O3.))(1>.O18.R2.O2.(14.&40.O16.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_mla_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PD,$?.Pdl,$?.PS,$?.Psl,$?.Plo,$?.Pds,(4.(2.&40.))Pss,(4.(2.&40.))P,(19.O2.R8.R7.R2.)P,(20.O2.R9.R6.(21.R2.))P,(5.(22.=R8.)(22.R8.+2710.))P,(5.(22.=R7.)(22.R7.+2710.))P,(22.R:.(23.(1;.(2.&40.)R6.)))P,(22.R9.(23.(1;.(2.&40.)R6.)))P,(24.(5.(6.$?.R;.R=.)(6.(4.(2.&40.))R7.R8.))(24.(22.(11.R;.(12.+4.(23.(1;.(2.&40.)R7.))))R=.)(22.(11.R=.(12.+4.(23.(1;.(2.&40.)R8.))))R;.)))P,(6.$?.(25.R>.+4.)=)P,(6.$?.(25.R=.+4.)=)P,(26.=R10.)P,(24.(6.$?.R>.=)(26.=R?.))P,(26.(11.R12.(12.+4.(23.(1;.(2.&40.)R=.))))(27.+2.+40.))P,(26.(11.R11.(12.+4.(23.(1;.(2.&40.)R=.))))(27.+2.+40.))P,(1>.O2.R15.R10.(14.&40.R35.))P,(22.R11.(13.(14.&40.R36.)$15.))P,(6.$?.(25.(14.&40.R37.)+10.)=)P,(24.(22.(11.R17.(12.+4.(23.(1;.(2.&40.)R12.))))R13.)(22.(14.&40.R38.)R17.))P,(24.(22.(11.R16.(12.+4.(23.(1;.(2.&40.)R12.))))R14.)(22.(14.&40.R39.)R16.))P,(18.O2.R1:.)P,(6.$?.(25.(14.&40.R3<.)+2.)=)P,(6.(2.&40.)R34.(28.&40.R1;.))P,(6.(2.&40.)R34.(28.&40.R1;.))P,(6.(2.&40.)R34.(28.&40.R1;.))P,(6.(2.&40.)R34.(28.&40.R1;.))(29.O2.(2:.O2.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.R1?.R1>.R1:.R1;.R20.)(7.(8.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(28.&40.O1.)R21.(:.(2.&40.))R20.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Ltac mla_dinv_tac D dl ds0 ld m lo sp :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx D ?l |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
  lazymatch goal with Hi' : mem_inv _ mx |- _ =>
  lazymatch goal with Hs : stk _ mx lo _ |- _ =>
  lazymatch goal with Hf : same_from (Z.to_nat dl) ?ds ds0 |- _ =>
    try replace (4 * dl + D) with (D + 4 * dl) in Hm by xlia0;
    assert (DI' : u32arr usegs mx D l /\ Z.of_nat (length l) = ld /\ same_from (Z.to_nat dl) l ds0
                  /\ munch [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)] m mx /\ wmono usegs m mx /\ mem_inv usegs mx
                  /\ stk usegs mx lo (bv_unsigned sp + -48));
    [split; [exact Hu| split; [rewrite ?upd_length; assumption| split; [repeat (apply same_from_upd_lt; [|lia]); exact Hf
      | split; [exact Hm| split; [exact Hw| split; [exact Hi'| exact Hs]]]]]] |]
  end end end end end end.
Ltac mla_ret_tac D dl ds0 m :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx D ?l |- _ =>
  lazymatch goal with Hf : same_from (Z.to_nat dl) ?ds ds0 |- _ =>
    lx_post;
    repeat lazymatch goal with
    | |- munch _ _ _ => lazymatch goal with Hm : munch _ m mx |- _ => try replace (4 * dl + D) with (D + 4 * dl) in Hm by xlia0; exact Hm end
    | |- wmono _ _ _ => assumption
    | |- mem_inv _ _ => assumption
    | |- stk _ _ _ _ => assumption
    | |- u32arr _ _ _ _ => exact Hu
    | |- length _ = length _ => rewrite ?upd_length; lia
    | |- skipn _ _ = skipn _ _ => apply same_from_skipn; [repeat (apply same_from_upd_lt; [|lia]); exact Hf | rewrite ?upd_length; lia]
    end
  end end.
(* [comment removed for export] *)
Ltac mla_sfact := first [ left; first [reflexivity | assumption] | right; split; assumption ].
Ltac mla_drop_vals :=
  repeat match goal with
  | H : @eq Z _ ?e |- _ => lazymatch e with context [zlow _ _] => clear H | context [zswrap _ _] => clear H end
  | H : Z.le _ ?e |- _ => lazymatch e with context [zlow _ _] => clear H | context [zswrap _ _] => clear H end
  end.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (D dl S sl slm ld ls lo : Z) (ds0 ss : list word).
  Hypothesis Hdl : 0 <= dl <= 10000.
  Hypothesis Hsl : 0 <= sl <= 10000.
  Hypothesis Hslm : 0 <= slm /\ slm <= dl /\ slm <= sl.
  Hypothesis Ln : dl <= ld /\ sl <= ls.
  Hypothesis L0 : Z.of_nat (length ds0) = ld.
  Hypothesis LS : Z.of_nat (length ss) = ls.
  Hypothesis DB : 0 < D /\ D + 4 * ld < 2^64.
  Hypothesis SB : 0 <= S /\ S + 4 * ls < 2^64.
  Hypothesis ALD : D mod 4 = 0.
  Hypothesis ALS : S mod 4 = 0.
  Hypothesis NZS : sl = 0 \/ 0 < S.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 48.
  Hypothesis SX : D + 4 * ld <= lo \/ bv_unsigned sp <= D.
  Hypothesis SSX : S + 4 * ls <= lo \/ bv_unsigned sp <= S.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.

  Notation POST := (mpi_core_mla_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D dl ds0 lo m).
  Notation W := [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0]).
  (* [comment removed for export] *)
  Notation SFACT mm := (S = D \/ (bytes_at usegs mm S (u32s ss) /\ (S + 4 * ls <= D \/ D + 4 * ld <= S))).
  (* [comment removed for export] *)
  Notation DINV mm ds := (u32arr usegs mm D ds /\ Z.of_nat (length ds) = ld /\ same_from (Z.to_nat dl) ds ds0
                          /\ munch W m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -48)).

  Ltac mla_dinv := mla_dinv_tac D dl ds0 ld m lo sp.
  Ltac mla_ret := mla_ret_tac D dl ds0 m.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma excess_walk : forall (k : nat) (i : Z) (ds : list word) (mm : mem)
      (xt0 xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xa0 xa3 xa5 xa6 xa7 xt3 xt4 xt5 : word) (wp wc : word),
    Z.to_nat (dl - i) = k -> slm <= i < dl ->
    wp = Z_to_bv 64 (D + 4 * i) -> wc = Z_to_bv 64 (i - dl) ->
    DINV mm ds -> FRAME mm ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 wc (Z_to_bv 64 (-5)) xa3 (Z_to_bv 64 0)
             xa5 xa6 xa7 xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 wp)
          F (Z_to_bv 64 0x23cc4) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ds mm xt0 xt1 xt2 xs0 xs1 xs2 xs3 xs4 xs5 xa0 xa3 xa5 xa6 xa7 xt3 xt4 xt5 wp wc Hk Hi -> ->
      (HX & LX & FX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hi|].
    lx_run_tac (PLAN [0x23cc4] [] 40%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23cc4) _ _ _ _) =>
             mla_dinv; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => mla_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section WithB.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Lemma x1_walk : forall (k : nat) (i : Z) (ds : list word) (mm : mem)
        (xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 xt6 : word) (wps wpd wn : word),
      Z.to_nat (slm - i) = k -> 0 <= i < slm ->
      wps = Z_to_bv 64 (S + 4 * i) -> wpd = Z_to_bv 64 (D + 4 * i) -> wn = Z_to_bv 64 (slm - i) ->
      DINV mm ds -> SFACT mm -> FRAME mm ->
      evt usegs POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 0) wn (Z_to_bv 64 0) xs0 xs1 xa0
               (Z_to_bv 64 dl) wps (Z_to_bv 64 sl) wpd wpd (Z_to_bv 64 slm) xa7 xs2 xs3 xs4 xs5
               s6 s7 s8 s9 s10 s11 (Z_to_bv 64 5) (Z_to_bv 64 (-5)) wps xt6)
            F (Z_to_bv 64 0x23c38) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ds mm xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 xt6 wps wpd wn Hk Hi -> -> ->
        (HX & LX & FX & MU & WM & MI & ST) AS FR; [exfalso; xlia Hk Hi|].
      assert (SP : 0 < S) by xlia NZS Hi Hslm.
      destruct AS as [ES|[HS DIS]]; [rewrite ES in IH |- * |].
      all: lx_run_tac (PLAN [0x23c38; 0x23cc4] [] 80%N); lx_tree.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23c38) _ _ _ _) =>
               mla_dinv; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | exact DI' | mla_sfact | assumption]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23cc4) _ _ _ _) =>
               mla_dinv; eapply (excess_walk (Z.to_nat (dl - slm)) slm); [reflexivity | klia | f_equal; klia | f_equal; klia | exact DI' | assumption]
           | |- _ => mla_ret
           end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Lemma x8_walk : forall (k : nat) (j n8 : Z) (ds : list word) (mm : mem)
        (xt2 xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 : word) (wps wpd wn : word),
      Z.to_nat (n8 - j) = k -> 0 <= j < n8 -> 8 * n8 <= slm < 8 * n8 + 8 ->
      wps = Z_to_bv 64 (S + 32 * j) -> wpd = Z_to_bv 64 (D + 32 * j) -> wn = Z_to_bv 64 (n8 - j) ->
      DINV mm ds -> SFACT mm -> FRAME mm ->
      evt usegs POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp wps wn xt2 xs0 xs1 xa0
               (Z_to_bv 64 dl) wps (Z_to_bv 64 sl) wpd wpd (Z_to_bv 64 slm) xa7 xs2 xs3 xs4 xs5
               s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4) (Z_to_bv 64 (-5)))
            F (Z_to_bv 64 0x23a00) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros j n8 ds mm xt2 xs0 xs1 xa0 xa7 xs2 xs3 xs4 xs5 wps wpd wn Hk Hj Hn8 -> -> ->
        (HX & LX & FX & MU & WM & MI & ST) AS FR; [exfalso; xlia Hk Hj|].
      assert (SP : 0 < S) by xlia NZS Hj Hn8 Hslm.
      destruct AS as [ES|[HS DIS]]; [rewrite ES in IH |- * |].
      all: lx_run_tac (PLAN [0x23a00; 0x23c38; 0x23cc4] [] 300%N); lx_tree.
      all: mla_drop_vals.
      all: lazymatch goal with
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23a00) _ _ _ _) =>
               mla_dinv; eapply (IH (j + 1) n8); [xlia Hk Hj | klia | exact Hn8 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | exact DI'
                                       | mla_sfact | assumption]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23c38) _ _ _ _) =>
               rewrite land_7_mod' in *; mla_dinv;
               eapply (x1_walk (Z.to_nat (slm - 8 * n8)) (8 * n8)); [reflexivity | klia | f_equal; klia | f_equal; klia | f_equal; klia | exact DI'
                                       | mla_sfact | assumption]
           | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23cc4) _ _ _ _) =>
               rewrite land_7_mod' in *; mla_dinv;
               eapply (excess_walk (Z.to_nat (dl - slm)) slm); [reflexivity | klia | f_equal; klia | f_equal; klia | exact DI' | assumption]
           | |- _ => mla_ret
           end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithB.
End Walk.

Local Ltac mla_main_side da :=
  first [ eassumption | reflexivity | (f_equal; klia)
        | (destruct da as [[? ?]|?]; [left; assumption | right; split; [eassumption | assumption]])
        | klia ].
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?M36024859108.65M37530971075.65M41998576579.65M47656824824.6500000?00M00[00nS1D2ds3NZD4DTOPS2dl2sl3Hdl2H2S2dl2sl3Hsl2H2S2dl2sl2ds2ss2LX2LS". (* [comment removed for export] *)
Lemma U_mpi_core_mla_spec : mpi_core_mla_stmt usegs U_MPI_CORE_MLA.
Proof.
  unfold mpi_core_mla_stmt, U_MPI_CORE_MLA.
  intros until ss. intros HX HS Hdl Hsl LX LS DA ALD ALS NZD NZS DTOP STOP ST LO SPA SX SSX MI RA -> -> -> ->.
  unfold MPI_CORE_MLA_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as DB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (AS : S = D \/ (bytes_at usegs m S (u32s ss) /\ (S + 4 * Z.of_nat (length ss) <= D \/ D + 4 * Z.of_nat (length ds) <= S))).
  { destruct DA as [[ES _]|DIS]; [left; exact ES | right; split; [exact HS | exact DIS]]. }
  (* [comment removed for export] *)
  pose proof (munch_refl [(D, D + 4 * dl); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0.
  change (2 ^ Z.of_N 64) with (2^64) in SPR.
  carve_frame 48%nat ST; lxp_split_frame [8;8;8;8;8;8]%nat.
  lx_run_tac (PLAN [0x23a00; 0x23c38; 0x23cc4] [] 200%N); lx_tree.
  all: lx_gc; try lx_same_mem.
  all: pose proof (same_from_refl (Z.to_nat dl) ds) as FX0.
  all: assert (L00 : Z.of_nat (length ds) = Z.of_nat (length ds)) by reflexivity.
  all: repeat (rewrite land_7_mod' in * ); repeat (rewrite Z.shiftr_div_pow2 in * by xlia0); change (2^3) with 8 in *.
  all: lazymatch goal with
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v6) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x23a00) _ _ _ _) =>
      mla_dinv_tac D dl ds (Z.of_nat (length ds)) m lo sp;
      eapply x8_walk with (S := S) (sl := sl) (slm := v6) (ld := Z.of_nat (length ds)) (ls := Z.of_nat (length ss)) (ds0 := ds) (ss := ss)
                          (k := Z.to_nat (v6 / 8 - 0)) (j := 0) (n8 := v6 / 8);
      mla_main_side DA
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v6) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x23c38) _ _ _ _) =>
      mla_dinv_tac D dl ds (Z.of_nat (length ds)) m lo sp;
      eapply x1_walk with (S := S) (sl := sl) (slm := v6) (ld := Z.of_nat (length ds)) (ls := Z.of_nat (length ss)) (ds0 := ds) (ss := ss)
                          (k := Z.to_nat (v6 - 0)) (i := 0);
      mla_main_side DA
  | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v6) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x23cc4) _ _ _ _) =>
      mla_dinv_tac D dl ds (Z.of_nat (length ds)) m lo sp;
      eapply excess_walk with (S := S) (sl := sl) (slm := v6) (ld := Z.of_nat (length ds)) (ls := Z.of_nat (length ss)) (ds0 := ds) (ss := ss)
                          (k := Z.to_nat (dl - v6)) (i := v6);
      mla_main_side DA
  | |- _ => mla_ret_tac D dl ds m
  end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mla_window_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A i dl : Z) (ws : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lws',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O19.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.(11.O6.(12.+4.O5.))(11.(11.O6.(12.+4.O5.))(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O17.)$15.)(14.&40.O17.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O19.O1.R2.)(5.(18.O19.R2.)(5.(19.O19.R2.O6.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(31.(2.&40.)(1=.O5.)R1.)(31.(2.&40.)(1=.O5.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.(11.O5.O4.))R1.)(1<.(2.&40.)(1=.(11.O5.O4.))O3.))(1>.O19.R2.O2.(14.&40.O17.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L18832045976.92L19724688908.67L22072888816.67L31541875041.92L32990620730.92L33572284922.67L33574382520.92L44042767527.64L4447919927.91 L46086150197.92L47039822340.92L47769615620.67L51260582390.67L5644963610.67 L60613163719.67L64560512919.9200000M00n01X02<02g03D03h04L05Z06:06^07T08b09E09b0:MS2ra2sp1A1i1S2ws2ss2LP3ds'2LDS2ra2sp1A1i1S2ws2ss2Hi3ALA3NZA2LPS2ra2sp1A1i2dl1S2ws2ss3Hdl2LX3NZA2AT2AB2LPS2ra2sp1A1i2dl1S2ws2ss3NZA2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss3Hdl2LX3NZA2LP3ds'2LDS2ra2sp1A1i1S2ws2ss2Hi3NZA2LPS2ra2sp1A1i1S2ws2ss2Hi3NZA2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss2Hi3Hdl2LX3NZAS2ra2sp1A1i2dl1S2lo2ws2ss2Hi3Hdl2LX3DIS3ALA3ALS3NZA2LO3SPA2SX3SSX2AB2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss3NZA2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss2Hi3Hdl2LX3DIS3ALA3ALS3NZA2AB2LPS2ra2sp1A1i2dl1S2sl2lo2ws2ss2Hi3Hdl3Hsl2LX2LS3DIS3ALA3ALS3NZA3SPA2SX3SSX2AB2LPS2ra2sp1A1i2dl1S2ws2ss2Hi2LX3NZA2LPS2ra2sp1A1i1S2ws2ss2Hi3NZA2LPS2ra2sp1A1i2dl1S2ws2ss2Hi3Hdl3NZA2LP3ds'2LD". (* [comment removed for export] *)
Lemma mla_window : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mla ()) "Psegs,(4.$32.)PENTRY,$?.P,(33.R2.R1.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$?.Pi,$?.Pdl,$?.PS,$?.Psl,$?.Plo,$?.Pws,(4.(2.&40.))Pss,(4.(2.&40.))P,(19.R2=.R9.R8.R2.)P,(20.R2>.R:.R6.(21.R2.))P,(22.=R9.)P,(5.(22.=R9.)(22.R9.+2710.))P,(5.(22.=R8.)(22.R8.+2710.))P,(22.(11.R<.R;.)(23.(1;.(2.&40.)R7.)))P,(22.R:.(23.(1;.(2.&40.)R7.)))P,(24.(22.(11.R<.(12.+4.(23.(1;.(2.&40.)R8.))))R?.)(22.(11.R?.(12.+4.(23.(1;.(2.&40.)R9.))))R<.))P,(6.$?.(25.R10.+4.)=)P,(6.$?.(25.R>.+4.)=)P,(26.=R12.)P,(24.(6.$?.R?.=)(26.=R10.))P,(26.(11.R14.(12.+4.(23.(1;.(2.&40.)R>.))))(27.+2.+40.))P,(26.(11.R12.(12.+4.(23.(1;.(2.&40.)R>.))))(27.+2.+40.))P,(1>.R3;.R17.R11.(14.&40.R37.))P,(22.R12.(13.(14.&40.R38.)$15.))P,(6.$?.(25.(14.&40.R39.)+10.)=)P,(24.(22.(11.R19.(12.+4.(23.(1;.(2.&40.)R13.))))R14.)(22.(14.&40.R3:.)R19.))P,(24.(22.(11.R17.(12.+4.(23.(1;.(2.&40.)R13.))))R15.)(22.(14.&40.R3;.)R17.))P,(18.R40.R1<.)P,(6.$?.(25.(14.&40.R3>.)+2.)=)P,(6.(2.&40.)R36.(28.&40.(11.R1=.(12.+4.R1<.))))P,(6.(2.&40.)R36.(28.&40.R1<.))P,(6.(2.&40.)R36.(28.&40.R1<.))P,(6.(2.&40.)R36.(28.&40.R1<.))(29.R46.(34.R46.R43.R42.R41.R40.R3<.R3;.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.R21.R20.R1?.R1;.R1<.R22.)(7.(8.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R24.(28.&40.R45.)R23.(:.(2.&40.))R22.(;.R46.)))")
(* [comment removed for export] *).
Proof.
  intros segs ENTRY SPEC. intros until ss. intros HX HS Hi Hdl Hsl LX LS DIS ALA ALS NZA NZS AT ST_ ST LO SPA SX SSX MI RA -> -> -> ->.
  pose proof (u32arr_bound _ _ _ _ HX) as AB.
  pose proof (firstn_skipn (Z.to_nat i) ws) as EY. symmetry in EY.
  assert (LP : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length; lia).
  pose proof HX as HX0. rewrite EY in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi. rewrite LP in HXhi.
  replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) in HXhi by lia.
  eapply evt_mono.
  { eapply (SPEC ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (A + 4 * i) dl S sl lo (skipn (Z.to_nat i) ws) ss);
        try reflexivity; try eassumption; try (rewrite ?skipn_length; lia). }
  intros ms' PO. unfold mpi_core_mla_post in PO. unfold mla_window_post.
  flat constr:(PO) 25%nat. flclear PO. intros xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 m' ds' -> MU WM MI' HD LD SK ST'.
  flexi 16%nat. exists (firstn (Z.to_nat i) ws ++ ds'). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  assert (HXlo' : u32arr segs m' A (firstn (Z.to_nat i) ws)).
  { eapply u32arr_transport; [exact HXlo | exact MU | exact WM |]. cbn [disjoint_from]. rewrite LP. unfold MPI_CORE_MLA_STACK in *. lia. }
  split; [|split; [|split; [|split]]].
  - apply u32arr_app. split; [exact HXlo'|]. rewrite LP. replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) by lia. exact HD.
  - rewrite app_length, LD, LP, skipn_length. lia.
  - rewrite firstn_app, LP, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by lia. reflexivity.
  - replace (Z.to_nat (i + dl)) with (Z.to_nat i + Z.to_nat dl)%nat by lia.
    rewrite skipn_app, LP. replace (Z.to_nat i + Z.to_nat dl - Z.to_nat i)%nat with (Z.to_nat dl) by lia.
    rewrite skipn_all2 by (rewrite LP; lia). cbn [app]. rewrite SK, skipn_skipn. f_equal. lia.
  - exact ST'.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
