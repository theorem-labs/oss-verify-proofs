(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Set Printing Width 200.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0017071b8acad48e 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P0049fef51f451f0e 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P004bb833c45781f7 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P00b1ff647609557e 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P00c56ca7b5efbe26 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P010ce683ebb7a476 0 4 0 1 58 1 64 1 65 1P012a4c933d7cf7d9 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P01309fe256c3c766 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P016c9a7eb2965cb0 0 4 0 1 64 1 70 1 71 1P01869a3cd410ff63 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P019dce1caabbbb93 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P019de4af0d1adcf3 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P01b2db625878cb77 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P01c2507db4b08015 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P01d50b7d3e03c00f 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P021a89835a5e871a 0 4 0 1 58 1 64 1 65 1P02233ca8415e2c02 0 4 0 1 70 1 76 1 77 1P022776f977ee5f09 0 5 1 16 59 16 60 16 65 16 66 16P0234ad2afcae0756 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P029de5f338755420 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P02bf3fc48897999e 0 5 1 16 65 16 66 16 71 16 72 16P02e7a281159f7288 0 4 0 1 70 1 76 1 77 1P03029d4dc4a496e6 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P03423c2bc663b092 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P036f0509f75ac03b 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P03a1c0cc2ade9b23 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P03dfa1ba0628d155 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P041d5ca66277db67 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P042f00411e047775 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P04584680e3510514 0 5 1 16 65 16 66 16 71 16 72 16P047bb19ebea94262 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P04ac32d7aeab8fba 0 4 0 1 58 1 64 1 65 1P04b9452efa2d4e88 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P050c810ac2c01675 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0514d1ad4ab6d8b0 0 5 1 16 73 16 74 16 79 16 80 16P051e32efee3a4767 0 4 0 1 64 1 70 1 71 1P05504f5004aac790 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P05590e246f93f5ac 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0573c2cd5346e50c 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P0574052aebc30bc8 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P05823befcde3dcc7 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0582fb8f46e5c77b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P05f7bbab3357b907 0 5 1 16 59 16 60 16 65 16 66 16P06203180197e5518 0 4 0 1 72 1 78 1 79 1P06699e43dbb5b38a 0 4 0 1 58 1 64 1 65 1P06700b6590efc8b0 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0683b649afcd741e 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P06964c7089e47e37 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P06b62869232818d7 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P06efd38c5be4aad1 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P06fc4c44a1cf9ad4 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P06fe044e5dcf0cca 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P070238c4ca8441ba 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P070e630317a37d23 0 4 0 1 58 1 64 1 65 1P0731fcef9ddf8234 0 4 0 1 58 1 64 1 65 1P07a2a5e3ae0e387a 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P07b13b1d6a451eee 0 4 0 1 64 1 70 1 71 1P07e89903c785ef4a 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P08254f070edaaae3 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0893bbcbc3540e96 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0894c290a6067364 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P08a296b8a6901739 0 4 0 1 64 1 70 1 71 1P08c489007f967b02 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P0922ef7fae14b0b0 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P097a37de8e8edba3 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P0981a68bf088b5e0 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P0982f7cd56a647bc 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P09e075ca7bb370d2 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P09e91bcf3dd82bb1 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P09f471bc78447036 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0a498dc0affc26dc 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0a81ace915001e16 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P0aab9918ad293648 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0abdb3e0247e5e62 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P0af3396b6b5828a7 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P0af63538786dd9b0 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P0b2b921ce92ba6cc 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0b3c7fc2d01b5479 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0b3f89947d556bf8 0 5 1 16 59 16 60 16 65 16 66 16P0b45c5f1ae9d62ab 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P0ba1a2cd3d5ce53a 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P0bbd9c8a735ca583 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0bd88fb8123a2cd4 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P0be835ba11a24290 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P0bf03802471c22c7 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0c01ac9f4f9d9b53 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P0c0a225e8d4543d8 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0c0f6d45e2d76f77 0 4 0 1 58 1 64 1 65 1P0c4a841bb6553318 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0c534517dc0947d1 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0c62dbbd8fe1a352 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0c714d94ce740dea 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0cad694c2d76bd07 0 4 0 1 58 1 64 1 65 1P0cade3445cef0e61 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0cdb0afe460ffe83 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P0d15a1fb881c675d 0 4 0 1 72 1 78 1 79 1P0ddc30cd11cf270e 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0de02baa7d5bda10 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0df8f2ade9318a7a 0 4 0 1 70 1 76 1 77 1P0dfb103e3313861d 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P0e3036b2e5b82c2f 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P0e46e3ea31e4ce84 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P0e69451e9d2acdfc 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P0eacd43390355016 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P0ec58dc9f9ec27c6 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0ec8d31fa37c8484 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0ee94ffa63bafaca 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P0f1fa7d0ecd604d5 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0f2c676b27ddcc3f 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0f405b1fef713a0f 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0f998c99630680d7 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P0fa3e750367e2557 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P0fc96aed5eb8326b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P102fea7eeabb4bbf 0 4 0 1 64 1 70 1 71 1P1047ef44afc5a66a 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P10800919d53d80d4 0 4 0 1 58 1 64 1 65 1P108244292eb8c0e5 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P1092dae431b9a376 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1093b0c36bbc78a0 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P10eaf8802dc0a47c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P10fccb74c519774c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P111dc76eee852f0f 0 4 0 1 58 1 64 1 65 1P111fb0c9dbb94b20 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P112445a9ffc8e1be 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P114f40ea434654e0 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P115e9353f387927b 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P11730d0617c801fd 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P11995b7d9a45307c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P11a28b3259efaac3 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P11d1b0b44d7e3135 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P11ecd02aa22661b8 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P12049dc0db996e13 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1211809049115967 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P121878bdd4497241 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1292eb0acb0d8ea2 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P12aaa5498649c467 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P12b1f8c06f63405f 0 4 0 1 72 1 78 1 79 1P12c0c02a0e270e90 0 4 0 1 58 1 64 1 65 1P1300e1a1c12007b0 0 4 0 1 70 1 76 1 77 1P13112d03f0d6626f 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P13271f0048842800 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1332ad72b2988e3b 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P13332848f8a4abab 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P137c08ae33b5e03d 0 4 0 1 72 1 78 1 79 1P13a94629fcaa5de8 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P13ab6ed7d8199943 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P13c409b42b0e1285 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P13ec03f3527b6ee3 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P141f7c1a493677bb 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P145924df130fe5d1 0 4 0 1 58 1 64 1 65 1P147092648653e7c8 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P14ad7ba2ed3f50b6 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P151cb779c1c79679 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P156cd978cdfc658e 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P158c5cff5b3004df 0 4 0 1 64 1 70 1 71 1P15baaea04c10507c 0 4 0 1 58 1 64 1 65 1P15f7dc30d9768292 0 4 0 1 72 1 78 1 79 1P16068758ad88eaec 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P166bd74cdfc41c42 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P16a0d05aaa92716b 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P16ee12d7a0b23357 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1708e8ca4f40d55a 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P170e2d433a9be977 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P172f2306bf1a6000 0 4 0 1 70 1 76 1 77 1P173c9d20f2b762ae 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P173df2022a395c32 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P176e6d13bbcaadb1 0 4 0 1 70 1 76 1 77 1P179279677c8e6c0d 0 4 0 1 64 1 70 1 71 1P17c5e87dcf40aa1f 0 5 1 16 59 16 60 16 65 16 66 16P17d899555a7078b3 0 4 0 1 58 1 64 1 65 1P17d993defeea2528 0 4 0 1 58 1 64 1 65 1P180f87de141288c8 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P182d393a17c70864 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1839b2b0f36a7237 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P185011b6e6975e3f 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P185f33c5c7d126bc 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P18bcddb4b2d22562 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P18ca2b19889ca44f 0 4 0 1 58 1 64 1 65 1P19093ee4f27202bc 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P19b22f3c803ac1cf 0 4 0 1 58 1 64 1 65 1P19c3ec2f3b1e4029 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P19d4de510af1ffe5 0 4 0 1 58 1 64 1 65 1P19eba814fd1e70e5 0 4 0 1 72 1 78 1 79 1P19f90a6bfbc97321 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P19fa0257ad0bf784 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P1a09d7870a910b32 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1a5638d65849aab7 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P1ab6a7ac5bff0495 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1ad7fc73bcaf39b7 0 4 0 1 70 1 76 1 77 1P1ade40870935e6cf 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1adffab789ce7ccc 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1b57684d6167fbc2 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P1b65d1efa98b1f4c 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P1b7a414d4d168de5 0 5 1 16 59 16 60 16 65 16 66 16P1b905d3eb3e5ab02 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P1bd6b180e2a0f458 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1bdc08966f05a57f 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P1c9cd4cdb48fe33d 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P1c9d62e2f1a8bec1 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1c9fecf5d040363e 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1ca683b6cb200965 1 1 16 2 0 1 77 1 4 71 1 72 1 78 1 79 16P1cb9b4307349c359 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1d0395e2f9670f7b 0 4 0 1 58 1 64 1 65 1P1d216106c8d2fdde 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1d2587639ce506f3 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P1d2adfdf8afffba2 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1d510347d345b6fb 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1d603b890bed9b9f 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1d6cef0231b6ed08 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1dd5755615217572 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1ddf34d4b73c4e55 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1ddf4ba93f103ca3 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P1de20f035cfbcf69 0 4 0 1 70 1 76 1 77 1P1de2bac74be189c1 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P1dfe9238df2b0ca6 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P1e631759e296e57c 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1e95d6ab3ea9e4d2 0 5 1 16 65 16 66 16 71 16 72 16P1ea2d4840484d133 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1eb100f89d351cea 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1ebc91eb099168df 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P1ecd1fa1e74725a3 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P1f7add23789794c4 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1f96f11a95425aca 0 4 0 1 70 1 76 1 77 1P1fa60b27fa943751 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1fba9e6f94bbc077 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P1ff64a23ef1dbf79 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P20241fadfee3c9b6 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P204f16cb48b35a3e 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P205308952489472e 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P20575fa36601a812 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P206026d10ece7567 0 4 0 1 58 1 64 1 65 1P2064ab8bf41edbff 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2096fa47d59dc3af 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P20a33062fba9b1f2 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P20a38b634ec5116b 0 4 0 1 64 1 70 1 71 1P20b46a74b2a7ad60 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P20db2992821ed0d6 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P20e3eb0ca33d092a 0 4 0 1 64 1 70 1 71 1P21056d05e7231c09 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P211522937230cd5f 0 4 0 1 58 1 64 1 65 1P215c76f3072bb1cb 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P219ab13e8c4f5350 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P21a0df3626bb5cbb 0 4 0 1 70 1 76 1 77 1P21f8d16bcc30486e 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2219ce13a2ec6036 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2221fbacfa596b06 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P225a5c3c579be490 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P225aac597a999d41 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2262ab41a61d9fcc 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2286009aef88b5f1 0 4 0 1 70 1 76 1 77 1P22893852dd167594 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P228a4db0076649ad 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P22ba32a9ed38bad2 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P22c8edccc2bc329b 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P22e6be9fb9491914 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P2359233c319daa0f 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2376cf9d21be2e7c 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P237910575454510c 0 4 0 1 58 1 64 1 65 1P237de40ab69b8560 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P238b9e552a14178e 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P239649beafea5326 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P23a952a0e2e6ab1f 0 4 0 1 64 1 70 1 71 1P23cbc60be98a1ef5 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P23ced92103fc8b10 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P23d63ee0861c9eb8 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P23e9c2d3ce7c94b4 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P24016d24e1d29228 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2405dcff3adf72ac 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P2470574be21b5642 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P24b35dfd36a39285 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P24b45e06c1b1e6df 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P24c23974334a4276 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P24d3daf0d4a39688 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P24f6d1a015a5f63a 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P2501a0a7b6f75015 0 4 0 1 70 1 76 1 77 1P250853124dd9ca58 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P255365c8b2e6179b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P25a1069a8efe18c6 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P25d5870ecac4c1b5 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P25d970c5de106d10 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P25e847e310222db1 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P2626680e6e6a9b7c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P26310af385b55603 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P266621f5271acf6f 0 4 0 1 64 1 70 1 71 1P26d1ce6c467d78a7 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P26f4ff11c3e67885 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P26f594e283134e61 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P270ccff9223550ad 0 5 1 16 73 16 74 16 79 16 80 16P273bfdc1986d0c99 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P27609a5a4ea6e97b 0 4 0 1 58 1 64 1 65 1P278915a61d536b14 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P27af2de3fb7f2468 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P27b6226b6eb0b7d8 0 4 0 1 70 1 76 1 77 1P27b720b5cdbf746a 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P27d1628bde2b327c 0 4 0 1 58 1 64 1 65 1P27e2e699adcd967c 0 4 0 1 58 1 64 1 65 1P27eae9ee48adad16 0 4 0 1 72 1 78 1 79 1P27fec1d2837cf514 0 5 1 16 59 16 60 16 65 16 66 16P280af3cf6bf3c7e3 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P2819be5932c858c7 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P2842a4375c8db2ce 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2850e2bb192288d9 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P291fece93a61364c 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P294933ea639f3df0 0 4 0 1 70 1 76 1 77 1P295e7ba116fc97de 0 4 0 1 64 1 70 1 71 1P29a211cc465160ea 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P29ab04eb1905d1e3 0 5 1 16 65 16 66 16 71 16 72 16P29bd91b3a9f0f080 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P2a3d81dc3ae51fa1 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P2a6a2f30052670df 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2a8db6e01a7699dc 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P2acb3ff6bfcdb19e 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2ae8815c40ac9eb9 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2b06ddb0dfed415d 0 4 0 1 64 1 70 1 71 1P2b389ec03c401cda 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2b3900f2ceb6c864 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P2bdd72c75f40befd 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2c101f09dfe75b43 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2c5e2d8d29b297d1 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2c903b12b5fce27d 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2c94ad2b6f78a879 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2ceb772cc0853285 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2d440336040f6587 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P2d47b2176fc8e94c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2df7ed44f494680d 0 4 0 1 58 1 64 1 65 1P2e06dc794bbde44f 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2e1aa82a79f9b0c0 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2e2f026f5be793c3 0 5 1 16 73 16 74 16 79 16 80 16P2e390f3c178dd39f 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2e3f6fcd5cb0e39f 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2ecf9fcf1d5678cd 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P2eeb534390f1a32f 0 4 0 1 58 1 64 1 65 1P2f0832bc62d8aa70 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P2f3496b18742d0cf 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P2f36ff1fd821334e 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P2f4bf764350a35f5 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2f5047eea9468819 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P2f52c24b4bd895a0 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P2f56ec05b7c5656b 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P2f848bdb2300458b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P2fb76f7307c3bac3 0 4 0 1 64 1 70 1 71 1P2fd82c4a3b4c29fa 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P30182f2447dd679d 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P3057fb5f20e5b9be 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P30a1e065811af492 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P31408b3f299f13a9 0 5 1 16 59 16 60 16 65 16 66 16P316aa7c23daf7e68 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P317dce6a76c4fb82 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P318a02558fadfc9d 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P319c540f5db18662 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P31a3b2ca41969741 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P31afd3b818d6ea7d 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P31dbb0095cf46fd7 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P31dd430de513f42f 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P31f70e54ad63d612 0 4 0 1 70 1 76 1 77 1P32298562d6eb8bd2 0 4 0 1 70 1 76 1 77 1P326e0084b6d2ad70 0 5 1 16 59 16 60 16 65 16 66 16P334eea479559ee72 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P338746fd2368fc56 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P339763c3fb7ca3de 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P33c9cf980ea56cf1 0 4 0 1 58 1 64 1 65 1P33cd5c6d581edfee 0 4 0 1 58 1 64 1 65 1P33ddd1d2c77764e9 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P33f39bd62690d6b3 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P33ffc4eee8c887ee 0 4 0 1 70 1 76 1 77 1P341b557c2ac33357 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P344802b898f0454f 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P34765391a72d7b9c 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P34b1444e8c454082 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P34b90bce12538e1d 0 4 0 1 64 1 70 1 71 1P34df37f05bbea7d8 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P34e410f6f639804a 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P35193363c330306b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P354db74a443b18e2 0 4 0 1 70 1 76 1 77 1P355734f9d38a55a2 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P355b60352be5160b 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P35705cf95719151b 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3571ee3e50924db4 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P35b9c1dd233df9bc 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P35df0b92fe720044 0 5 1 16 59 16 60 16 65 16 66 16P35efef8fe159df4c 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P36141574ab723de6 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P361c42c1b11b4952 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P36330b3de0d0158f 0 4 0 1 58 1 64 1 65 1P363f783b778e165a 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P36b165a61eeab3ee 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P36b60a32876eaa43 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P36bcf80e81eeadf9 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P36c163f40b62364a 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P36cae8ffffd9ddd5 0 4 0 1 58 1 64 1 65 1P36cd6e6eb80071d0 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P36e125b14eb26ba2 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P36ffea5be0a06d3b 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P375fd2e1b8dc181a 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3763779c7c56cb28 1 1 16 2 0 1 77 1 4 71 1 72 1 78 1 79 16P378d3e8c26a67652 1 2 16 2 0 1 77 1 16 2 1 1 78 1 2 79 1 80 1P3795d30f57762509 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P37b67b751d7894a3 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P37bf50429bd37c9f 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P37ef16958f19d711 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P382f7938e7681df4 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P38396418994f584d 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P383aa44e91505075 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P383c1702b5e6fd64 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P38510c4f2ab9e2a3 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P390c08a81b3efa71 0 4 0 1 58 1 64 1 65 1P3914340a4f263d63 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P393236a4d6297ac6 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P395f15412faa5f5d 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P396bd415aa0fa88e 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P398185c4a40aaa80 0 4 0 1 64 1 70 1 71 1P39bc16ef83ecc929 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P3a0b0a4a060b4dca 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P3a7d063d62527b1a 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P3a7f80fa4808ebb8 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3a810af3c33253dc 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3ac17f744e8d85dd 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P3b447a9ed7d2c6db 0 4 0 1 70 1 76 1 77 1P3b860599e569087f 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P3be1620d20632873 0 5 1 16 59 16 60 16 65 16 66 16P3c1706ffad69f455 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P3c1d9cface35a031 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3c44582786860f26 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P3ca0a057035dd293 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P3ca94182db9f0723 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3cca61bb59ec2fcd 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3cfedc908863abd1 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P3d59383d3b8461ac 1 1 16 2 0 1 78 1 4 72 1 73 1 79 1 80 16P3db00dca4965b987 0 4 0 1 58 1 64 1 65 1P3db8aabde15af74c 1 2 16 2 0 1 66 1 16 2 1 1 65 1 2 67 1 68 1P3e2508a43b3cad2e 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P3e2c5baa57b708f8 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P3e45ecf98463d833 0 4 0 1 58 1 64 1 65 1P3e53880178a86434 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3e736c21c5a9e42e 0 4 0 1 58 1 64 1 65 1P3ebc930af9f3a621 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P3f1d0d87414bc415 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3f20d3b293f497b7 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P3f211b5943811677 1 1 16 2 0 1 64 1 4 58 1 59 1 65 1 66 16P3f2ac63954debcae 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P3f426954a78aab58 1 1 16 2 1 1 65 1 4 59 1 60 1 66 1 67 16P3f8fb9b0e9ece7b0 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16P3fce9229e183f79d 0 4 0 1 58 1 64 1 65 1P3fec4c9333efb1af 1 1 16 2 1 1 79 1 4 73 1 74 1 80 1 81 16P3fec66789c516f58 1 1 16 2 1 1 71 1 4 65 1 66 1 72 1 73 16N01561c24961f1771N01d33ecba35e8fd6N01fff709e4058682N02126dfabd52d999N026ab4430ff42b57N02e8b7cd74e71237N02f236e5dd95c636N038fb5fba179a4bcN03a6fdabaf307b59N04326863ee2724f6N044db8138397c4e9N054e279f331fac99N05a3582a760dda52N0613747f53da4742N06b7c1bd7df52524N06e6699ee4df5078N071185de33ba5574N0730fac0d8c350beN07490063f1aab0bdN078e4fca7c2f676dN08382c95e0ce750fN089ebcdc9746c1faN08ea1e3ca78338b4N08f2f8c61657243bN091e9e47ba36e0bbN09b606a28aa5d72dN09c67d4da47333a2N09e78a5d18e7c31dN0ab761f04120ae1eN0aee48f13aa3503dN0b125341014524e1N0b4f14a956253c9cN0b685364c1055020N0bcb023a73fd5627N0c04e16491897a2cN0c7dbaf46e7e2929N0cb04c90052e9023N0cce0d3ff0d1d597N0d75706a0dc74f1eN0d809ac02148c6d5N0df578568de54602N0e094684d988516aN0e44a6c704139730N0eb81b9da75ff044N0ee53db008f1268fN0f49b169a18f4e0fN0f737f36e367a31cN0f893fe8eba9598dN0fd7bb4bfca4357dN10352a410d2f4dc4N10524bbc136d7791N10b807ec8742faa8N10fc1b3005a0aee6N10fceb749d8da896N11005a97fa4c1fc5N113cd079ba77653cN113d8f085b229289N11797caebe36eac9N12200d2d25f71668N126270a98af09f9fN127723f24f53aeefN12e52dd894799865N133e1c802f558895N136b711b1a472234N13787420a2f5e590N1407a9c84a56e489N14293a6f3ed22881N148a73b38140896aN14cebdaf22f3deb4N150356fbbbdc6e23N154d9c4763e896ccN15e981869ae8fc60N16320e40a9d0745eN16880e3ce6dc7959N17cac62376a5aed1N1890df1fa3da2b01N19041f8eb4393019N1926421fb08004daN193b6d02a95a8686N197829dc01fe5830N1a0dd15d6e138dc7N1a29a3116d5644f4N1a50086058a264dcN1abafeb0fea2ac0bN1b5291d1cbb9bf3bN1bddf8b4de11ec06N1bf8828f0f738e06N1c1a2005a1868108N1c5725508e2a4b24N1c954097b98f8f99N1cde7bae62bd7db5N1cfcb225fe54e987N1e18c65d90ff1a96N1ee807007a69dea5N1ef078a1b5eca2b9N1f04b288822b945dN1fd02ee37e63470bN1feb7fb57bc264ebN204977bd44451ee5N2060ecfb173dbef2N2063847e458d6c2dN20c435662c47f0baN20dc699ed176507bN20dc6b8ba1903f1aN20f47f99b7c2b925N20f73b9220b08112N212c1e1ee82000f3N214e107f198d0533N219d255671765da0N21a0a7be65f98f8eN22134d5aa7ba60b7N221da86c663a0d11N22e01ca237efd276N2300d1569cf77629N23758a84b59c1b57N23c02d97c1a74c2eN246e99763697b3e5N24b90f5ef77fd301N24cb46602483412dN24d76cd60e8924abN251570cecd6e52fcN253a4243dbe3c1a5N25af4ecf365e7cdaN25f75462775e519eN260db9aca49abe63N2685f8d04f8f071cN2695987e204adcc2N269736e527047f7dN26994dda11425d2dN26f82f47dddebe92N2771fa500690e221N27746988c8383c9eN278994be10cc1b5eN27987d19c4d5a15cN2846a02dbf4b8766N289fd142e635cc6aN2918adadc201b530N2928e20c52ec1c2bN2947cb8281c60e71N29de9958eb913a17N2a00386711681e39N2a2fe5f3e2b591acN2aef60d78d7987efN2b6108d7254488c3N2bd2ede42019553dN2bf6ba7d4a4d3f74N2c615511201411abN2c922c3d44ba8582N2cb820cd05f3df96N2d887b5fe2f53d0aN2dbf723abd0508b7N2f576e27a4d53ca2N30476b67841649a0N308276ab6c84ba76N30cf2c77178bcc38N3191c8e30a931656N31bf5b074c6cb6f1N33fd7f62d7f1ab3cN341d54890b327794N359c57a43c60738cN35a3d4649af45242N35b7b9ff46a833eaN360219d58f7c0e13N363b61a3b88ee28eN36438df5b8139426N36e1eec895ae0a07N37762ebb69c28774N37c43e079d3e2c4fN37ed638d544dc043N38a071eaf3e76d02N3954743f3b476f9cN398d042fc804c83bN39e8b1050edebe1bN3a396bcfb84f1837N3b36d704e6dd50b6N3bbb8d332383fdccN3bf5472cff9f860aN3c2235a5ae644de4N3c5d28945166238dN3c5dc129b75c9caaN3d6dc0d5351615beN3d78da3a784ae8eeN3dcebd07b6bcca12N3dcee8834091365eN3de3a81b9daf7961N3ea0932e2159ccc6N3eee605ae747d522N3f1083efaa6a67bbN3f78beadb4a5d9bbN3f84c3c93b18577dN3f9fb9a1f34ae5c6N3fa03d1db1b2a2da"%lxh.
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
Ltac2 gd_tbl_A_unreg_globals () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_exit_lib.mapped"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.memset_sh_post"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.AGLOB_LO"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.AGLOB_HI"; "Walk.unreg_consts"; "Walk.iter_a_post"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Walk.iter_post"; "Walk.g_q"; "Walk.g_sz"; "Walk.g_kq"; "Walk.g_nm"; "Walk.g_md"; "Walk.g_dy"; "Walk.g_lc"; "Walk.g_odr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Walk.grec"; "Walk.table_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.ltb"; "Corelib.Init.Datatypes.bool"; "Walk.grec_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Peano.le"; "Walk.loop_post"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "grec"; "table_at"; "grec_ok"; "Corelib.Init.Datatypes.nat"; "Outer.unreg_got"; "unreg_consts"; "Stdlib.ZArith.BinInt.Z.modulo"; "Outer.module_dtor_post"; "table_img_b"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"].


Notation SB := 0x7fff8000 (only parsing).
(* [comment removed for export] *)
Notation SHLO := 0x7fffa000 (only parsing).   (* [comment removed for export] *)
Notation SHHI := 0x800d3000 (only parsing).   (* [comment removed for export] *)

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Record unreg_consts (m : mem) : Prop := {
    uc_inited : ro_cells asegs m 0x10a6d8 [C1 (Z_to_bv 8 1)];          (* [comment removed for export] *)
    uc_repglob : ro_cells asegs m 0x107210 [C4 (Z_to_bv 64 1)];        (* [comment removed for export] *)
    uc_sb : ro_cells asegs m 0x1099f8 [C8 (Z_to_bv 64 SB)];            (* [comment removed for export] *)
    uc_canpoison : ro_cells asegs m 0x10925c [C1 (Z_to_bv 8 1)];       (* [comment removed for export] *)
    uc_thresh : ro_cells asegs m 0x19b5a0 [C8 (Z_to_bv 64 0xffffffffffffffff)];   (* [comment removed for export] *)
    uc_memset : ro_cells asegs m 0x0f7cd0 [C8 (Z_to_bv 64 0x0eadc4)]  (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L17747144802.11L49165508254.11L61028786748.1100000300>00?S1xS1q2kq1x2HxS". (* [comment removed for export] *)
  Lemma shadow_range_aok : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pq,$0.Pkq,$0.P,(1.VCS,(2.+8.R2.)(2.+8.R1.))Px,$0.P,(3.(4.(5.+7???8000.R4.)R1.)(6.R1.(5.(5.+7???8000.R4.)R3.)))(7.VAL,VCS,R2.)")
(* [comment removed for export] *).
  Proof.
    intros q kq CR x Hx. right; left. exists (8 * (x - SB)). split.
    - apply CR. lia.
    - unfold shadow_of. rewrite ASB. rewrite Z.mul_comm, Z.div_mul by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition memset_sh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (S k : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Lms',$8.(9.(:.&40.)Lt0,(:.&40.)(9.(:.&40.)Lt1,(:.&40.)(9.(:.&40.)Lt2,(:.&40.)(9.(:.&40.)La1',(:.&40.)(9.(:.&40.)La2',(:.&40.)(9.(:.&40.)La3,(:.&40.)(9.(:.&40.)La4,(:.&40.)(9.(:.&40.)La5,(:.&40.)(9.(:.&40.)La6,(:.&40.)(9.(:.&40.)La7,(:.&40.)(9.(:.&40.)Lt3,(:.&40.)(9.(:.&40.)Lt4,(:.&40.)(9.(:.&40.)Lt5,(:.&40.)(9.(:.&40.)Lt6,(:.&40.)(9.P,(:.&40.)(;.(:.&8.))Lm',P,(:.&40.)(;.(:.&8.))(3.(<.$8.R10.(=.(>.O15.O14.O13.O12.R?.R>.R=.O11.O10.(?.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(10.O15.)O4.(11.(:.&40.))R1.(12.$13.)))(3.(14.(15.(16.$0.$0.)(17.$0.$0.O3.(5.O3.O2.))(18.(16.$0.$0.)))O1.R1.)(3.(19.$13.O1.R1.)(3.(1:.$13.R1.)(1;.R1.+7???:000.+800=3000.))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L18926354325.45L21280504788.72L22301625619.45L22699771039.71L22699771039.72L25607221340.47L31809857225.47L35195389389.45L35462506719.72L51852737711.68L57020438579.47L66925877906.45L66927942289.47L68075425904.68L68077641454.4500000100600=00G00Q00X00b00l01901:01;01B01I01J01KSS1q1yS1q3QLOS1q2kq1y1nS1q2kq1y1nS1q3QLOS1q2kq3QHIS1q2kq3QHIS1q2kq1y1l2l0SSS2kq2KQS2kq2KQSS". (* [comment removed for export] *)
  Lemma memset_sh_spec : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pra,(:.&40.)Psp,(:.&40.)Pgp,(:.&40.)Ptp,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Ps0,(:.&40.)Ps1,(:.&40.)Pa0,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Ps2,(:.&40.)Ps3,(:.&40.)Ps4,(:.&40.)Ps5,(:.&40.)Ps6,(:.&40.)Ps7,(:.&40.)Ps8,(:.&40.)Ps9,(:.&40.)Ps10,(:.&40.)Ps11,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)PF,(1<.&5.(:.&40.))Pfc,(:.&20.)Pm,P,(:.&40.)(;.(:.&8.))Pq,$0.Pkq,$0.P,(1;.R3.+7???:000.+800=3000.)P,(1:.$13.R4.)P,(1.VCS,(2.+8.R4.)(2.+8.R3.))P,(4.+2000.R5.)P,(4.=R5.)P,(4.(2.+8.(5.R7.R6.))+65?000.)P,(<.(:.&40.)R21.(?.&40.(5.+7???8000.R8.)))P,(<.(:.&40.)R21.(?.&40.=))P,(<.(:.&40.)R21.(?.&40.R9.))(1=.$13.VAL,VCS,(1>.R2=.R2<.R2;.R2:.R26.R25.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R>.R=.(5.+7???8000.R;.)R:.R<.)(=.(>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(?.&40.+>:=<4.)R=.(11.(:.&40.))R<.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros until kq. intros MP MI CR QLO KQ QHI -> -> ->.
    destruct (mapped_rw_slice m SHLO SHHI (SB + q) kq MP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk SH].
    eapply evtA_mono.
    - eapply (A_memset_evtA_aok AL CS IMG) with (S := SB + q) (k := kq) (v := 0) (junk := junk);
        [ exact SH | exact MI | apply shadow_range_aok; exact CR | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity ].
    - cbn beta. intros ms' PO. unfold memset_postZ in PO. destruct_exs PO. destruct PO as (E & MU & WM & MI' & ZS).
      unfold memset_sh_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
      eapply mapped_transport; [exact MP | exact MU | unfold AIMG_HI; lia | lia |].
      intros y Hy. destruct (Z_le_dec (SB + q) y); [destruct (Z_lt_dec y (SB + q + kq))|].
      + right. replace y with (SB + q + (y - (SB + q))) by lia. eapply rw_cells_mrd; [exact ZS | lia].
      + left. cbn. lia.
      + left. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Notation REGS ra s0 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 rec rem :=
    (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x19b528) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 2) (Z_to_bv 64 0x1db1b) (Z_to_bv 64 rec) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 0x107270)
         (Z_to_bv 64 0x0f7cd0) (Z_to_bv 64 0x1072b0) (Z_to_bv 64 0x1071f8) (Z_to_bv 64 0x1099f8) (Z_to_bv 64 rem)
         t3 t4 t5 t6) (only parsing).

  (* [comment removed for export] *)
  Definition iter_a_post (rec rem q kq : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Lms',$8.(9.(:.&40.)Lra,(:.&40.)(9.(:.&40.)Ls0,(:.&40.)(9.(:.&40.)Lt0,(:.&40.)(9.(:.&40.)Lt1,(:.&40.)(9.(:.&40.)Lt2,(:.&40.)(9.(:.&40.)La0,(:.&40.)(9.(:.&40.)La1,(:.&40.)(9.(:.&40.)La2,(:.&40.)(9.(:.&40.)La3,(:.&40.)(9.(:.&40.)La4,(:.&40.)(9.(:.&40.)La5,(:.&40.)(9.(:.&40.)La6,(:.&40.)(9.(:.&40.)La7,(:.&40.)(9.(:.&40.)Lt3,(:.&40.)(9.(:.&40.)Lt4,(:.&40.)(9.(:.&40.)Lt5,(:.&40.)(9.(:.&40.)Lt6,(:.&40.)(9.P,(:.&40.)(;.(:.&8.))Lm',P,(:.&40.)(;.(:.&8.))(3.(<.$8.R13.(=.(>.R12.Vsp,Vgp,Vtp,R10.R?.R>.R11.(?.&40.+19;528.)R=.R<.R;.R:.R9.R8.R7.R6.(?.&40.+2.)(?.&40.+1=;1;.)(?.&40.O5.)(?.&40.+2000000000000000.)(?.&40.+107270.)(?.&40.+?7<=0.)(?.&40.+1072;0.)(?.&40.+1071?8.)(?.&40.+1099?8.)(?.&40.O4.)R5.R4.R3.R2.)VF,(?.&40.+56204.)Vfc,(11.(:.&40.))R1.(12.$13.)))(3.(14.(15.(16.$0.$0.)(17.$0.$0.(5.+7???8000.O3.)(5.(5.+7???8000.O3.)O2.))(18.(16.$0.$0.)))O1.R1.)(3.(19.$13.O1.R1.)(3.(1:.$13.R1.)(1?.$13.R1.(5.+7???8000.O3.)(15.$20.(21.(22.O2.)(23.(:.&8.)(?.&8.=)(22.O2.)))(18.$20.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01N0?C7520491497.79 L1278623069.2  L13126487133.2 L1519956452.60 L19628677917.60L23019277985.60L24122673473.60L25607156699.60L26074541961.60L28923391757.60L29112965213.2 L31809791310.60L33080100625.60L34150196914.61L3478116370.60 L37196404897.0 L39120847666.61L41617534916.60L4418656093.2  L46546729053.2 L46548031261.3 L4804264189.60 L52067113769.60L53516898208.61L53518944813.60L57020505012.60L5750712013.60 L59577446157.60L59974601522.61L60199053024.60L61413967695.60L62715921776.61L63279041.61   L65501951249.60L66371815768.62L66927876374.60L6693134395.2  L7404291005.60 L8863336797.2  O20610402913.78O28468609121.78O52898638433.78O56814256225.78O59073424423.78O59390808545.78O61828543585.78O7520491497.79 P1291382330.78 P13130833722.78P29117532986.78P4421944378.78 P46551034682.78P46551811194.78P6681523036.79 P8867093050.78 Q10406819345.60Q11262829823.60Q11264876914.61Q12606627739.60Q12860591583.60Q13277010897.60Q15545019921.60Q22958496031.60Q24588101535.60Q24991937937.60Q28764365915.60Q28929487963.60Q35962998678.61Q35965012507.60Q43853485019.60Q46232625182.60Q50763803537.60Q50839566751.60Q51238672273.60Q52632458783.60Q5280907032.60 Q5301367889.60 Q53139064351.60Q53520163505.61Q53522310972.60Q58933674331.60Q61234319808.60Q63621165553.60Q63623181436.61Q64469161842.60Q65838732561.60Q65910205201.60Q66336949521.60Q67807997329.60Q706917851.60  Q9471003221.60 Q9473183704.61 Q9545243409.60 R66371815768.6200000100200300D00E00L00M00T00e00f00g01101201301901:01;01L01M01N01O01`01a01b01c01d01j01k01l02302@02G02L02M02N02U02V02W02X02Y02Z02[02\02]02^02_02`02j03403>03H03R03d03e03o04004904B04K04L04M04V04W04X04Y04b04k05<05M05V05W05`05a05b05c05l06506606@06J06S06d06e06f07707807A07B07K07T07e08608?08@FFFS1q2kq3QLO2KQ3QHIFS2kq2KQFS1q3QLOS1q2kq3QLO2KQ3QHISFS1q2kq3QHISSS1q2kqSSS1q2kq3QLO2KQ3QHIFFFS1q2kq3QLO2KQ3QHIFSSSS1q2kqSSS2kq2KQS1q2kq2KQ3QHIS2kq2KQS3recSFS2kq2KQFSFFFFFFFFFS1q2kq3QLOS1q2kq3QLOS1q2kq3QLOS1q2kq3QLOS1q2kq3QLOS3rec1q2kq3RHI3QLOFS1q2kq3QLOSS3rec3RLOS3rec3RLOS2AL4IMG'FSS2AL4IMG'FFSS2AL4IMG'S2AL4IMG'S2AL3rec3RHI4IMG'S2AL3rec3RHI4IMG'S2AL4IMG'FS2AL4IMG'FSFS3rec3RLOS2AL4IMG'FS2AL5ALWF'S2AL5ALWF'S2AL4IMG'S2AL3rec3RHI4IMG'FFS2AL3rec3RLO4IMG'SS2AL4IMG'SS2AL4IMG'S2AL4IMG'S2AL3rec3RLO4IMG'S2AL3rec3RLO4IMG'S2AL4IMG'F". (* [comment removed for export] *)
  Lemma unreg_iter_a : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pra,(:.&40.)Ps0,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa0,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)Pm,P,(:.&40.)(;.(:.&8.))Prec,$0.Prem,$0.Pq,$0.Px1,$0.Pkq,$0.Px3,$0.Px4,$0.Px5,$0.Px6,$0.Podr,$0.Pjunk,(24.(:.&8.))P,(25.$13.R<.R;.(15.$20.(26.(?.&40.(2.+8.R9.)))(15.$20.(26.(?.&40.R8.))(15.$20.(26.(?.&40.(2.+8.R7.)))(15.$20.(26.(?.&40.R6.))(15.$20.(26.(?.&40.R5.))(15.$20.(26.(?.&40.R4.))(15.$20.(26.(?.&40.R3.))(15.$20.(26.(?.&40.R2.))(18.$20.))))))))))P,(4.$27.R<.)P,(4.(5.R=.+40.)$28.)P,(4.+2000.R<.)P,(3.(4.+1.R;.)(4.R;.+1000.))P,(4.(2.+8.(5.R>.R<.))+65?000.)P,(1.VCS,(2.+8.R?.)(2.+8.R=.))P,(1?.$13.R13.(5.+7???8000.R10.)(15.$20.(21.(22.R>.)R8.)(18.$20.)))P,(29.R14.)P,(1:.$13.R15.)(1=.$13.VAL,VCS,(2:.R15.R14.R13.R11.R16.)(=.(>.R27.Vsp,Vgp,Vtp,R25.R24.R23.R26.(?.&40.+19;528.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(?.&40.+2.)(?.&40.+1=;1;.)(?.&40.R15.)(?.&40.+2000000000000000.)(?.&40.+107270.)(?.&40.+?7<=0.)(?.&40.+1072;0.)(?.&40.+1071?8.)(?.&40.+1099?8.)(?.&40.R14.)R1:.R19.R18.R17.)VF,(?.&40.+5621<.)Vfc,(11.(:.&40.))R16.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros until junk. intros REC RLO RHI QLO KQ QHI CR SH UC MI. al_facts.
    unfold AGLOB_LO, AGLOB_HI in RLO, RHI.
    destruct UC as [UC1 UC2 UC3 UC4 UC5 UC6].
    pose proof (munch_refl [(SB + q, SB + q + kq)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. rewrite sx32_small by lia. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879. if_trueU.
    (* [comment removed for export] *)
    zstep. zstep. replace (Z.land (8 * q) 7) with 0 by (rewrite land_7_mod, Z.mul_comm; symmetry; apply Z_mod_mult). if_falseU.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (bytes_at_read asegs mx rec _ 16 1 (proj2 REC) ltac:(lia) ltac:(cbn; lia)) as RDB end.
    change (Z.to_nat 16) with 16%nat in RDB.
    cbn [firstn skipn cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app] in RDB.
    zstep. zstep. zstep. rewrite low_byte_mul8_land7. if_falseU. clear RDB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (8 * q + 8 * kq + -8) with (8 * (q + kq - 1)) by lia. rewrite !shiftr3_mul8. rewrite !Z.mod_small by lia.
    replace (2147450880 + (q + kq - 1) + 1 - (2147450880 + q)) with kq by lia. if_trueU.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    callxA (eapply (A_memset_evtA_aok AL CS IMG) with (S := SB + q) (k := kq) (v := 0) (junk := junk);
            [ exact SH | assumption | apply shadow_range_aok; exact CR | lia | lia | lia | lia | reflexivity | reflexivity | reflexivity ]).
    finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition iter_post (rec rem q kq : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists ra s0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (REGS ra s0 a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (rec + 64) (rem - 1))
               F (Z_to_bv 64 (if Z.eqb rem 1 then 0x56420 else 0x5621c)) fc None m' (seg_rom asegs)
      /\ munch [(SB + q, SB + q + kq); (0x63c080, 0x63c084)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ mapped m' SHLO SHHI.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L15632792610.23L37512458089.23L51852885546.19L57623029406.22L57623029406.23L68075213557.1900000500B00C00P00]00^S1q1xS1q2kq1x1l2l0SS1q2kq1x2Hx1nS1q2kq1x2Hx1nS". (* [comment removed for export] *)
  Lemma mapped_after_iter : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Pq,$0.Pkq,$0.P,(14.(15.(16.$0.$0.)(17.$0.$0.(5.+7???8000.R2.)(5.(5.+7???8000.R2.)R1.))(15.(16.$0.$0.)(17.$0.$0.+63<080.+63<084.)(18.(16.$0.$0.))))R4.R3.)P,(1?.$13.R4.(5.+7???8000.R3.)(15.$20.(21.(22.R2.)(23.(:.&8.)(?.&8.=)(22.R2.)))(18.$20.)))P,(4.=R3.)P,(1;.R7.+7???:000.+800=3000.)(1;.R7.+7???:000.+800=3000.)")
(* [comment removed for export] *).
  Proof.
    intros m m' q kq MU ZS KQ MP. eapply mapped_transport; [exact MP | exact MU | unfold AIMG_HI; lia | lia |].
    intros x Hx. destruct (Z_le_dec (SB + q) x); [destruct (Z_lt_dec x (SB + q + kq))|].
    - right. replace x with (SB + q + (x - (SB + q))) by lia. eapply rw_cells_mrd; [exact ZS | lia].
    - left. cbn. lia.
    - left. cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0?C7520491497.78 C7520491497.80 L1414996148.76 L18928417809.56L19781577491.3 L22303624855.56L230332557.75  L230332557.77  L23448568519.76L25493135954.76L30802704916.76L35197453897.56L43492405225.2 L44723545041.75L44723545041.77L46548031261.3 L49430649469.75L49430649469.77L49432567933.75L49432567933.77L53516963345.75L53516963345.77L53519250449.75L53519250449.77L66925370666.75L66925370666.77L66927650602.75L66927650602.77L66927876374.56L6693134395.2  L68075642218.56L8458708502.76 O59073424423.77O59073424423.79O7520491497.78 O7520491497.80 P19794700693.79P43496025455.79P46551811194.77P46551811194.79P6681523036.78 P6681523036.80 Q24853235745.79Q25010376810.74Q25010376810.76Q27071441792.74Q27071441792.76Q29323175524.74Q29323175524.76Q35286167861.77Q45619101883.77Q48563448619.78Q53520148542.77Q53534812711.74Q53534812711.76Q57302696161.77Q60144914126.74Q60144914126.76Q65064169310.79Q65077163815.7700000100200<00=00>00E00Q00]00g01101;01E01F01S01`01a01j02302<02E02F02G02H02I02P02W02^02e02l02m02n02o03003103203303I03[03m04?04@04A04P04Q04R04c05405=05F05X05j06406>06H06R06\06m07>07?07@FFS3odr4ODRRSFS1q3QLOS3rem3REM2E1S3rem3REM2E1S3odr4ODRRS3odr4ODRRS3odr4ODRRS1q2kq3QHIFS3rem3REM3NE1S3rem3REM3NE1FS3rem3REMS3rem3REMS3rem3REMS3rem3REMSSSSS2kq2KQS2kq2KQS2kq2KQS2kq2KQS2kq2KQFSSFFFFS1q2kq3odr3QLO2KQ4ODRRS3rec3odr3RHI4ODRRS3rec1q2kq3RHI3QLOS3rec1q2kq3RHI3QLOFFS1q2kq3odr4ODRRFFS2AL3rec3RHI4IMG'S2AL3rec3RHI4IMG'S3rec3RLOS3rec3RLOS2AL3odr4ODRR4IMG'S2AL3odr4ODRR4IMG'S3odr4ODRRS2AL5ALWF'S2AL5ALWF'S2AL5ALWF'S3odr4ODRRS2AL3rec3RLO4IMG'S2AL3rec3RLO4IMG'FF". (* [comment removed for export] *)
  Lemma unreg_iter : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pra,(:.&40.)Ps0,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa0,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)Pm,P,(:.&40.)(;.(:.&8.))Prec,$0.Prem,$0.Pq,$0.Px1,$0.Pkq,$0.Px3,$0.Px4,$0.Px5,$0.Px6,$0.Podr,$0.P,(25.$13.R;.R:.(15.$20.(26.(?.&40.(2.+8.R8.)))(15.$20.(26.(?.&40.R7.))(15.$20.(26.(?.&40.(2.+8.R6.)))(15.$20.(26.(?.&40.R5.))(15.$20.(26.(?.&40.R4.))(15.$20.(26.(?.&40.R3.))(15.$20.(26.(?.&40.R2.))(15.$20.(26.(?.&40.R1.))(18.$20.))))))))))P,(4.$27.R;.)P,(4.(5.R<.+40.)$28.)P,(3.(4.+1.R<.)(4.R<.+2>?.))P,(4.+2000.R<.)P,(3.(4.+1.R;.)(4.R;.+1000.))P,(4.(2.+8.(5.R>.R<.))+65?000.)P,(1.VCS,(2.+8.R?.)(2.+8.R=.))P,(1;.R13.+7???:000.+800=3000.)P,(2;.(<.$0.R:.(2<.(2=.+2.+40.)+1.))(3.(4.+63<080.R:.)(6.R:.+63<084.)))P,(29.R15.)P,(1:.$13.R16.)(1=.$13.VAL,VCS,(2>.R16.R15.R14.R12.R17.)(=.(>.R28.Vsp,Vgp,Vtp,R26.R25.R24.R27.(?.&40.+19;528.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.(?.&40.+2.)(?.&40.+1=;1;.)(?.&40.R16.)(?.&40.+2000000000000000.)(?.&40.+107270.)(?.&40.+?7<=0.)(?.&40.+1072;0.)(?.&40.+1071?8.)(?.&40.+1099?8.)(?.&40.R15.)R1;.R1:.R19.R18.)VF,(?.&40.+5621<.)Vfc,(11.(:.&40.))R17.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros until odr. intros REC RLO RHI REM QLO KQ QHI CR MP ODR UC MI. al_facts.
    pose proof (munch_refl [(SB + q, SB + q + kq); (0x63c080, 0x63c084)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold AGLOB_LO, AGLOB_HI in RLO, RHI.
    destruct (mapped_rw_slice m SHLO SHHI (SB + q) kq MP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [junk SH].
    destruct ODR as [-> | ODRR].
    - callxA (eapply unreg_iter_a with (q := q) (kq := kq) (junk := junk); try eassumption; unfold AGLOB_LO, AGLOB_HI; try lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      destruct (Z.eqb_spec rem 1) as [E1|NE1].
      + if_trueU. unfold iter_post. rewrite (proj2 (Z.eqb_eq rem 1) E1). finish. eapply mapped_after_iter; eauto; lia.
      + if_falseU. unfold iter_post. rewrite (proj2 (Z.eqb_neq rem 1) NE1). finish. eapply mapped_after_iter; eauto; lia.
    - callxA (eapply unreg_iter_a with (q := q) (kq := kq) (junk := junk); try eassumption; unfold AGLOB_LO, AGLOB_HI; try lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_trueU.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => pose proof (store_ok_6d4 mx odr 1 ltac:(lia) ltac:(cbn; lia)) as SOK end.
      zstep. store_done. zstep. zstep. zstep.
      destruct (Z.eqb_spec rem 1) as [E1|NE1].
      + if_falseU. zstep. unfold iter_post. rewrite (proj2 (Z.eqb_eq rem 1) E1). finish. eapply mapped_after_iter; eauto; lia.
      + if_trueU. unfold iter_post. rewrite (proj2 (Z.eqb_neq rem 1) NE1). finish. eapply mapped_after_iter; eauto; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Record grec := GR { g_q : Z; g_sz : Z; g_kq : Z; g_nm : Z; g_md : Z; g_dy : Z; g_lc : Z; g_odr : Z }.

  Definition grec_cells (r : grec) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "(15.$20.(26.(?.&40.(2.+8.(2?.O1.))))(15.$20.(26.(?.&40.(30.O1.)))(15.$20.(26.(?.&40.(2.+8.(31.O1.))))(15.$20.(26.(?.&40.(32.O1.)))(15.$20.(26.(?.&40.(33.O1.)))(15.$20.(26.(?.&40.(34.O1.)))(15.$20.(26.(?.&40.(35.O1.)))(15.$20.(26.(?.&40.(36.O1.)))(18.$20.)))))))))")
(* [comment removed for export] *).

  Fixpoint table_at (m : mem) (rec : Z) (rs : list grec) : Prop :=
    match rs with
    | [] => True
    | r :: rs' => ro_cells asegs m rec (grec_cells r) /\ table_at m (rec + 64) rs'
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5675691540.2400000JS2lo2hi1a1n2a'2n'2D12H12H2". (* [comment removed for export] *)
  Lemma disjoint_from_sub : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "PW,(24.$37.)Pa,$0.Pn,$0.Pa',$0.Pn',$0.P,(38.R5.R4.R3.)P,(4.R5.R3.)P,(4.(5.R4.R3.)(5.R6.R5.))P,(4.=R4.)(38.R9.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    induction W as [|[lo hi] W IH]; intros a n a' n' D H1 H2 H3; cbn in D |- *; [exact I|].
    destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L25233010328.22L30117718093.22L33666907028.22L40011917923.22L52202110130.22L53944876591.2200000500=00>00B00J00OS3recS2rs3recSS2rsS2rs3recS3rec". (* [comment removed for export] *)
  Lemma table_at_transport : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "PW,(24.$37.)Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Prs,(24.$39.)Prec,$0.P,(3:.R4.R1.R2.)P,(14.R6.R5.R4.)P,(38.R7.R3.(2.+40.(3;.(3<.$39.R4.))))(3:.R6.R4.R5.)")
(* [comment removed for export] *).
  Proof.
    intros W m m'. induction rs as [|r rs IH]; intros rec T MU D; [exact I|]. cbn [table_at] in T |- *. destruct T as [R T]. split.
    - eapply ro_cells_transport; [exact R | exact MU |]. cbn [length] in D. eapply disjoint_from_sub; [exact D| lia | cbn; lia | cbn; lia].
    - apply IH; [exact T | exact MU |]. cbn [length] in D. eapply disjoint_from_sub; [exact D | lia | lia | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition grec_ok (r : grec) : bool := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "(3=.(3=.(3=.(3=.(3=.(3=.(3>.+2000.(2?.O1.))(3>.+1.(31.O1.)))(3>.(31.O1.)+1000.))(3>.(2.+8.(5.(2?.O1.)(31.O1.)))+65?000.))(3?.(40.(36.O1.)(2<.(2=.+2.+40.)+1.))(3=.(3>.+63<080.(36.O1.))(41.(36.O1.)+63<084.))))(3?.(3>.(2.+8.(5.(2?.O1.)(31.O1.)))(2<.+?5>50.+3?.))(3>.+?5>90.(2.+8.(2?.O1.)))))(3?.(3>.(2.+8.(5.(2?.O1.)(31.O1.)))(2<.+1099?8.+3?.))(3>.+109:38.(2.+8.(2?.O1.)))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18625205583.13000005S1r1H". (* [comment removed for export] *)
  Lemma grec_ok_sound : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pr,$39.P,(<.$42.(43.R1.)$44.)(3.(4.+2000.(2?.R2.))(3.(3.(4.+1.(31.R2.))(4.(31.R2.)+1000.))(3.(4.(2.+8.(5.(2?.R2.)(31.R2.)))+65?000.)(3.(2;.(<.$0.(36.R2.)(2<.(2=.+2.+40.)+1.))(3.(4.+63<080.(36.R2.))(6.(36.R2.)+63<084.)))(3.(2;.(4.(2.+8.(5.(2?.R2.)(31.R2.)))(2<.+?5>50.+3?.))(4.+?5>90.(2.+8.(2?.R2.))))(2;.(4.(2.+8.(5.(2?.R2.)(31.R2.)))(2<.+1099?8.+3?.))(4.+109:38.(2.+8.(2?.R2.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros r H. unfold grec_ok in H.
    rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Bool.andb_true_iff in H.
    rewrite !Z.leb_le, !Z.ltb_lt, !Z.eqb_eq in H. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition img_cs : Prop := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pa,$0.Pn,$0.P,(4.+10000.R2.)P,(4.(5.R3.R2.)+65?000.)P,(2;.(4.(5.R4.R3.)(2<.+?5>50.+3?.))(4.(5.+?5>50.+40.)R4.))P,(2;.(4.(5.R5.R4.)(2<.(45.VAL,)+3?.))(4.(5.(45.VAL,)+40.)R5.))(1.VCS,R6.R5.)")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis IMGCS : img_cs.

  Definition loop_post (rec : Z) (n : nat) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Lms',$8.(9.(:.&40.)Lra,(:.&40.)(9.(:.&40.)Ls0,(:.&40.)(9.(:.&40.)Lt0,(:.&40.)(9.(:.&40.)Lt1,(:.&40.)(9.(:.&40.)Lt2,(:.&40.)(9.(:.&40.)La0,(:.&40.)(9.(:.&40.)La1,(:.&40.)(9.(:.&40.)La2,(:.&40.)(9.(:.&40.)La3,(:.&40.)(9.(:.&40.)La4,(:.&40.)(9.(:.&40.)La5,(:.&40.)(9.(:.&40.)La6,(:.&40.)(9.(:.&40.)La7,(:.&40.)(9.(:.&40.)Lt3,(:.&40.)(9.(:.&40.)Lt4,(:.&40.)(9.(:.&40.)Lt5,(:.&40.)(9.(:.&40.)Lt6,(:.&40.)(9.P,(:.&40.)(;.(:.&8.))Lm',P,(:.&40.)(;.(:.&8.))(3.(<.$8.R13.(=.(>.R12.Vsp,Vgp,Vtp,R10.R?.R>.R11.(?.&40.+19;528.)R=.R<.R;.R:.R9.R8.R7.R6.(?.&40.+2.)(?.&40.+1=;1;.)(?.&40.(5.O3.(2.+40.(3;.O2.))))(?.&40.+2000000000000000.)(?.&40.+107270.)(?.&40.+?7<=0.)(?.&40.+1072;0.)(?.&40.+1071?8.)(?.&40.+1099?8.)(?.&40.=)R5.R4.R3.R2.)VF,(?.&40.+56420.)Vfc,(11.(:.&40.))R1.(12.$13.)))(3.(14.(15.(16.$0.$0.)(17.$0.$0.+7???:000.+800=3000.)(15.(16.$0.$0.)(17.$0.$0.+63<080.+63<084.)(18.(16.$0.$0.))))O1.R1.)(3.(19.$13.O1.R1.)(3.(1:.$13.R1.)(1;.R1.+7???:000.+800=3000.)))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00e0@L10315083271.108L1278623069.2   L13126487133.2  L14015661163.0  L15201329579.0  L18288036651.0  L18991483929.87 L19231565229.56 L20581874186.89 L23318460859.89 L2340420287.40  L23705451243.0  L2454109483.0   L29112965213.2  L29918233707.0  L31283838517.56 L32971354551.89 L35193854657.56 L35419768107.0  L3629063755.69  L3694260075.0   L36994887979.0  L40954795883.0  L4418656093.2   L46155988854.69 L46546083083.9  L46546729053.2  L51212846889.69 L55032619271.56 L56952244843.0  L61140953304.89 L61307226923.0  L61431234258.89 L7464271550.89  L8863336797.2   N16973398212.92 N27482195754.92 N28809473834.92 N28864588420.92 O20610402913.91 O28468609121.91 O52898638433.91 O56814256225.91 O59073424423.91 O59390808545.91 O61828543585.91 P1291382330.91  P13130833722.91 P29117532986.91 P4421944378.91  P46551034682.91 P46551811194.91 P8867093050.91  00000\00]00^00_00`00a01I01i02U02f04804904:04;04<04Q04f05;05<05=05>05?05@05A05i05j05k06W06l06m07>07?07k07l07m07n08_09P0:A0:B0:C0:D0:E0:F0:G0:H0;30;^0<I0=40=_0=`0>KS1q2sz2kq2nm2md2dy2lc3odr2r'3rs'3rec3RHI3LENFFSSSS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LENS2AL1r2rs3rec3RHI3LEN4IMG'2Q22Q6S1q2sz2kq2nm2md2dy2lc3odr2r'3rs'3rec3RHI3LENS3rs'3rec3RHI3LENS2AL2CS2sp2gp2tp1F2fc2ra2s02t02t12t22a02a12a22a32a42a52a62a72t32t42t52t61m3rec3LENSSFSS1r2rs3rec3RHI3LEN2Q5S3rs'3rec3RLO3RHI3LENS1r2rs3rec3RHI3LEN2Q1SFSSSFS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LENFFS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RLO3RHI3LENS1r2rs3rec3RHI3LEN2Q3SS3rs'3rec3RHI3LENSS1q2sz2kq2nm2md2dy2lc3odr2r'3rs'3rec3RHI3LENFFFS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q13x171CS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q13x171CS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q33x171CFFFFFFFS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1S1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1S1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1S1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1S1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1FS1q2sz2kq2nm2md2dy2lc3odr2rs3rec3RHI3LEN2Q1". (* [comment removed for export] *)
  Lemma unreg_loop : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Prs,(24.$39.)Pra,(:.&40.)Ps0,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa0,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)Pm,P,(:.&40.)(;.(:.&8.))Prec,$0.P,(3:.R2.R1.R14.)P,(46.$39.Lr,$39.(<.$42.(43.R1.)$44.)R15.)P,(4.$27.R3.)P,(4.(5.R4.(2.+40.(3;.(3<.$39.R17.))))$28.)P,(47.#1.(3<.$39.R18.))P,(1;.R7.+7???:000.+800=3000.)P,(29.R8.)P,(1:.$13.R9.)(1=.$13.VAL,VCS,(48.R9.(3<.$39.R1<.)R:.)(=.(>.R1;.Vsp,Vgp,Vtp,R19.R18.R17.R1:.(?.&40.+19;528.)R16.R15.R14.R13.R12.R11.R10.R?.(?.&40.+2.)(?.&40.+1=;1;.)(?.&40.R9.)(?.&40.+2000000000000000.)(?.&40.+107270.)(?.&40.+?7<=0.)(?.&40.+1072;0.)(?.&40.+1071?8.)(?.&40.+1099?8.)(?.&40.(3;.(3<.$39.R1<.)))R>.R=.R<.R;.)VF,(?.&40.+5621<.)Vfc,(11.(:.&40.))R:.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    induction rs as [|r rs IH]; intros until rec; intros TBL OK RLO RHI LEN MP UC MI; [cbn in LEN; lia|].
    al_facts. unfold AGLOB_LO, AGLOB_HI in RLO, RHI. cbn [length] in RHI.
    pose proof (munch_refl [(SHLO, SHHI); (0x63c080, 0x63c084)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    cbn [table_at] in TBL. destruct TBL as [REC TBL].
    apply Forall_cons_iff in OK. destruct OK as [OKr OK].
    destruct (grec_ok_sound r OKr) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
    assert (CR : crange CS (8 * g_q r) (8 * g_kq r)) by (apply IMGCS; lia).
    destruct r as [q sz kq nm md dy lc odr]. cbn [g_q g_sz g_kq g_nm g_md g_dy g_lc g_odr grec_cells] in *.
    destruct UC as [UC1 UC2 UC3 UC4 UC5 UC6].
    callxA (eapply unreg_iter with (q := q) (kq := kq) (rem := Z.of_nat (length ((GR q sz kq nm md dy lc odr) :: rs)));
            try eassumption; unfold AGLOB_LO, AGLOB_HI; cbn [length]; try lia; split; assumption).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (TBL1 : table_at m1 (rec + 64) rs).
    { eapply table_at_transport; [exact TBL | exact MU |]. cbn. lia. }
    destruct rs as [|r' rs'].
    - (* [comment removed for export] *) cbn [length Z.of_nat Pos.of_succ_nat]. cbn. finish.
    - replace (Z.of_nat (length (GR q sz kq nm md dy lc odr :: r' :: rs')) =? 1) with false by (cbn [length]; symmetry; apply Z.eqb_neq; lia).
      replace (Z.of_nat (length (GR q sz kq nm md dy lc odr :: r' :: rs')) - 1) with (Z.of_nat (length (r' :: rs'))) by (cbn [length]; lia).
      callxA (eapply IH; try eassumption; unfold AGLOB_LO, AGLOB_HI; cbn [length] in *; try lia; split; assumption).
      replace (rec + 64 + 64 * Z.of_nat (length (r' :: rs'))) with (rec + 64 * Z.of_nat (length (GR q sz kq nm md dy lc odr :: r' :: rs')))
        by (cbn [length]; lia).
      finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Section Outer.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi' : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = SB.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis IMGCS : img_cs AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Ltac lx_mkR :=
    lazymatch goal with
    | |- context [MS ?R _ _ _ _ _ _] =>
      lazymatch R with
      | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
      | TNode
        (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
           (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
        None
        (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
           (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
        change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
      end
    end.

  (* [comment removed for export] *)
  Record unreg_got (m : mem) : Prop := {
    ug_start : ro_cells asegs m 0x0f6ad0 [C8 (Z_to_bv 64 0x0fa780)];   (* [comment removed for export] *)
    ug_stop : ro_cells asegs m 0x0f6ad8 [C8 (Z_to_bv 64 0x106340)];    (* [comment removed for export] *)
    ug_flags : ro_cells asegs m 0x0f5e48 [C8 (Z_to_bv 64 0x1071f8)];   (* [comment removed for export] *)
    ug_gsb : ro_cells asegs m 0x0f5e50 [C8 (Z_to_bv 64 0x1099f8)];     (* [comment removed for export] *)
    ug_mid1 : ro_cells asegs m 0x0f5e58 [C8 (Z_to_bv 64 0x10a6e8)];    (* [comment removed for export] *)
    ug_mid2 : ro_cells asegs m 0x0f5e60 [C8 (Z_to_bv 64 0x10a6f0)];    (* [comment removed for export] *)
    ug_high : ro_cells asegs m 0x0f5e68 [C8 (Z_to_bv 64 0x10a6e0)];    (* [comment removed for export] *)
    ug_cf : ro_cells asegs m 0x0f5e40 [C8 (Z_to_bv 64 0x19b528)];      (* [comment removed for export] *)
    ug_rms : ro_cells asegs m 0x0f5e70 [C8 (Z_to_bv 64 0x0f7cd0)];     (* [comment removed for export] *)
    ug_psz : ro_cells asegs m 0x0f5e30 [C8 (Z_to_bv 64 0x1994a0)]      (* [comment removed for export] *)
  }.

  Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Lms',$8.(9.(:.&40.)Lt0,(:.&40.)(9.(:.&40.)Lt1,(:.&40.)(9.(:.&40.)Lt2,(:.&40.)(9.(:.&40.)La0,(:.&40.)(9.(:.&40.)La1,(:.&40.)(9.(:.&40.)La2,(:.&40.)(9.(:.&40.)La3,(:.&40.)(9.(:.&40.)La4,(:.&40.)(9.(:.&40.)La5,(:.&40.)(9.(:.&40.)La6,(:.&40.)(9.(:.&40.)La7,(:.&40.)(9.(:.&40.)Lt3,(:.&40.)(9.(:.&40.)Lt4,(:.&40.)(9.(:.&40.)Lt5,(:.&40.)(9.(:.&40.)Lt6,(:.&40.)(9.P,(:.&40.)(;.(:.&8.))Lm',P,(:.&40.)(;.(:.&8.))(3.(<.$8.R11.(=.(>.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(10.O14.)O3.(11.(:.&40.))R1.(12.$13.)))(3.(14.(15.(16.$0.$0.)(17.$0.$0.+7???:000.+800=3000.)(15.(16.$0.$0.)(17.$0.$0.+63<080.+63<084.)(15.(16.$0.$0.)(17.$0.$0.+106340.+106348.)(15.(16.$0.$0.)(17.$0.$0.+1072;0.+1072;8.)(15.(16.$0.$0.)(17.$0.$0.(2<.(49.&40.O13.)+110.)(49.&40.O13.))(18.(16.$0.$0.)))))))O1.R1.)(3.(19.$13.O1.R1.)(3.(1:.$13.R1.)(3.(4:.$13.R1.O2.(49.&40.O13.))(3.(1;.R1.+7???:000.+800=3000.)(3.(1?.$13.R1.+106340.(15.$20.(26.(?.&40.=))(18.$20.)))(1?.$13.R1.+1072;0.(15.$20.(26.(?.&40.=))(18.$20.))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02i0@C13666631894.150L10053364023.0  L11816954103.2  L12899379667.0  L14015661163.0  L15098765931.0  L15201329579.0  L15433929110.103L16004336349.2  L16183917523.0  L1724713771.0   L18288036651.0  L18642517459.0  L1925678391.0   L20207301227.0  L20703944491.0  L20757077803.0  L2079353143.0   L21708514313.103L22469659859.0  L22706556426.131L22706556426.132L23051341966.103L23705451243.0  L24012163942.103L2454109483.0   L24713418551.0  L26167142867.0  L27002396447.1  L278628501.84   L28086984503.0  L28244149267.1  L28270288171.0  L28573891711.189L28573892092.86 L28573892092.88 L28630606667.1  L29844052279.0  L29918233707.0  L30663247277.84 L31991338643.1  L32173364243.1  L3246209131.0   L32522618123.1  L32539400659.0  L33389800747.0  L33748836645.84 L34135691115.0  L35419768107.0  L3581870903.0   L35943741643.1  L3694260075.0   L36994887979.0  L39079161043.0  L39255635155.0  L40058546795.0  L40255337233.103L40255573680.118L40661301355.0  L40954795883.0  L42513553707.0  L43371556235.1  L44286541623.0  L44423118699.0  L44965666207.1  L45290871095.0  L46397833235.1  L46401846483.0  L46805790539.1  L4897997599.1   L49398093504.103L50676171019.1  L51319976266.103L51850785674.84 L51850856962.187L51850858243.129L52008329003.0  L52735170871.0  L5481626411.0   L56356340535.0  L56952244843.0  L5926711006.84  L59726336417.0  L60350795929.103L6041240427.0   L61307226923.0  L61457513259.0  L6187784119.0   L61990255827.0  L62364799275.0  L63096796215.2  L63140321695.1  L63472765803.0  L63525461303.0  L63990470967.0  L64035452715.118L64143895763.0  L64572361747.1  L65265456083.0  L65921841975.0  L66171815019.0  L66449562440.103L66487328055.0  L66777539895.0  L67281293109.103L67355034306.85 L67519788943.103L67617291475.0  L67958953171.0  L68077233116.129L68077233885.187L68077313877.84 L68419464403.0  L7211625683.0   L7409390699.0   L7935177171.0   L8827212575.1   L8885554131.0   L9675045163.0   N19351260545.124N22776112698.124N27512689208.124N28839967288.124N32551241272.124N34673462266.124N44996863098.124N6625057658.124 N7314227512.124 O13511008764.106O14259605469.122O16338510813.122O21006210684.106O26865423425.106O28372361724.106O29648265181.122O35166031197.122O41198951932.106O44780590145.106O46330885490.122O48512514397.122O52560166396.106O57922971260.106P11821087378.106P15990905016.122P27007061499.122P28245838999.111P28245838999.149P28245838999.150P28626956719.106P31981297175.111P32166141079.149P32166141079.150P32526243823.106P35947358767.106P43384684399.106P44977704827.122P46395820183.111P46395820183.150P46793719215.106P4885926395.122 P50671506415.106P63083619922.106P63144987515.122P64562840727.111P8840299003.122 Q24984932896.108Q24984932908.147Q31990129204.111Q31990129204.150Q34090167207.108Q34090167211.147Q37279323361.147Q37279323373.108Q3962128625.109 Q3962128625.148 Q53519997318.147Q53519997322.108Q57135153575.108Q57135153579.147Q60435725114.111Q60435725114.149Q64762115760.108Q64762115772.147Q9276262327.147 Q9276262331.108 00000100200300400500600700G00H00I00J00K00L00M00N00O00P00Q00R00S01801M01]01^02:02;02<02=02>02?02@02A02B02g03L03a03b03c03d04404504604704804904:04J04K04L04M04N04O04P04Q04R04S04c05305405505605705805905:05;05<05=05>05?05@05A05Q05a06106A06B06C06D06E06F06V06W06X06Y06Z06[06\06]06^06_06`06a06b06c07307407507607707807907:07;07K07g08708808908I08Y08i08j08k08l08m08n08o09009109209B09R09b0:20:30:40:D0:E0:F0:G0:H0:I0:J0:K0:L0:M0:N0:O0:P0:Q0:R0:g0;<0;U0<=0<e0=M0=f0>N0?60?^0@70@P0@i0AB0Aj0BR0Bk0CD0C]0D20DK0E30EL0E`0F40F50F60FH0FZ0Fl0G>0GK0GX0Gk0H>0HH0HR0Hn0IJ0IK0IL0IV0I`SSFSSSSS2ra2sp4recs3LENFSSSSSSSSSFSS2ra2sp2lo4recs3LEN4LOLO3SPL3SPR1y2HyS2ra2sp4recs3LEN1y2HyS2ra2sp4recs3LENSS2AL2ra2sp4recs3LEN4GSB03SPRSSSFFSFSS2ra2sp4recs3LEN1y2Hy2lo4LOLO3SPL3SPRS2ra2sp2lo4recs3LEN4LOLO3SPL3SPR1x2HxS2ra2sp4recs3LEN1x2HxFSSS2ra2sp4recs3LENFFSFSSS2ra2sp4recs3LENSSSFSSSSSS2ra2sp4recs3LENS2ra2sp4recs3LENSSSFSSFSFSFFFFS2ra2sp4recs3LENS2ra2sp4recs3LENS2ra2sp4recs3LENS2ra2sp4recs3LENSSSSSS2ra2sp4recs3LENSFSSSSSSFFSSSS2ra2sp4recs3LENSFSSSFSSS2ra2sp4recs3LENS2ra2sp2lo4recs3LEN4LOLO3SPLS2ra2sp4recs3LENSSS2ra2sp4recs3LENS2ra2sp4recs3LENS2ra2sp4recs3LENSSSSFSSFFS4recs3LEN3x311CS4recs3LEN3x311CS4recs3LEN3x311CS4recs3LEN3x311CFFS4recs3LEN3x311CFFFFFFFFFFFFFFS2sp2lo4recs3LEN4LOLOS2sp2lo4recs3LEN4LOLOS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLOS2sp2lo4recs3LEN4LOLO3SPLS2sp2lo4recs3LEN4LOLO3SPL2HB5Ha_st5Hl_stS2sp2lo4recs3LEN4LOLO3SPLS2ra2sp4recs3LEN3SPRS2ra2sp4recs3LEN3SPRFFS2AL4recs3LEN4IMG'S2AL4recs3LEN4IMG'S2AL4recs3LEN4IMG'S2AL4recs3LEN4IMG'S4recs3LEN2HBS4recs3LEN2HBS2AL4recs3LEN5ALWF'S2AL4recs3LEN5ALWF'S4recs3LENS4recs3LENS2sp4recs3LEN2HB5Ha_st5Hl_stS2sp4recs3LEN2HB5Ha_st5Hl_stFFS4recs3LENS4recs3LEN". (* [comment removed for export] *)
  Lemma module_dtor_spec : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Pra,(:.&40.)Psp,(:.&40.)Pgp,(:.&40.)Ptp,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Ps0,(:.&40.)Ps1,(:.&40.)Pa0,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Ps2,(:.&40.)Ps3,(:.&40.)Ps4,(:.&40.)Ps5,(:.&40.)Ps6,(:.&40.)Ps7,(:.&40.)Ps8,(:.&40.)Ps9,(:.&40.)Ps10,(:.&40.)Ps11,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)PF,(1<.&5.(:.&40.))Pfc,(:.&20.)Pm,P,(:.&40.)(;.(:.&8.))Plo,$0.Precs,(24.$4;.)P,(4<.R3.+?:780.R1.)P,(46.$4;.Lr,$4;.(<.$42.(4=.R1.)$44.)R2.)P,(<.$4>.(3<.$4;.R3.)#2>?.)P,(4?.R6.)P,(50.R7.)P,(1?.$13.R8.+106340.(15.$20.(26.(?.&40.+1.))(18.$20.)))P,(1?.$13.R9.+1072;0.(15.$20.(26.(?.&40.=))(18.$20.)))P,(1;.R:.+7???:000.+800=3000.)P,(4:.$13.R;.R:.(49.&40.R2;.))P,(4.+800=3000.R;.)P,(4.R<.(2<.(49.&40.R2=.)+110.))P,(4.(49.&40.R2>.)(2=.+2.+2?.))P,(<.$0.(51.(49.&40.R2?.)+10.)=)P,(1.VCS,R?.(2<.(49.&40.R30.)R?.))P,(1:.$13.R11.)P,(<.$0.(51.(49.&40.R33.)+2.)=)(1=.$13.VAL,VCS,(52.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R12.R13.)(=.(>.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(?.&40.+996?4.)R14.(11.(:.&40.))R13.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros until recs. intros TBL OK LEN UG UC FLAG MUX MP ST LOLO SPL SPH SPA SCS MI RA. al_facts.
    (* [comment removed for export] *)
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    destruct UG as [UG1 UG2 UG3 UG4 UG5 UG6 UG7 UG8 UG9 UG10]. destruct UC as [UC1 UC2 UC3 UC4 UC5 UC6].
    (* [comment removed for export] *)
    pose proof (munch_refl [(0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x56108] [] 250%N). lx_tree.
    lazymatch goal with H : munch _ m ?mx, W : wmono _ m ?mx', I : mem_inv _ ?mx'' |- _ (MS _ _ _ _ _ ?my _) => rename H into MU; rename W into WM end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lx_mkR.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x5621c] [] 100%N). lx_tree.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      repeat match goal with H : ?T |- _ =>
        lazymatch T with context [mx] => fail | _ =>
          lazymatch T with rw_cells _ _ _ _ => clear H | ro_cells _ _ _ _ => clear H | stk _ _ _ _ => clear H | mem_inv _ _ => clear H | munch _ _ _ => clear H | wmono _ _ _ => clear H end end end;
      repeat match goal with mq : mem |- _ => lazymatch goal with |- context [mq] => fail | _ => lazymatch mq with m => fail | _ => clear mq end end end end.
    lazymatch goal with H : munch _ m ?mx, W : wmono _ m _, I : mem_inv _ _ |- _ (MS _ _ _ _ _ ?my _) => rename H into MU0; rename W into WM; rename I into MI0 end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
    assert (MP0 : mapped m0 SHLO SHHI).
    { eapply mapped_transport; [exact MP | exact MU0 | unfold AIMG_HI; lia | lia |]. intros x Hx. left. cbn. lia. }
    assert (TBL0 : table_at m0 0x0fa780 recs).
    { eapply table_at_transport; [exact TBL | exact MU0 |]. rewrite LEN. cbn. lia. }
    (* [comment removed for export] *)
    assert (MU : munch [(SHLO, SHHI); (0x63c080, 0x63c084); (0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m m0).
    { eapply munch_weaken; [| exact MU0]. intros x Hx. cbn in Hx |- *. lia. }
    clear MU0 MP TBL.
    replace 751 with (Z.of_nat (length recs)) by (rewrite LEN; reflexivity).
    callxA (eapply unreg_loop with (sp := Z_to_bv 64 (bv_unsigned sp + -208)) (rs := recs) (rec := 0x0fa780);
            try eassumption; unfold AGLOB_LO, AGLOB_HI; rewrite ?LEN; try lia; split; assumption).
    rewrite LEN. change (1025920 + 64 * Z.of_nat 751) with 1073984.
    clear MP0 TBL0. rename POST into MP1.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    change (lx_hidden (munch [(SHLO, SHHI); (0x63c080, 0x63c084); (0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m m1)) in MU.
    lx_run_tac (PLAN [0x0eadc4] [] 100%N). lx_tree.
    lazymatch goal with H : munch _ m1 ?mx, W : wmono _ m1 _ |- _ (MS _ _ _ _ _ ?my _) => rename H into MU2; rename W into WM2; rename mx into m2 end.
    assert (MP2 : mapped m2 SHLO SHHI) by (eapply mapped_transport; [exact MP1 | exact MU2 | unfold AIMG_HI; lia | lia | intros y Hy; left; cbn; lia]).
    unfold lx_hidden in MU.
    assert (MU' : munch [(SHLO, SHHI); (0x63c080, 0x63c084); (0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros y Hy. cbn in Hy |- *. lia. }
    pose proof (wmono_trans _ _ _ _ WM WM2) as WM'.
    clear MU WM MU2 WM2 MP1 MI. rename MU' into MU. rename WM' into WM.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      repeat match goal with H : ?T |- _ =>
        lazymatch T with context [mx] => fail | _ =>
          lazymatch T with rw_cells _ _ _ _ => clear H | ro_cells _ _ _ _ => clear H | stk _ _ _ _ => clear H | mem_inv _ _ => clear H end end end end.
    try clear m1.
    (* [comment removed for export] *)
    callxA (eapply memset_sh_spec with (q := 128240) (kq := 6008); try eassumption; try lia; try reflexivity; apply IMGCS; lia).
    clear MP2. rename POST into MP3.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    assert (RO8 : ro_cells asegs m3 0x10408 [C8 (Z_to_bv 64 12682135451164737535)]).
    { eapply CellsX.ro_cells_reshape; [apply (Image.ro_cells_image asegs m3 0x10408 (cells_bytes [C8 (Z_to_bv 64 12682135451164737535)])); [exact MI | vm_compute; reflexivity | lia | cbn; lia] | cbn; repeat split; try lia; try exact I | reflexivity ]. }
    (* [comment removed for export] *)
    change (lx_hidden (munch [(SHLO, SHHI); (0x63c080, 0x63c084); (0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m m3)) in MU.
    change (lx_hidden (wmono asegs m m3)) in WM.
    pose proof (munch_refl [(0x106340, 0x106348); (0x1072b0, 0x1072b8); (bv_unsigned sp - 272, bv_unsigned sp)] m3) as MU3.
    pose proof (wmono_refl asegs m3) as WM3.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [0x56478] [] 100%N). lx_tree.
    lazymatch goal with E : ?mx = m3 |- _ => subst mx end.
    lazymatch goal with H : munch _ m3 m3, W : wmono _ m3 m3 |- _ => rename H into MU3; rename W into WM3 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lx_mkR.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
      repeat match goal with H : ?T |- _ =>
        lazymatch T with context [mx] => fail | _ =>
          lazymatch T with rw_cells _ _ _ _ => clear H | ro_cells _ _ _ _ => clear H | stk _ _ _ _ => clear H end end end end.
    (* [comment removed for export] *)
    lx_run_tac (PLAN ([] : list Z) [] 100%N). lx_tree.
    lazymatch goal with H : munch _ m3 ?mx, W : wmono _ m3 _, I : mem_inv _ _, ST' : stk _ _ lo (bv_unsigned sp), FL : rw_cells _ _ 1073984 _, MX : rw_cells _ _ 1077936 _ |- _ (MS _ _ _ _ _ ?my _) =>
      unfold lx_hidden in MU, WM;
      apply evtA_done; unfold module_dtor_post; do 16 eexists;
      split; [reflexivity|];
      split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact H]; intros y Hy; cbn in Hy |- *; lia|];
      split; [exact (wmono_trans _ _ _ _ WM W)|];
      split; [exact I|];
      split; [exact ST'|];
      split; [eapply mapped_transport; [exact MP3 | exact H | unfold AIMG_HI; lia | lia | intros y Hy; left; cbn; lia]|];
      split; [exact FL| exact MX] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Outer.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint table_img_b (rec : Z) (rs : list grec) : bool :=
  match rs with
  | [] => true
  | r :: rs' => Statics.img_bytes_b asegs rec (cells_bytes (grec_cells r)) && table_img_b (rec + 64) rs'
  end.

Lemma grec_cells_length : forall r, length (cells_bytes (grec_cells r)) = 64%nat.
Proof. intros r. unfold grec_cells. cbn [cells_bytes cbytes app length]. rewrite !length_app, !length_le8. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L10062824371.10L16629958127.10L25239364748.10L47378431072.10L5280886919.10 L60661254263.10L7874927165.12 00000<00H00T00d01401@01QS2rs3rec3HhiS2rs3rec3HhiS2rs3rec3HhiS2rs3rec3Hlo3HhiS2rs3rec3Hlo3HhiS2rs3rec3HhiS2rs3rec3Hhi1a2Ha". (* [comment removed for export] *)
Lemma table_at_pristine : ltac2:(CDefT.buildp (gd_tbl_A_unreg_globals ()) "Prs,(24.$4;.)Prec,$0.Pm,Px,(:.&40.)(;.(:.&8.))P,(<.$42.(53.R2.R3.)$44.)P,(4.=R3.)P,(4.(5.R4.(2.+40.(3;.(3<.$4;.R5.))))(2=.+2.+40.))P,Pa,$0.P,(3.(4.R6.R1.)(6.R1.(5.R6.(2.+40.(3;.(3<.$4;.R7.))))))(<.(;.(:.&8.))A1.R6.(54.R2.)(11.(:.&8.)))(4<.R5.R6.R7.)")
(* [comment removed for export] *).
Proof.
  induction rs as [|r rs IH]; intros rec m Hb Hlo Hhi HP; [exact I|].
  cbn [table_img_b] in Hb. apply andb_prop in Hb. destruct Hb as [Hb Hrest]. cbn [length] in Hhi, HP.
  split.
  - split. { unfold grec_cells. cbn. repeat split. }
    eapply (Statics.pristine_bytes_at asegs rec (rec + 64) (fun _ => False) m).
    + split; [lia|]. split; [lia|]. intros a Ha _. apply HP. lia.
    + exact Hb.
    + lia.
    + rewrite grec_cells_length. lia.
    + intros a _ F. exact F.
  - apply IH; [exact Hrest | lia | lia |]. intros a Ha. apply HP. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
