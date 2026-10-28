(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00245a094f9e2acc 0 2 0 1 25 1P004aad0b305e91a7 0 2 0 1 30 1P00afe13aeb54dbb2 0 2 0 1 56 1P017e11bd6ac5af6c 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P02592d2ea9d2e45a 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P02921e20a195dc65 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P02a9d474fe209d14 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P0315e601fee137ad 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P0325ab6436fdc301 1 1 8 1 0 1 2 25 1 41 1P032dbc5e40078aa5 0 2 0 1 25 1P0336fb8954a923f3 0 2 0 1 30 1P03e2cf68ee05f058 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P03ebfb212a1336a3 0 2 0 1 9 1P0472828960e3994b 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P047e2f20e1ec73a1 0 2 0 1 9 1P0498205edfc7a25a 0 2 0 1 56 1P0533092d2bb8f825 1 1 16 2 1 1 62 1 2 46 1 67 1P057d4b332f550d68 0 2 0 1 56 1P0591838d768534a4 0 2 0 1 25 1P05948a8144226554 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P05f57dab61a4f642 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P061f3f5f76e2fbb4 0 2 0 1 21 1P0693c74d217be4b9 0 2 0 1 58 1P06a3bba9f559503f 0 2 0 1 21 1P06d1e7941eebdfc7 0 2 0 1 23 1P06dc0dd7b0d84e8c 0 2 0 1 25 1P07542b4430f52062 0 2 0 1 14 1P075a022e9bd2c0f3 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P07643a35d53296bb 0 2 0 1 19 1P081cad2fb07356c8 2 31 0 2 0 1 2 1 0 3 0 1 1 1 32 1P08cc715227d85e78 1 1 8 1 0 1 2 27 1 42 1P08f1b580b8f81ebf 0 2 0 1 21 1P091f6593b654be8b 0 2 0 1 21 1P0964739c79bcdb7e 0 2 0 1 19 1P097b6e92e298fccf 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P098130d52d95ee30 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P099a54e1366fdb86 2 58 0 2 0 1 2 1 0 3 0 1 1 1 60 1P09e3560658abe3ba 0 2 0 1 58 1P09ff206967062989 0 2 0 1 19 1P0a0d66029a6e63ff 0 2 0 1 23 1P0a4ce3b0c369ca18 0 2 0 1 23 1P0a4ff0c59f37a079 2 57 0 2 0 1 2 1 0 3 0 1 1 1 58 1P0a53dd6cc7374ab9 0 2 0 1 14 1P0a672cb97c4cfa55 2 59 0 2 0 1 2 1 0 3 0 1 1 1 60 1P0a7d2344b8061148 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P0b630a85dd375112 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P0b7300cca0dcb500 1 1 8 1 1 1 2 27 1 42 1P0b89845b7bd20881 0 2 0 1 19 1P0c46714dc4d67fd0 1 1 8 1 0 1 2 26 1 41 1P0c7507edce52772b 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P0c8bb7ac71c78737 0 2 0 1 25 1P0cd0a320759c71cb 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P0cd5fb3d124fff66 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P0ce3771f898168cb 0 2 0 1 15 1P0cf6150ebdb8cc78 0 2 0 1 25 1P0d1048ef85200453 0 2 0 1 54 1P0d9e55d0549be3c7 0 2 0 1 19 1P0da1490937b906dc 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P0e2550b5dff20fea 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P0e40cc2da31d0f18 1 1 8 1 0 1 2 26 1 41 1P0e44da63f8e2e437 0 2 0 1 30 1P0eca8cf97e9b69dc 0 2 0 1 23 1P0f02202fc17be57b 0 2 0 1 21 1P0f61e2f5f6bcb01a 0 2 0 1 16 1P0fc8811492cc8df1 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P0fd4fd6e18b249a5 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P1040ad70bca9475c 0 2 0 1 30 1P108c50cf307d5de7 1 1 16 2 1 1 66 1 2 47 1 71 1P11060990c8aa928b 0 2 0 1 30 1P112c00749d24ab61 0 2 0 1 30 1P116136fb72c6c2aa 0 2 0 1 23 1P1176aea5fd18bac1 0 2 0 1 25 1P1181490ab1770e88 1 1 16 2 0 1 65 1 2 46 1 70 1P11ce5c2adbd067f4 2 65 0 2 0 1 2 1 0 3 0 1 1 1 60 1P11f240c1ea1b0bec 2 57 0 2 0 1 2 1 0 3 0 1 1 1 58 1P127ecd7a80b6c932 2 30 0 2 0 1 2 1 0 3 0 1 1 1 32 1P129455894b8a0aa6 0 2 0 1 9 1P12ab55d40c20117c 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P12d6f1c81b1ff0c0 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P130f6b60e9954227 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P132d65a664a67eed 2 30 0 2 0 1 2 1 0 3 0 1 1 1 32 1P1353d83d8ae0b2d5 0 2 0 1 25 1P13df6547b3852f7a 1 1 16 2 1 1 66 1 2 47 1 71 1P1492e3e54bb3660d 0 2 0 1 54 1P15173df179734d2e 2 35 1 1 8 2 0 1 2 1 2 28 1 43 1 1 1 8 2 0 1 1 1 2 27 1 43 1P15260d341e14fb7d 1 1 16 2 1 1 66 1 2 47 1 71 1P153b7f3ffde5ed47 0 2 0 1 23 1P155f3ce873589a25 0 2 0 1 23 1P15a1b6c973cfa42e 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P15e097f980057f93 0 2 0 1 23 1P16178fa04998922f 0 2 0 1 64 1P1641f969e83ab549 0 2 0 1 25 1P164a443cd48eab55 0 2 0 1 11 1P166e6265798e0b70 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P16720ee1657b8e62 0 2 0 1 56 1P16813b251292984d 0 2 0 1 23 1P16acc224fa8d9a16 0 2 0 1 30 1P16f12c9b446539fe 0 2 0 1 23 1P16f4a893f3d4e3b0 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P171558ba58ef8c46 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P1717b397dfc66760 0 2 0 1 23 1P17343538f7e37999 0 2 0 1 25 1P176a282c0507d3f3 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P177c88b122087b7a 0 2 0 1 19 1P17a1f11ba674a1b5 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P17a2766abdf21e41 0 2 0 1 58 1P17d7f1c8714ae647 0 2 0 1 56 1P17df9da71b1cb3c3 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P1806c37adbe62957 0 2 0 1 21 1P18452a2cd7d2b820 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P186b6bfc5623a97c 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P18b8c11153efa975 0 2 0 1 21 1P18bef376c6f61ed6 0 2 0 1 19 1P18c9e50bd2ea456f 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P1904a74a2baf927d 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P190fa1757ff2324c 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P1915bef8311066aa 0 2 0 1 23 1P19298d5a94d5181e 0 2 0 1 23 1P1990f6fd498c607b 0 2 0 1 25 1P19af5531ed149c0c 0 2 0 1 23 1P19b513fe53f5e564 0 2 0 1 25 1P19c32cd7c065a7f6 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P19db61748874646d 0 2 0 1 6 1P19f2e020288230b6 0 2 0 1 21 1P1a271efcf506e601 0 2 0 1 19 1P1a2e9edd9be8d791 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P1a5d0888cdba4e2b 0 2 0 1 23 1P1ab65e2d7b6ded57 0 2 0 1 56 1P1b6071ca8c158397 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P1b62fd22eef89775 0 2 0 1 58 1P1b9b3e65947cedaa 0 2 0 1 19 1P1ba3159a00c7c6ab 0 2 0 1 14 1P1bd5b6a26a44c55d 0 2 0 1 16 1P1c0c9bcba240f9be 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P1c13d1a8cfcddffa 2 56 0 2 0 1 2 1 0 3 0 1 1 1 58 1P1c1d63774b532bb6 0 2 0 1 25 1P1c3617cb82340493 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P1c68ca736353c010 0 2 0 1 25 1P1ca09433e59a931f 2 30 1 1 8 2 0 1 2 1 2 28 1 43 1 1 1 8 3 0 1 1 1 32 1 2 27 1 43 1P1ccbaf06e879f56a 0 2 0 1 15 1P1d39f04c8e4dc037 0 2 0 1 25 1P1d8918fb6f3465cb 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P1d8d3e928aa7ca15 0 2 0 1 15 1P1daf82fda3e00736 0 2 0 1 23 1P1dbdbc34fdaf13d1 0 2 0 1 16 1P1debde81ac5d510b 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P1e0f9a214665f060 0 2 0 1 60 1P1e367c8c235fe7f1 0 2 0 1 30 1P1e402e853bdd6da5 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P1e6a1dda0f2b4c9a 0 2 0 1 21 1P1e7abbe751a48a68 0 2 0 1 21 1P1eac004f7902eed1 0 2 0 1 19 1P1f021de40bfed889 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P1f087b83543f7345 0 2 0 1 58 1P1f0e54b787f54984 0 2 0 1 56 1P1fb3b6862b9da442 0 2 0 1 19 1P1fe6f2d1a7e0d21b 2 58 0 2 0 1 2 1 0 3 0 1 1 1 60 1P201e1ddf23db41f2 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P205c40ee5439c4b6 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P206cb2a493472084 1 1 16 2 1 1 62 1 2 46 1 67 1P208b7f9cddb449a4 0 2 0 1 25 1P20922cb3129e0550 0 2 0 1 25 1P218de3e45ac7c991 0 2 0 1 30 1P21dd679fee08d1a2 0 2 0 1 23 1P21ee7fec3ab2aa36 0 2 0 1 30 1P225d96827d19c655 0 2 0 1 30 1P22626c8adc305b89 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P227b25ecb0eacf3a 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P227e31ec82213733 2 57 0 2 0 1 2 1 0 3 0 1 1 1 58 1P22bb05332ddbec15 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P22f7c929bf1f0ccd 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P2378f9f57d456424 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P23bc012556796fe6 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P23bfcc290ba0aa32 0 2 0 1 25 1P23f353cc9884743b 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P246df103cb5766fe 0 2 0 1 6 1P252d6e3e83e0a4c2 0 2 0 1 19 1P2563575aaf882489 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P258a1bff2254c32e 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P25a9a990e3321828 0 2 0 1 8 1P25c254004e2b8ef0 2 59 0 2 0 1 2 1 0 3 0 1 1 1 60 1P25d297a25799cc86 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P25e48f51c1ca704f 0 2 0 1 21 1P25e4ab6acf7c0fe3 2 56 0 2 0 1 2 1 0 3 0 1 1 1 58 1P26034fa98bc2ae29 0 2 0 1 19 1P270b0f28991967fd 0 2 0 1 21 1P2817588306a8effe 2 57 0 2 0 1 2 1 0 3 0 1 1 1 58 1P284d168401070773 0 2 0 1 19 1P28ca43b9f881252c 0 2 0 1 25 1P28dc12b58ba3d54d 0 2 0 1 21 1P28f2ba01af0c6333 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P2940e03441404ae8 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P2962a70d3bd45d4f 2 30 0 2 0 1 1 1 0 3 0 1 2 1 32 1P2966603c8fff9abd 0 2 0 1 11 1P299b36e6baff49f5 0 2 0 1 30 1P29d9bec7bc332703 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P29edf608f2c6fbbc 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P2a1c4271a30c314f 0 2 0 1 15 1P2a20ad5dfaf433ed 2 56 0 2 0 1 2 1 0 3 0 1 1 1 58 1P2a301e3f5ba5ab5c 0 2 0 1 14 1P2a80f445162af766 0 2 0 1 31 1P2a9150ef0663ed29 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P2aeb4961cf9bfb77 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P2b46b6260ebee5c1 0 2 0 1 19 1P2b4aad06221f7fa5 0 2 0 1 30 1P2b6ec580f79ab3f5 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P2b7f9f66c22ff9a1 0 2 0 1 30 1P2b881e5ab60fc4b6 0 2 0 1 30 1P2c01463645a4162f 0 2 0 1 7 1P2c32fc7600e362c1 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P2ca4d009c0573d2f 2 56 0 2 0 1 2 1 0 3 0 1 1 1 58 1P2cd717740576d36a 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P2d2c6d52c39c55f6 0 2 0 1 15 1P2d44beb9ed1606b3 0 2 0 1 19 1P2d7e862212215ab5 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P2e57d753b7d8cab5 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P2e6e62c2f28ffbb8 0 2 0 1 21 1P2e87aadc98a39194 2 20 0 2 0 1 1 1 0 3 0 1 2 1 25 1P2eb016553a8b9778 0 2 0 1 21 1P2ec179e516852c34 0 2 0 1 21 1P2ef8d20c236053ec 0 2 0 1 23 1P2f0dd71f5c025348 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P2f140dcf0f8a9d77 0 2 0 1 25 1P2f22980e223cc761 1 1 16 2 1 1 62 1 2 46 1 67 1P2f57a4f5ae9cd1db 0 2 0 1 58 1P2f86ecfda4a83715 0 2 0 1 15 1P2fa6123c7183a1bd 0 2 0 1 7 1P30038ca227ebe3ca 0 2 0 1 25 1P30609fc7b06a245d 0 2 1 1 62 1P309c3d55bb4cbc71 0 2 0 1 30 1P30d0cb1fd2583fc7 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P30e2a384ad27a562 0 2 0 1 30 1P312029ac2b0f669f 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P312f145264fa6572 2 59 0 2 0 1 2 1 0 3 0 1 1 1 60 1P3133e9f4cccc9ba7 0 2 0 1 21 1P3139115894e600f7 2 35 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 2 0 1 2 1 2 27 1 43 1P314f9903c20ded44 0 2 0 1 21 1P316f3e13da29519d 0 2 0 1 21 1P31d83cf937c63da2 1 1 16 2 1 1 62 1 2 46 1 67 1P32618d8b3ee3b132 1 1 16 2 0 1 61 1 2 45 1 66 1P326ef34f72246dc6 0 2 0 1 19 1P32772b031dbc8351 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P32f137d7c1fdee2f 0 2 0 1 15 1P3387f380100a4fca 0 2 0 1 30 1P33dbf38f11f4ecf8 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P33e18f32c8019725 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P34588334a12d9360 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P34bf4c5fdafcb0e2 0 2 0 1 30 1P34c54033c5dfac38 0 2 0 1 19 1P350256a0e88acee5 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P35593c03bc065e11 1 1 8 1 0 1 2 27 1 42 1P3579b5c5901927e5 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P36c5ec24daa22c84 2 22 0 2 0 1 1 1 0 3 0 1 2 1 27 1P3735b70ea16ee811 0 2 0 1 15 1P376fe6fabfbcb94a 1 1 16 2 1 1 66 1 2 47 1 71 1P37a693d6e5a91bea 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P37e2a8b52dd9ddbe 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P3890165cebf69796 2 58 0 2 0 1 2 1 0 3 0 1 1 1 60 1P38aa727e4be588c0 0 2 0 1 56 1P38af9bdb50cb8b86 0 2 0 1 58 1P38fd03544b34eea2 0 2 0 1 58 1P398dc3530e09a0fa 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P39b79a27dc5d147c 0 2 0 1 25 1P3a213e9a44b0dfba 0 2 0 1 23 1P3a4bf452b0d87342 2 58 0 2 0 1 2 1 0 3 0 1 1 1 60 1P3a582551d1382fc4 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P3a9cef57dd5e9632 0 2 0 1 19 1P3aa1f4fc13f15e89 2 21 0 2 0 1 1 1 0 3 0 1 2 1 23 1P3afacf155c4d6f85 0 2 0 1 21 1P3afb0d8169368630 0 2 0 1 21 1P3b3323cdbb0bc4b2 0 2 0 1 19 1P3bad980e9d88f175 2 25 0 2 0 1 1 1 0 3 0 1 2 1 25 1P3befcdd9309dc17a 0 2 0 1 19 1P3c4cf34d2d23b138 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P3c50b1ab5f34d588 2 31 0 2 0 1 1 1 0 3 0 1 2 1 32 1P3c64082f10f3e0bd 2 19 0 2 0 1 1 1 0 3 0 1 2 1 21 1P3c8b112c53133686 0 2 0 1 23 1P3c8ebdd4e018fd10 0 2 0 1 26 1P3cb051a44e3fa8e4 2 27 0 2 0 1 1 1 0 3 0 1 2 1 27 1P3ce0ac4f1532686c 0 2 0 1 30 1P3d27ad64881ce041 2 30 1 1 8 2 0 1 1 1 2 28 1 43 1 1 1 8 3 0 1 2 1 32 1 2 27 1 43 1P3d9e6bf7acee4e8f 0 2 0 1 23 1P3db7c6510c0bc7f9 0 2 0 1 25 1P3dc33e9a1c75f898 0 2 0 1 9 1P3e0304c3fbd8eb6f 0 2 0 1 21 1P3e69677b2ed8a420 0 2 0 1 30 1P3f59fb2775c3966c 0 2 0 1 19 1P3f74e0185de1ac09 0 2 0 1 21 1P3fa0d742eec55437 0 2 0 1 19 1P3fa318bcf0a7bf8a 0 2 0 1 25 1N00407db57b24e13aN007063d79759ab36N020340ce77058073N03b15429011c743aN044e09b2624dc58bN05a8152fb769bcc6N05bdfc0a31dcd021N062d1d1bb49ff359N06fc464e25be3762N0765ced9b7d5a3faN089723391a067811N096f7341edb7a766N0b05e4c5cf44efe4N0b14914cc73350d6N0b97e68afc4c6c74N0bdfa41bfb035cb5N0d2a730d6c07ec0eN0db82c8c41edb614N0e0d10b91ed20238N0e5a0cece1d8e565N0f440c7bb95de11dN11a37142461f7bacN137142852d02e94bN144eea2d841f0a94N147d86c01c1e21f8N15c8caeeb7944193N16e714030bd89069N17628fe862531d03N18036217430d262dN18c8374905a5a93eN1aa07700c5b6c722N1d23e3f03f657188N1d9d89c7ae8e9124N1ec1edb42c62f092N20360ee8b94272dbN21112fa19f4c8a86N21df9f3f4ea7d4f2N22cff00643333c52N2320cb7a09c96f63N234cb0408e47b0f7N239e866af98f42b3N27a89b33d6f40110N27aad59280679fa0N28e1bee3c321e265N2a00533d970e1ab5N2a925bf2d36ea6c8N2b69a3a7e57bcc70N2c3029929e83ac6cN2cdc791d86401d43N2dab0e92c30a3681N2ebee1e020ffd095N2f43d4512ba91ed9N30b5381f34e15c4cN30c34ad13e1a012fN30f22f40bcdec7faN31c82b9036d9636aN331656e5f99ab3eaN3359a51657ff05efN35971f351f7fe7ceN35aa87af7698c95aN360e41ad9c6f0704N365c386f7d13156dN36d3ebded1d55b45N37b15fcf97e7b4aeN3a3db450ffaacb18N3b8dc4c303f6b9a3N3baf9d5966a65174N3bfffd65d11210adN3d0c2744b679f82eN3d514eaaf07af3caN3d8cb85ec4ab26baN3ea8df3d6e54d3eeN3ed1293b2b6fbb30N3f31fd241b766054"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Enqueue () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "ARUN_1.Enqueue.qc_cells"; "ARUN_1.Enqueue.batch_hdr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Enqueue.enq_append_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_ENQUEUE"; "ARUN_1.A_ENQ_POP"; "ARUN_1.Enqueue.pc24_cells"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.Enqueue.enq_at_pop"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QPUT_RA1"; "ARUN_1.Enqueue.enq_frame"; "ARUN_1.A_ENQ_BACK"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.A_REFILL"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "ARUN_1.A_SPIN_ENQ"].

Section ARUN_1. Context {hAR : arun}.
Definition A_REFILL : Z := 0x4c758.          (* [comment removed for export] *)
Definition A_ENQ_POP : Z := 0x4be64.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ENQ_BACK : Z := 0x4bf78.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SPIN_ENQ : Z := 0x4bfb4.        (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L13672538410.12L38652544530.1 L39332637397.0 L42757602284.12L47875776232.12L67504450086.12L9011965710.12 00000400800900B00H00N00WS2wsS2wsSS1A2ws2W1S1A2wsS1A2wsS1A2ws2W0". (* [comment removed for export] *)
Lemma u64arr_append : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pv,(0.&40.)P,(4.$5.R4.R3.R2.)P,(6.$5.R5.(7.R4.(8.+8.(9.(:.(0.&40.)R3.))))+8.)(4.$5.(;.R6.(<.(7.R5.(8.+8.(9.(:.(0.&40.)R4.)))))(=.R3.))R5.(>.(0.&40.)R4.(?.(0.&40.)R3.(10.(0.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros m A ws v [HB HW] HW8. pose proof HW8 as (W0 & W1 & _). pose proof HW as (V0 & V1 & _). split.
  - rewrite u64s_app. apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact HB| lia| rewrite length_le8; lia|]. left. rewrite u64s_length. lia.
    + rewrite u64s_length. cbn [u64s]. rewrite app_nil_r.
      replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia.
      apply bytes_at_write_same; [lia| rewrite length_le8; lia].
  - rewrite app_length. cbn [length]. apply wr_at_write.
    replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
    apply (proj2 (wr_at_app asegs m A (8 * Z.of_nat (length ws)) 8 ltac:(clear; lia) ltac:(clear; lia))). split; [exact HW| exact HW8].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L4062777295.12 L42133566526.14L55373127629.12L57921984173.1400000;00M00\00cS1A1k2H02HkS1n1k1j2Hk2Hn1i2HiS1A1n1k1j2H12HnS1A1k1i". (* [comment removed for export] *)
Lemma wr_at_sub : forall m A n k j, wr_at asegs m A n -> 0 <= k -> 0 <= j -> k + j <= n -> wr_at asegs m (A + k) j.
Proof.
  intros m A n k j (H0 & H1 & H) Hk Hj Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L13033789162.3L16473279335.3L18873492550.3L41510314692.3L44015171046.3L49249115687.300000300900:00@00A00BS1xS1x2HxSS1x2HxSS". (* [comment removed for export] *)
Lemma shl32_shr30 : forall x, 0 <= x < 2^31 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = x * 4.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (split; [lia|]; change (2^32) with 4294967296; lia).
  change (2^32) with (4 * 2^30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma u64arr_of_C8 : forall m A (v : word), rw_cells asegs m A [C8 v] -> u64arr asegs m A [v].
Proof. intros m A v [[_ HB] HW]. split; [exact HB| exact HW]. Qed.

Section Enqueue.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition qc_cells (len first last bytes : Z) : list cell :=
    [C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 first); C8 (Z_to_bv 64 last); C8 (Z_to_bv 64 bytes)].
  (* [comment removed for export] *)
  Definition batch_hdr (next size count : Z) : list cell :=
    [C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 count)].

  (* [comment removed for export] *)
  Definition enq_append_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (C len first last bytes bsize n cb lo : Z) (elems : list word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Lms',$11.(12.(0.&40.)La0,(0.&40.)(12.(0.&40.)La1,(0.&40.)(12.(0.&40.)La2,(0.&40.)(12.(0.&40.)La3,(0.&40.)(12.(0.&40.)La4,(0.&40.)(12.(0.&40.)La5,(0.&40.)(12.(0.&40.)La6,(0.&40.)(12.(0.&40.)La7,(0.&40.)(12.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(13.(14.$11.R:.(15.(16.O23.(17.&40.O24.)O22.O21.O20.O1?.O1>.O1=.O1<.R9.R8.R7.R6.R5.R4.R3.R2.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.)O3.(18.O23.)O2.(19.(0.&40.))R1.(1:.$5.)))(13.(1;.(?.(1<.$2.$2.)(1=.$2.$2.O5.O24.)(?.(1<.$2.$2.)(1=.$2.$2.O=.(7.O=.+20.))(?.(1<.$2.$2.)(1=.$2.$2.O:.(7.O:.+2000.))(10.(1<.$2.$2.)))))O1.R1.)(13.(1>.$5.O1.R1.)(13.(1?.$5.R1.)(13.(20.$5.R1.O=.(21.O<.O;.O:.(7.O9.O7.)))(13.(20.$5.R1.O:.(22.=(7.O8.O7.)(7.(9.(:.(0.&40.)O4.))+1.)))(13.(4.$5.R1.(7.O:.+18.)(>.(0.&40.)O4.(?.(0.&40.)(17.&40.O6.)(10.(0.&40.)))))(13.(6.$5.R1.O:.+2000.)(23.$5.R1.O5.O24.))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L19218556870.5 L21784409824.89L24114453479.2 L30264553959.3 L37491800026.73L39332637397.0 L40247760258.3 L41137316136.10L51489811886.73L6114107092.3  L63312216928.8800000E00b00m01?01b01c02002Y03a04304JS4last5elems2L05countS3hAR5bytes1n5elems3CNT5countS5elems3CNTS4last5elems5countS3hAR2SP1C4last2lo5elems5count1y2HySS5elems5countS2SP1C4last2lo5elems5count4SEP04SEP24CNTZS3hAR2SP1C4last2lo5elems2L05count5LOIMG3SPL4SEP14SEP24CNTZ1y2Hy2H72H92H8S5elems5count4CNTZS3hAR5bsize1n5elems3CNT". (* [comment removed for export] *)
  Lemma enq_append : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa2,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$2.PC,$2.PCACHE,$2.Plen,$2.Pfirst,$2.Plast,$2.Pbytes,$2.Pbsize,$2.Pn,$2.Pcb,$2.Plo,$2.Pelems,(3.(0.&40.))PF,(24.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(13.(25.+1.R<.)(26.R<.(27.+2.+3?.)))P,(13.(25.=R<.)(26.R<.(27.+2.+40.)))P,(25.+65?000.R<.)P,(25.(7.R=.+2000.)(27.+2.+2?.))P,(25.=R=.)P,(26.(7.R>.R<.)(27.+2.+3?.))P,(25.=R>.)P,(26.(7.R?.R>.)(27.+2.+3?.))P,(13.(25.=R?.)(26.R?.(27.+2.+20.)))P,(13.(25.=R?.)(26.R?.(27.+2.+40.)))P,(13.(25.=R17.)(26.R17.(27.+2.+40.)))P,(28.(:.(0.&40.)R?.)#3?=.)P,(13.(25.+1000.R1:.)(29.(25.(7.R1:.+20.)+10000.)(25.+65?000.R1:.)))P,(25.(7.R1;.+20.)(27.+2.+2?.))P,(20.$5.R?.R1<.(21.R1:.R19.R18.R17.))P,(2:.VCS,R1=.+20.)P,(20.$5.R11.R1:.(22.=R18.(9.(:.(0.&40.)R14.))))P,(4.$5.R12.(7.R1;.+18.)R15.)P,(6.$5.R13.R1<.+2000.)P,(2:.VCS,R1=.+2000.)P,(29.(25.(7.R22.+20.)R1>.)(25.(7.R1>.+2000.)R22.))P,(23.$5.R16.R1:.R24.)P,(25.(2;.VhAR,)R1;.)P,(25.R1<.(2<.R26.+40.))P,(25.R27.(27.+2.+3>.))P,(29.(25.R28.R27.)(25.(7.R27.+20.)R1>.))P,(29.(25.R29.R24.)(25.(7.R24.+2000.)R1?.))P,(2:.VCS,R20.(2<.R2:.R20.))P,(1?.$5.R1=.)(2=.$5.VAL,VCS,(2>.R2<.R46.R45.R44.R43.R42.R41.R40.R3?.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2;.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)(15.(16.R46.(17.&40.R2<.)R45.R44.R43.R42.R41.R40.R3?.(17.&40.R2;.)(17.&40.R2:.)R3>.(17.&40.R23.)(17.&40.R24.)R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R20.(17.&40.$2?.)R1?.(19.(0.&40.))R1>.(1:.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP C CACHE len first last bytes bsize n cb lo elems F fc m
      LB FB L0 L1 BY0 BY1 BS0 BS1 NB CBB CAB CNT C0 C1 QC CCS BH BE BW BCS SEP0 ST LOIMG SPL SPH SEP1 SEP2 SCS MI.
    unfold qc_cells, batch_hdr in *. unfold A_ENQUEUE.
    set (count := Z.of_nat (length elems)) in *.
    assert (CNTZ : 0 <= count <= 1020) by (subst count; clear -CNT; lia).
    (* [comment removed for export] *)
    destruct (lxw_wr_at_cells m (last + (24 + 8 * count)) 8 ltac:(clear -L0 CNTZ; lia)
                (wr_at_sub m last 8192 (24 + 8 * count) 8 BW ltac:(clear -CNTZ; lia) ltac:(clear; lia) ltac:(clear -CNTZ; lia))) as [sj SLOT].
    pose proof (munch_refl [(lo, SP); (C, C + 32); (last, last + 24); (last + (24 + 8 * count), last + (24 + 8 * count) + 8)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N).
    apply evtA_done. unfold enq_append_post, qc_cells, batch_hdr.
    lazymatch goal with MUl : munch _ m lxm, WMl : wmono _ m lxm, SL : rw_cells _ lxm (last + _) [C8 _] |- _ =>
      lx_exs; lx_ands;
      [ lx_mseq
      | eapply munch_weaken; [| exact MUl]; lx_subfp
      | exact WMl
      | assumption
      | match goal with K : rw_cells _ lxm C _ |- _ => lx_rwx K end
      | subst count; match goal with K : rw_cells _ lxm last _ |- _ => lx_rwx K end
      | apply (proj2 (lxw_u64arr_app lxm (last + 24) elems [Z_to_bv 64 cb])); split;
          [ eapply (u64arr_transport asegs); [exact BE| exact MUl| exact WMl| fold count; cbn [disjoint_from]; clear -CNTZ SEP0 SEP2 SPL; lia]
          | fold count; match type of SL with rw_cells _ _ ?a _ => replace (last + 24 + 8 * count) with a by (clear; lia) end; apply lxw_u64arr_of_C8; exact SL ]
      | exact (wr_at_transport _ _ _ _ _ BW WMl)
      | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition enq_frame (m : mem) (SP : Z) (fr : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : Prop :=
    rw_cells asegs m (SP + -64) [CB 8 fr; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition pc24_cells (count max : Z) (csz : word) : list cell := [C4 (Z_to_bv 64 count); C4 (Z_to_bv 64 max); C8 csz].

  (* [comment removed for export] *)
  Definition enq_pop_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T len first last bytes n cb b count max lo lw : Z) (csz : word) (cks : list word)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (a0 a1 a2 a3 a4 a5 a6 a7 : word) (m' : mem) (stj : word),
      ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, SP); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (b, b + 32); (last, last + lw)] m0 m'
      /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (T + 80) (qc_cells (len + 1) (if len =? 0 then b else first) b (bytes + (n + 8192)))
      /\ rw_cells asegs m' (T + 2128) (pc24_cells (count - 1) max csz) /\ u32arr asegs m' (T + 2144) cks
      /\ rw_cells asegs m' (T + 2784) [C8 stj]
      /\ rw_cells asegs m' b (batch_hdr 0 (n + 8192) 1) /\ u64arr asegs m' (b + 24) [Z_to_bv 64 cb] /\ wr_at asegs m' b 8192
      /\ (len <> 0 -> rw_cells asegs m' last [C8 (Z_to_bv 64 b)])
      /\ stk asegs m' lo SP.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@L10647867613.110L10647867613.117L11168243120.106L11168243120.112L11216697202.2  L11334938573.105L11334938573.111L16591383828.110L16591383828.117L16792370204.118L16792370591.129L1734333276.105 L1734333276.111 L17529991960.109L17529991960.118L17969253532.119L18758923744.3  L18939318893.113L1949808229.129 L1949808614.118 L1950178611.2   L20360721481.110L20360721481.119L21908294117.108L21908294117.117L21954417017.105L21954417017.111L23525713192.8  L24483416543.111L24483416543.119L25521808235.105L25521808235.111L27188654220.111L27188654220.119L28524174813.110L28524174813.117L30333636840.105L30333636840.111L32080810205.110L32080810205.117L32175637690.105L32175637690.111L35204929079.105L35204929079.111L4012635613.110 L4012635613.117 L41137578753.10 L43318383946.106L43318383946.112L47049263781.105L47049407238.111L47367836074.106L47367836074.112L49698585326.109L49698585326.116L49756545612.111L49756935151.105L5078790621.2   L51489811882.97 L51489811883.103L54610135556.2  L56417017448.105L56417017448.111L62444466525.111L62444585214.105L6380856847.106 L6380856847.112 L6960964073.106 L6960964073.112 L8162289145.105 L8162289145.111 L9344264216.109 L9344264216.118 L9387410519.2   00000]01J01c02<02G02\03103d04W04l05A05P05_06206E07=07H07W07j08=08D08Y08n09A09T09c0:20:L0;[0=E0=\0>30>h0?]0@J0A70AF0AU0B<0Bc0C20CA0CB0CC0Ch0DM0E20EA0EP0Eg0F>0FY0G40GQ0Gn0H=0HL0HS0I80Ig0Io0J>0JM0J\0Jk0K:0KI0KX0Kg0L60LE0LX0Lk0M6S3hAR1T5count3cks3CKL3HB05Ha_st5Hl_st3stj3cszS3hAR1T5count3cks3CKL3HB05Ha_st5Hl_st3stj3cszS3hAR1T5count3cks3CNT3CKLS3hAR1T5count3cks3CNT3CKLS5count3CNTS3hAR1T3cks3CKL2Tq2TQS3hAR1T3cks3CKL2Tq2TQS3hAR1T5count3cks3CKL2Tq2TQ3HB05Ha_st5Hl_st3stj3cszS3hAR1T5count3cks3CKL2Tq2TQ3HB05Ha_st5Hl_st3stj3cszS3hAR5bytes1n3cks3CKLS3hAR5bytes1n3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKL3HB0S3hAR1T3cks3CKL3HB0S3hAR1T4last5count3cks3CKL5LSEP13HB05Ha_st5Hl_st3stj3cszS3len2LB2L0S3hAR1T3cks3CKLS3hAR2SB2ck3cks3CKLS3hAR2SB2ck3cks3CKLS2SB2ckS3hAR1T5count3cks3CKLS3hAR1T5count3cks3CKLS3hAR5count3cks3CKLS3hAR5count3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS2SP1T2SB2ck2lo5SEPTB4SEP1S3hAR2SP1T1b5count2lo3cks3CKL5SEPTB5LOIMG3SPL4SEP14SEP23HB05Ha_st5Hl_st3stj3cszS3hAR2SP1T3len4last1b5count2lo3cks2LB3CKL5LSEP15LSEP35SEPTB5LOIMG3SPL4SEP14SEP22L03HB05Ha_st5Hl_st3stj3cszS3hAR1T3cks3TB13TB23CKLS3hAR1T3cks3TB13TB23CKLS3hAR1T1b5count3cks3CKL5SEPTB3HB05Ha_st5Hl_st3stj3cszS3hAR1T1b5count3cks3CKL5SEPTB3HB05Ha_st5Hl_st3stj3cszS3hAR1T5count3cks3CKL3HB05Ha_st5Hl_st3stj3cszS3hAR1T5count3cks3CKL3HB05Ha_st5Hl_st3stj3cszS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR3stj3csz1T3cks3CKL3HB05Ha_st5Hl_stS3hAR3stj3csz1T3cks3CKL3HB05Ha_st5Hl_stS3hAR1T3cks3CKLS3hAR1T3cks3CKLFFS3hAR1T5count3cks3CKL3HB05Ha_st5Hl_stS3hAR1T5count3cks3CKL3HB05Ha_st5Hl_stS2SP1T2SB4last2ck2lo5LSEP15SEPTB4SEP1S3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR5count3cks3CNT3CKLS3hAR5count3cks3CNT3CKLS3hAR1T5count3cks3CKL5CNT16S3hAR1T5count3cks3CKL5CNT16S3hAR1T3cks3TB23CKL3HB05Ha_stS3hAR1T3cks3TB23CKL3HB05Ha_stS3hAR1T3cks3CKLS3hAR1T3cks3CKLS2SB2ckS3hAR2SP1T2SB4last2ck2lo3cks3CKL1y2HyS3hAR2SP1T2SB3len4last2ck2lo3cks2LB3CKL2L01y2HyS2ck3CKBS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKLS3hAR1T3cks3CKL3HB0S3hAR1T3cks3CKL3HB0S5count3CNT". (* [comment removed for export] *)
  Lemma enq_pop : forall
      (ra gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax x8 x9 x18 x19 x20 x21 stj csz lnext : word)
      (SP T SB len first last bytes n cb b ck count max lo lw : Z) (cks : list word) (fr : list byte) (j0 j1 j2 j3 : word)
      (F : bvmap 5 word) (fc : bv 32) (m0 m : mem),
      lw = (if len =? 0 then 0 else 8) ->
      Timg T -> T + 4096 <= 2^47 -> T mod 4096 = 0 ->
      0 <= len < 2^62 -> 0 <= first < 2^64 -> 0 <= last < 2^64 -> 0 <= bytes -> bytes + n + 8192 < 2^63 -> 0 <= n < 2^32 -> 0 <= cb < 2^64 ->
      1 <= count < 2^31 -> 0 <= max < 2^32 -> length cks = 16%nat -> count <= 16 -> nth_error cks (Z.to_nat (count - 1)) = Some (Z_to_bv 64 ck) -> 0 <= ck < 2^32 ->
      0 < SB -> b = SB + 103079215104 + 16 * ck -> b + 8192 <= 2^47 ->
      rw_cells asegs m (T + 80) (qc_cells len first last bytes) ->
      rw_cells asegs m (T + 2128) (pc24_cells count max csz) -> u32arr asegs m (T + 2144) cks ->
      rw_cells asegs m (T + 2784) [C8 stj] -> crange CS T 4096 ->
      ro_cells asegs m A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB)] ->
      rw_cells asegs m b [C8 j0; C8 j1; C8 j2; C8 j3] -> wr_at asegs m b 8192 -> crange CS b 8192 ->
      (len <> 0 -> 0x65f000 <= last /\ last + 8192 <= 2^47 /\ (T + 4096 <= last \/ last + 8192 <= T) /\ (b + 8192 <= last \/ last + 8192 <= b) /\ (SP <= last \/ last + 8192 <= lo)) ->
      (len <> 0 -> rw_cells asegs m last [C8 lnext]) -> (len <> 0 -> crange CS last 8) ->
      (T + 4096 <= b \/ b + 8192 <= T) ->
      enq_frame m SP fr s5 s4 s3 s2 s1 s0 ra ->
      stk asegs m lo (SP + -64) -> ACEIL <= lo -> lo <= SP - 64 -> SP <= 2^62 ->
      (SP <= T \/ T + 4096 <= lo) -> (SP <= b \/ b + 8192 <= lo) ->
      munch [(lo, SP); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (b, b + 32); (last, last + lw)] m0 m ->
      wmono asegs m0 m -> mem_inv asegs m -> crange CS lo (SP - lo) ->
      evtA asegs AL CS (enq_pop_post SP ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                          T len first last bytes n cb b count max lo lw csz cks F fc m0)
        (MS (mkR rax (Z_to_bv 64 (SP + -64)) gp tp t0 t1 t2 x8 x9
                (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) a2 (Z_to_bv 64 cb) (Z_to_bv 64 n) (Z_to_bv 64 count) a6 a7
                x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_ENQ_POP) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax x8 x9 x18 x19 x20 x21 stj csz lnext
      SP T SB len first last bytes n cb b ck count max lo lw cks fr j0 j1 j2 j3 F fc m0 m
      LW TB1 TB2 TAL LB FB LAB BY0 BY1 NB CBB CNT MXB CKL CNT16 HCK CKB SB0 HB B1 QC PC CK STT TCS SBC BJ BW BCS LASTF LNX LCS SEPTB
      FR ST LOIMG SPL SPH SEP1 SEP2 MU WM MI SCS.
    facts. unfold qc_cells, pc24_cells, batch_hdr, enq_frame in *. unfold A_ENQ_POP, A_QPUT_RA1, A_SPACEBEG_CELL, A_INSTANCE in *.
    change (1074072 + 32) with 1074104 in SBC.
    (* [comment removed for export] *)
    pose proof (Z.div_mod T 4096 ltac:(lia)) as TQ. rewrite TAL, Z.add_0_r in TQ. set (Tq := T / 4096) in TQ. clearbody Tq. clear TAL.
    destruct (Z.eq_dec len 0) as [L0 | L0].
    - (* [comment removed for export] *)
      clear LNX LCS LASTF. subst len. cbn [Z.eqb] in LW. subst lw.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. rewrite (shl32_shr30 (count + -1)) by (clear -CNT; lia).
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32arr_read asegs _ (T + 2144) cks (count + -1) _ _ CK ltac:(replace (count + -1) with (count - 1) by lia; exact HCK) ltac:(clear -CNT; lia) eq_refl) as RD.
      zstep. clear RD. rewrite (zx32_lit ck) by (clear -CKB; lia).
      zstep.
      (* [comment removed for export] *)
      subst b. lx_hide MU. lx_hide WM. lx_aceil.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (munch_refl [(lo, SP); (T + 80, T + 112); (SB + 103079215104 + 16 * ck, SB + 103079215104 + 16 * ck + 32)] mc) as MU2;
        pose proof (wmono_refl asegs mc) as WM2 end.
      lx_run (PLAN [] [] 60%N).
      lx_unhide. apply evtA_done. unfold enq_pop_post, qc_cells, pc24_cells, batch_hdr. cbn [Z.add Z.eqb Pos.add].
      lazymatch goal with MUl : munch _ m lxm, WMl : wmono _ m lxm, BB : rw_cells _ lxm (16 * ck + _) [_; _; _; _] |- _ =>
        chunk_split BB 3%nat BH' BE';
        lx_exs; lx_ands;
        [ lx_mseq
        | lx_munch MU MUl
        | lx_wmono WM WMl
        | assumption
        | match goal with K : rw_cells _ lxm (T + 80) _ |- _ => lx_rwx K end
        | match goal with K : rw_cells _ lxm (T + 2128) _ |- _ => lx_rwx K end
        | eapply (u32arr_transport asegs); [exact CK| exact MUl| exact WMl| rewrite CKL; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; clear -SEPTB SEP1 SPL; lia]
        | eassumption
        | lx_rwx BH'
        | apply lxw_u64arr_of_C8; lx_rwx BE'
        | exact (wr_at_transport _ _ _ _ _ BW WMl)
        | intros X; exfalso; exact (X eq_refl)
        | assumption ] end.
    - specialize (LNX L0). specialize (LCS L0). specialize (LASTF L0). destruct LASTF as (LA0 & LA1 & LSEP1 & LSEP2 & LSEP3).
      rewrite (proj2 (Z.eqb_neq len 0) L0) in LW. subst lw.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. rewrite (shl32_shr30 (count + -1)) by (clear -CNT; lia).
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32arr_read asegs _ (T + 2144) cks (count + -1) _ _ CK ltac:(replace (count + -1) with (count - 1) by lia; exact HCK) ltac:(clear -CNT; lia) eq_refl) as RD.
      zstep. clear RD. rewrite (zx32_lit ck) by (clear -CKB; lia).
      zstep.
      (* [comment removed for export] *)
      assert (LP : 0 < len) by (clear -L0 LB; lia).
      subst b. lx_hide MU. lx_hide WM. lx_aceil.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (munch_refl [(lo, SP); (T + 80, T + 112); (SB + 103079215104 + 16 * ck, SB + 103079215104 + 16 * ck + 32); (last, last + 8)] mc) as MU2;
        pose proof (wmono_refl asegs mc) as WM2 end.
      lx_run (PLAN [] [] 60%N).
      lx_unhide. apply evtA_done. unfold enq_pop_post, qc_cells, pc24_cells, batch_hdr.
      replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; exact L0).
      lazymatch goal with MUl : munch _ m lxm, WMl : wmono _ m lxm, BB : rw_cells _ lxm (16 * ck + _) [_; _; _; _] |- _ =>
        chunk_split BB 3%nat BH' BE';
        lx_exs; lx_ands;
        [ lx_mseq
        | lx_munch MU MUl
        | lx_wmono WM WMl
        | assumption
        | match goal with K : rw_cells _ lxm (T + 80) _ |- _ => lx_rwx K end
        | match goal with K : rw_cells _ lxm (T + 2128) _ |- _ => lx_rwx K end
        | eapply (u32arr_transport asegs); [exact CK| exact MUl| exact WMl| rewrite CKL; cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; clear -SEPTB SEP1 SPL LSEP1; lia]
        | eassumption
        | lx_rwx BH'
        | apply lxw_u64arr_of_C8; lx_rwx BE'
        | exact (wr_at_transport _ _ _ _ _ BW WMl)
        | intros _; match goal with K : rw_cells _ lxm last _ |- _ => lx_rwx K end
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition enq_at_pop (SP : Z) (rax gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T STK n cb count : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Lms',$11.(12.(0.&40.)La2,(0.&40.)(12.(0.&40.)La6,(0.&40.)(12.(0.&40.)La7,(0.&40.)(14.$11.R4.(15.(16.O1>.(17.&40.(7.O1?.-40.))O1=.O1<.O1;.O1:.O19.O18.O17.(17.&40.(7.O8.+50.))(17.&40.(7.O8.+=0.))R3.(17.&40.O5.)(17.&40.O6.)(17.&40.O4.)R2.R1.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O3.(17.&40.$30.)O2.(19.(0.&40.))O1.(1:.$5.))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18758923744.3 L33681730744.58L33681730744.62L43469365577.76L43469365577.84L54740509038.1 L55594025368.1 L59308513491.3 00000;00J00Y00a00i00m01101<S3len2LB2L0S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS2SPS2SPS3len2NE2L0". (* [comment removed for export] *)
  Lemma enq_new : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pcsz,(0.&40.)PSP,$2.PT,$2.PSTK,$2.Plen,$2.Pfirst,$2.Plast,$2.Pbytes,$2.Pn,$2.Pcb,$2.Pcount,$2.Pmax,$2.Plcount,$2.Plo,$2.Plnext,(0.&40.)Plsize,(0.&40.)PF,(24.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(13.(25.+1000.R11.)(29.(25.(7.R11.+1000.)+10000.)(25.+65?000.R11.)))P,(25.(7.R12.+1000.)(27.+2.+2?.))P,(13.(25.=R11.)(26.R11.(27.+2.+3?.)))P,(13.(25.=R10.)(26.R10.(27.+2.+40.)))P,(13.(25.+1.R=.)(26.R=.(27.+2.+1?.)))P,(13.(25.=R15.)(26.R15.(27.+2.+40.)))P,(29.(14.$2.R15.=)(14.$2.R=.+3?=.))P,(20.$5.R8.(7.R18.+50.)(21.R16.R15.R14.R13.))P,(20.$5.R9.(7.R19.+850.)(31.R11.R10.R1;.))P,(2:.VCS,R1:.+1000.)P,P,(32.(14.$2.R19.=))(13.(20.$5.R<.R18.(?.$33.(34.R10.)(?.$33.(34.R?.)(?.$33.(34.(17.&40.R12.))(10.$33.)))))(13.(2:.VCS,R18.+18.)(13.(25.+65?000.R18.)(13.(25.(7.R18.+18.)(27.+2.+2?.))(29.(25.R1=.R18.)(25.(7.R18.+18.)R11.))))))P,(23.$5.R<.R11.R1=.)P,(25.(2;.VhAR,)R12.)P,(25.R13.(2<.R1?.+40.))P,(25.R20.(27.+2.+3>.))P,(29.(25.R21.R20.)(25.(7.R20.+1000.)R15.))P,(2:.VCS,R16.(2<.R22.R16.))P,(1?.$5.R12.)(2=.$5.VAL,VCS,Lms',$11.(12.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(12.(3.(0.&8.))Lfr,(3.(0.&8.))(13.(35.R27.(17.&40.$36.)R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R26.R25.R20.R1?.R1>.R18.R17.R2.R3.)(13.(1;.(?.(1<.$2.$2.)(1=.$2.$2.R1;.R27.)(10.(1<.$2.$2.)))R16.R2.)(13.(1>.$5.R16.R2.)(13.(1?.$5.R2.)(13.(37.R2.R27.R1.R33.R34.R35.R36.R3:.R3;.(17.&40.$36.))(23.$5.R2.R1;.(7.R27.-40.)))))))))(15.(16.(17.&40.$36.)(17.&40.R24.)R3=.R3<.R3;.R3:.R39.R38.R37.(17.&40.(7.R23.+50.))(17.&40.(7.R23.+=0.))(17.&40.R22.)(17.&40.R1<.)(17.&40.R1=.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R15.(17.&40.$2?.)R14.(19.(0.&40.))R13.(1:.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 csz SP T STK len first last bytes n cb count max lcount lo lnext lsize F fc m
      TB1 TB2 LB LAB CNT STKB NEW QC PC TCS LASTF ST LOIMG SPL SPH SEP1 SCS MI.
    unfold qc_cells, pc24_cells in *. unfold A_ENQUEUE, A_QPUT_RA1.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    destruct (Z.eq_dec len 0) as [L0 | L0].
    - clear LASTF. subst len.
      (* [comment removed for export] *)
      lx_run (PLAN [A_ENQ_POP] [] 30%N).
      apply evtA_done. lx_junk_under lo (SP + -56) 8%nat fr FRa.
      lx_exs; lx_ands; [ unfold enq_at_pop, A_QPUT_RA1, A_ENQ_POP; do 3 eexists; reflexivity | assumption .. | exact FRa | assumption ].
    - destruct (LASTF L0) as (LC & LCS & LA0 & LA1 & LSEP). destruct NEW as [NE|NE]; [exfalso; clear -NE L0; lia|]. subst lcount.
      assert (LP : 0 < len) by (clear -L0 LB; lia).
      (* [comment removed for export] *)
      lx_run (PLAN [A_ENQ_POP] [] 30%N).
      apply evtA_done. lx_junk_under lo (SP + -56) 8%nat fr FRa.
      lx_exs; lx_ands; [ unfold enq_at_pop, A_QPUT_RA1, A_ENQ_POP; do 3 eexists; reflexivity | assumption .. | exact FRa | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18758923744.3 L33681730744.56L33681730744.60L43469365577.74L43469365577.82L54740509038.1 L55594025368.1 L59308513491.3 00000;00J00Y00a00i00m01101<S3len2LB2L0S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS2SPS2SPS3len2NE2L0". (* [comment removed for export] *)
  Lemma enq_refill : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pcsz,(0.&40.)PSP,$2.PT,$2.PSTK,$2.Plen,$2.Pfirst,$2.Plast,$2.Pbytes,$2.Pn,$2.Pcb,$2.Pmax,$2.Plcount,$2.Plo,$2.Plnext,(0.&40.)Plsize,(0.&40.)PF,(24.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(13.(25.+1000.R10.)(29.(25.(7.R10.+1000.)+10000.)(25.+65?000.R10.)))P,(25.(7.R11.+1000.)(27.+2.+2?.))P,(13.(25.=R10.)(26.R10.(27.+2.+3?.)))P,(13.(25.=R?.)(26.R?.(27.+2.+40.)))P,(13.(25.=R13.)(26.R13.(27.+2.+40.)))P,(29.(14.$2.R13.=)(14.$2.R<.+3?=.))P,(20.$5.R7.(7.R16.+50.)(21.R14.R13.R12.R11.))P,(20.$5.R8.(7.R17.+850.)(31.=R?.R19.))P,(2:.VCS,R18.+1000.)P,P,(32.(14.$2.R17.=))(13.(20.$5.R;.R16.(?.$33.(34.R?.)(?.$33.(34.R>.)(?.$33.(34.(17.&40.R11.))(10.$33.)))))(13.(2:.VCS,R16.+18.)(13.(25.+65?000.R16.)(13.(25.(7.R16.+18.)(27.+2.+2?.))(29.(25.R1;.R16.)(25.(7.R16.+18.)R10.))))))P,(23.$5.R;.R10.R1;.)P,(25.(2;.VhAR,)R11.)P,(25.R12.(2<.R1=.+40.))P,(25.R1>.(27.+2.+3>.))P,(29.(25.R1?.R1>.)(25.(7.R1>.+1000.)R14.))P,(2:.VCS,R15.(2<.R20.R15.))P,(1?.$5.R11.)(2=.$5.VAL,VCS,Lms',$11.(12.(0.&40.)La5',(0.&40.)(12.(0.&40.)La6',(0.&40.)(12.(0.&40.)La7',(0.&40.)(12.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(12.(3.(0.&8.))Lfr,(3.(0.&8.))(13.(14.$11.R6.(15.(16.(17.&40.$38.)(17.&40.(7.R28.-40.))R41.R40.R3?.R3>.R3=.(17.&40.(7.R27.+850.))(17.&40.(7.R27.+=0.))(17.&40.(7.R27.+=0.))(17.&40.(7.R27.+850.))(17.&40.$39.)(17.&40.+18.)(17.&40.R21.)R5.R4.R3.(17.&40.R20.)(17.&40.(7.R27.+50.))(17.&40.R26.)(17.&40.R21.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)R1:.(17.&40.$3:.)R19.(19.(0.&40.))R2.(1:.$5.)))(13.(1;.(?.(1<.$2.$2.)(1=.$2.$2.R1=.R28.)(10.(1<.$2.$2.)))R18.R2.)(13.(1>.$5.R18.R2.)(13.(1?.$5.R2.)(13.(37.R2.R28.R1.R34.R35.R36.R37.R3;.R3<.(17.&40.$36.))(23.$5.R2.R1=.(7.R28.-40.))))))))))))(15.(16.(17.&40.$36.)(17.&40.R22.)R3;.R3:.R39.R38.R37.R36.R35.(17.&40.(7.R21.+50.))(17.&40.(7.R21.+=0.))(17.&40.R20.)(17.&40.R1:.)(17.&40.R1;.)R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R14.(17.&40.$2?.)R13.(19.(0.&40.))R12.(1:.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 csz SP T STK len first last bytes n cb max lcount lo lnext lsize F fc m
      TB1 TB2 LB LAB STKB NEW QC PC TCS LASTF ST LOIMG SPL SPH SEP1 SCS MI.
    unfold qc_cells, pc24_cells in *. unfold A_ENQUEUE, A_QPUT_RA1, A_ENQ_BACK, A_REFILL, A_INSTANCE.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    destruct (Z.eq_dec len 0) as [L0 | L0].
    - clear LASTF. subst len.
      (* [comment removed for export] *)
      lx_run (PLAN [A_REFILL] [] 40%N).
      apply evtA_done. lx_junk_under lo (SP + -56) 8%nat fr FRa.
      lx_exs; lx_ands; [ lx_mseq | assumption .. | exact FRa | assumption ].
    - destruct (LASTF L0) as (LC & LCS & LA0 & LA1 & LSEP). destruct NEW as [NE|NE]; [exfalso; clear -NE L0; lia|]. subst lcount.
      assert (LP : 0 < len) by (clear -L0 LB; lia).
      (* [comment removed for export] *)
      lx_run (PLAN [A_REFILL] [] 40%N).
      apply evtA_done. lx_junk_under lo (SP + -56) 8%nat fr FRa.
      lx_exs; lx_ands; [ lx_mseq | assumption .. | exact FRa | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma enq_back_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pcsz,(0.&40.)PSP,$2.PT,$2.PSTK,$2.Pn,$2.Pcb,$2.Pr,$2.Pcount,$2.Pmax,$2.Plo,$2.PF,(24.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))PW,(3.(1<.$2.$2.))P,(13.(25.+1000.R=.)(29.(25.(7.R=.+1000.)+10000.)(25.+65?000.R=.)))P,(25.(7.R>.+1000.)(27.+2.+2?.))P,(13.(25.+1.R:.)(26.R:.(27.+2.+1?.)))P,(13.(26.=R<.)(26.R<.(27.+2.+40.)))P,(20.$5.R6.(7.R11.+850.)(31.R<.R;.R13.))P,(2:.VCS,R12.+1000.)P,(25.(2;.VhAR,)R<.)P,(25.R=.(2<.R15.+40.))P,(25.R16.(27.+2.+3>.))P,(1;.(?.(1<.$2.$2.)(1=.$2.$2.R?.R17.)R:.)R<.R;.)P,(1>.$5.R=.R<.)P,(1?.$5.R=.)(2=.$5.VAL,VCS,Lms',$11.(13.(35.R1;.(17.&40.$38.)R32.R31.R30.R2?.R2>.(17.&40.(7.R1:.+850.))(17.&40.(7.R1:.+=0.))(17.&40.R17.)(17.&40.(7.R1:.+50.))(17.&40.R19.)(17.&40.R18.)R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1:.R19.R18.R17.R15.R12.R11.R?.R1.)(13.(1;.(?.(1<.$2.$2.)(1=.$2.$2.R13.R1;.)R>.)R10.R?.)(13.(1>.$5.R10.R?.)(13.(1?.$5.R?.)(20.$5.R?.(7.R1:.+850.)(31.R15.R14.R1<.))))))(15.(16.(17.&40.$38.)(17.&40.(7.R1:.-40.))R31.R30.R2?.R2>.R2=.(17.&40.(7.R19.+850.))(17.&40.(7.R19.+=0.))(17.&40.R15.)R2<.R2;.R2:.R29.R28.R27.R26.(17.&40.R16.)(17.&40.(7.R19.+50.))(17.&40.R18.)(17.&40.R17.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R11.(17.&40.$38.)R10.(19.(0.&40.))R>.(1:.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 csz SP T STK n cb r count max lo F fc m0 m W
      TB1 TB2 CNT RB PC TCS LOIMG SPL SPH MU WM MI.
    unfold pc24_cells in *. unfold A_ENQ_BACK. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [A_ENQ_POP] [] 20%N). lx_same.
    apply evtA_done. split. { unfold enq_at_pop, A_ENQ_BACK, A_ENQ_POP. do 3 eexists. reflexivity. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact PC].
  Qed.

  (* [comment removed for export] *)
  Lemma enq_back_spin : ltac2:(CDefT.buildp (gd_tbl_AW_Enqueue ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$2.PF,(24.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(3;.$5.R1.$3<.(?.$33.(34.(17.&40.+1.))(10.$33.)))P,(3;.$5.R2.$3=.(?.$33.(34.(17.&40.$3>.))(10.$33.)))P,(3;.$5.R3.$3>.(?.$33.(3?.(17.&40.=))(10.$33.)))P,(1?.$5.R4.)(2=.$5.VAL,VCS,(40.R6.$41.)(15.(16.(17.&40.$38.)(17.&40.R8.)R24.R23.R22.R21.R20.R18.R17.(17.&40.=)R1?.R1>.R1=.R1<.R1;.R1:.R19.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R7.(17.&40.$38.)R6.(19.(0.&40.))R5.(1:.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m GS GD DY MI.
    unfold A_ENQ_BACK, A_GOT_SEALED2, A_GOT_DYING, A_DYING, A_SPIN_ENQ in *.
    (* [comment removed for export] *)
    lx_run (PLAN [A_SPIN_ENQ] [] 20%N). lx_same.
    apply evtA_done. unfold die_post. do 3 eexists. reflexivity.
  Qed.
End Enqueue.

End ARUN_1.
