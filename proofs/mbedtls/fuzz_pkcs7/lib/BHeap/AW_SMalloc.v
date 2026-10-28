(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_SFree5 AW_FakeDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00105e90b1479143 0 2 1 1 40 1P0032bfe120a2f212 0 4 1 1 24 1 26 1 27 1P00628eb7a38b76de 0 2 0 1 54 1P006fdbc3e39648d7 0 4 1 1 31 1 33 1 34 1P00e8788fe8a229d9 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P01a5cf98f88b114c 0 2 0 1 12 1P01bbb7a50a0bdc80 0 2 0 1 25 1P01ccbf9b18445cd4 0 4 1 1 24 1 26 1 27 1P0233f233e28e2635 0 2 0 1 36 1P02405160c1ae16e9 0 4 1 1 24 1 26 1 27 1P02483d25b4a38672 0 4 1 1 24 1 26 1 27 1P02be704f206d072c 0 4 1 1 31 1 33 1 34 1P02bf8873dd948883 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0302f2eba555f4f0 0 2 0 1 19 1P0324972d655efe0c 0 2 0 1 19 1P032f3e20c01a07e1 0 2 0 1 28 1P03c075a4ee2923d1 0 4 1 1 31 1 33 1 34 1P03d9e0bd09a7c843 0 4 1 1 31 1 33 1 34 1P0431227ae372d246 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0454c07187272ec0 0 2 0 1 13 1P04ddd0c99918a19e 0 4 1 1 31 1 33 1 34 1P05185bab86cc5b23 0 2 0 1 25 1P052258a361567f39 0 4 1 1 31 1 33 1 34 1P054442ccf169f7bf 0 4 1 1 24 1 26 1 27 1P0560881be8da048b 0 4 1 1 31 1 33 1 34 1P0563d94746b7e755 0 2 0 1 19 1P0573dee3d314abf5 0 4 1 1 33 1 34 1 36 1P05887d8b08105e47 0 2 0 1 25 1P058ab826356cc1e6 0 2 1 1 40 1P05b4b805ec329a1b 0 4 1 1 20 1 21 1 22 1P05f7d085e3c6c00e 0 2 0 1 32 1P060697bb3a881f34 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P060b472a2fd15efe 0 2 0 1 25 1P06328d28acad1718 0 2 0 1 1 1P06aa8a229405e167 0 4 1 1 24 1 26 1 27 1P071195104dc69910 0 2 0 1 25 1P075fbeecb4648228 0 4 1 1 24 1 26 1 27 1P077adb19b366b42f 0 2 0 1 19 1P08069fe9675536be 0 2 0 1 54 1P08272686df22420b 1 1 8 3 0 1 62 1 63 1 4 37 1 61 1 64 1 65 8P08407e102fef3a61 0 4 1 1 26 1 27 1 30 1P08413467718dbb60 0 4 1 1 31 1 33 1 34 1P084fff2c29bc44f5 0 4 1 1 24 1 26 1 27 1P08a60a02419d2931 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P08b0159227869575 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P08c0b8220cd9a5d4 0 4 1 1 24 1 26 1 27 1P0909f0ffa8f2e0ff 0 4 1 1 24 1 26 1 27 1P092394f8713b7aca 0 4 1 1 24 1 26 1 27 1P092b9c8f6cb9161b 0 4 1 1 24 1 26 1 27 1P094e5a9ce8d36aba 0 4 1 1 24 1 26 1 27 1P0973128695cbf316 0 4 1 1 33 1 34 1 35 1P097355aa31dd32dd 0 2 0 1 25 1P0999b1a590ad771c 0 2 0 1 25 1P0a101a32c2393538 0 4 0 8 4 8 65 8 66 8P0a287bd2a3274e3d 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0a2dd225f81b190f 0 2 0 1 7 1P0a450796f0deb3c3 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P0a5bad06cefe6584 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0a60d29be7c739ae 0 2 0 1 12 1P0a71430166d7655b 0 2 0 1 42 1P0a754965a23aa82a 0 2 0 1 13 1P0a7d758424b643b8 0 2 0 1 25 1P0aa2b141c01402e1 0 4 1 1 24 1 26 1 27 1P0ad4db9a3c5dabac 0 4 1 1 24 1 26 1 27 1P0b4e298312cf4a02 0 4 1 1 24 1 26 1 27 1P0b62b0a22936f0fb 0 4 1 1 18 1 20 1 21 1P0b8c9ff8ca74144d 0 2 0 1 32 1P0b92f13fffebfd0e 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P0b9cd5ef2b107527 0 2 1 1 40 1P0bac7fa6942be8de 0 2 0 1 54 1P0bb4cd40e77ab014 0 4 1 1 33 1 34 1 36 1P0bbbab0c8f21b4c5 0 4 1 1 20 1 21 1 22 1P0bf9c7cc4a3f006c 0 4 1 1 31 1 33 1 34 1P0c27fe1d0e93c66c 0 4 1 1 33 1 34 1 36 1P0c3b8400b62770d3 0 2 0 1 19 1P0c60b7c1449b6c5b 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0c890e7b6662db97 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0cacfbe8d4074ed9 0 4 1 1 33 1 34 1 35 1P0cf9195a2ea3a747 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0d02f68d11fde02b 0 2 0 1 32 1P0d461559cc54bc56 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P0d55978372641a0f 1 1 504 7 0 64 50 1 64 1 65 64 66 1 67 1 68 64 6 35 32768 50 512 64 512 66 512 67 512 69 4096P0d9cdd49988cd354 0 2 0 1 15 1P0db3521de2042501 0 8 0 8 34 512 40 8 49 8 60 8 63 8 65 8 66 8P0de5ca835d928889 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0e3ad9e7e9a67d87 0 4 1 1 26 1 27 1 30 1P0e48e46806ea9d87 0 2 0 1 25 1P0e6de681ff85d3c7 0 4 1 1 31 1 33 1 34 1P0eb75153aad1b9e4 0 2 0 1 32 1P0ee5c4087931d62d 0 4 1 1 33 1 34 1 35 1P0ee92e181af6f429 0 4 1 1 31 1 33 1 34 1P0f0d4d87ce3b1cdf 0 4 1 1 31 1 33 1 34 1P0f2714a624999786 0 4 1 1 24 1 26 1 27 1P0f2765ead190ef78 0 4 1 1 31 1 33 1 34 1P0f73e0bbc684c9a6 0 4 1 1 31 1 33 1 34 1P0fab2bc68ea35ead 1 1 8 3 0 1 61 1 64 1 4 36 1 62 1 63 1 65 8P0fb4ebb7697af0f3 0 2 0 1 19 1P0fbbdba1c0a3de51 0 4 1 1 24 1 26 1 27 1P0fe236817cf94d2d 0 4 1 1 24 1 26 1 27 1P100ddd646a8afdef 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1062c611531686c9 0 2 0 1 25 1P10a1f8d6461ba143 0 2 0 1 25 1P10a9e51f87b07bfb 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P10b161216914009a 0 4 1 1 26 1 27 1 30 1P10b4bd17d57406bd 0 2 0 1 21 1P10c907b040411aef 0 4 1 1 26 1 27 1 30 1P10ce5d8d7017202c 0 4 1 1 31 1 33 1 34 1P10d45232995ea804 0 2 0 1 25 1P10daa45359639451 0 2 0 1 32 1P10e4ac1c78c33eaa 0 4 1 1 24 1 26 1 27 1P1121d229d96e4700 0 2 0 1 54 1P1135cbd1c32a0569 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P11368421e2738131 0 4 1 1 24 1 26 1 27 1P1138800a3dd01473 0 4 1 1 24 1 26 1 27 1P113991014b35db3e 0 4 1 1 31 1 33 1 34 1P1146eef13b6f1710 0 4 1 1 24 1 26 1 27 1P115cce4ad4abb212 0 4 1 1 31 1 33 1 34 1P1181bfb4ae138c08 0 2 0 1 32 1P11b9dc9eb131ef02 0 2 1 1 40 1P12037f4bde840a7a 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P1263706b5fc848ec 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P12817603c81b85fe 0 2 0 1 54 1P12a37a823f72c5ac 0 2 0 1 13 1P12d805980c76397d 0 4 1 1 33 1 34 1 35 1P12fe1bcbeaa5d24b 0 4 1 1 24 1 26 1 27 1P130198ef4e26f1bf 0 4 1 1 26 1 27 1 30 1P13454cac8f229da9 0 4 1 1 24 1 26 1 27 1P135f62e062c5b228 0 2 0 1 54 1P1380873b3074a522 0 4 1 1 24 1 26 1 27 1P1382ce29ca314cab 0 4 1 1 24 1 26 1 27 1P13b418e21ff627ee 0 2 0 1 54 1P13d5db8d028d7c9b 0 4 1 1 24 1 26 1 27 1P13da870b766d7db2 0 2 0 1 25 1P13e80d654122d854 0 2 0 1 13 1P1406d782eeaa5750 0 4 1 1 24 1 26 1 27 1P1451d86f336aa6a0 0 4 1 1 24 1 26 1 27 1P1471462e6ffd1bf1 0 2 1 1 40 1P14a1e519f5e3a16f 0 2 0 1 32 1P14c31f6036d8c4ee 0 2 0 1 23 1P14d8cb4b0391c25b 0 2 0 1 25 1P14e232ffc6658121 0 2 0 1 19 1P14f0c874cf645a11 0 4 1 1 24 1 26 1 27 1P15b57b3641ca4d25 0 4 0 1 14 1 15 1 16 1P15d0df3a52241675 0 4 1 1 20 1 21 1 22 1P1603a1c053faa4fb 1 1 504 7 0 64 50 1 64 1 65 64 66 1 67 1 68 64 6 35 64 50 1 64 1 66 1 67 1 69 8P161544f556173528 0 4 1 1 24 1 26 1 27 1P1668b4c24c6e9a9a 0 4 1 1 31 1 33 1 34 1P167f4adfcd5a9b0c 0 4 1 1 18 1 20 1 21 1P16aaccdf6bb48639 0 2 0 1 32 1P16c86a58def06885 0 4 1 1 31 1 33 1 34 1P16c9617f19425678 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P16ff982cc569a304 0 2 0 1 32 1P1704045624189b72 0 4 1 1 24 1 26 1 27 1P17442adb8443a689 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P17ca14dec2d86fcd 0 4 1 1 24 1 26 1 27 1P17ce7d183a475465 0 2 0 1 32 1P180ed001128992e9 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P1821dbce64f1675f 0 4 1 1 24 1 26 1 27 1P183405d754a51e32 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P18528b1381343ace 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P1871247e490bd59f 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P18cf5326c35b85d1 0 2 0 1 42 1P1990fe6d41fd775e 0 2 0 1 32 1P19e9a11629dde00a 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P19ea3084c8100753 0 4 1 1 24 1 26 1 27 1P1a0d6089af578c4b 0 4 1 1 31 1 33 1 34 1P1a1746f909fd46bc 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P1a5987e6270cba1b 0 4 1 1 26 1 27 1 30 1P1a80f74db66c0136 0 4 1 1 24 1 26 1 27 1P1a82f02f2fe5b036 0 2 0 1 19 1P1a99dde2f99388f6 0 2 0 1 25 1P1ab93fa5d7a3b01e 0 4 1 1 24 1 26 1 27 1P1ad38a77d7c794f6 0 4 1 1 24 1 26 1 27 1P1b0b9ed43c335ad8 0 4 1 1 24 1 26 1 27 1P1b1da431892ffb17 0 4 1 1 24 1 26 1 27 1P1b35b2c1d89774b2 0 4 1 1 24 1 26 1 27 1P1b3bb8c4393912b6 0 4 1 1 20 1 21 1 22 1P1b642483a7f1bd4e 0 4 1 1 24 1 26 1 27 1P1b75d34e6df98cd2 0 4 1 1 24 1 26 1 27 1P1b8c2945bdb14b54 0 4 1 1 31 1 33 1 34 1P1b8d6b127d74cb0f 0 2 0 1 54 1P1bf2e4c9398add39 0 6 0 1 51 1 52 1 57 1 62 1 63 1P1c7bb5faf55b8cff 0 2 0 1 12 1P1ca248acfb78dd05 0 4 1 1 24 1 26 1 27 1P1ca4ea594b3b3215 0 4 1 1 24 1 26 1 27 1P1cdd81fdd2c0daeb 0 4 1 1 24 1 26 1 27 1P1cec3e4eff96bdd9 0 4 1 1 26 1 27 1 30 1P1cec9c85d1c56c55 0 4 1 1 24 1 26 1 27 1P1cfadbfd0dd9538f 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1cfdb87efafd5634 0 4 1 1 24 1 26 1 27 1P1d02f1f2166abb5d 0 4 1 1 24 1 26 1 27 1P1d2bd46a47770495 0 4 1 1 24 1 26 1 27 1P1d3ffba9638992f6 0 4 1 1 20 1 21 1 22 1P1d611082147e509a 0 2 0 1 54 1P1d68563d0b4f22a1 0 2 0 1 25 1P1d84382e8bb0e7e7 0 4 1 1 24 1 26 1 27 1P1dfc7f73e7e25378 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1e0a0f5ab354647c 0 2 0 1 28 1P1e1d50e0d0514ba6 0 2 1 1 40 1P1e5519b48e97bf4d 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P1e6da8be663105d0 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1ecf82f842fde89b 0 2 0 1 25 1P1ee8a9678ef525b3 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P1eefc87d5a21fcb8 0 2 0 1 19 1P1ef0845545dbabd1 1 1 8 3 0 1 63 1 64 1 4 38 1 62 1 65 1 66 8P1f1924e0516cf267 0 4 1 1 31 1 33 1 34 1P1f6462d8400507d5 0 2 0 1 25 1P1f6bc3927d74d397 0 5 0 8 36 8 45 8 65 8 66 8P1f8b7bd560888992 0 4 1 1 33 1 34 1 35 1P1ff20f5b4e06b395 0 4 0 8 4 8 65 8 66 8P1ff7555b3e825b3d 0 2 0 1 54 1P1ff83ce6c0791d15 0 2 0 1 32 1P200586220f9ccfff 0 4 1 1 24 1 26 1 27 1P2021d78ab0edf57c 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2023337dbb1032c6 0 4 1 1 24 1 26 1 27 1P204f2e5da70825bc 0 4 1 1 24 1 26 1 27 1P205ad85f6c782693 0 4 1 1 24 1 26 1 27 1P206144cfeb6dfb11 0 2 0 1 25 1P20958b1e7be7464b 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P20bb627ea0c7216b 0 2 0 1 25 1P20bbd154e91401d0 0 2 0 1 25 1P20f8ec47bb7ebae0 0 2 0 1 13 1P2157e10fbf4ba362 0 2 0 1 25 1P216a498987fe057d 0 1 1 1P2195860d55112aa1 0 4 1 1 18 1 20 1 21 1P21b8dacf0cf2f8a9 0 4 1 1 20 1 21 1 22 1P21caf0052565d3e7 0 4 1 1 24 1 26 1 27 1P21e291ce7821e4cd 0 4 1 1 24 1 26 1 27 1P21f3bbd9f78767fd 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P220accd4bb4e1fe5 0 4 1 1 31 1 33 1 34 1P2295311dfa21390b 0 4 1 1 31 1 33 1 34 1P22d96977d16551a4 0 2 1 1 40 1P233409450044d9c7 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P2341929d9d3dad2a 1 1 504 7 0 64 50 1 64 1 65 64 66 1 67 1 68 64 6 35 32768 50 512 64 512 66 512 67 512 69 4096P2357bec7e3558e04 0 2 0 1 25 1P238afb2aa732d820 0 4 1 1 31 1 33 1 34 1P23959b273b909a2c 0 2 0 1 25 1P23c44764b191dfef 0 2 0 1 17 1P23f0e9c8e40c8f75 0 2 0 1 25 1P245932adb7ccd74d 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P245d33c28e1eb714 0 4 1 1 31 1 33 1 34 1P24b3bc4e5d5e24a1 0 4 1 1 24 1 26 1 27 1P250749d02c3bc754 0 4 1 1 24 1 26 1 27 1P253069c68c6601db 0 4 1 1 31 1 33 1 34 1P2550a58a6ca1ee13 0 2 0 1 32 1P2568356203327eb0 0 2 0 1 17 1P25700ce0a65a67e8 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P257b44b9b1644766 0 4 1 1 26 1 27 1 30 1P2580fd1796067402 0 4 1 1 24 1 26 1 27 1P25a9fb1e910d9021 0 4 1 1 24 1 26 1 27 1P25c895a242fcf396 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P25d88a79de839b60 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P262de5a7bb7c1593 0 2 0 1 32 1P2656adfefcd074f3 0 2 0 1 32 1P269d0cc7184989be 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P26ccbabcb86ac545 0 2 0 1 25 1P26d1eb52e70ea520 0 4 1 1 31 1 33 1 34 1P273568ef48af7622 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2736249ee335938c 0 4 1 1 24 1 26 1 27 1P2797f6d55fb60b85 0 4 1 1 24 1 26 1 27 1P27a6f8d8f7580c63 0 4 1 1 24 1 26 1 27 1P27d638114bc3cb68 1 1 504 7 0 64 50 1 64 1 65 64 66 1 67 1 68 64 6 35 64 50 1 64 1 66 1 67 1 69 8P27daf6a901bdea14 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P27f243a73789ce87 0 4 1 1 31 1 33 1 34 1P27fdf35ef37df392 0 4 1 1 31 1 33 1 34 1P288c7f6132e6bc05 0 4 1 1 24 1 26 1 27 1P291ff3940e524378 0 4 1 1 31 1 33 1 34 1P2940c492b3fe638e 0 2 0 1 12 1P294a23315a92a5ec 0 4 1 1 24 1 26 1 27 1P29951de25024a45d 0 2 0 1 21 1P299dad6a05f92b75 0 2 0 1 25 1P29c9e1dc3a1ecf5a 0 4 1 1 18 1 20 1 21 1P29d2e836122e4d7d 0 4 1 1 24 1 26 1 27 1P29f7a045349c4ee7 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2a10d3926155f1ca 0 4 1 1 24 1 26 1 27 1P2a27dc539c1d088a 0 4 1 1 31 1 33 1 34 1P2a2e542dcc263f49 0 4 1 1 24 1 26 1 27 1P2a6b1beded407f51 0 2 0 1 25 1P2a862bfb81fe8e1a 0 4 1 1 24 1 26 1 27 1P2abe720b07e0d4ed 0 4 1 1 31 1 33 1 34 1P2adbd40d93b9dcd5 0 4 1 1 24 1 26 1 27 1P2afbb646dfaa767b 0 4 1 1 24 1 26 1 27 1P2b1bfdc2b6146c29 0 4 1 1 24 1 26 1 27 1P2b2bc46121b14cc7 0 4 1 1 24 1 26 1 27 1P2b41fa3b16de4d1a 0 4 1 1 31 1 33 1 34 1P2b4d3902c289f8d2 0 4 1 1 24 1 26 1 27 1P2bbed198ce03996d 0 2 0 1 25 1P2bcf2f450c012246 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P2bd410c0a6bd6721 0 4 1 1 24 1 26 1 27 1P2bea871b04a8f7f1 0 4 1 1 24 1 26 1 27 1P2c50a7b1edf21de2 0 4 1 1 26 1 27 1 30 1P2c9657fdf226a9da 0 2 0 1 25 1P2ccb1145187e2184 0 4 1 1 24 1 26 1 27 1P2d565a354bfc340d 0 2 0 1 19 1P2d76fbdcd3e42a90 0 4 1 1 24 1 26 1 27 1P2d7cf3c509709839 0 4 1 1 31 1 33 1 34 1P2dcfc1cade2cb62e 0 2 1 1 40 1P2e26b00077a61a6f 0 4 1 1 24 1 26 1 27 1P2e4915f4bf0d86a9 0 4 1 1 26 1 27 1 30 1P2ec207c1c8150357 0 2 0 1 19 1P2ee77253337adf1c 0 4 1 1 33 1 34 1 36 1P2f2849fc1f20d603 0 4 1 1 24 1 26 1 27 1P2f6238357931df76 0 4 1 1 20 1 21 1 22 1P2f7500e98875cd75 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2f8c313dab153511 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P2f9c46a49e0d114f 0 2 1 1 40 1P2fdaf5573942cab9 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P2fe42d68eb7b66de 0 4 1 1 24 1 26 1 27 1P301056f7047605cb 0 2 0 1 25 1P30202f395199fe67 0 2 0 1 32 1P302b02c5b919ef69 0 4 1 1 26 1 27 1 30 1P307f8ae5cd927627 0 4 1 1 24 1 26 1 27 1P30c6787eba6bdaa8 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3165b9b7f91e6501 0 4 1 1 31 1 33 1 34 1P319b72ddbb713080 0 4 1 1 24 1 26 1 27 1P31b184f0892bea9f 0 4 1 1 31 1 33 1 34 1P31b2fd9c7bb37103 0 2 0 1 25 1P31da972f97de6ad8 0 4 1 1 24 1 26 1 27 1P31dc6bd8bd2b7be8 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P31f560e301f93853 0 4 1 1 31 1 33 1 34 1P3277300b091d7038 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P32a013c2a95485dd 0 4 1 1 24 1 26 1 27 1P32f3e2bab59e51f6 0 2 0 1 25 1P3319003a594d5b5a 0 2 0 1 25 1P331d5400f3fbea43 0 4 1 1 24 1 26 1 27 1P334afd19ddb27b24 0 4 1 1 26 1 27 1 30 1P34160c983f2c895b 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P345fe2f035edeaef 0 4 1 1 26 1 27 1 30 1P348a101da1c96fa5 0 2 0 1 25 1P34bd482b2a183732 0 2 0 1 25 1P34bdec18ea81feb4 0 2 0 1 19 1P34ec52d8349f971d 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P35080bc34fe6d526 0 6 0 8 36 8 65 8 66 8 67 8 68 8P351d4e57f07d6a30 0 2 0 1 25 1P356bb3596149b4eb 0 4 1 1 24 1 26 1 27 1P35dc8ed8a0d32a32 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P35eb46093743b218 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P35f786802f69bb68 0 4 1 1 24 1 26 1 27 1P3690a6fc7d43cfde 0 2 0 1 25 1P36eda25f1d23c7ad 0 2 0 1 36 1P371b67449c0f1cbe 0 2 0 1 25 1P37277575648de280 0 2 0 1 25 1P373709c312fbe33e 0 4 1 1 24 1 26 1 27 1P375032bdd8bf7df5 0 2 0 1 12 1P380f4aa5e2f7533e 0 4 1 1 24 1 26 1 27 1P3820eef6a62657ab 0 2 0 1 32 1P3845c785e38d62e4 0 4 1 1 26 1 27 1 30 1P3858c358580f121c 0 4 1 1 31 1 33 1 34 1P38d68ceb539f2598 0 4 1 1 31 1 33 1 34 1P38dc2cedb08d91af 0 2 0 1 25 1P391573ab854d612d 0 4 1 1 24 1 26 1 27 1P393971d1179c3f55 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3981a220edc149ab 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P398ddc0c91acf0d3 0 4 1 1 33 1 34 1 35 1P39a6c10bde1f5d2a 0 2 0 1 25 1P3a84155b191706f2 0 2 0 1 25 1P3ade214d84dd0dad 0 4 1 1 33 1 34 1 36 1P3ae4b9e4e4542fd6 0 4 1 1 31 1 33 1 34 1P3b090a694f64fa36 0 4 1 1 26 1 27 1 30 1P3b310580b3690c0d 0 2 0 1 25 1P3b552f15248e1399 0 2 0 1 25 1P3b5855935739a1aa 0 2 0 1 25 1P3c0e6dfe47aedd8c 0 4 1 1 31 1 33 1 34 1P3c2aaef623fcb753 1 2 4096 2 0 1 63 1 4096 2 1 1 62 1 2 64 1 65 1P3c34c8365cf7bf53 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P3c42b6cdae478255 0 4 1 1 24 1 26 1 27 1P3c72ba69def6fc08 0 4 1 1 24 1 26 1 27 1P3c7658d5f6444783 0 2 0 1 32 1P3ca156057472548c 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P3ca2dfb2339af8d9 0 4 1 1 24 1 26 1 27 1P3cd638f9614a06f0 0 4 1 1 24 1 26 1 27 1P3cf0320ce29183e2 0 4 1 1 31 1 33 1 34 1P3cf9bb389b53133a 0 4 1 1 24 1 26 1 27 1P3d307a11c2ac9743 0 2 1 1 40 1P3d575e8865083f03 0 4 1 1 31 1 33 1 34 1P3d5ccb1f918d30e8 0 4 1 1 33 1 34 1 36 1P3d7ad0adf61075cb 0 4 1 1 31 1 33 1 34 1P3d911ba16e8fde42 0 2 0 1 15 1P3db0bd937b33ed63 0 4 1 1 24 1 26 1 27 1P3e095e9e5efc71bd 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3e28780954268f0a 0 4 1 1 24 1 26 1 27 1P3ead072a070c507e 1 2 56 6 0 512 50 8 64 8 66 64 67 8 68 512 32768 5 35 64 50 1 64 1 67 1 69 1 3 45 1 67 1 70 4096P3eaeffc17bcefe2b 0 4 1 1 20 1 21 1 22 1P3eb4ad63d38fa8b3 0 4 1 1 31 1 33 1 34 1P3ee1f07d2604baf1 0 2 1 1 40 1P3ee731ee2a0e6489 0 2 0 1 25 1P3f0e3007530b3df6 0 4 1 1 24 1 26 1 27 1P3f21bc12c65bb73a 0 4 1 1 24 1 26 1 27 1P3f64c2d1f54d1ec3 0 4 1 1 31 1 33 1 34 1P3f974f6ee8e4eb74 0 2 1 1 40 1P3fa27ba6da3c713b 0 4 1 1 31 1 33 1 34 1P3fd0d7b198953516 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8N000811da5ec13f17N00106879c916194dN003bb9771a84d9a8N0041ed12fe2a6109N004ef0167a72f8a9N00653f66b3374dcbN00b0dac0d7d645cbN00b8ba35da5184f5N00bedabd2f4b6506N0121cde4e5611652N015ce2f8e29ce351N01892e9cec14c76bN01954f1d35a55dd1N0200bb16f2687013N022ac9b6d3144444N025c9965aa84050eN0267b0a7dd39fb79N0294fb0395bf04ecN02e0b72170b94f95N03738986803b728aN037cac27918b118aN0383ec38e485ade9N038f73e38b043a34N03d91c41b1a806adN0411b5107134eb71N043bf84131c3fa6aN0444efcb1b7229edN045b6a3eeb85ddc8N04b46c704b610095N04bd7bd14e49a014N053de9eefc84ffd4N054994856e5a9b9aN0578d507977323f9N05bf98da5b1903beN0623c93d989aed21N0625f1df336abfc0N063e2684155e89e1N069f4e9371c6c0f8N06b6fb7f8bf6cf5bN06f809b70ce15d69N07349b241db891d5N073b504e394d8242N0750b1fd4bf6a32dN075683117b229424N07b6a971f5dd50efN07e04811aeb69556N084b7672d8ec7377N086d3612eb5b5e8fN08c86d92481af1c2N08db40fab864e6eeN08eb1674ce504a11N095e4dbd5fddaaf1N0975166b9bf4e913N099b40749a65877aN09c908b68c9f90bdN09f9b994571577a2N0a8dffed9cba08f9N0aa205a5d1419603N0aa2ce362866d025N0aaf67ed105b3854N0ac2aa28bf14e296N0afe66a02f03007fN0b350de16668c8a6N0b514e76ac022031N0b7ac6a2be90e200N0bd1adc82508774eN0c114f2719ba7024N0c551ef482a69a17N0c64b9d236b7e42fN0c74aa90716d848cN0cb324741c157b4eN0cb5f373133a67b6N0cb9fe7fde5a1333N0d3c2d87d7c9d49aN0d8cf1c3223799fbN0dc667133e0e80f8N0dddad32a7f3da19N0df5a2fa50e6c1a6N0e0254acc1155f1aN0e0d29644c119957N0e589b5fba8180e4N0e6d5861eba961a5N0e7395118f20c578N0ea261f5f26c041dN0eaf59da35349f12N0f170b0736b8ea27N0f2bafe3ef75fe90N0f4710cbc2b5fa2eN0f4724417513be80N0fd13ec1b3dfe862N0fd9fb3770824854N0feae3df702c27cfN1012d5869e5a733fN1013a82153ce7676N10512918a832c6a3N1059b83259de9588N10f58effdce02c25N112da1920ec392f4N113311436b14baaaN119c6dbb3d933090N11ae0b651a475072N11ed78b02e68af45N124e17acf3ed763eN1283026b1b5c1c0cN12ed3b93f929e421N131f27b5c418953eN1325541e9067e944N1339b28d79927ce0N13de9f120cc72c52N13ec522c025c3c12N13f2935982e9343dN13fe1cd8522683fbN144e85d81bd322eeN1461fea8fbfd5116N14b4db6b1a22ced6N14cab332fee665b4N14d92782e88dae7cN14e86c7732a3e290N1516bd80f1b6ea10N1553e8cd270f2dbcN1568598a6158c3a0N15886324b376f774N158f1014817c1055N159f5b83ad0546a9N15ec3ff3d1fd0876N15fd195bf82e3329N1603cc5fb664d8e5N162513595538c49eN1639f18b700d86f2N16668ee1d3034289N167c052ac0dc3a1aN169afd7544402a30N16cf9272e2363379N16e4fb8596f2ec29N1720cdc1946385dcN1748a9799ccfd2b5N17912691b7d32bc5N179e9f3702fcbd65N17b0ff19e2aaace9N17b8bbddb552e7e5N17d21593808d2733N17ed87a773140328N18297afd7a4d6802N184e7776d9ca9657N187c27770beadcb1N1880a2351ccf1ddeN18af91b058c8a2d2N18d1864fe27e1f11N18ef7ba35219b306N18f12e1d8aba4c7bN1903b6f682579590N194fab360584575cN1974c44035f556ecN199243c7d306ec21N199e9cfb3043eaa3N19c4653213ae6611N19e7c7b382dd9459N19f6dcbc3d8d1544N1a012c8b233b72e9N1a1054c656b002ceN1a709fe570635ddbN1a9e86e5f5c13f9eN1ac1d4226bf33dd2N1ade503170700b7fN1b8b5cc12a17d264N1b9ed0d3f2b90538N1ba79f1d6ea23b8bN1cc4ec92ad1be67fN1cca466dce112dc4N1d0d378f2fd5c1c0N1d490afecfcf8a62N1d60673d13f8e07aN1dcff871af94a3dbN1dddabbb01c49414N1def471091b86c70N1def4ebe12d009edN1e0eebb402cb8d94N1e207308d1777de1N1e33b3f0b731114fN1e357980d6677547N1e36961a14c5a5dcN1e3ed0969e8add21N1e74f2fbff5a2f11N1e99e28346b9f4e0N1ed4da172f79c330N1f2bee7523f5c4e9N1f52e1d0e718e6b3N1f6fc4c7affd534eN1f8528aea90654bdN1f9de91e1479edcbN1fcb630c5f7d1c2eN1fcdc415f44f7b88N1ffdfc42eb29cd45N2026101a78b87092N20e6b85e63526b6eN20fa6bb38c3e664fN2121d5ff2bce1df3N21389f02734485d8N213e4c004154604cN21480e4463fd9da8N21547320d801c24aN21a6592f0292d604N2258a4592bd57ef6N229c47e6eefe4b94N22cdad41503ee916N22ced5e1c40dd692N22da35dd0ac400e1N22dfbbc88d757644N23126058a675b9a0N23295783cf1b3adbN237dc4ce631ef162N238e4b96603fb9afN23d948f66fb8b5d6N23ea96500923aa49N240c720a725776d3N243699a383cfdb32N24cc671ddefcec7bN24df0909b5ca8347N2528980eed343fddN25342d88daf2e859N257619ee54986e5bN259b3bd2da4f595cN25e3e13ae164587eN25ee34a7cbc35ebcN26000110a3d172bcN26377f08d97cdf12N26b0c77f407e9a6eN26b369b6dab68204N26d23c8f8aa938fbN26e7809832616e0eN2723794d0de448f0N273646e8dd01d43dN274398b590a3e50fN274cd3fb510cddacN276bc22f7cd74648N276f006d2fad2249N278a3edfb000caecN2790e54083cabf81N27a82d3d5031c754N27d4f2a893d8a323N27fd8e72e51a4291N28343473765ae5d6N286c153c229712c7N2939cf6b650f28afN29677ba13dc4f982N2984e935c0a9dd42N29a59a1cbc52dc08N2a0bfc3a06755f08N2a2a6e0dcf677eafN2af23759d336c85cN2b00fdd0bf568566N2b1de51cd43030e9N2b3303ad21fe1545N2b501a7eb92df445N2b7bf8f002103391N2b7eea6067e3262fN2bad2f9ab0092ca0N2be4f90b21b55a07N2bfd3e8fe32717a8N2c0d52eca4488d6dN2c17cc6a3a6668e7N2c5dc4fbe80283c4N2c5e8137266aa724N2c74b15282e83d06N2c9948f107dfd044N2ca817e96205abddN2cdb3f796cc0faf7N2d440e0fabca228fN2d72336b912094f1N2d74367bc4d880e1N2d8c3e37e7880f41N2dad84bf4d5d82bdN2dbe819c8e5b2fecN2dc11c54eabc6ff1N2dc35c2435c3e10bN2de1bd4be20d7d82N2e2197422d1be035N2e541bff8bf1f2e7N2e59ec57051cb20fN2e92d44d32983220N2eacb36c0701e921N2ecdb3a59d204a13N2ed96295437fb277N2efc49dbcff6e77bN2f6433541a3e3e16N2f9acd38b46cf072N2f9c4ba0dbee6554N3008bb235c58b71eN303546d1daa870bdN30374b80789c3283N30506f911d0b9508N307859abac0d6640N3080cf044680a1ccN308cba643af53ae1N30c4586073138655N30c6f5e45790b784N313274dd4d3aa8c7N3140e2816ba9b569N315545257c71f47bN3166812f628c70faN3173b38165eea085N31906473e3938ab3N319b0ddd8a0dd3dbN31a613c82c1d0a55N31d3a7c23015f324N32b5614be52a42feN32c5aab441b49093N3313ca5cd69679f4N332030e9966b46f1N335d8d57c6fca26bN3395c471c2538fc0N33971b15c3a6876bN33a130493e0f5156N33a98f9d3aef73adN33d821dea653e648N342efccd5101bfcfN34585025cde148b7N3460717a5253e123N3476858a47f2298eN348e8da8e918d27fN34be24dd4fc3d22aN34cd09940bbb0dcaN34dc0028eb1f6491N35246eddedf0505aN3527e10c1516bc58N352f21a050ca409cN35466ae3c98a1887N356315bd5713aee0N3563bb175cd5bc26N35970aa4d5498a63N35aadf0807e6891bN35c2965a0ccc1ecaN35d7779632fece28N35e4a3f869ab6cedN35e952eec6b3dd99N35f076473aae42c7N35fe3150d535e12bN361746166d47af2bN361f6d153c4676dbN362ce501804223d2N36418961e2e39048N36976452172f39afN369f862aab04c394N36be2399fba10580N3782c123cefc8e60N37a5c6425b1cbfbfN37f7c40eeabf24e1N3804b67956557ef7N3843b5d42da564d6N38ae3261a9d1ec95N3907bb6e2c955524N391085221e18d5baN39f9914c53d38d47N3a169277bf13cc8bN3a32708aa87583eeN3a736f229dc947a8N3aa907b7e64e54abN3aedc5bb5535a908N3b12b6a4415dbec7N3b22542ca3c9a0a2N3b38bc45976b2fa1N3b78cc04491df49aN3bbfd8610c54b9caN3bc6fcda8fdc986dN3c0bef9a443c3a9dN3c103196ea4dadfdN3c1fff36bed28bccN3c37d92388cdb6efN3c6940f5d85c6ee3N3c79b19db52f587eN3d0966ffa59a1e88N3d1e4d065617d728N3d38907a0b7384b4N3d5fba31dc2b2c75N3dd246add69f1b4bN3dd3a8b53bd461fcN3e089e7caf975d7dN3e1b19a48814e110N3e26bafe653ba00bN3e31bfaccb3bce29N3e4739956adcbc8eN3e509af5ab21c1a9N3e631d9e4150c621N3e650993eac3ad25N3e97a5f97852e5cdN3edec763d0822f03N3f0c68bdebeb73c8N3f976764bc1b3949"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_SMalloc () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "ARUN_1.A_GOT_TGA"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.A_MUSL_TGA"; "ARUN_1.A_TLSDESC_FS"; "ARUN_1.A_DTVP"; "ARUN_1.A_DTV"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.A_DTV1"; "ARUN_1.A_DTV1V"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "ARUN_1.A_CF_ITGA"; "ARUN_1.A_GOT_VERB"; "ARUN_1.A_VERB"; "ARUN_1.A_GOT_DTLS"; "ARUN_1.A_DTLSV"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.smalloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_DTLS_OTGA"; "ARUN_1.A_TGA_ICPT"; "ARUN_1.SMalloc.A_SM0_RA"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv_unsigned"; "ARUN_1.SMalloc.sm0_regs"; "ARUN_1.SMalloc.A_SM0_FOUND"; "Corelib.Init.Logic.not"; "ARUN_1.SMalloc.A_SM0_NONE"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.length"; "ARUN_1.SMalloc.scan0_post"; "ARUN_1.SMalloc.A_SM0_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "ARUN_1.SMalloc.sm0_A_post"; "ARUN_1.A_SMALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.shd"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.SMalloc.sm0_found_post"; "Corelib.Lists.ListDef.repeat"; "ARUN_1.SMalloc.smalloc0_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SMALLOC (k : Z) : Z :=                  (* [comment removed for export] *)
  match k with 0 => 0x52ef8 | 1 => 0x5306c | 2 => 0x531fc | 3 => 0x53398 | 4 => 0x53544 | _ => 0x53710 end.
Definition A_TLSDESC_FS : Z := 0x0f6b38.   (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_TGA_ICPT : Z := 0x5d06c.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GOT_TGA : Z := 0x0f7c08.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_MUSL_TGA : Z := 0x0eb5b4.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTVP : Z := 0x63ca88.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTV : Z := 0x63cab0.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTV1 : Z := 0x63cab8.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTV1V : Z := 0x63d290.       (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTLSV : Z := 0x63ca98.       (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DTLS_OTGA : Z := 0x805f0.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_CF_ITGA : Z := 0x19b5b1.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GOT_VERB : Z := 0x0f5ea0.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_VERB : Z := 0x199498.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GOT_DTLS : Z := 0x0f6b48.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition smalloc_statics (m : mem) (FS BLK T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "(0.(1.$2.O5.$3.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O5.$9.(4.$5.(:.(7.&40.$;.))(8.$5.)))(0.(1.$2.O5.$<.(4.$5.(:.(7.&40.+1.))(4.$5.(:.(7.&40.+?????????????800.))(8.$5.))))(0.(1.$2.O5.$=.(4.$5.(:.(7.&40.$>.))(8.$5.)))(0.(1.$2.O5.$?.(4.$5.(:.(7.&40.O4.))(8.$5.)))(0.(1.$2.O5.$10.(4.$5.(:.(7.&40.$11.))(8.$5.)))(0.(1.$2.O5.$12.(4.$5.(6.(7.&8.+1.))(4.$5.(13.#3.(4.(14.&8.)(7.&8.=)(4.(14.&8.)(7.&8.=)(4.(14.&8.)(7.&8.=)(8.(14.&8.))))))(4.$5.(15.(7.&40.=))(8.$5.)))))(0.(1.$2.O5.$16.(4.$5.(:.(7.&40.$17.))(8.$5.)))(0.(1.$2.O5.$17.(4.$5.(:.(7.&40.O1.))(8.$5.)))(0.(1.$2.O5.(18.O1.+98.)(4.$5.(:.(7.&40.O2.))(8.$5.)))(0.(1.$2.O5.$19.(4.$5.(:.(7.&40.$1:.))(8.$5.)))(0.(1.$2.O5.$1;.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O5.$1<.(4.$5.(:.(7.&40.$1=.))(8.$5.)))(0.(1.$2.O5.$1=.(4.$5.(15.(7.&40.=))(8.$5.)))(0.(1.$2.O5.$1>.(4.$5.(:.(7.&40.+8.))(8.$5.)))(0.(1.$2.O5.$1?.(4.$5.(:.(7.&40.O3.))(8.$5.)))(1.$2.O5.(18.O3.+18.)(4.$5.(:.(7.&40.$?.))(8.$5.)))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11022070611.11L15473608403.11L15820200019.11L16718068563.11L17682505955.11L1800699475.11 L19681308371.11L20234794067.11L21632378003.11L24694995923.11L33907719379.11L34844628819.11L38705866195.11L47238374355.11L53864989267.11L56836764115.1100000900B00K00T00]00f00o01801A01J01S01\01e01n02702@S3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTXS3BLK3CTX". (* [comment removed for export] *)
Lemma smalloc_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "PW,(20.$21.)Pm,P,(14.&40.)(22.(14.&8.))Pm',P,(14.&40.)(22.(14.&8.))PFS,$23.PBLK,$23.PT,$23.PCTX,$23.P,(24.R6.R4.R3.R2.R1.)P,(25.R8.R7.R6.)P,PA,$23.Pn,$23.P,(26.(0.(27.+10000.R2.)(27.(18.R2.R1.)+65?000.))(26.(0.(27.R5.R2.)(27.(18.R2.R1.)(18.R5.+10000.)))(0.(27.R7.R2.)(27.(18.R2.R1.)(18.R7.+1000.)))))(28.R<.R3.R2.)(24.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' FS BLK T CTX SS MU DJ. unfold smalloc_statics in *.
  unfold A_ASAN_INITED, A_GOT_TGA, A_TLSDESC_FS, A_TP, A_DTVP, A_DTV, A_DTV1, A_DTV1V, A_DTLSV, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_GOT_CFLAGS, A_CF_ITGA,
    A_GOT_VERB, A_VERB, A_GOT_DTLS in *.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- ro_cells _ _ ?A ?cs => eapply (ro_cells_transport asegs W m m' A cs); [tauto| exact MU| apply DJ; cbn; lia] end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11608697095.2000001S". (* [comment removed for export] *)
Lemma zbv_mod64 : forall x, Z_to_bv 64 (x mod 2^64) = Z_to_bv 64 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L2424960062.4000006S1n2Hn". (* [comment removed for export] *)
Lemma land_mask : forall c n, 0 <= n -> Z.land c (2^n - 1) = c mod 2^n.
Proof. intros c n Hn. rewrite <- (Z.land_ones c n) by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40349651931.2000001S". (* [comment removed for export] *)
Lemma land_16383 : forall c, Z.land c 16383 = c mod 16384. Proof. intros c. exact (land_mask c 14 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L5692428459.2000001S". (* [comment removed for export] *)
Lemma land_8191 : forall c, Z.land c 8191 = c mod 8192. Proof. intros c. exact (land_mask c 13 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L17208816571.2000001S". (* [comment removed for export] *)
Lemma land_4095 : forall c, Z.land c 4095 = c mod 4096. Proof. intros c. exact (land_mask c 12 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6163483787.2000001S". (* [comment removed for export] *)
Lemma land_2047 : forall c, Z.land c 2047 = c mod 2048. Proof. intros c. exact (land_mask c 11 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L17803660571.2000001S". (* [comment removed for export] *)
Lemma land_1023 : forall c, Z.land c 1023 = c mod 1024. Proof. intros c. exact (land_mask c 10 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51866039019.2000001S". (* [comment removed for export] *)
Lemma land_511 : forall c, Z.land c 511 = c mod 512. Proof. intros c. exact (land_mask c 9 ltac:(lia)). Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section SMalloc.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma dtls_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.PBLK,$23.PT,$23.PCTX,$23.Plo,$23.PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(22.(14.&8.))P,(0.(27.+1000.R7.)(26.(27.(18.R7.+1000.)+10000.)(27.+65?000.R7.)))P,(27.(18.R8.+1000.)(2:.VhAR,))P,(27.+65?000.R7.)P,(27.(18.R8.+10000.)(2:.VhAR,))P,(24.R5.R<.R;.R:.R9.)P,(2;.VCS,R<.+1000.)P,(2<.$2.R7.R:.R?.)P,(27.(2:.VhAR,)R;.)P,(27.R<.(2=.R11.+90.))P,(27.R12.(2>.+2.+3>.))P,(2;.VCS,R>.(2=.R13.R>.))P,(2?.$2.R<.)(30.$2.VAL,VCS,Lms',$31.(32.P,(14.&40.)(22.(14.&8.))Lm',P,(14.&40.)(22.(14.&8.))(32.(14.&40.)Lx11,(14.&40.)(32.(14.&40.)Lx12,(14.&40.)(32.(14.&40.)Lx13,(14.&40.)(0.(25.(4.(33.$23.$23.)(34.$23.$23.R15.R1:.)(8.(33.$23.$23.)))R12.R4.)(0.(35.$2.R12.R4.)(0.(2?.$2.R4.)(0.(2<.$2.R4.R15.R1:.)(36.$31.R5.(37.(38.R36.(7.&40.R1:.)R35.(7.&40.$?.)R34.R33.R32.R31.R30.(7.&40.=)R3.R2.R1.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R14.(39.R36.)R13.(3:.(14.&40.))R4.(3;.$2.)))))))))))(37.(38.R31.(7.&40.R15.)R30.(7.&40.$?.)R2?.R2>.R2=.R2<.R2;.(7.&40.$<.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R?.(7.&40.$3<.)R>.(3:.(14.&40.))R=.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo F fc m
      BL BH CL CH SS BCS ST LOIMG SPL SPH SCS MI.
    flat constr:(SS) 17%nat. intros _ _ DESC _ _ _ _ _ _ _ GCF ITGA GVB VB GDT DTP BE.
    unfold A_TLSDESC_FS, A_DTLS_OTGA, A_TP, A_GOT_CFLAGS, A_CFLAGS, A_CF_ITGA, A_GOT_VERB, A_VERB, A_GOT_DTLS, A_DTLSV in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide SS. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 80%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, MIl : mem_inv _ ?mx', STl : stk _ ?mx'' lo SP |- _ =>
      apply evtA_done; exists mx; do 3 eexists;
      split; [exact MUl|]; split; [exact WMl|]; split; [exact MIl|]; split; [exact STl| lx_mseq] end.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L26680463541.62L27846297964.3 L29149218542.1 L38235734261.1 L3958017386.4  L3958017390.4  L41599022925.2 L53826628947.3 L54437155233.0 L6353664149.1  L7872035019.54 L9448615682.3  L9448615686.2  L9678154644.12 00000@00G00K00O00P00Q00X00c00d00h01701801@01hS3hAR2SP2lo1y2HyS2SP2loS2SPS2loFFS2SP2loS2SP2lo3SPLSS2SPS3hAR2SP2lo3SPLFS2SP3SPHS3hAR2SP3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'". (* [comment removed for export] *)
  Lemma tga_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.PBLK,$23.PT,$23.PCTX,$23.Plo,$23.PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(22.(14.&8.))P,(0.(27.+1000.R7.)(26.(27.(18.R7.+1000.)+10000.)(27.+65?000.R7.)))P,(27.(18.R8.+1000.)(2:.VhAR,))P,(27.+65?000.R7.)P,(27.(18.R8.+10000.)(2:.VhAR,))P,(0.(27.+1000.R:.)(26.(27.(18.R:.+1000.)+10000.)(27.+65?000.R:.)))P,(27.(18.R;.+1000.)(2:.VhAR,))P,(24.R7.R>.R=.R<.R;.)P,(2;.VCS,R>.+1000.)P,(2;.VCS,R=.+10000.)P,(2;.VCS,R?.+1000.)P,(32.(14.&40.)Ltb,(14.&40.)(32.(14.&40.)Lte,(14.&40.)(1.$2.R=.(18.R12.+30.)(4.$5.(:.R2.)(4.$5.(:.R1.)(8.$5.))))))P,(2<.$2.R<.R?.R14.)P,(27.(2:.VhAR,)R10.)P,(27.R11.(2=.R16.+;0.))P,(27.R17.(2>.+2.+3>.))P,(2;.VCS,R13.(2=.R18.R13.))P,(2?.$2.R11.)(30.$2.VAL,VCS,Lms',$31.(32.P,(14.&40.)(22.(14.&8.))Lm',P,(14.&40.)(22.(14.&8.))(32.(14.&40.)Lx11,(14.&40.)(32.(14.&40.)Lx12,(14.&40.)(32.(14.&40.)Lx13,(14.&40.)(0.(25.(4.(33.$23.$23.)(34.$23.$23.R1:.R1?.)(8.(33.$23.$23.)))R17.R4.)(0.(35.$2.R17.R4.)(0.(2?.$2.R4.)(0.(2<.$2.R4.R1:.R1?.)(36.$31.R5.(37.(38.R3;.(7.&40.R1?.)R3:.(7.&40.$?.)R39.R38.R37.R36.R35.(7.&40.$?.)R3.R2.R1.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R19.(39.R3;.)R18.(3:.(14.&40.))R4.(3;.$2.)))))))))))(37.(38.R36.(7.&40.R1:.)R35.(7.&40.$?.)R34.R33.R32.R31.R30.(7.&40.$<.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R14.(7.&40.$3=.)R13.(3:.(14.&40.))R12.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo F fc m
      BL BH CL CH TL TH SS BCS CCS TCS (tb & te & TT) ST LOIMG SPL SPH SCS MI.
    flat constr:(SS) 11%nat. intros INI GTG DESC DTV TPFS DTV1 TSI TSP TSA TCX _.
    unfold A_TLSDESC_FS, A_TGA_ICPT, A_TP, A_ASAN_INITED, A_GOT_TGA, A_MUSL_TGA, A_DTVP, A_DTV, A_DTV1, A_DTV1V, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide SS. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x805f0] [] 80%N). lx_unhide.
    (* [comment removed for export] *)
    lazymatch goal with STl : stk _ ?mx lo (SP + -48), FRl : rw_cells _ _ (SP + -48) _ |- _ =>
      chunk_split FRl 2%nat FRx FRb; replace (SP + -48 + 16) with (SP + -32) in FRb by (clear; lia);
      lx_release STl FRx STl2; clear FRx STl; replace (SP + -48 + Z.of_nat 16) with (SP + -32) in STl2 by (clear; lia) end.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ =>
      eapply evtA_cut; [eapply dtls_spec with (SP := SP + -32) (FS := FS) (BLK := BLK) (T := T) (CTX := CTX) (lo := lo) (m := mx);
        first [exact BL | exact BH | exact CL | exact CH | exact BCS | exact LOIMG | assumption
              | eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL CH BH; lia
              | clear -SPL; lia | clear -SPH; lia
              | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia] ] |] end.
    cbv beta. intros ms1 (mB & x11 & x12 & x13 & MU1 & WM1 & MI1 & ST1 & ->).
    replace (ret_pc (Z_to_bv 64 0x5d0cc)) with (Z_to_bv 64 0x5d0cc) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRl : rw_cells _ _ (SP + -32) _ |- _ =>
      assert (FR1 : rw_cells asegs mB (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FRl| exact MU1| exact WM1| cbn; clear; lia]);
      assert (MU2 : munch [(lo, SP)] m mB) by (lx_munch MUl MU1);
      pose proof (wmono_trans asegs _ _ _ WMl WM1) as WM2;
      clear MU1 WM1 ST MI SS; lx_clear_mem mx; rename MU2 into MU; rename WM2 into WM; rename MI1 into MI; rename ST1 into ST
    end.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, MIl : mem_inv _ ?mx', STl : stk _ ?mx'' lo SP |- _ =>
      apply evtA_done; exists mx; do 3 eexists;
      split; [exact MUl|]; split; [exact WMl|]; split; [exact MIl|]; split; [exact STl| lx_mseq] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition A_SM0_RA : Z := 0x52f1c.      (* [comment removed for export] *) (* [comment removed for export] *)
  Definition A_SM0_LOOP : Z := 0x52f7c.    (* [comment removed for export] *)
  Definition A_SM0_NONE : Z := 0x52f98.    (* [comment removed for export] *)
  Definition A_SM0_FOUND : Z := 0x52ff4.   (* [comment removed for export] *)

  Definition sm0_regs (SP FS : Z) (gp t0 t1 t2 a0 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "(38.(7.&40.$3>.)(7.&40.(18.O19.-20.))O17.(7.&40.$?.)O16.O15.O14.(7.&40.O19.)(7.&40.O18.)O13.(7.&40.(18.O18.+1000.))O12.(7.&40.+3???.)O11.O10.O?.O>.(7.&40.+14.)O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition scan0_post (SP FS : Z) (gp t0 t1 t2 a4 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m : mem) (r cur : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Lms',$31.(26.(32.$23.Lr',$23.(32.$23.Lc,$23.(32.$23.Lpos,$23.(32.(14.&8.)Lb,(14.&8.)(0.(0.(27.=R3.)(3?.R3.(2>.+2.+40.)))(0.(36.$23.R2.(40.R3.+4000.))(0.(36.(22.(14.&8.))(41.(14.&8.)O4.(42.R2.))(43.(14.&8.)R1.))(0.(36.$23.(44.&8.R1.)=)(36.$31.R5.(37.(45.O1:.O19.O18.O17.O16.O15.(7.&40.R4.)(7.&40.R3.)O14.(7.&40.(18.(18.O19.+1000.)R2.))(7.&40.R2.)(7.&40.=)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(7.&40.$46.)O5.(3:.(14.&40.))O3.(3;.$2.)))))))))))(0.Pj,$23.P,(0.(27.=R1.)(3?.R1.O2.))(32.(14.&8.)Lb,(14.&8.)(0.(36.(22.(14.&8.))(41.(14.&8.)O4.(42.(40.(18.O1.R3.)+4000.)))(43.(14.&8.)R1.))(47.(36.$23.(44.&8.R1.)=))))(32.(14.&40.)Lx12,(14.&40.)(32.(14.&40.)Lx15,(14.&40.)(32.(14.&40.)Lx16,(14.&40.)(32.(14.&40.)Lx17,(14.&40.)(36.$31.R5.(37.(45.O1:.O19.O18.O17.O16.O15.(7.&40.=)R4.O14.R3.R2.R1.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(7.&40.$48.)O5.(3:.(14.&40.))O3.(3;.$2.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11608399893.9L3579524304.1200000100?SS3cur1j1q2rr1D". (* [comment removed for export] *)
  Lemma scan0_shift : forall cur j, (((cur + 1) mod 2^64) + (j - 1)) mod 16384 = (cur + j) mod 16384.
  Proof.
    intros cur j. pose proof (Z.div_mod (cur + 1) (2^64) ltac:(lia)) as D.
    set (q := (cur + 1) / 2^64) in *. set (rr := (cur + 1) mod 2^64) in *.
    replace (cur + j) with ((rr + (j - 1)) + (q * (2^64 / 16384)) * 16384) by (change (2^64 / 16384) with 1125899906842624; lia).
    rewrite Z_mod_plus_full. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L10103580561.5 L12529075241.4 L13278302029.2 L18941427511.50L23970772284.57L24663162352.45L2625671488.7  L29008555810.56L29994332920.5 L36364150030.54L59310648043.5 L60519880076.2 L60665368681.54L64930759789.5 L8929160544.6  00000800C00K00Z01002[02k03A03O03h04;04A04Z04h054S1n1r2HnS1r1j2Hj2NES3cur2PBS3hAR1n1r2fl2HnS3hAR1n1r3cur2fl2Hn2HrS3hAR2AL2CS1r3cur2gp2t02t12t22a43x153x163x172s32s42s52s62s72s82s93s103s112t32t42t52t62SP2FS2fl1F2fc1m2Hn2HrS1n1r2Hn2Kr1j2HjS3hAR1n1r3cur2fl2Hn2HrS1n1r2Hn2Hr2KrS3hAR1n1r3cur2FS2fl2Hn2PBS3cur2fl3FLL2PB3NTHS1r2HrS3hAR1n1r3cur2FS2fl2Hn2PBS1n1r2Hn2Hr2KrS1n1r3cur2Hn". (* [comment removed for export] *)
  Lemma scan0_loop : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pn,$49.Pr,$23.Pcur,$23.Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Pa4,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.Pfl,(20.(14.&8.))PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(22.(14.&8.))P,(36.$23.(4:.R1>.)R1=.)P,(0.(27.+1.R1>.)(27.R1>.(2>.+2.+>.)))P,(0.(27.=R1>.)(3?.R1>.(2>.+2.+40.)))P,(4;.$2.R4.(18.R8.+1000.)R7.)P,(36.$23.(4:.(4<.(14.&8.)R8.))(2>.+2.+>.))P,(2;.VCS,(18.R:.+1000.)(2>.+2.+>.))P,(27.+65?000.R;.)P,(27.(18.R<.+;09000.)(2:.VhAR,))P,(2?.$2.R9.)(30.$2.VAL,VCS,(4=.R?.R>.R24.R23.R22.R21.R20.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R<.R;.R=.R:.R26.R25.)(37.(45.R?.R>.R24.R23.R22.R21.(7.&40.R26.)(7.&40.R25.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R<.(7.&40.$4>.)R;.(3:.(14.&40.))R:.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros r cur gp t0 t1 t2 a4 x15 x16 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS fl F fc m
      Hn Hr Hc FLA FLL FLCS FS0 FS1 MI; [lia|].
    facts. unfold sm0_regs, A_SM0_LOOP, A_SM0_RA, A_TP in *.
    pose proof (Z.mod_pos_bound cur 16384 ltac:(lia)) as PB.
    destruct (nth_error fl (Z.to_nat (cur mod 16384))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear -NTH PB FLL; lia].
    pose proof (u8arr_read asegs m (FS + 4096) fl (cur mod 16384) b _ FLA NTH ltac:(clear -PB; lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. first [rewrite (land_16383 cur) | rewrite Z.land_comm, (land_16383 cur)].
    zstep. zstep. clear RD.
    zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *)
      cbv beta. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      replace (Z_to_bv 64 (bv_unsigned b)) with (Z_to_bv 64 0) by (rewrite Kb; reflexivity).
      apply evtA_done. left. exists r, cur, (cur mod 16384), b.
      split; [exact Hc|]. split; [reflexivity|]. split; [exact NTH|]. split; [exact Kb| reflexivity].
    - (* [comment removed for export] *)
      cbv beta in Kb. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      assert (NZ0 : exists b0 : byte, nth_error fl (Z.to_nat ((cur + 0) mod 16384)) = Some b0 /\ bv_unsigned b0 <> 0).
      { exists b. rewrite Z.add_0_r. split; [exact NTH| exact Kb]. }
      (* [comment removed for export] *)
      zstep. rewrite (swrap32_small (r + -1)) by (clear -Hr; lia).
      zstep.
      zstep. if_cases Kr; zify_cond Kr.
      + (* [comment removed for export] *)
        rewrite <- (zbv_mod64 (cur + 1)).
        eapply evtA_mono.
        * eapply (IH (r + -1) ((cur + 1) mod 2^64)); try eassumption; try (clear -Hn Hr Kr; lia).
          all: pose proof (Z.mod_pos_bound (cur + 1) (2^64) ltac:(clear; lia)) as MPB; clear -MPB; lia.
        * cbv beta. intros ms' [P | [ALL P]]; [left; exact P| right]. split; [| exact P].
          intros j Hj. destruct (Z.eq_dec j 0) as [->|NE]; [exact NZ0|].
          destruct (ALL (j - 1) ltac:(clear -Hj NE; lia)) as (b1 & N1 & Z1). exists b1. rewrite <- (scan0_shift cur j). split; [exact N1| exact Z1].
      + (* [comment removed for export] *)
        apply evtA_done. right. split.
        * intros j Hj. replace j with 0 by (clear -Kr Hr Hn Hj; lia). exact NZ0.
        * unfold A_SM0_NONE. replace (r + -1) with 0 by (clear -Kr Hr Hn; lia). do 4 eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition sm0_A_post (SP FS lo hint : Z) (ra gp t0 t1 t2 s0 s1 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Lms',$31.(32.P,(14.&40.)(22.(14.&8.))Lm1,P,(14.&40.)(22.(14.&8.))(0.(36.$31.R2.(37.(45.O1?.O1>.O1:.O19.O18.O17.(7.&40.+4000.)(7.&40.O1<.)(7.&40.(18.O1<.+4000.))(7.&40.+3???.)O13.O12.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(7.&40.$4>.)O2.(3:.(14.&40.))R1.(3;.$2.)))(0.(25.(4.(33.$23.$23.)(34.$23.$23.O1=.O1?.)(8.(33.$23.$23.)))O1.R1.)(0.(35.$2.O1.R1.)(0.(2?.$2.R1.)(0.(4?.$2.R1.(18.O1?.-20.)(4.$5.(:.O11.)(4.$5.(:.O15.)(4.$5.(:.O16.)(4.$5.(:.O1;.)(8.$5.))))))(2<.$2.R1.O1=.(18.O1?.-20.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11330676608.7 L11923395103.4 L16143243576.5 L25696891297.0 L26238223716.5 L26680464573.65L27846297964.3 L29753927507.3 L38235734261.1 L3958017386.4  L3958017390.4  L41599022925.2 L64915203461.5 L9448615682.3  L9448615686.2  L9678154644.12 00000F00T00i00j01:01J01Q01\01`01a01b01i02>02?02G02oS3hAR2SP1T2lo2TH5LOIMGS3hAR2lo5LOIMGS3hAR2FS2lo3FSH5LOIMGSS2SP2lo2A'2n'2H'S3hAR2SP2lo1y2HyS2SP2loS2SP2lo3SPLS2loFFS2SP2loS3hAR2FS2lo3FSH5LOIMGFS2SP3SPHS3hAR2SP3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'". (* [comment removed for export] *)
  Lemma sm0_A : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.PBLK,$23.PT,$23.PCTX,$23.Plo,$23.Phint,$23.PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(22.(14.&8.))P,(0.(27.+1000.R8.)(26.(27.(18.R8.+1000.)+10000.)(27.+65?000.R8.)))P,(27.(18.R9.+1000.)(2:.VhAR,))P,(27.+65?000.R8.)P,(27.(18.R9.+10000.)(2:.VhAR,))P,(0.(27.+1000.R;.)(26.(27.(18.R;.+1000.)+10000.)(27.+65?000.R;.)))P,(27.(18.R<.+1000.)(2:.VhAR,))P,(0.(27.+65?000.R?.)(26.(27.(18.R?.$50.)+7???7000.)(27.+10007???8000.R?.)))P,(27.(18.R10.$50.)(2:.VhAR,))P,(0.(27.=R<.)(3?.R<.(2>.+2.+40.)))P,(24.R:.R12.R11.R10.R?.)P,(2;.VCS,R12.+1000.)P,(2;.VCS,R11.+10000.)P,(2;.VCS,R13.+1000.)P,(32.(14.&40.)Ltb,(14.&40.)(32.(14.&40.)Lte,(14.&40.)(1.$2.R10.(18.R16.+30.)(4.$5.(:.R2.)(4.$5.(:.R1.)(8.$5.))))))P,(1.$2.R?.(18.R17.+58.)(4.$5.(:.(7.&40.+14.))(4.$5.(6.(7.&8.=))(8.$5.))))P,(4?.$2.R10.R18.(4.$5.(:.(7.&40.R13.))(8.$5.)))P,(2;.VCS,R19.+1000.)P,(2<.$2.R12.R16.R1;.)P,(27.(2:.VhAR,)R17.)P,(27.R18.(2=.R1=.+=0.))P,(27.R1>.(2>.+2.+3>.))P,(2;.VCS,R1:.(2=.R1?.R1:.))P,(2?.$2.R17.)(30.$2.VAL,VCS,(51.R21.R20.R1<.R1;.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1:.R19.R18.)(37.(38.R3>.(7.&40.R21.)R3=.(7.&40.$?.)R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R1:.(7.&40.(52.=))R19.(3:.(14.&40.))R18.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m
      BL BH CL CH TL TH FSL FSH HNT SS BCS CCS TCS TT HDR HC FCS ST LOIMG SPL SPH SCS MI.
    unfold kHighMemBeg, kFakeBytes in *. cbn [A_SMALLOC].
    flat constr:(SS) 6%nat. intros _ _ _ _ TPFS _. unfold A_TP in TPFS.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide SS. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x5d06c] [] 20%N). lx_unhide.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -32) |- _ =>
      eapply evtA_cut; [eapply tga_spec with (SP := SP + -32) (FS := FS) (BLK := BLK) (T := T) (CTX := CTX) (lo := lo) (m := mx);
        first [exact BL | exact BH | exact CL | exact CH | exact TL | exact TH | exact BCS | exact CCS | exact TCS | exact LOIMG | assumption
              | eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL CH BH; lia
              | (flat constr:(TT) 3%nat; flclear TT; intros tb te TT'); exists tb, te; eapply ro_cells_transport; [exact TT'| exact MUl| cbn; clear -LOIMG SPL TH; lia]
              | clear -SPL; lia | clear -SPH; lia
              | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia] ] |] end.
    cbv beta; intros ms1 (mA & x11 & x12 & x13 & MU1 & WM1 & MI1 & ST1 & ->).
    unfold A_TP in *; replace (ret_pc (Z_to_bv 64 0x52f1c)) with (Z_to_bv 64 0x52f1c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP + -32)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRl : rw_cells _ _ (SP + -32) _, TPl : ro_cells _ _ 6539920 _,
                        HDRl : ro_cells _ ?mx' (FS + 88) _, HCl : rw_cells _ ?mx'' FS _ |- _ =>
      assert (FR1 : rw_cells asegs mA (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FRl| exact MU1| exact WM1| cbn; clear; lia]);
      assert (TPFS' : ro_cells asegs mA 6539920 [C8 (Z_to_bv 64 FS)])
        by (eapply ro_cells_transport; [exact TPl| exact MU1| apply LO1; cbn; clear -LOIMG H; lia]);
      assert (HDR1 : ro_cells asegs mA (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)])
        by (eapply ro_cells_transport; [exact HDRl| exact MU1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (HC1 : rw_cells asegs mA FS [C8 (Z_to_bv 64 hint)])
        by (eapply rw_cells_transport; [exact HCl| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (MU2 : munch [(lo, SP)] m mA) by (lx_munch MUl MU1);
      pose proof (wmono_trans asegs _ _ _ WMl WM1) as WM2;
      clear MU1 WM1 ST MI TPFS HDR HC SS TT; lx_clear_mem mx; rename MU2 into MU; rename WM2 into WM; rename MI1 into MI; rename ST1 into ST
    end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x52f7c] [] 40%N).
    apply evtA_done. unfold sm0_A_post, sm0_regs, A_SM0_LOOP, A_SM0_RA, A_TP. exists lxm.
    lx_ands; [ lx_mseq | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sm0_none : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Px12,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.Plo,$23.Phint,$23.PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm0,P,(14.&40.)(22.(14.&8.))Pm,P,(14.&40.)(22.(14.&8.))P,(0.(27.+65?000.R7.)(26.(27.(18.R7.$50.)+7???7000.)(27.+10007???8000.R7.)))P,(27.(18.R8.$50.)(2:.VhAR,))P,(4?.$2.R3.R9.(4.$5.(:.(7.&40.R7.))(8.$5.)))P,(2;.VCS,R:.+1000.)P,(4?.$2.R5.(18.R<.-20.)(4.$5.(:.R1:.)(4.$5.(:.R1?.)(4.$5.(:.R20.)(4.$5.(:.R25.)(8.$5.))))))P,(2<.$2.R6.R;.(18.R=.-20.))P,(27.(2:.VhAR,)R<.)P,(27.R=.(2=.R?.+20.))P,(27.R10.(2>.+2.+3>.))P,(2;.VCS,R?.(2=.R11.R?.))P,(25.(4.(33.$23.$23.)(34.$23.$23.R10.R12.)(4.(33.$23.$23.)(34.$23.$23.R11.(18.R11.+8.))(8.(33.$23.$23.))))R<.R;.)P,(35.$2.R=.R<.)P,(2?.$2.R=.)(30.$2.VAL,VCS,Lms',$31.(32.P,(14.&40.)(22.(14.&8.))Lm',P,(14.&40.)(22.(14.&8.))(0.(36.$31.R2.(37.(38.R30.(7.&40.R17.)R2?.(7.&40.$?.)R2>.R2=.R2<.R2;.R2:.(7.&40.=)(7.&40.(18.R16.+1000.))R29.(7.&40.+3???.)(7.&40.(18.R14.+4000.))R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R13.(39.R30.)R12.(3:.(14.&40.))R1.(3;.$2.)))(0.(25.(4.(33.$23.$23.)(34.$23.$23.R15.R17.)(4.(33.$23.$23.)(34.$23.$23.R16.(18.R16.+8.))(8.(33.$23.$23.))))R11.R1.)(0.(35.$2.R11.R1.)(0.(2?.$2.R1.)(0.(4?.$2.R1.R16.(4.$5.(:.(7.&40.(18.R14.+4000.)))(8.$5.)))(2<.$2.R1.R15.R17.)))))))(37.(45.R15.R14.R2=.R2<.R2;.R2:.(7.&40.=)R27.(7.&40.(18.R12.+4000.))R26.R25.R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(7.&40.$48.)R10.(3:.(14.&40.))R>.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 x12 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo hint F fc m0 m
      FSL FSH HC FCS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm0_regs, A_SM0_NONE, A_SM0_RA, A_TP in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_post.
  Qed.

  (* [comment removed for export] *)
  Definition sm0_found_post (SP FS lo pos c : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Lms',$31.(32.(14.&40.)Lx5,(14.&40.)(32.(14.&40.)Lx11,(14.&40.)(32.(14.&40.)Lx12,(14.&40.)(32.(14.&40.)Lx13,(14.&40.)(32.(14.&40.)Lx14,(14.&40.)(32.(14.&40.)Lx15,(14.&40.)(32.(14.&40.)Lx16,(14.&40.)(32.(14.&40.)Lx17,(14.&40.)(32.P,(14.&40.)(22.(14.&8.))Lm',P,(14.&40.)(22.(14.&8.))(32.(20.(14.&8.))Lj1,(20.(14.&8.))(32.(20.(14.&8.))Lj2,(20.(14.&8.))ZFB,$23.(53.O1=.=O1;.)(0.(36.$31.R=.(37.(38.O19.(7.&40.O1>.)O18.(7.&40.$?.)R<.O16.O15.O14.O13.(7.&40.R1.)R;.R:.R9.R8.R7.R6.R5.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(39.O19.)O3.(3:.(14.&40.))R4.(3;.$2.)))(0.(25.(4.(33.$23.$23.)(34.$23.$23.O1<.O1>.)(4.(33.$23.$23.)(34.$23.$23.O1=.(18.O1=.+8.))(4.(33.$23.$23.)(34.$23.$23.(18.(18.O1=.+1000.)O1;.)(18.(18.(18.O1=.+1000.)O1;.)+1.))(4.(33.$23.$23.)(34.$23.$23.R1.(18.R1.+40.))(4.(33.$23.$23.)(34.$23.$23.(54.R1.)(18.(54.R1.)+8.))(8.(33.$23.$23.)))))))O1.R4.)(0.(35.$2.O1.R4.)(0.(2?.$2.R4.)(0.(4?.$2.R4.O1=.(4.$5.(:.(7.&40.(18.O1:.+1.)))(8.$5.)))(0.(4;.$2.R4.(18.O1=.+1000.)(55.(14.&8.)O2.(42.O1;.)(7.&8.+1.)))(0.(4?.$2.R4.R1.(4.$5.(13.#18.R3.)(4.$5.(:.(7.&40.O1>.))(4.$5.(13.#18.R2.)(4.$5.(:.(7.&40.(18.(18.O1=.+1000.)O1;.)))(8.$5.))))))(0.(4?.$2.R4.(54.R1.)(4.$5.(:.(7.&40.=))(8.$5.)))(0.(56.R4.)(2<.$2.R4.O1<.O1>.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L10187340561.105L12378669435.2  L12381266366.103L13335596837.102L13335596837.103L1641455751.102 L17120848823.0  L21943567510.16 L24642758929.105L24973756177.105L25456994354.102L25458997615.104L27048764373.98 L29984749841.105L3129187939.105 L32350501012.2  L32960757601.105L35842253073.105L37445298776.3  L38364278545.105L39188636933.0  L44706278166.105L45867630865.105L51489812398.74 L53726409072.2  L53830988561.105L54205848890.3  L54961663500.98 L55204150092.1  L55588686165.0  L57794683085.105L622053815.9    L62746513610.105L65271643703.0  L65919261776.2  00000T00\01001T02802R02S03F03j04N05605^06006T06U06]07407X07c08G08H09C09g0:F0:G0:k0;70;I0;M0;N0<90<\0=[0=\0=dS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3posS3hAR2FS3pos1c2fl2FBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FBSS3hAR2SP2FS2lo3pos2FB5LOIMG2PB3FBR2SR4FSL02A'2n'2H'S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos2fl2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0FS3pos2PBS3hAR2FS3pos1c2fl2FB2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0SS3hAR2FS3pos1c2fl2FB3FSA2Hc2HP3HFB3DFS3FBR2SR3FBA4FSL04FSL1S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB1y2HyFS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos3DFSS3hAR2FS3pos2fl2PBS2FBSS3hAR2FS3pos1c2fl2FB2Hc2HP3HFB3DFS3FBR4FSL0S3hAR2FS3pos2FB3FSL3FSH3HFB3DFS3FBRS3hAR2SP2FS2lo3pos1c2fl2FB3FSH2Hc2HP5LOIMG3SPL3HFB3DFS3FBR4FSL0SS2FS3pos". (* [comment removed for export] *)
  Lemma sm0_found : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa4,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.Plo,$23.Ppos,$23.Pc,$23.Pr',$23.Ph0,(14.&40.)Pfl,(20.(14.&8.))Pjunk,(20.(14.&8.))Psj,(20.(14.&8.))PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm0,P,(14.&40.)(22.(14.&8.))Pm,P,(14.&40.)(22.(14.&8.))ZFB,$23.(53.R=.=R;.)P,(0.(27.+65?000.R>.)(26.(27.(18.R>.$50.)+7???7000.)(27.+10007???8000.R>.)))P,(27.(18.R?.$50.)(2:.VhAR,))P,(36.$23.(40.R10.+1000.)=)P,(0.(27.=R>.)(3?.R>.(2>.+2.+40.)))P,(36.$23.R10.(40.R?.+4000.))P,(4?.$2.R7.R13.(4.$5.(:.R>.)(8.$5.)))P,(4;.$2.R8.(18.R14.+1000.)R>.)P,(36.$23.(4:.(4<.(14.&8.)R?.))(2>.+2.+>.))P,(4?.$2.R:.R9.(4.$5.(13.#40.R?.)(8.$5.)))P,(4?.$2.R;.(54.R:.)(4.$5.(13.#8.R?.)(8.$5.)))P,(2;.VCS,R18.$50.)P,(56.R=.)P,(4?.$2.R>.(18.R1;.-20.)(4.$5.(:.R29.)(4.$5.(:.R2;.)(4.$5.(:.R2<.)(4.$5.(:.R31.)(8.$5.))))))P,(2<.$2.R?.R1:.(18.R1<.-20.))P,(27.(2:.VhAR,)R1;.)P,(27.R1<.(2=.R1>.+20.))P,(27.R1?.(2>.+2.+3>.))P,(2;.VCS,R1>.(2=.R20.R1>.))P,(25.(4.(33.$23.$23.)(34.$23.$23.R1?.R21.)(4.(33.$23.$23.)(34.$23.$23.R20.(18.R20.+8.))(4.(33.$23.$23.)(34.$23.$23.(18.(18.R20.+1000.)R1>.)(18.(18.(18.R20.+1000.)R1>.)+1.))(4.(33.$23.$23.)(34.$23.$23.R13.(18.R13.+40.))(4.(33.$23.$23.)(34.$23.$23.(54.R13.)(18.(54.R13.)+8.))(8.(33.$23.$23.)))))))R15.R14.)P,(35.$2.R16.R15.)P,(2?.$2.R16.)(30.$2.VAL,VCS,(57.R24.R23.R22.R21.R20.R3:.R39.R38.R37.R36.R35.R34.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1:.R19.R1=.R18.)(37.(45.R24.R23.R39.R38.R37.R36.(7.&40.R1?.)(7.&40.R20.)R33.(7.&40.(18.(18.R23.+1000.)R21.))(7.&40.R21.)(7.&40.=)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R1:.(7.&40.$46.)R19.(3:.(14.&40.))R17.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' h0 fl junk sj F fc m0 m FB
      FSL FSH FSA Hc HP HC FLA FLL FRM FSHD FCS PS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm0_regs, A_SM0_FOUND, A_SM0_RA, A_TP in *.
    assert (HFB0 : FB = fsk_frame FS 0 pos) by reflexivity. clearbody FB. unfold shd in *.
    assert (HFB : FB = FS + 36864 + pos * 64) by (rewrite HFB0; unfold fsk_frame; clear; lia).
    pose proof (Z.mod_pos_bound c 16384 ltac:(clear; lia)) as PB. rewrite <- HP in PB.
    pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
    assert (FB8 : FB = (FS / 4096 * 512 + 4608 + pos * 8) * 8) by (rewrite HFB; clear -DFS; lia).
    assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + pos * 8) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; rewrite FB8, Z.div_mul; [reflexivity| clear; lia]).
    assert (FBR : FS + 36864 <= FB /\ FB + 64 <= FS + 36864 + 2^20) by (rewrite HFB; clear -PB; lia).
    assert (SR : 0x80000000 <= 2147450880 + Z.shiftr FB 3 /\ 2147450880 + Z.shiftr FB 3 + 8 <= 0x10007fff8000) by (rewrite FBD; clear -FBR FSL FSH DFS HFB; lia).
    assert (FBA : FB mod 8 = 0) by (rewrite FB8; apply Z_mod_mult).
    clear FB8 FBD.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP); (FS, FS + 8); (FS + 4096 + pos, FS + 4096 + pos + 1); (FB, FB + 64); (2147450880 + Z.shiftr FB 3, 2147450880 + Z.shiftr FB 3 + 8)] m) as MUS.
    pose proof (wmono_refl asegs m) as WMS.
    flat constr:(PS) 10%nat. intros _ GSB SBC GMB MB GME ME GHE HE _.
    unfold A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND in GSB, SBC, GMB, MB, GME, ME, GHE, HE.
    lx_hide PS. lx_aceil. flat constr:(FSL) 2%nat. flclear FSL. intros FSL0 FSL1. flat constr:(FLA) 2%nat. flclear FLA. intros FLAb FLAw.
    (* [comment removed for export] *)
    lx_run (PLAN [0x53008] [] 10%N).
    (* [comment removed for export] *)
    lazymatch goal with FLAl : bytes_at _ ?mx (FS + 4096) fl, WMl : wmono _ m _ |- _ =>
      pose proof (conj FLAl (wr_at_transport _ _ _ _ _ FLAw WMl) : u8arr asegs mx (FS + 4096) fl) as FLAx; clear FLAl FLAb end.
    pose proof (u8arr_store_ok asegs _ (FS + 4096) fl pos _ FLAx ltac:(rewrite FLL; clear -PB; lia) eq_refl) as SOK.
    zstep. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      pose proof (u8arr_write asegs mx (FS + 4096) fl pos (Z_to_bv 8 1) FLAx ltac:(rewrite FLL; clear -PB; lia)) as FLA'
    end.
    store_done. try clear FLAx. try clear SOK.
    flat constr:(FLA') 2%nat. flclear FLA'. intros FLAb2 FLAw2.
    assert (FLz : Z.of_nat (length (upd fl (Z.to_nat pos) (Z_to_bv 8 1))) = 16384) by (rewrite upd_length, FLL; reflexivity).
    (* [comment removed for export] *)
    lx_run (PLAN [0x53018] [] 20%N).
    repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] =>
      lazymatch b with context [pos] => replace (a + b) with FB by (rewrite HFB; clear; lia) end end.
    (* [comment removed for export] *)
    destruct FSL1 as [FSLO|FSHI]; lx_run (PLAN [] [] 90%N); lx_unhide;
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', FLl : bytes_at _ ?mx'' (FS + 4096) _ |- _ =>
        apply evtA_done; unfold sm0_found_post; cbv zeta; rewrite <- HFB0; unfold shd;
        lx_exs; lx_ands;
        [ lx_mseq
        | eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUl]; lx_subfp]
        | exact (wmono_trans asegs _ _ _ WM WMl)
        | assumption | assumption
        | split; [exact FLl| rewrite upd_length; exact (wr_at_transport _ _ _ _ _ FLAw WMl)]
        | match goal with K : rw_cells _ _ FB [_; _; _; C8 (Z_to_bv 64 ?e)] |- _ => replace e with (FS + 4096 + pos) in K by (clear; lia); exact K end
        | replace (2147450880 + Z.shiftr FB 3) with (Z.shiftr FB 3 + 2147450880) by (clear; lia); assumption
        | eapply (poison_statics_transport _ _ _ PS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL FSL0 FBR SR PB H; lia
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition smalloc0_post (SP FS BLK T CTX lo hint : Z) (fl : list byte)
      (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Lms',$31.(32.(14.&40.)Lx5,(14.&40.)(32.(14.&40.)Lx11,(14.&40.)(32.(14.&40.)Lx12,(14.&40.)(32.(14.&40.)Lx13,(14.&40.)(32.(14.&40.)Lx14,(14.&40.)(32.(14.&40.)Lx15,(14.&40.)(32.(14.&40.)Lx16,(14.&40.)(32.(14.&40.)Lx17,(14.&40.)(32.P,(14.&40.)(22.(14.&8.))Lm',P,(14.&40.)(22.(14.&8.))(32.$23.Lr,$23.(0.(36.$31.R;.(37.(38.O18.(7.&40.O20.)O17.(7.&40.$?.)R:.O15.O14.O13.O12.(7.&40.R1.)R9.R8.R7.R6.R5.R4.R3.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(39.O18.)O2.(3:.(14.&40.))R2.(3;.$2.)))(0.(35.$2.O1.R2.)(0.(2?.$2.R2.)(0.(2<.$2.R2.O1;.O20.)(0.(24.R2.O1?.O1>.O1=.O1<.)(0.(56.R2.)(32.$23.Lpos,$23.(32.$23.Lc,$23.(32.(14.&8.)Lb,(14.&8.)(32.(20.(14.&8.))Lj1,(20.(14.&8.))(32.(20.(14.&8.))Lj2,(20.(14.&8.))ZFB,$23.(53.O1?.=R5.)(0.(36.$23.R7.R1.)(0.(0.(27.=R5.)(3?.R5.(2>.+2.+40.)))(0.(36.$23.R6.(40.R5.+4000.))(0.(36.(22.(14.&8.))(41.(14.&8.)O19.(42.R6.))(43.(14.&8.)R4.))(0.(36.$23.(44.&8.R4.)=)(0.(25.(4.(33.$23.$23.)(34.$23.$23.O1;.O20.)(4.(33.$23.$23.)(34.$23.$23.O1?.(18.O1?.+8.))(4.(33.$23.$23.)(34.$23.$23.(18.(18.O1?.+1000.)R6.)(18.(18.(18.O1?.+1000.)R6.)+1.))(4.(33.$23.$23.)(34.$23.$23.R1.(18.R1.+40.))(4.(33.$23.$23.)(34.$23.$23.(54.R1.)(18.(54.R1.)+8.))(8.(33.$23.$23.)))))))O1.R8.)(0.(4?.$2.R8.O1?.(4.$5.(:.(7.&40.(18.R5.+1.)))(8.$5.)))(0.(4;.$2.R8.(18.O1?.+1000.)(55.(14.&8.)O19.(42.R6.)(7.&8.+1.)))(0.(4?.$2.R8.R1.(4.$5.(13.#18.R3.)(4.$5.(:.(7.&40.O20.))(4.$5.(13.#18.R2.)(4.$5.(:.(7.&40.(18.(18.O1?.+1000.)R6.)))(8.$5.))))))(4?.$2.R8.(54.R1.)(4.$5.(13.#8.(58.(14.&8.)(7.&8.=)#8.))(8.$5.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).                   (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L16648947209.1 L17120848823.0 L2106043955.7  L21943567510.23L222370686.1   L226564034.2   L22706556426.7 L2416881682.3  L27157704107.5 L28302452952.3 L3045768613.0  L32350501012.2 L36518867962.2 L39188636933.0 L45051584734.1 L47128140407.9 L51213415004.2 L52172457863.2 L55588686165.0 L62083074719.1 L622021552.7   L62546499173.1 L63489361093.10L63489361093.6 L64913007653.5 L65271643703.0 L65919261776.2 L9678154644.5  00000400500P01h01i02202H02S02i03503603>03G03H03L04004104204304704T04X05=05T05j05k06306CS2FSSS3hAR2FS2lo5LOIMG3pos2FB2SRS3hAR2SP2FS3BLK3CTX2lo2BH2CH3BHI3CHI4SEP14SEP25LOIMG4FSL'4FSH'3pos2PB2FB3HFB2SR2A'2n'2H'FS2FS4FSL'S2SP2FS2lo3pos2FB1y2HyS2SP2lo3SPLS3hAR2FS2lo5LOIMG4FSH'S2FS3pos3DFSSS3pos2PBS4hint2i0SS2FSS3hAR2FS2lo5LOIMG4FSH'3pos2PB2FB3HFBFFSS2FSS3hAR2FS4FSL'4FSH'3pos2PB3DFSS2FSS3hAR3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'S3hAR2lo5LOIMG2A'2n'2H'S3hAR2FS2lo5LOIMG4FSH'SS2FS3posS2SP2lo2A'2n'2H'". (* [comment removed for export] *)
  Lemma smalloc0_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc ()) "Pra,(14.&40.)Pgp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$23.PFS,$23.PBLK,$23.PT,$23.PCTX,$23.Plo,$23.Phint,$23.Pfl,(20.(14.&8.))PF,(29.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(22.(14.&8.))P,(0.(27.+1000.R9.)(26.(27.(18.R9.+1000.)+10000.)(27.+65?000.R9.)))P,(27.(18.R:.+1000.)(2:.VhAR,))P,(27.+65?000.R9.)P,(27.(18.R:.+10000.)(2:.VhAR,))P,(0.(27.+1000.R<.)(26.(27.(18.R<.+1000.)+10000.)(27.+65?000.R<.)))P,(27.(18.R=.+1000.)(2:.VhAR,))P,(0.(27.+65?000.R10.)(26.(27.(18.R10.$50.)+7???7000.)(27.+10007???8000.R10.)))P,(27.(18.R11.$50.)(2:.VhAR,))P,(36.$23.(40.R12.+1000.)=)P,(0.(27.=R>.)(3?.R>.(2>.+2.+40.)))P,(0.(0.(27.+1000.R13.)(26.(27.(18.R13.+1000.)+10000.)(27.+65?000.R13.)))(26.(27.(18.R13.+1000.)+7???7000.)(27.+10007???8000.R13.)))P,(0.(27.+65?000.R12.)(26.(27.(18.R12.+10000.)+7???7000.)(27.+10007???8000.R12.)))P,(26.(27.(18.R13.+10000.)R16.)(27.(18.R16.$50.)R13.))P,(26.(27.(18.R16.+1000.)R17.)(27.(18.R17.$50.)R16.))P,(24.R?.R18.R17.R16.R15.)P,(56.R10.)P,(2;.VCS,R19.+1000.)P,(2;.VCS,R18.+10000.)P,(2;.VCS,R1:.+1000.)P,(2;.VCS,R1=.$50.)P,(32.(14.&40.)Ltb,(14.&40.)(32.(14.&40.)Lte,(14.&40.)(1.$2.R17.(18.R1>.+30.)(4.$5.(:.R2.)(4.$5.(:.R1.)(8.$5.))))))P,(1.$2.R16.(18.R1?.+58.)(4.$5.(:.(7.&40.+14.))(4.$5.(6.(7.&8.=))(8.$5.))))P,(4?.$2.R17.R20.(4.$5.(:.(7.&40.R1;.))(8.$5.)))P,(4;.$2.R18.(18.R21.+1000.)R1;.)P,(36.$23.(4:.(4<.(14.&8.)R1<.))(2>.+2.+>.))P,Pi,$23.Pb,(14.&8.)P,(0.(27.=R2.)(3?.R2.(2>.+2.+>.)))P,(36.(22.(14.&8.))(41.(14.&8.)R20.(42.R3.))(43.(14.&8.)R2.))P,(36.$23.(44.&8.R3.)=)(32.(20.(14.&8.))Ljunk,(20.(14.&8.))(32.(20.(14.&8.))Lsj,(20.(14.&8.))(0.(4?.$2.R21.(53.R2:.=R7.)(4.$5.(13.#40.R2.)(8.$5.)))(4?.$2.R21.(54.(53.R2:.=R7.))(4.$5.(13.#8.R1.)(8.$5.))))))P,(32.$23.Li0,$23.(32.(14.&8.)Lb0,(14.&8.)(0.(0.(27.=R2.)(3?.R2.+4000.))(0.(36.(22.(14.&8.))(41.(14.&8.)R20.(42.R2.))(43.(14.&8.)R1.))(36.$23.(44.&8.R1.)=)))))P,(2<.$2.R1<.R21.R26.)P,(27.(2:.VhAR,)R22.)P,(27.R23.(2=.R28.+=0.))P,(27.R29.(2>.+2.+3>.))P,(2;.VCS,R25.(2=.R2:.R25.))P,(2?.$2.R21.)(30.$2.VAL,VCS,(59.R2<.R2;.R2:.R29.R28.R27.R26.R25.R49.R48.R47.R46.R45.R44.R43.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R24.R23.R22.)(37.(38.R49.(7.&40.R2<.)R48.(7.&40.$?.)R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R24.(7.&40.(52.=))R23.(3:.(14.&40.))R22.(3;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
      BL BH CL CH TL TH FSL FSH FSA HNT BHI CHI SEP1 SEP2 SS PS BCS CCS TCS FCS TT HDR HC FLA FLL HFR FREE ST LOIMG SPL SPH SCS MI.
    pose proof FSL as FSL'. pose proof FSH as FSH'. unfold kHighMemBeg, kFakeBytes in FSL', FSH', BHI, CHI, SEP1, SEP2.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (sm0_A ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m);
        first [eassumption | eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia]]. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    assert (FLA1 : u8arr asegs m1 (FS + 4096) fl)
      by (eapply u8arr_transport; [exact FLA| exact MU1| exact WM1| apply LO1; rewrite <- (Nat2Z.id (length fl)), FLL; clear -LOIMG FSH'; lia]).
    assert (HC1 : rw_cells asegs m1 FS [C8 (Z_to_bv 64 hint)])
      by (eapply rw_cells_transport; [exact HC| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH'; lia]).
    assert (SS1 : smalloc_statics m1 FS BLK T CTX)
      by (eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG CH BH; lia).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ _ _ PS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (scan0_loop (Z.to_nat 16384) 16384 hint); first [reflexivity | exact HNT | exact FLA1 | exact FLL | exact MI1 | clear; lia | idtac];
        [eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia] | clear -FSL'; lia | exact FSH']. }
    cbv beta. intros ms2 [(r' & c & pos & b & Hc & HP & NTH & Hb & ->) | (ALL & x12 & x15 & x16 & x17 & ->)].
    - (* [comment removed for export] *)
      assert (PB : 0 <= pos < 16384) by (rewrite HP; apply Z.mod_pos_bound; clear; lia).
      destruct (HFR pos b ltac:(clear -PB; lia) NTH Hb) as (junk & sj & FRM & FSHD).
      set (FB := fsk_frame FS 0 pos) in *.
      assert (HFB : FB = FS + 36864 + pos * 64) by (subst FB; unfold fsk_frame; clear; lia).
      pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
      assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + pos * 8).
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
        replace FB with ((FS / 4096 * 512 + 4608 + pos * 8) * 8) by (rewrite HFB; clear -DFS; lia). rewrite Z.div_mul; [reflexivity| clear; lia]. }
      assert (SR : 0x80000000 <= shd FB /\ shd FB + 8 <= 0x10007fff8000) by (unfold shd; rewrite FBD; clear -PB FSL' FSH' DFS; lia).
      assert (FRM1 : rw_cells asegs m1 FB [CB 64 junk])
        by (eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH' HFB PB; lia]).
      assert (FSHD1 : rw_cells asegs m1 (shd FB) [CB 8 sj])
        by (eapply rw_cells_transport; [exact FSHD| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG SR; lia]).
      assert (MUW : munch [(lo, SP); (FS, FS + 8); (FS + 4096 + pos, FS + 4096 + pos + 1); (FB, FB + 64); (shd FB, shd FB + 8)] m m1).
      { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros y Hy. lia. }
      eapply evtA_mono.
      { eapply (sm0_found ra gp t0 t1 t2 s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' _ fl junk sj F fc m m1);
          first [sassumption | cassumption | exact FSL | exact FSH | exact FSA | exact Hc | exact HP | exact HC1 | exact FLA1 | exact FLL | exact FRM1 | exact FSHD1
                | exact FCS | exact PS1 | exact FR1 | exact ST1 | exact LOIMG | exact SCS | exact MUW | exact WM1 | exact MI1
                | clear -SPL; lia | clear -SPH; lia]. }
      cbv beta. intros ms3 (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m3 & j1 & j2 & -> & MU3 & WM3 & MI3 & HC3 & FLA3 & FRM3 & FSH3 & PS3 & ST3).
      unfold smalloc0_post. exists x5, x11, x12, x13, x14, x15, x16, x17, m3, FB.
      split; [reflexivity|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU3). intros A' n' H'. cbn. change (fsk_frame FS 0 pos) with FB.
               clear -H' LOIMG CH BH FSL' FSH' HFB SR PB BHI CHI SEP1 SEP2. lia. }
      split; [exact PS3|].
      exists pos, c, b, j1, j2. cbv zeta.
      split; [reflexivity|]. split; [exact Hc|]. split; [exact HP|]. split; [exact NTH|]. split; [exact Hb|].
      split; [exact MU3|]. split; [exact HC3|]. split; [exact FLA3|]. split; [exact FRM3|].
      eapply rw_cells_reshape; [exact FSH3| cbn; split; [reflexivity| exact I] | vm_compute; reflexivity].
    - (* [comment removed for export] *)
      exfalso. flat constr:(FREE) 5%nat. flclear FREE. intros i0 b0 Hi0 N0 Z0.
      destruct (ALL ((i0 - hint) mod 16384) ltac:(apply Z.mod_pos_bound; clear; lia)) as (b1 & N1 & Z1).
      rewrite Zplus_mod_idemp_r in N1. replace (hint + (i0 - hint)) with i0 in N1 by (clear; lia).
      rewrite Z.mod_small in N1 by exact Hi0. rewrite N0 in N1. injection N1 as <-. exact (Z1 Z0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SMalloc.

End ARUN_1.
