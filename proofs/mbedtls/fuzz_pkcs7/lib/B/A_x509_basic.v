(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_bool A_asn1_get_int_loops A_asn1_get_int A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_basic_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001492db071c853d 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P0094c6066ffd5614 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P00abe744aaaaa80c 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P00da42acf6be427b 0 4 0 1 61 1 74 1 75 1P015138c39337dae6 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P0187f75873d37480 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P022a8be00e628abb 0 4 0 1 61 1 74 1 75 1P02c3d8f40602636c 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P037c51af10e0cee8 0 4 0 1 61 1 74 1 75 1P03ab7ca237135e45 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P03ecbb3e31e7700e 0 4 0 1 66 1 74 1 75 1P03fc1cbf22891f70 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P04513676cd8bf9a3 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P04a23ae4ebb0e473 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P0530355301c22f78 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P06a4f76344087562 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P071aec87424513d1 0 5 0 1 40 1 61 1 74 1 75 1P07371a83a202cbb8 0 4 0 1 61 1 74 1 75 1P07644d6eb4dc77ca 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P07b153e87ed220bf 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P089044b125d6b0c4 0 6 0 1 62 1 63 1 66 1 74 1 75 1P08bed90d6ecd293d 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P0a0b6ace9508f723 0 4 0 1 66 1 74 1 75 1P0a3a9aae2aa7ffd7 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P0a3b56ec10540e71 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P0a99daa4b721b35b 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P0ab844db33bbcc10 0 4 0 1 66 1 74 1 75 1P0adcb7240bf029e2 0 4 0 1 66 1 74 1 75 1P0b13c5e2b4af27ab 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P0b9f5df980342c1a 0 6 0 1 62 1 63 1 66 1 74 1 75 1P0c47a5a201395959 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P0ccb325aa49d25c2 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P0d6e21bfd9ba8113 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P0d77c3c3cd88b35c 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P0d85e6fb0f9496a4 0 5 0 1 40 1 61 1 74 1 75 1P0da5b496a3a9335e 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P0dc7c93d21478095 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P0f06442cd6730501 0 4 0 1 61 1 74 1 75 1P0fb25efa3725f3d0 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P0ff697ec9722ad02 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P110d54713f509108 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P1150899ed26145c8 0 4 0 1 66 1 74 1 75 1P116049b1cf5c1566 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P1163448b707ededc 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P120c57871898f735 0 4 0 1 61 1 74 1 75 1P12e82a2d57f21227 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P143ac72720ad8afd 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P148a56a16539498f 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P14c6dac01cfc2af6 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P150da59cb84df2f1 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P15912eabaaaff80b 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P15ab60c8d232694a 0 4 0 1 66 1 74 1 75 1P15c0a7bfd51f9672 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P15f81d0c50da407c 0 5 0 1 40 1 61 1 74 1 75 1P169ad51a1e72c9ee 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P171a26453afe85f7 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P17972d48ce86bf54 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P18680b4a8f18363c 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P190f5a153e37e3be 0 5 0 1 40 1 61 1 74 1 75 1P19331d6dfc226ebb 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P19c57a747b8ebef8 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P1a2d4a92214bea5b 0 4 0 1 66 1 74 1 75 1P1b9c4db27d3e905f 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P1c037a264c74c27e 0 4 0 1 61 1 74 1 75 1P1c62a63cd24672af 0 6 0 1 62 1 63 1 66 1 74 1 75 1P1d5db6866eb79871 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P1db5ce27511591a6 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P1ddbe18b317fe601 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P1df9563bdb7ddd07 0 5 0 1 40 1 61 1 74 1 75 1P1e7381721c5a25de 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P1e8a0f352f76b9d7 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P1e98ba56ac243bf9 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P1ec7011a3270ec7e 0 3 0 1 46 1 52 1P1f1705baa61b88e8 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P1f93999b7fa3caae 0 4 0 1 66 1 74 1 75 1P202fab4d2d44e36b 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P206ef6d6a6914ac0 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P20d44b861eb6c236 0 5 0 1 40 1 61 1 74 1 75 1P20d5da8a56e120c8 0 5 0 1 40 1 61 1 74 1 75 1P20ed4270c6b44f7d 1 1 16 2 38 1 74 1 3 0 1 75 1 76 16P21298f0caa757856 0 4 0 1 66 1 74 1 75 1P213f1acaed6ebacb 0 5 0 1 40 1 61 1 74 1 75 1P215c035dfbf9dda1 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P218010b4f2941acd 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P2196d1665b049460 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P21b2c24f0708602f 0 5 0 1 40 1 61 1 74 1 75 1P22310a1377a5d20c 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P230431b846f52d86 0 4 0 1 61 1 74 1 75 1P23cf9a44506f0285 0 4 0 1 61 1 74 1 75 1P24a8891d81f258c1 0 4 0 1 66 1 74 1 75 1P24b22b75b6118e3a 0 6 0 1 62 1 63 1 66 1 74 1 75 1P24ff145be1e8781d 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P251fb35d46835768 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P26148459b7ef7f0e 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P2622929cca2649e8 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P27341fb35caec9e1 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P27b7a50bf878f946 0 4 0 1 61 1 74 1 75 1P27c3f027d1bb3f5d 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P27d5a422ce6753ee 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P287bb4e35e2de0c5 0 6 0 1 62 1 63 1 66 1 74 1 75 1P289f767aa70b64b7 0 5 0 1 40 1 61 1 74 1 75 1P28ecd7abda6b1bee 0 6 0 1 62 1 63 1 66 1 74 1 75 1P298b33a745de130e 0 6 0 1 62 1 63 1 66 1 74 1 75 1P299384f940fd5243 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P2aa75e9f67cf61d2 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P2aa818579b05dea5 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P2ab3035764a3dddb 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P2b64cf09516f04b0 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P2c08737e2767ccfc 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P2d781da44e8374ab 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P2dfaa907da38f103 0 6 0 1 62 1 63 1 66 1 74 1 75 1P2e3dba166b26d365 0 6 0 1 62 1 63 1 66 1 74 1 75 1P2e52fb055c7f4a45 0 4 0 1 66 1 74 1 75 1P2e837adc7805009c 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P2ea5e62d334775e9 0 4 0 1 66 1 74 1 75 1P2ed743bcfaacece9 0 3 0 1 47 1 55 1P2fd620281ca88863 0 5 0 1 40 1 61 1 74 1 75 1P305f45e15c8dc9b4 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P317c10c876bfcdbf 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P318f6182565b37c9 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P321c6ca20ad1a02a 0 6 0 1 62 1 63 1 66 1 74 1 75 1P322b886540df0adc 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P327dc9e676ff43bf 0 5 0 1 40 1 61 1 74 1 75 1P32a301f313d42bea 0 4 0 1 61 1 74 1 75 1P335e3661381e1839 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P33ab603ecd762f5a 0 4 0 1 61 1 74 1 75 1P33ca18dd38be35c0 0 6 0 1 62 1 63 1 66 1 74 1 75 1P33e9c6888b71298f 0 4 0 1 66 1 74 1 75 1P340eb96739aa4de1 0 4 0 1 61 1 74 1 75 1P3437cee74ecf06a4 0 5 0 1 40 1 61 1 74 1 75 1P34baf590a0e7af58 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P360b44938913de99 0 6 0 1 62 1 63 1 66 1 74 1 75 1P362afdc22269702b 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P36536ae1d5f607ff 0 4 0 1 61 1 74 1 75 1P37ae365c6aba1be4 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P37ba3cea7100b316 1 1 16 2 0 1 74 1 3 10 1 75 1 76 16P37c67531ecb41d4c 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P386615e3ca2fb386 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3879e3aab0216baf 2 64 1 1 8 3 2 1 77 1 78 1 5 0 2 68 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 4 0 2 77 2 78 2 80 16P389b7c8719117873 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P38fd99c334485a6a 1 1 16 2 1 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P399c61e835492478 0 4 0 1 66 1 74 1 75 1P39c3d9140bdb61c0 2 62 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P3a5e606fd27f7b3c 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P3a612764a17610ef 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3acf5c09d816cff7 1 2 16 3 0 1 48 1 76 1 16 3 1 1 47 1 75 1 2 77 1 78 1P3ada30f377e7cb27 1 1 16 3 1 1 47 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3af8ee3bc28bf216 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3c2a6aee96c8b779 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P3c3ecd46587f176d 0 6 0 1 62 1 63 1 66 1 74 1 75 1P3c46efefc711363d 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3cf2da32264c808d 2 63 1 1 4 3 2 1 77 1 78 1 5 0 4 68 4 76 4 79 4 80 16 1 1 4 3 1 1 76 1 79 1 4 0 4 77 4 78 4 80 16P3e8fa8868ced3d1e 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P3ebf1ff66249f998 0 6 0 1 62 1 63 1 66 1 74 1 75 1P3ee03348932dae27 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16P3ee1a3561bf023dc 3 61 0 2 1 1 2 1 0 5 0 1 3 1 69 1 77 1 78 1 0 4 0 1 2 1 77 1 78 1P3f28af593119c1bf 0 5 0 1 40 1 61 1 74 1 75 1P3fb0a4c60c1659fb 1 1 16 4 1 1 43 1 49 1 75 1 7 46 1 56 1 63 1 64 1 67 1 76 1 77 16N005c308c74d2bf39N00c87f168802632cN01f98d2ff78256d5N0257ddd666c5a08dN02ac824314a69ac5N03f4cf9fccf79089N05eddaa5331514f8N069af545a046a30dN06d7453f874c8ac4N075130504aa69cc6N0914b7b59085c4e3N09a8d486ac0c2784N0ae835b93e557b05N0c6d1f2a7ad34ecfN0cb309e2647de8b4N0eb27bda2509936bN0ed6f50b427fc428N0f3d803c4e49991eN0f455137cfacca98N0f63f79028064acfN1118afd22821caf0N1134c4c06b821db7N11a91f0868506121N11de482cd669b6ebN128cee819f201e5cN12bc76effa6147cdN13a40ea8a527bb60N13df77e6e1265037N14189807e4cd5167N1419bedbd79078d1N1524feb727e48df3N15b85dda732e795eN160e34b70ff68791N195c9543a511b15fN1b2d71c9e7e13e16N1c39f7302b5d0258N1dbca4da0f36c2e9N1e13daf8b7e9e8dcN20ee923fa358dc84N21149c1400983df6N227c05fcf55383b8N22dc9139dcde0feeN24a200135c26f655N263f291907e8331eN27a357857eff74adN27efb94f7dbc998aN28f62ec332de2182N2ac6d9964edbf28fN2cef3f89a580230fN2d92d0eb36dd8491N2ee78a63f6f8cc5bN2fbd5972899ba44dN2fe4a1e1add3314fN2fe4ed550a919e63N30c6e09fc97d61d1N32f6811c1a3d394dN338413be15d5584dN3434c639036c3baaN358fbba97261d2e2N360b39da2b1f6f41N36d86e82d70ab3afN370829ca33b9ba09N3779d873f25f8fd5N3814773d6daa47b4N3860bfa7574ed259N38793393c0a87c92N390ea699aeb64263N3922ebe5b830a8ecN3a96e6db838c9ab5N3af86befe41b9021N3be061ef546b3230N3f6212ca4b19997dN3f99ee411fa1ee7eN3ff87433566f83ac"%lxh.
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
Ltac2 gd_tbl_A_x509_basic () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_basic_A.x509_basic_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_basic_A.A_X509_BASIC"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_basic_A.x509_basic_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GB : asn1_get_bool_stmtA asegs AL A_ASN1_GET_BOOL.
  Hypothesis GI : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CA MP P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CA \/ CA + 4 <= PP.
  Hypothesis D2 : PP + 8 <= MP \/ MP + 4 <= PP.
  Hypothesis D3 : CA + 4 <= MP \/ MP + 4 <= CA.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ CA + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= CA.
  Hypothesis D6 : Z.of_nat (length bs) = 0 \/ MP + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MP.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CA mod 4 = 0.
  Hypothesis AL3 : MP mod 4 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis CAB : 0 < CA /\ CA + 4 <= 2^64.
  Hypothesis MPB : 0 < MP /\ MP + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_BASIC_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 144 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CA + 4 <= lo \/ bv_unsigned sp <= CA.
  Hypothesis DS3 : MP + 4 <= lo \/ bv_unsigned sp <= MP.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo CA 4.
  Hypothesis CR3 : client_range L (LB ++ fdata LF) lo MP 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CA 4.
  Hypothesis CW3 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MP 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_BASIC_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_basic_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP CA MP P END lo slo).
  Local Notation W := [(PP, PP + 8); (CA, CA + 4); (MP, MP + 4)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.

  Ltac rw_at_hyp :=
    match goal with
    | H : rw_cells _ ?m ?A' ?cs |- rw_cells _ ?m ?A _ =>
        first [ exact H | replace A with A' by (clear; lia); exact H ]
    end.
  Ltac bw_side :=
    first
      [ eassumption
      | lazymatch goal with
        | |- rw_cells _ _ _ _ => rw_at_hyp
        | |- crange _ _ _ => solve_crange
        | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
        | |- wcover _ _ _ _ _ _ _ => solve_wcover
        | |- shadow_free _ _ _ _ _ _ _ =>
            first [ match goal with WL : wlow _ _ _ |- _ => apply (shadow_free_of_wlow _ _ _ _ _ _ _ WL); qlia end
                  | match goal with WL : wlow _ _ _, FR : fresh_apart _ _ _ _ _, HHx : HM _ _ _ _ _ _ _ |- _ =>
                      eapply (shadow_free_of_fresh' _ _ _ _ _ _ _ _ _ _ _ _ _ WL FR HHx); qlia end ]
        | |- forall b, In b _ -> In b _ =>
            let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
            first [ exact Hb | apply fdata_cons_sub; exact Hb | right; exact Hb ]
        | |- forall x, _ <= x < _ -> _ \/ in_block _ x =>
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            first [ left; clear_disj; lia
                  | right; match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; clear - Hx; lia] end
                  | right; exists (x - (x - _), 64) ]
        | |- _ \/ _ => first [ solve [clear_mods; clear_disj; lia] | pqlia ]
        | |- _ => first [ qlia | pqlia ]
        end ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01m0@D10639329459.135D15748604667.136D18607476203.177D23993074991.137D2455714710.204 D27392810573.204D32457002573.204D3254889317.176 D3373657269.204 D33956323578.178D33956323578.179D33956323578.180D41440366531.204D42088721945.136D46793042006.135D50254960491.178D51604233958.178D51604233958.179D51604233958.180D53232575014.178D53232575014.179D53232575014.180D560907437.138  D57437304838.178D57437304838.179D57437304838.180D60098777666.136D60109265003.137D60111245650.135D62011770191.138D6395731754.178 D65842053514.137D68405212918.204D6909863155.204 L10989370580.5  L12583145818.129L15756354262.7  L17921795213.192L19013159470.0  L19959024712.1  L19980016842.7  L29738741675.1  L3551623394.2   L35680140202.3  L38996969702.129L39268637205.0  L39332637397.0  L39618635427.2  L40228640085.0  L40753528314.3  L43055370171.127L48117620905.110L50790731766.8  L52249874585.0  L57355539152.178L58790154276.6  L59308677456.15 L59922446343.1  L60558678699.1  L63738252715.1  L64009471222.1  L6406266636.194 L65357366945.0  L7040749983.130 L7422344154.193 L9356559645.13  L9873114841.7   P1056307012.176 P1056307012.178 P13035286404.176P13035286404.178P36462068749.177P36465839390.176P48728591664.176P48728591664.178Q10523111610.143Q10651763882.145Q10651763890.140Q12660624649.148Q1530342990.178 Q15742314711.141Q15742314715.146Q18960117882.141Q21829627469.204Q23925414036.149Q23927511187.143Q23993074983.147Q23993074987.142Q27944911788.204Q31021924279.176Q31805155683.204Q32147227074.142Q32436491433.204Q33196749132.148Q33963892682.204Q35653441506.121Q38250992823.150Q40271359350.178Q42082427957.141Q42082427961.146Q42439168719.176Q42441479401.151Q43878048875.150Q46805771343.145Q46805771351.140Q47230721791.143Q48119867062.204Q49077563264.204Q50796826103.178Q53718120221.204Q59867617334.151Q60109315147.121Q6192914196.176 Q62009673036.149Q62011770187.143Q63266981118.140Q64681502656.151Q65842053506.147Q65842053518.142Q67026483294.177Q67038703949.176Q6909863155.204 Q9356560156.159 Q9487040953.143 Q9646450869.204 00000G00^00_01601701Y02;02<02=02g03Q03R04404K04b04c04d04e04f04g04h04i05H05I05J05K05k06K06k07D07g08>08?08a0940:30:A0:B0:C0:H0:`0:d0:k0;50;L0;M0;N0;X0;Y0;e0<C0<b0=30=40=50=K0=^0=b0=f0=j0=n0>T0>U0?@0?b0@Q0@m0Ad0B[0CR0DI0E10E20Ei0F`0G00G>0GL0G[0H10H?0HM0Ha0Ho0IB0Ia0Io0J=0JZ0K90Kl0L@0LA0LP0MF0Mh0N60NI0NW0Ne0O;0OQ0Ob0P00P>0PO0Pn0QK0Qf0Qg0Qh0R<0RK0RX0Re0S90S\0Sj0T80T[0U>0UL0Uc0Ud0V=S2LF2sp2PP2CA2MP2bs3LFBS2LF2sp2PP2CA2MP2bs3LFBFS2LF2sp2PP2CA2MP2bs3LFBFS2LF2sp2PP2CA2MP2bs3LFB3sp13H242FBS2LF2sp2PP2CA2MP2bs3LFB3sp13H242FBFFS2LF2sp2PP2CA2MP3BUF2bs3LFB3sp13H243x142HxS2LF2sp2PP2CA2MP3BUF2bs3LFB3sp13H243x142HxFS2LF2sp2PP2CA2MP2bs3LFB3sp13H242FBS2LF2sp2PP2CA2MP2bs3LFBS2LF2sp2PP2CA2MP2bs3LFBFFFFFFFS1R3HIA1h2LF2sp2PP2CA2MP2bs3LFBFFFS1R2LF2sp2PP2CA2MP2lo2bs3LOS3LFBS1R2LF2sp2PP2CA2MP2lo2bs3LOS3LFBS1R2LF2sp2PP2CA2MP2lo2bs3LOS3LFBS1R2LF2sp2PP2CA2MP2bs3LFBS2LF2sp2PP2CA2MP2bs3LFB3sp13H223H24S2LF2sp2PP2CA2MP2bs3LFBFS2LF2sp2PP2CA2MP2bs3LFB3sp13H242FBS2sp2lo3SLO3sp13SP1S2LF2sp2PP2CA2MP2bs3PPB3CAB3MPB3SPA3LFB3SPR3sp13H203H213H223H24S1R2lo3LOS3ALOFSS3sp1S1R3HIA1h2sp3TOP3sp13SP1S2FBS2bs2EQS2FB2x22HxS2LF2sp2PP2CA2MP2bs3LFBSSS3sp14SP1MSS2sp3sp13SP1S2LF2sp2PP2CA2MP2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSSFS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2spS2FBS2FBS2bsS2LF2sp2PP2CA2MP2bs3LFB3sp13H223H242FBSS2LF2sp2PP2CA2MP2bs3CAB3LFB3SPR3sp13H203H24S2LF2sp2PP2CA2MP2bs3LFB3sp13H242FBS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2MP1P3END3BUF2lo2bs2B12B22B33SLO3DS33LFB3sp13SP1S2LF2sp2MP1P3END3BUF2lo2bs2B12B22B33SLO3DS33LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2CA1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2CA1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H22S2LF2CA2bs3LFBS2LF2CA2bs3LFBS2LF2PP2CA2MP2bs3LFBS2LF2bs3LFB2FBS1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS2LF2MP2bs3LFBS2LF2MP2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'S2LF2PP2CA2MP2bs3LFBFS2LF3BUF2bs3LFBS2LF2sp2PP2CA2MP2bs3PPB3CAB3MPB3LFB3SPR3sp13H242FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBS1R3HIA1h2LF2bs3LFBS2LF2CA2bs3LFBS2LF2CA2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R2LF2sp2lo2bs3SLO3LOS3LFBFFS1R2LF2lo2bs3LOS3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS2LF2PP2CA2MP2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS2LF2MP2bs3LFBS2LF2MP2bs3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H233H24FS1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_basic ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pca0,(0.&40.)Pmp0,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VCA,(4.$5.(9.R4.)(8.$5.)))P,(3.$2.Vm,VMP,(4.$5.(9.R4.)(8.$5.)))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VCA,+4.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VMP,+4.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VCA,VMP,VP,VEND,Vlo,Vslo,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R19.R18.R17.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VCA,)(7.&40.VMP,)R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until mp0.
  intros HH HPP HCA HMP HBUF ST SS MI OPP OCA OMP OBUF.
  unfold A_X509_BASIC.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 225%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -128) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64);
                  [ exact HHc | exact LFB | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
                  | exact LOS | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SLO3 SP1; lia
                  | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SP1 TOP; lia
                  | assumption | exact TPV | reflexivity ])
      end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      (* [comment removed for export] *)
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 0)) with 64%nat in FRM by reflexivity.
      replace (64 * 2 ^ 0) with 64 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [24; 8; 8; 16; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HLEN FRM3. chunk_split FRM3 1%nat FD2 G2.
      replace (FB + 24 + 8) with (FB + 32) in HLEN, FD2, G2 by (clear; lia).
      replace (FB + 32 + 8) with (FB + 40) in FD2, G2 by (clear; lia). replace (FB + 40 + 16) with (FB + 56) in G2 by (clear; lia).
      cb8_to_c8 HLEN (@nil cell).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -128 + 24) with (bv_unsigned sp + -104) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -128) |- _ => release_frame FRa ST2x (bv_unsigned sp + -104); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 16) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell). rename SLOT0 into SLOT.
      (* [comment removed for export] *)
      assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo CA 4 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client _ LB LF lo MP 4 FB 64 FRSH CR3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP3.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_basic_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_basic ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.=)$23.)(24.$2.R5.R4.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  pose proof (A_asn1_get_bool_spec (L := arl_L R) (arl_AL R) IMG) as GB. pose proof (A_asn1_get_int_spec (L := arl_L R) (arl_AL R) IMG) as GI.
  unfold x509_basic_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
