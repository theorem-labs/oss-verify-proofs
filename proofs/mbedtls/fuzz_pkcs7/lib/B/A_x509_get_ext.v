(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_ext_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P011081fe675efd03 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P01340a4541b46c07 0 6 0 1 59 1 60 1 63 1 71 1 72 1P02515fa9fc6886e4 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P02597e018b0ca410 0 4 0 1 58 1 71 1 72 1P02c922a4a5907ff9 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P03146b52182f4da8 0 5 0 1 37 1 58 1 71 1 72 1P0329aa994718cbb1 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P04180285e23d1f1e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P049c4eb7e52c9a4a 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P052c1ae29f0629a4 0 4 0 1 63 1 71 1 72 1P05713d7f7f6cdf06 0 4 0 1 58 1 71 1 72 1P05dcb28f32f9e87f 0 4 0 1 63 1 71 1 72 1P05f791105b4ee444 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P05fcb6d29b08cb24 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0679a4ff09da168e 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P069b05de0722c8f5 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P06c27a9121d1235b 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P06cbc5784e57843c 0 3 0 1 43 1 49 1P06ea9bd613c90994 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P06ef89b0d57057a6 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P079052a47ee322ad 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P07a6aa928c799bfa 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0800827e1195a004 0 6 0 1 59 1 60 1 63 1 71 1 72 1P083ec25e2dfa9992 0 5 0 1 37 1 58 1 71 1 72 1P0a2c4488f9934ca9 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0b0d80c0ce434f77 0 5 0 1 37 1 58 1 71 1 72 1P0bda603a03573c63 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0cc859433c0ab352 0 5 0 1 37 1 58 1 71 1 72 1P0cd1965cc6dbec04 0 5 0 1 37 1 58 1 71 1 72 1P0d1cb84bdacdb716 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0d8499022e000503 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0d99596a0a42a987 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0ecb82f54c5afb03 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0effeec7f205769e 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0f2540ac8dcf7693 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0f357254d6a1c45b 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0f5c663f86a11df2 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1054e4005f4880dc 0 4 0 1 58 1 71 1 72 1P10e5559e9cba858e 0 4 0 1 58 1 71 1 72 1P1157e157048a99eb 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P118cae6279323323 0 5 0 1 37 1 58 1 71 1 72 1P11e1159ebf47978a 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P12035295657994f8 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P125a0f43acd03183 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P137b8e7dabdd13b8 0 5 0 1 37 1 58 1 71 1 72 1P139875133bcc816e 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P13c9cb991fb8d43e 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1413310bb0a0a3a9 0 5 0 1 37 1 58 1 71 1 72 1P1416adca092764a7 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1493ef037ab4e7c7 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P14a37c3056a96550 0 4 0 1 58 1 71 1 72 1P15190f52827e517e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P155debee4648859e 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P157df7bb21aa0a01 0 4 0 1 58 1 71 1 72 1P15a11f5c71b035c3 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P164ced20920a6356 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P165d65c0c9f21a09 0 4 0 1 63 1 71 1 72 1P17735f90e581e4f2 0 4 0 1 58 1 71 1 72 1P179a105eafe3fde5 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P17b87b68f7d9e641 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P17c92a29e99d78b0 0 4 0 1 58 1 71 1 72 1P18ad8d02ceee9830 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P18b5fbb3130a4c44 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P190143a217be2e13 0 6 0 1 59 1 60 1 63 1 71 1 72 1P19688e01ad689891 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P199a978c43b5c023 0 4 0 1 63 1 71 1 72 1P19a0f093b8813733 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1a8f0b0895f25719 0 4 0 1 63 1 71 1 72 1P1ac51eb98664550c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1ae95cd0e756c49e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1b98e5c922757969 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1c3e75216528d874 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1ca5d18313ffd906 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1d3be85d6b870de7 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1e351fd8a47e624d 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1e76099bfb9b0b6e 0 4 0 1 63 1 71 1 72 1P1ec496bde7dacf2b 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1f8a1cb1290828bb 0 4 0 1 63 1 71 1 72 1P1f9466e86bff33f4 0 4 0 1 63 1 71 1 72 1P1fed8bbd754bc666 0 4 0 1 63 1 71 1 72 1P1fef485e950c06fc 0 5 0 1 37 1 58 1 71 1 72 1P20c6671378a9a594 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2150af6f26882bc0 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P23744df88775e428 0 4 0 1 58 1 71 1 72 1P23c3c120d61d046c 0 4 0 1 58 1 71 1 72 1P23f53a2fb631cf00 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P245b56ef75ba83d4 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P2524aa41684775a8 0 6 0 1 59 1 60 1 63 1 71 1 72 1P25bf355c4f58a8a7 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P26135ec94989d81e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2614eae169d7e6ff 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P26648abb215d2b49 0 4 0 1 58 1 71 1 72 1P26907291e98cdf6f 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P26f8f1bfdc35dfec 0 4 0 1 63 1 71 1 72 1P27ab37ac87f19a17 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P28920c49b215ea38 0 3 0 1 44 1 52 1P28a45c5adc908759 0 4 0 1 63 1 71 1 72 1P290495af8059815e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P29d635a781b5ae9d 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2b51df1ef00d2c1b 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2be9bbf04d36e2de 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2bfe37a6d9883c1d 0 4 0 1 58 1 71 1 72 1P2c4d192afd401371 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2c53b54e729b806b 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2cbfcf795c8c7ff9 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2d9c88a0387f3d52 0 4 0 1 63 1 71 1 72 1P2e41f6a68e6ae1c9 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2eb7c7ce976fd1aa 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3120a5c03e15c7bc 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P31724b050542fc60 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P31d8fd1e4ba963d5 0 5 0 1 37 1 58 1 71 1 72 1P325bb96a8bf79109 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P338f98437452c316 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P33dd0585e4e5cff6 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P33ee5bf5f0aa215b 0 4 0 1 63 1 71 1 72 1P34a3da2185eea2dc 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P34b8d6044a267d8d 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P34da77918a3b10e5 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P34e038e39e29a0a8 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P36110ce8b0d61dfb 0 4 0 1 58 1 71 1 72 1P36df926d45d943f4 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P36eb24672e741def 0 5 0 1 37 1 58 1 71 1 72 1P37871e14a3f4c066 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P37927997817adbfb 0 5 0 1 37 1 58 1 71 1 72 1P37abce858b573f13 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P37d7fac96c0e2212 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P37ef8b7a5db23fe0 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3a839320b194091c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3aaab9501a3b7712 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3c290b6b20d0f086 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3d5d891739d80fe7 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3e4b2c9ffa81c3a6 0 5 0 1 37 1 58 1 71 1 72 1P3f7a2b3b2d9bdbe3 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3fa9a7e3d0246f38 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1N008e023b45ea0cd4N00d649c835bba888N0169c619ad270599N01ec1b31eb347f07N04491c2769d5c530N044aa0ae8c9198c8N056cf216794daa73N05e095ece22e0ac8N0777d9e5734cfad8N082d997f0353d1e1N0892656f7ec0aa65N0a4753001469b6e4N0a93ebc58df4f033N0adc2070fcb6a51eN0bc07f8088954b49N0bd958c3b405c578N0dc98fa103ccd252N10a9a7bb9ec08283N119ca6cdf558365bN137726b578c6d4f1N141c03cb2aa29791N150cfdc444d445c4N153dab4c18b73a2aN17edd159d2765a6eN18984c11f1c4d75fN1a5797dbe90e0a1aN1b49a3369876c4e3N1c741c12e6b036feN1f7e4f3cd51dd0aaN207cee3214fdb991N20c36d048b71ea56N21183c59678794a9N22cc3cd45db42988N23a1d17fc640a7a9N2564f1cc4f0a9d38N2589d00229d173e4N299f60ad2e18a583N2c2f55d9e5d85dd2N2cd7527a8b5fe494N2d75f73919061c30N2deb014a5dee1d36N2e91342fb2a534c9N30f014452bbd8cbfN31edee81cdd61c74N3236308513151428N328365e101acf9bcN32e0bf036a0cba8dN34aff3358666b08fN3d7ff5212f935906N3d825b33e700f5deN3e6465d8f52302acN3e7e2f3a04432870N3ea1e25fcb5f1386N3ff504b0dfb378bf"%lxh.
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
Ltac2 gd_tbl_A_x509_get_ext () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_ext_A.x509_get_ext_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_ext_A.A_X509_GET_EXT"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_ext_A.x509_get_ext_stmtA"].


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
            (PP EXT P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= EXT \/ EXT + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ EXT + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= EXT.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : EXT mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SGB : 0 < EXT /\ EXT + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_GET_EXT_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 144 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : EXT + 24 <= lo \/ bv_unsigned sp <= EXT.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo EXT 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) EXT 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_GET_EXT_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_get_ext_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP EXT P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (EXT, EXT + 24)].
  Local Notation SAVEL := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis LFB : (length LF < 512)%nat.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01a0@D10639329459.125D18607476203.164D19005365622.165D19005365622.166D19005365622.167D2459889674.191 D27388597713.191D32452855249.191D3254889317.163 D3386124073.191 D33956323578.165D33956323578.166D33956323578.167D41452831839.191D46793042006.125D50254960491.165D53232575014.165D53232575014.166D53232575014.167D55388259819.126D560907438.127  D56744380514.126D60098777666.126D60111245650.125D62011770188.127D6395731754.165 D68409458026.191D6897397615.191 L10989370580.5  L12583145818.122L15756354262.7  L17921795213.184L19013159470.0  L19980016842.7  L25985555144.1  L26258305825.0  L29738741675.1  L3551623394.2   L35680140202.3  L38996969702.119L39076636629.0  L39332637397.0  L39618635427.2  L40228640085.0  L43055370171.117L43554043994.180L44847795975.1  L48117620907.105L50790731766.8  L52249874585.0  L57355539152.169L58790154276.6  L59308677456.15 L60558678699.1  L63738252715.1  L64009471222.1  L6406266636.181 L7040749983.123 L9356559645.13  L9826573818.3   L9873114841.7   P1056307012.163 P1056307012.165 P25675156076.163P25675156076.165P36462068749.164P36465839390.163Q10523111608.131Q10651763882.133Q10651763890.129Q12660624644.135Q1530342990.165 Q21584170359.130Q21842126289.191Q23927511185.131Q23927511197.136Q27940636720.191Q31021924279.163Q31801074431.191Q32440606517.191Q32681887700.131Q33196749121.135Q33967969366.191Q3482560409.191 Q35653441506.111Q38248895676.137Q40216283646.191Q40271359350.165Q42439168719.163Q42439382240.138Q43880146016.137Q46805771343.133Q46805771351.129Q47230721789.131Q48132468010.191Q49081869340.191Q50796826103.165Q55390359488.130Q55390359493.134Q56754864713.130Q56754864716.134Q59865520191.138Q60109315147.111Q60740903729.129Q6192914196.163 Q62011770181.136Q62011770185.131Q64683599817.138Q67026483294.164Q67038703949.163Q6897397615.191 Q9356560156.146 Q9633850153.191 00000E00F00G00H00I00J00j01J01K01L02402\02]03=03R03S03T03U03V03k04H04]05;05Y06006Q06R07207E08>08L08M08N08f08k08l09009709A09V09W09X09b09c0:?0:_0:c0;B0;S0;T0;U0;k0<>0<B0<F0<J0<n0=S0>B0>N0>j0?a0@X0AP0BH0C00C10CA0CO0C]0Cl0DB0DT0Db0EA0ET0F10FP0GC0GD0GE0GT0HD0I50IW0Ie0If0J90JO0Je0K60KD0KR0Kc0LB0L_0M:0MI0MX0Mg0N60N70NK0N]0Nl0O90OF0Oi0PL0Po0Q=0QT0QmS2LF2sp2PP3EXT2bs3LFBFFFFFS2LF2sp2PP3EXT2bs3LFB3sp13H222FBS2LF2sp2PP3EXT2bs3LFB3sp13H222FBFFS2LF2sp2PP3EXT3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP3EXT3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP3EXT2bs3LFB3sp13H222FBS2LF2sp2PP3EXT2bs3LFBFFFFS2LF2sp2PP3EXT2bs3LFBS1R3HIA1h2LF2sp2PP3EXT2bs3LFBS2LF2sp2PP3EXT2bs3LFBS1R2LF2sp2PP3EXT2lo2bs3LOS3LFBS1R2LF2sp2PP3EXT2lo2bs3LOS3LFBS1R2LF2sp2PP3EXT2bs3LFBS2LF2sp2PP3EXT2bs3LFB3sp13H203H22FS2LF2sp2PP3EXT2bs3LFB3sp13H222FBS2sp2lo3SLO3sp13SP1S2LF2sp2PP3EXT2bs3PPB3SGB3SPA3LFB3SPR3sp13H183H193H203H22S1R2lo3LOS3ALOFSS1R3HIA1h2sp3TOP3sp13SP1S3sp1SS2FBS2bs2EQS2FB2x22HxS2LF2sp2PP3EXT2bs3LFBSSS3sp14SP1MSS2LF2sp2PP3EXT2lo2bs3SLO3LFBS2LF2sp2PP3EXT2bs3LFB3sp13H222FBS2spS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSSFS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS2FBS2bsS2LF2sp2PP3EXT2bs3LFB3sp13H203H222FBS2LF2sp2PP3EXT2bs3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp3EXT1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp3EXT1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2PP3EXT2bs3LFBS2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'FFS2LF3BUF2bs3LFBS2LF2sp2PP3EXT2bs3PPB3SGB3LFB3SPR3sp13H222FB3F64S2LF2sp2PP3EXT2bs3PPB3SGB3LFB3SPR3sp13H224SP1M2FBS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF3EXT2bs3LFBS2LF3EXT2bs3LFBS2LF3EXT2bs3LFBS2LF3EXT2bs3LFBFS1R2LF2lo2bs3LOS3LFBS2LF2PP3EXT2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_ext ()) "Ptag,$0.Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Ptg0,(1.&40.)Plen0,$0.Pq0,$0.P,(2.$3.VR,VHIA,Vh,VLB,VLF,Vm,)P,(4.$3.Vm,VPP,(5.$6.(7.(8.&40.VP,))(9.$6.)))P,(4.$3.Vm,VEXT,(:.R5.Vpad,R4.R3.))P,(;.$3.Vm,VBUF,Vbs,)P,(<.$3.Vm,Vlo,(=.&40.Vsp,))P,(>.$3.(?.VR,)Vm,Vslo,(=.&40.Vsp,))P,(10.$3.Vm,)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VPP,+8.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VEXT,+18.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VBUF,(13.(14.(1.&8.)Vbs,)))(15.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)(16.$3.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VEXT,VP,VEND,Vlo,Vslo,Vpad,Vm,)(17.(18.Vra,Vsp,Vgp,Vtp,R18.R17.R16.Vs0,Vs1,(8.&40.VPP,)(8.&40.VEND,)(8.&40.VEXT,)(8.&40.R19.)R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(8.&40.$19.)Vfc,(1:.(1.&40.))Vm,(1;.$3.)))")
(* [comment removed for export] *).
  Proof.
  intros until q0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_GET_EXT.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  unfold buf_cells in HSG.
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 191%N). lx_tree.
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
      zstep. zstep. zstep.
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
      replace (bv_unsigned sp + -128 + 32) with (bv_unsigned sp + -96) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -128) |- _ => release_frame FRa ST2x (bv_unsigned sp + -96); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -96) (sp1 + 24) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell). rename SLOT0 into SLOT.
      (* [comment removed for export] *)
      assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo EXT 24 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      pose proof (hm_abase asegs R HIA h1 LB _ m3 ltac:(eassumption)) as AB3.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (tag := tag) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_get_ext_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_ext ()) "PR,$1<.PHIA,(1=.$3.R1.)P,(1>.(?.R2.))P,(1?.$0.(20.R3.)$21.)P,(1?.$0.(22.R4.=)$23.)(24.$3.R5.R4.$19.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  unfold x509_get_ext_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
