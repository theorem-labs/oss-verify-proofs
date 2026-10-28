(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int_loops A_asn1_get_int
     A_oid A_oid_md_alg A_asn1_get_alg_A A_asn1_get_alg A_asn1_get_alg_null_A A_asn1_get_alg_null A_x509_hash_alg_A A_x509_hash_alg A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_hash_alg.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_rsassa_pss_A A_x509_rsassa_pss_B A_x509_rsassa_pss_C.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0013390df4e00d68 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P00741be6af7681e5 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P00c14a34156f0bd2 0 5 0 1 43 1 64 1 82 1 83 1P020bf171c0f2950f 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P023a5d60c616dadf 0 6 0 1 65 1 66 1 73 1 82 1 83 1P02cb819a79349b83 0 5 0 1 43 1 64 1 82 1 83 1P031ef27738ab7143 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0495ac368584f4b9 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P05d1c35f7d75ad49 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P05e13ce48e914401 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0603531e3a9d4543 0 6 0 1 65 1 66 1 73 1 82 1 83 1P0678caf6a592680c 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P06c0da3ea03cd08c 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0709e2f64983f58e 0 3 0 1 50 1 58 1P07541cd2db5af13d 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P07568ec4deec120d 0 4 0 1 64 1 82 1 83 1P077bfa21ae654512 0 4 0 1 64 1 82 1 83 1P087f2a9bb0bba598 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0a102c7c441eaaba 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0a566e4c83e4e378 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0a72a2b2463834b4 0 6 0 1 65 1 66 1 73 1 82 1 83 1P0abb333aeb500cf8 0 4 0 1 73 1 82 1 83 1P0b02bc5ee2140b6a 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0b09f9c0adfb9b3a 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0b1dcf362269d1c0 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0b2bd676985be2cc 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0b4764d7508fa6bc 0 5 0 1 43 1 64 1 82 1 83 1P0b65334c40c72711 0 5 0 1 43 1 64 1 82 1 83 1P0bf8cbf2b351afad 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P0caf78525391aa7a 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0cc36df2e4d7d085 0 6 0 1 65 1 66 1 73 1 82 1 83 1P0d0ce6ee4efc84f0 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0d247fab25ecf0ca 0 4 0 1 64 1 82 1 83 1P0d58206ec0de7cdd 0 4 0 1 64 1 82 1 83 1P0d8f6a3f6275e8df 0 4 0 1 64 1 82 1 83 1P0daf9d6be8ec6b71 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P0ddb3679df61b7c9 0 4 0 1 64 1 82 1 83 1P0e296c9030f6ab1e 0 3 0 1 49 1 55 1P0e62f0ddccfb17fa 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P0e8c54dcf6efdfde 0 6 0 1 65 1 66 1 73 1 82 1 83 1P0f31a1bab673d498 0 4 0 1 73 1 82 1 83 1P0f333a0ca570f7cb 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0f6398147b390480 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P0fa34439825d64ed 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P10310c7755a9fc90 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P1101925bcd712448 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P11187b973360d733 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P111df9aae6cd4b9f 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P116b68ad0db665ae 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P129456ef276d2cfc 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P1294e47d2f3eddcc 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P13a96654ec34403c 0 4 0 1 73 1 82 1 83 1P13c26a5d32a11205 0 5 0 1 43 1 64 1 82 1 83 1P143a1cf3392a72ff 0 4 0 1 73 1 82 1 83 1P1487a2965a287ba7 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P1535d0a8ff76c97d 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P161e9a1b64cfc8b6 0 4 0 1 64 1 82 1 83 1P16560a0c3c3a5722 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P16a3b5e1d71b8a2f 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P16d7dac5eae96dbd 1 1 16 2 0 1 82 1 3 11 1 83 1 84 16P16e398ba459c6453 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P16ffe9b199d2203a 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P172e6056e1becec0 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P174c05cffa3205a9 0 5 0 1 43 1 64 1 82 1 83 1P1782e36894f48048 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P17f5f936136f7695 0 6 0 1 65 1 66 1 73 1 82 1 83 1P18303596cc95edfd 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P187aa8ad3256cae2 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P18b2b338dc4d0068 0 4 0 1 73 1 82 1 83 1P18f8e0a5ca3fcdda 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P1a67c5777429b942 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P1a81d1973d95420c 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P1a84ab67969b7795 0 4 0 1 64 1 82 1 83 1P1ada0f34ca3bfae7 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P1aedeca510e558d6 0 4 0 1 64 1 82 1 83 1P1b7fe2bb25cee3ab 0 4 0 1 73 1 82 1 83 1P1c8c5c4ef697a0c0 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P1ca4d456fd33f590 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P1ca94657a552707f 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P1cf1e30770190dc1 0 6 0 1 65 1 66 1 73 1 82 1 83 1P1e10795bdcf4f874 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P1e132385f90712d2 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P1e2de8fc56190eb2 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P1e6263f1a93c2a3e 0 4 0 1 73 1 82 1 83 1P1e727eada7e0cfad 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P1f2ffa3a99822c02 0 5 0 1 43 1 64 1 82 1 83 1P1f41298c5efa7bdc 0 5 0 1 43 1 64 1 82 1 83 1P1f669b399a7e043b 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P1f8c3959f4937e25 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P1f9821553a0b5506 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P2007fba93984e2ac 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P202288f616258369 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P205a14bd6b655c77 0 5 0 1 43 1 64 1 82 1 83 1P207730ec177db805 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P20aacf98dcc89725 0 4 0 1 73 1 82 1 83 1P20c265a4836f8b30 0 6 0 1 65 1 66 1 73 1 82 1 83 1P21b8665c4b9d8b8e 0 5 0 1 43 1 64 1 82 1 83 1P22698f7cace8e057 0 6 0 1 65 1 66 1 73 1 82 1 83 1P241f44d69bf3b839 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P247afb2c994b1178 0 4 0 1 73 1 82 1 83 1P24ced23ea4125790 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P24f32b12d8c1ef8f 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P250923f5c79b1c2c 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P2516931aaf428ef1 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P254ad6d78373b773 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P25da3470159c9377 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P26f87a3b3e37a3c8 0 4 0 1 64 1 82 1 83 1P285202d6b0eb3676 0 4 0 1 73 1 82 1 83 1P28991f15d3ad7151 0 6 0 1 65 1 66 1 73 1 82 1 83 1P291af1153259cd67 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P29d4bad78b3d68f1 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P29dd9ef63fb10203 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P2a4ff99278c6064b 0 4 0 1 64 1 82 1 83 1P2a6df0bd2e7d10a7 0 5 0 1 43 1 64 1 82 1 83 1P2ab6b72bffece22f 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P2af95e705b32f4a3 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P2b5a713abe2480df 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P2b855e5984a97e9d 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P2bca73a21e67d070 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P2c7b0e765b6ae4db 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P2d456d0fecc4769f 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P2da22240a781da04 0 6 0 1 65 1 66 1 73 1 82 1 83 1P2dcadb000a1a5f24 0 4 0 1 73 1 82 1 83 1P2dea2c5ee217242a 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P2e4c6eb60d4eb6e9 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P2eb346f2ba73005b 1 2 16 2 0 1 84 1 16 2 1 1 83 1 2 85 1 86 1P2f404ded9267810d 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P30106a53924e6457 1 1 16 2 41 1 82 1 3 0 1 83 1 84 16P3041b624c9f12d41 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P30d708c0d9d26fa9 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P30ec85668eb497a4 0 4 0 1 73 1 82 1 83 1P3138491c968d6db0 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P3179a41330a8df58 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P319787819eb874d2 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P319adf2bb6208194 0 6 0 1 65 1 66 1 73 1 82 1 83 1P31bf49f44e0e2919 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P31f21057fd4cfd20 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P332908a08c4decbf 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P332a1877e793b1dd 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P33544c0caf01cbd6 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P3417b100a14e4d1a 0 5 0 1 43 1 64 1 82 1 83 1P3479646bb331d25f 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P34bc90b7740c681c 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P351f1387cc3c4428 0 4 0 1 73 1 82 1 83 1P35252bfb60df097d 0 4 0 1 64 1 82 1 83 1P35a7c098b61bd1dc 2 70 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P35d9e82625d02a2a 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P35ec3aba25bbdaba 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P3662983c145755c1 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P379d9b2ea9411d42 0 4 0 1 73 1 82 1 83 1P37faf1fec8bacd99 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P38000c0543215e2c 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1P383eece302c14f26 0 5 0 1 43 1 64 1 82 1 83 1P38a5da603c836a5a 0 4 0 1 64 1 82 1 83 1P3916364570806a9e 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P39c77ae386fca427 0 6 0 1 65 1 66 1 73 1 82 1 83 1P3aff0cad02daa7ba 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3b0b7aaa0c9bd40f 0 6 0 1 65 1 66 1 73 1 82 1 83 1P3b41ca62441c0a62 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3b8e49c98263035d 1 2 16 3 0 1 51 1 84 1 16 3 1 1 50 1 83 1 2 85 1 86 1P3bea5d433809561f 1 1 16 2 1 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3c0eb792c3750386 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P3c3e56a13252aa03 0 5 0 1 43 1 64 1 82 1 83 1P3c897714b136abf3 2 69 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P3cba04a1bd5f376c 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P3dbb61ebf680621a 2 72 1 1 8 3 2 1 85 1 86 1 5 0 2 75 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 4 0 2 85 2 86 2 88 16P3dedf894d439e8ae 1 1 16 3 1 1 50 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3e5a8d105ba8281f 0 4 0 1 64 1 82 1 83 1P3eafa8a493126bd4 2 71 1 1 4 3 2 1 85 1 86 1 5 0 4 75 4 84 4 87 4 88 16 1 1 4 3 1 1 84 1 87 1 4 0 4 85 4 86 4 88 16P3eca290c660f2ad4 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3f32cbfa9240ddfd 1 1 16 4 1 1 46 1 52 1 83 1 7 49 1 59 1 66 1 67 1 74 1 84 1 85 16P3ffc2de6d6920148 3 68 0 2 1 1 2 1 0 5 0 1 3 1 76 1 85 1 86 1 0 4 0 1 2 1 85 1 86 1N00869e39bfcfb2f9N012c80c345bea097N017cafdd2fc8c49fN01b206956be59dfdN038950de606d5f83N039e3b31cf9a73c3N04762267dbc8f96fN056ac3feb66fa497N0576f6928c1810d6N06ff90ef6b22d944N07f2ea40992c64edN080f2c10c3c9e8e7N089281a69a1b9d93N0a2e856ed487c74cN0a4aafb828f6e065N0a84299404dc162bN0ae09802d1842438N0ba7fca785f2ddd7N0c0868e56470256eN0c6fa9fb895ce98fN0c9504d5191558c6N0cdd091b29dea2feN0dbd1907d7f5dca0N0ead451327a80e20N0f2b49290f5db8ffN0fb566dcea0f0d71N1045f073f5110711N10574fe3a2d2ec7bN10650a7cce6089d5N1086159f7fcebaeeN10bd9720a443938fN10ca823cde291400N126229cf8efae141N134022728da85a5dN14617c0c1a4d6153N14b0faf2e72f5d75N14c5939623837257N14efba1a2e3d7b85N155b7a200b157539N15a066e539a85b7bN15a8c1d50d9b3ef2N15fd65ff0877e4e0N1602ebe36e57671cN1798291305e04a23N1819ac050fa80f8aN1869c2727b6338a6N19984fea39307d4fN19a21f69fdaf6eb0N1b3d684378addae0N1b94bdf257645dfcN1c0234bb165d9d6eN1c1f0d7fc7334a7aN1f7cca063bed854bN20e97701ec6052b6N212615f24bc90808N224b18300601f2dbN2322c77d3cba240aN2565df9025045af7N263ad238728cfe43N26f0a1a407b5e419N270e96f016693119N293a2a9e2ecf807fN295e60b3e8951dc1N29c6651b541d539aN2a7ddca5ca12f1b7N2b72ed7a88ff1bcbN2bec774850d85547N2bf78993133cf771N2dc1276120cc6bd9N2e5a00266a493753N31aada1692bea77fN32332c401faf1adcN32b8a79baf42660eN341c560f9b7d120bN344e5c04d86e1e2bN34ba71f06f072056N34d5d533812558d6N36ff33b02ee6cc64N39da834596172191N3a3b6cebd44e47c1N3b3ad3e699fe0cf5N3bc27f10b12b5c11N3be635182b179740N3bf25a08655b5b1bN3cb535f75e05c279N3dfc6156d038efb1N3e104f78c397fca1N3e5b1eff255d053bN3eca6b4d2db4acbdN3f0ce0a39a412118N3f90db4cc6d4d33a"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
(* [comment removed for export] *)
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
Ltac chunk_split H n H1 H2 ::=
  lazymatch type of H with
  | OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.firstn n cs) in
      let post := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.skipn n cs) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx A (Corelib.Init.Datatypes.app pre post)) in H;
      apply (proj1 (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.CellsX.rw_cells_app sg mx A pre post)) in H;
      destruct H as [H1 H2];
      let z := eval cbv in (Stdlib.ZArith.BinInt.Z.of_nat (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.cells_size pre)) in
      change (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx (Stdlib.ZArith.BinInt.Z.add A z) post) in H2
  end.
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
Ltac2 gd_tbl_A_x509_rsassa_pss () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_rsassa_pss_A.x509_pss_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_rsassa_pss_A.A_X509_RSASSA_PSS"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_rt_hyps"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_x509_rsassa_pss_A.A_SMALLOC_2P"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_SMALLOC_1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_alg_null_A.A_AMEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_WRAP_MEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_x509_rsassa_pss_A.x509_pss_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GSBH : al_gsb AL = AGSB.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GI : asn1_get_int_stmtA asegs AL A_ASN1_GET_INT.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG 64.
  Hypothesis GALG : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.
  Hypothesis GNULL : asn1_get_alg_null_stmtA asegs R HIA A_ASN1_GET_ALG_NULL.
  Hypothesis GHASH : x509_hash_stmtA asegs R HIA A_X509_HASH_ALG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo slo : Z) (bs : list byte) (ptag ppad plen : word).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis HAP : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss ()) "(0.(1.(2.$3.Vpp,=)(2.$3.(4.&40.Vplen,)=))(1.(5.VBUF,Vpp,)(5.(6.Vpp,(4.&40.Vplen,))(6.VBUF,(7.(8.(9.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis D12 : MD + 4 <= MGF \/ MGF + 4 <= MD.
  Hypothesis D13 : MD + 4 <= SALT \/ SALT + 4 <= MD.
  Hypothesis D23 : MGF + 4 <= SALT \/ SALT + 4 <= MGF.
  Hypothesis D1P : MD + 4 <= PAR \/ PAR + 24 <= MD.
  Hypothesis D2P : MGF + 4 <= PAR \/ PAR + 24 <= MGF.
  Hypothesis D3P : SALT + 4 <= PAR \/ PAR + 24 <= SALT.
  Hypothesis D1B : Z.of_nat (length bs) = 0 \/ MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD.
  Hypothesis D2B : Z.of_nat (length bs) = 0 \/ MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF.
  Hypothesis D3B : Z.of_nat (length bs) = 0 \/ SALT + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= SALT.
  Hypothesis ALP : PAR mod 8 = 0.
  Hypothesis AL1 : MD mod 4 = 0.
  Hypothesis AL2 : MGF mod 4 = 0.
  Hypothesis AL3 : SALT mod 4 = 0.
  Hypothesis PARB : 0 < PAR /\ PAR + 24 <= 2^64.
  Hypothesis MDB : 0 < MD /\ MD + 4 <= 2^64.
  Hypothesis MGFB : 0 < MGF /\ MGF + 4 <= 2^64.
  Hypothesis SALTB : 0 < SALT /\ SALT + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_PSS_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 288 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 480 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLO5 : lo <= bv_unsigned sp - 352 - arl_need_bcmp R.
  Hypothesis RTB0 : 0 <= arl_need_bcmp R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DSP : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS1 : MD + 4 <= lo \/ bv_unsigned sp <= MD.
  Hypothesis DS2 : MGF + 4 <= lo \/ bv_unsigned sp <= MGF.
  Hypothesis DS3 : SALT + 4 <= lo \/ bv_unsigned sp <= SALT.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PAR 24.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo MD 4.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo MGF 4.
  Hypothesis CR3 : client_range L (LB ++ fdata LF) lo SALT 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MD 4.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MGF 4.
  Hypothesis CW3 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SALT 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_PSS_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_pss_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo slo).
  Local Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation fctx := (pss_fctx R HIA h LB LF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 PAR MD MGF SALT BUF lo slo bs).

  Ltac fctx_open D :=
    destruct D as (HH & ECS & ETOP & ESTK & HKI & EFLAG & EVOL & EFR & SP1 & SP1M & FH & FSH & CFB & FBAL & FB0 & FBS1
                   & FWH & FWD & FWS & SUBLF & APP & AP1 & AP2 & AP3 & AP4 & ST1 & SEPF & STK2 & SPILL & OMD & OMGF & OSALT & MI & PRES & WL & WCF & SFF
                   & SS1 & SS2 & FRSH & F64);
    unfold pss_fshl in FSH.
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  (* [comment removed for export] *)
  Ltac fctx_build :=
    lazymatch goal with |- pss_fctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac end;
    unfold pss_fctx, pss_fshl; spine; first [ eassumption | match goal with |- ?g => idtac "FCTX-LEFT:" g end ].

  (* [comment removed for export] *)
  Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss ()) "Pr,$3.Pc,$3.P,(1.(:.-10000.R2.)(5.R2.=))P,(1.(5.(;.(<.+2.+40.)+10000.)R2.)(:.R2.(<.+2.+40.)))(2.$3.(=.&20.(6.(>.R4.+10000000000000000.)R3.))(6.R4.(;.R3.(<.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  Ltac fin_postA PRES :=
    apply evtA_done; unfold x509_pss_postA;
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

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2P.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@D18607476203.199D23960434386.200D23960434386.201D23960434386.202D2455714710.232 D27392810573.232D30270010155.156D32457002573.232D3254889317.198 D3373657269.232 D33956323578.200D33956323578.201D33956323578.202D35658891568.156D35863881398.200D35863881398.201D35863881398.202D37565809595.155D43072654946.155D4467592459.157 D50254960491.200D51038213418.200D560907437.158  D60098777666.156D60109265003.157D60111245650.155D61436582618.200D61436582618.201D61436582618.202D62011770191.158D66345248706.157D67392436163.232D68405212918.232D6909863155.232 D8208137750.200 D8208137750.201 D8208137750.202 L11196010649.0  L14558062586.3  L15756354262.7  L16810015495.1  L17921795213.214L19959024712.1  L19980016842.7  L20858515662.0  L21980071943.1  L24524441946.143L24956540167.1  L25985555144.1  L27729706458.216L29738741675.1  L32463525127.1  L3551623394.2   L3801083770.3   L38224815777.0  L39076636629.0  L39268637205.0  L39618635427.2  L40753528314.3  L43055370171.147L43300649301.0  L44032381512.1  L48117620905.122L50790731766.8  L51052909836.217L54437681876.5  L57355539152.195L57781587882.3  L58790154276.6  L59308677456.15 L61437265048.2  L62371012871.1  L64009471222.1  L7040749983.144 L7715476710.149 L9356559645.13  L9873114841.7   P30065013446.200P36462068749.199P36465839390.198P42311556712.198P42311556712.200P58050840408.198P58250600268.198P58250600268.200P65663408556.198P65663408556.200Q10523111610.163Q12658527490.169Q1530342990.200 Q16988962113.161Q23925414039.170Q23927511187.163Q2521097805.232 Q25852324973.165Q30280497415.161Q30280497418.167Q31021924279.198Q32436491433.232Q32846585050.162Q33194651975.169Q33963892682.232Q35653441506.141Q35660991249.167Q35660991260.161Q37568023179.166Q37578510266.160Q38250992822.171Q40271359350.200Q42304729984.232Q42439168719.198Q42441479406.172Q43074897746.166Q43076993635.160Q43878048874.171Q4467592448.168 Q4467592463.162 Q47230721791.163Q48119867062.232Q50796826103.200Q51671229878.160Q54431339875.232Q57371609409.232Q59867617329.172Q60109315147.141Q60309968170.165Q6192914196.198 Q62009673039.170Q62011770187.163Q64681502663.172Q66222295477.163Q66345248710.162Q66345248713.168Q67026483294.199Q67038703949.198Q6909863155.232 Q9350548487.181 Q9646450869.232 00000100200300400500c01A01o02002102g03]03^04<04=04>04?04]05;05Y05Z06I06o07V08=08d09V09W0:I0:i0;G0<50<60<d0<e0<f0<g0<h0=40=B0=F0=G0=L0=d0=e0=i0?70?;0?@0?n0@20@60@=0@I0@J0@K0@L0@V0@b0AG0AH0AM0Al0B=0Bo0CB0CC0CM0Cc0D60D>0DB0DF0EB0E`0FO0Fk0GU0HB0HC0Hm0IW0JA0Jj0KS0L>0Li0M90MH0Mc0N:0NM0Nl0O?0ON0O]0Ol0PP0PQ0Ph0Q70RA0Rc0S20SA0SO0S]0Sk0TC0Te0U@0UV0Ud0V20VC0VS0Vc0W40WX0X80XO0YG0YH0YI0Y]0Yl0Z@0ZM0ZZ0[=0[>0[N0[^0\F0\n0]A0]]0^;FFFFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'2FBS2LF2sp3PAR2MD3MGF4SALT2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'2FBFFS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3sp13H264LFB'3x142HxS2LF2sp3PAR2MD3MGF4SALT3BUF2bs3LFB3sp13H264LFB'3x142HxFS2LF2sp3PAR2MD3MGF4SALT2bs3LFBFFFS2LF2sp3PAR2MD3MGF4SALT2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFBFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H243H264LFB'S1R3HIA1h2LF2sp3PAR2MD3MGF4SALT2bs3LFBS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOSS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOSS1R2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3LOSS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'3x142HxFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'3x142HxS1R2LF2sp3PAR2MD3MGF4SALT2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'2FBFS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'2FBFFFSS2sp3sp13SP1S1R2lo3LOS3ALOS2FBFS3sp1S1R3HIA1h2sp3TOP3sp13SP1SS2spS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3SPA3SPR3sp13H223H233H243H26S2FBS3sp1S2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H264LFB'2FBS2FBS2FBS2bs2EQS2sp3sp13SP1SSSS3sp14SP1MS2sp3sp13SP1S2LF2sp3PAR2MD3MGF4SALT2lo2bs3LFB3SLOSS3sp1S1R2LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R2sp2lo3SLO3LOSS2LF2sp3PAR2MD3MGF4SALT2bs3LFB3sp13H243H264LFB'2FBS2sp2lo3SLO3sp13SP1FS2FB2x22HxS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2LF3LFBS2FBS2bsS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB3SPR3sp13H223H26S2LF2sp3PAR2MD3MGF4SALT2bs3LFBS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp3PAR2lo2bs3LFB3SLO3DSP3sp13SP14LFB'S2LF2sp3BUF2lo2bs3LFB3SLO3DS43sp13SP14LFB'2NEFS2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP14LFB'S2LF2sp3MGF2lo2bs3LFB3SLO3DS23sp13SP14LFB'S2LF2sp3PAR2lo2bs3LFB3SLO3DSP3sp13SP14LFB'S2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP14LFB'S2LF2sp2MD2lo2bs3LFB3SLO3DS13sp13SP14LFB'S2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP14LFB'S2LF2sp4SALT2lo2bs3LFB3SLO3DS33sp13SP14LFB'S1R2LF2sp2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H244LFB'S2LF2MD3MGF4SALT2bs3LFBS1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS2LF2bs3LFB4LFB'2FBS2LF3PAR2bs3LFBS2LF3MGF2bs3LFBS2LF3MGF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4LFB'FS2LF2MD3MGF4SALT2bs3LFBS2LF3BUF2bs3LFBS2LF2sp3PAR2MD3MGF4SALT2bs3LFB4PARB3MDB4MGFB5SALTB3SPR3sp13H264LFB'2FB3F64S1R3HIA1h2LF2sp2lo2bs3LFB3TOP4HTOPS2LF3MGF2bs3LFBS2LF3MGF2bs3LFBS2LF2MD2bs3LFBS2LF2MD2bs3LFBS2LF2lo2bs3LFBS1R3HIA1h2LF2bs3LFB4LFB'S1R2LB2LF2bs3LFB3ALO4LFB'2FB5FRSH'S1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOSS2LF2MD2bs3LFBS2LF2MD2bs3LFBS2LF2sp2lo2bs3LFBS2LF4SALT2bs3LFBS2LF4SALT2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R2LF2sp2lo2bs3LFB3SLO3LOS4LFB'S2LF2MD3MGF4SALT2bs3LFBS1R2LB2LF2sp2lo2bs3LFB3SLO3LOS3ALO3sp13SP14LFB'2FB5FRSH'FFS1R2LF2lo2bs3LFB3LOSS2LF3PAR2bs3LFBS2LF2bs3LFB3sp14LFB'S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPFS2LF4SALT2bs3LFBS2LF4SALT2bs3LFBS1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'S1R2LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'S2LF2bs3LFB4LFB'2FBS2LF2bs3LFB3sp13H253H264LFB'S1R2LB2LF2bs3LFB4LFB'2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss ()) "Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pv1,(9.&40.)Pv2,(9.&40.)Pv3,(9.&40.)P,(?.$10.VR,VHIA,Vh,VLB,VLF,Vm,)P,(11.$10.Vm,VPAR,(12.$13.(14.Vptag,)(12.$13.(14.Vppad,)(12.$13.(15.Vplen,)(12.$13.(15.(16.&40.Vpp,))(17.$13.))))))P,(11.$10.Vm,VMD,(12.$13.(14.R5.)(17.$13.)))P,(11.$10.Vm,VMGF,(12.$13.(14.R5.)(17.$13.)))P,(11.$10.Vm,VSALT,(12.$13.(14.R5.)(17.$13.)))P,(18.$10.Vm,VBUF,Vbs,)P,(19.$10.Vm,Vlo,(4.&40.Vsp,))P,(1:.$10.(1;.VR,)Vm,Vslo,(4.&40.Vsp,))P,(1<.$10.Vm,)P,(1=.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)Vm,VPAR,+18.)P,(1=.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)Vm,VMD,+4.)P,(1=.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)Vm,VMGF,+4.)P,(1=.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)Vm,VSALT,+4.)P,(1=.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)Vm,VBUF,(7.(8.(9.&8.)Vbs,)))(1?.$10.(1;.VR,)(1>.$10.VR,VHIA,Vh,)(20.$10.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMD,VMGF,VSALT,Vlo,Vslo,Vm,)(21.(22.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(16.&40.VPAR,)(16.&40.VMD,)(16.&40.VMGF,)(16.&40.VSALT,)R19.R18.R17.R16.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R15.R14.R13.R12.)VF,(16.&40.$23.)Vfc,(24.(9.&40.))Vm,(25.$10.)))")
(* [comment removed for export] *).
  Proof.
  intros until v3.
  intros HH HPAR HMD HMGF HSALT HBUF ST SS MI OPAR OMD OMGF OSALT OBUF.
  unfold A_X509_RSASSA_PSS.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_2P in SM2.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
  carve_frame 160%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 439%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -160) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340476 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 256);
                  [ exact HHc | exact LFB' | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
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
      replace (Z.to_nat (8 * 2 ^ 2)) with 32%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 2)) with 256%nat in FRM by reflexivity.
      replace (64 * 2 ^ 2) with 256 in FRSH, HH1 by reflexivity.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [24; 8; 8; 24; 8; 24; 4; 4; 8; 8; 40; 4; 4; 8; 8; 40; 4; 28]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HPL FRM3. chunk_split FRM3 1%nat RZ1 FRM4.
      chunk_split FRM4 1%nat HLN FRM5. chunk_split FRM5 1%nat RZ2 FRM6. chunk_split FRM6 4%nat HAID FRM7. chunk_split FRM7 1%nat RZ3 FRM8.
      chunk_split FRM8 4%nat HAPR FRM9. chunk_split FRM9 1%nat RZ4 FRM10. chunk_split FRM10 1%nat HTRL RZ5.
      clear G1 RZ1 RZ2 RZ3 RZ4 RZ5.
      replace (FB + 24 + 8) with (FB + 32) in HPL by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24) with (FB + 64) in HLN by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 24) with (FB + 96) in HAID by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 24 + 24 + 40) with (FB + 160) in HAPR by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 24 + 24 + 40 + 24 + 40) with (FB + 224) in HTRL by (clear; lia).
      cb8_to_c8 HPL (@nil cell). cb8_to_c8 HLN (@nil cell).
      cb4_to_c4 HTRL (@nil cell).
      cb4_to_c4 HAID (@nil cell).
      lazymatch type of HAID with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 HAID [c0] end.
      lazymatch type of HAID with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb8_to_c8 HAID [c0; c1] end.
      lazymatch type of HAID with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb8_to_c8 HAID [c0; c1; c2] end.
      cb4_to_c4 HAPR (@nil cell).
      lazymatch type of HAPR with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 HAPR [c0] end.
      lazymatch type of HAPR with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb8_to_c8 HAPR [c0; c1] end.
      lazymatch type of HAPR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb8_to_c8 HAPR [c0; c1; c2] end.
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa ST2x (bv_unsigned sp + -104); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 16) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp16 SLOT16].
      cb8_to_c8 SLOT16 (@nil cell).
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 24) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp24 SLOT24].
      cb8_to_c8 SLOT24 (@nil cell).
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 48) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp48 SLOT48].
      cb8_to_c8 SLOT48 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 256) ((FB, 256) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 256 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 216) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PAR 24 FB 256 FRSH CRP ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APP.
      pose proof (fresh_apart_client _ LB LF lo MD 4 FB 256 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo MGF 4 FB 256 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client _ LB LF lo SALT 4 FB 256 FRSH CR3 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP3.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 256 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_rsassa_pss_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_rsassa_pss ()) "PR,$26.PHIA,(27.$10.R1.)P,(28.R2.R1.)P,(2.$3.(29.R3.)$2:.)P,(2.$3.(2;.R4.+2.)$2<.)P,(2.$3.(2;.R5.+1.)$2=.)P,(2.$3.(2>.R6.)$2?.)P,(2.$3.(30.R7.)$31.)P,(5.=(32.R8.))(33.$10.R9.R8.$23.)")
(* [comment removed for export] *).
Proof.
  intros R HIA ORT UARG SM2 SM1 AMS MSI NEED0. flat constr:(ORT) 6%nat. intros IMG GSBH MCI RTC NEEDB ISH.
  pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  pose proof (A_asn1_get_int_spec (L := arl_L R) (arl_AL R) IMG) as GI.
  pose proof (A_oid_get_md_alg_spec R HIA ORT) as MDALG.
  pose proof (A_asn1_get_alg_spec R HIA IMG MSI RTC NEED0) as GALG.
  pose proof (A_asn1_get_alg_null_spec R HIA IMG UARG SM1 AMS MSI RTC NEED0) as GNULL.
  pose proof (A_x509_hash_alg_spec R HIA ORT UARG SM2) as GHASH.
  unfold x509_pss_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
