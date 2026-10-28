(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_asn1_get_alg_null_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002a4cbd384984d3 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P00fcd21ea8386735 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P0109da229a5d555d 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P012dfb50e1d38569 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P01732f09c555c305 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P025f8f0f9c7ff3fd 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P02dcfdac8e5a3aae 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P037a09566a8d7556 0 4 0 1 62 1 78 1 79 1P03ecd5b0200419f7 1 1 16 2 0 1 78 1 3 4 1 79 1 80 16P03fb59259049bb6b 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P046ff74e55c08140 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P047a6060f3239220 1 1 32 3 1 1 100 1 103 1 13 40 2 46 2 65 2 68 2 70 2 75 2 77 2 85 2 86 2 87 2 101 2 102 2 104 64P053b8f08bbf791d1 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P0546753deeed3ab4 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P056936772f714068 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P05e99e7112fe2d07 0 4 0 1 62 1 78 1 79 1P0691c7fb737c6f1c 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P0699990c67407d90 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P06c0be1246cbfc18 0 5 0 1 34 1 62 1 78 1 79 1P0776494b01669121 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P07cfd522cc9d2193 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P07e28ea36bbc280b 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P07e791bd0d3ba009 0 11 0 1 39 1 64 1 67 1 69 1 74 1 84 1 85 1 86 1 99 1 100 1P0805413b517a5a00 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P080c49913f8d2e49 1 1 16 3 0 1 101 1 102 1 12 46 1 65 1 68 1 70 1 75 1 77 1 85 1 86 1 87 1 100 1 103 1 104 16P08e943a31553b745 1 1 16 3 0 1 101 1 102 1 12 46 1 65 1 68 1 70 1 75 1 77 1 85 1 86 1 87 1 100 1 103 1 104 16P08f4b84e46f04599 0 5 0 1 34 1 62 1 78 1 79 1P0a2be814636fc238 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P0b55d4b93cd4d301 1 1 16 3 0 1 100 1 101 1 4 59 2 99 2 102 2 103 32P0b7794ae5017bd27 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P0ba72f05b7480499 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P0bad94b938afa2ee 0 5 0 1 34 1 62 1 78 1 79 1P0bcb8ff41ca33d59 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P0c15d42f6f20b223 1 1 64 2 5 1 99 1 3 0 1 100 1 101 64P0c71bdf12ef4fa0f 0 3 0 1 31 1 42 1P0d2a5711f7345eb3 0 4 0 1 62 1 78 1 79 1P0d4814dc24a4ad12 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P0e0caa16584e91e3 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P0e33de616e9ec9b8 0 5 0 1 34 1 62 1 78 1 79 1P0f1dae6ccc67b4ec 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P0ff61682f7c82feb 0 4 0 1 62 1 78 1 79 1P11cc1d83addc0fd2 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P1231116b5ac3364c 0 5 0 1 34 1 62 1 78 1 79 1P127eb22801c4063c 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P12b12987f4f7e87d 1 1 32 3 0 1 99 1 102 1 13 39 2 45 2 64 2 67 2 69 2 74 2 76 2 84 2 85 2 86 2 100 2 101 2 103 64P13ee95713be1bd98 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P14da87733b392907 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P152d252cf6e85a51 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P16965b61f11c7b2b 0 5 0 1 34 1 62 1 78 1 79 1P17ace5e1eab7228d 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P17edeae4783ff9a5 0 9 0 1 39 1 64 1 67 1 69 1 74 1 84 1 99 1 100 1P1841fcb7d5054b39 0 4 0 1 62 1 78 1 79 1P19337f9d5f8b5971 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1968f79ec74ad47a 0 5 0 1 34 1 62 1 78 1 79 1P1a0c0c10b33ae2d1 0 5 0 1 34 1 62 1 78 1 79 1P1a924f97ac867a83 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1ac8a43a981c1198 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1acce360483d7221 0 4 0 1 62 1 78 1 79 1P1b189a9e49aa902b 1 2 32 3 0 1 100 1 103 1 32 3 1 1 101 1 102 1 2 104 2 105 2P1b1ad56ed76b8a09 1 1 32 3 0 1 99 1 102 1 13 39 2 45 2 64 2 67 2 69 2 74 2 76 2 84 2 85 2 86 2 100 2 101 2 103 64P1b3d243b082ab1c7 0 4 0 1 62 1 78 1 79 1P1c03ea55459daba0 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P1c3938a28578f607 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P1d5dc4b2e9967a1e 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1d5f1b19d8473eae 0 4 0 1 62 1 78 1 79 1P1d72c3e588138db8 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1d9f538d5653cd8b 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P1e7aece9db32a945 0 6 0 1 56 1 59 1 83 1 99 1 100 1P1e8028aa64ddcd56 0 5 0 1 34 1 62 1 78 1 79 1P1f4d87420902fd7e 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P1fc43b3a29cb9a9c 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P1fd308b738c9c9eb 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P201b05e8bbfc74bb 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P2020b0f13c7e79ad 1 2 16 3 1 1 26 1 79 1 16 3 0 1 27 1 80 1 2 81 1 82 1P2042bc49ef79084f 0 8 0 1 64 1 67 1 69 1 74 1 84 1 99 1 100 1P207c00b23930e0cc 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P209cfb33cf596c15 1 1 16 3 0 1 101 1 102 1 12 46 1 65 1 68 1 70 1 75 1 77 1 85 1 86 1 87 1 100 1 103 1 104 16P21dc54dcc2e83a83 1 1 16 3 0 1 100 1 101 1 12 45 1 64 1 67 1 69 1 74 1 76 1 84 1 85 1 86 1 99 1 102 1 103 16P22059476fec3cce9 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P224b0331886495c4 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P22ce2cb2ad370bb1 0 5 0 1 34 1 62 1 78 1 79 1P2362896b791f61cf 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P23d9551dd4335737 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P2536454ac622c330 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P25b7865e5028cf0c 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P25d3f2a58df45e00 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P2649a047806535a3 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P26557c0849290b26 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P26974111b608372d 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P26f65f61a32f1823 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P2861ff8283274d2b 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P286b6d3c0f57e36d 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P286d45bad105aeb5 0 3 0 1 43 1 61 1P28a551eb80be88b9 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P2a05ba2f36705e3d 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P2a52c40dbf7974de 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P2a9e14ff77da0351 0 4 0 1 62 1 78 1 79 1P2b0d5f8bd7545fad 0 4 0 1 62 1 78 1 79 1P2b3ac33cb8887e3c 1 1 32 3 0 1 100 1 103 1 13 40 2 46 2 65 2 68 2 70 2 75 2 77 2 85 2 86 2 87 2 101 2 102 2 104 64P2b661567b6018baa 0 4 0 1 62 1 78 1 79 1P2bbe496d8f113d63 1 1 64 2 0 1 99 1 3 6 1 100 1 101 64P2bc67d70f52d7fa1 0 4 0 1 62 1 78 1 79 1P2be5a13e0c1f6755 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P2c0d090f51fb06f0 0 5 0 1 34 1 62 1 78 1 79 1P2c2772a1b9c3c74a 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P2c6cb43d8fe73874 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P2c74d9b79ded2bbb 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P2d96b68b7de7ad72 1 1 16 2 1 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P2e1224f560c72f87 0 5 0 1 34 1 62 1 78 1 79 1P2ec049986489e441 0 11 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 68 1 78 1 79 1P2f193152f32f6443 0 4 0 16 61 16 78 16 79 16P30908bbcc83fabb2 1 2 32 3 0 1 100 1 103 1 32 3 1 1 101 1 102 1 2 104 2 105 2P31e58d58e3a7b168 1 1 32 3 1 1 100 1 103 1 13 40 2 46 2 65 2 68 2 70 2 75 2 77 2 85 2 86 2 87 2 101 2 102 2 104 64P327cf42ebb03d9fb 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P33836f80037e41bc 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P3609d7ee74fd0b1d 0 5 0 1 34 1 62 1 78 1 79 1P37acb0c7ce350926 1 1 16 3 1 1 26 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P380171314a5d492b 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P38188dafdf109124 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P383af10c9a6b02d5 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P39a7a30b249bd1b6 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P39ce0218c890fe55 0 12 0 1 39 1 64 1 67 1 69 1 74 1 84 1 85 1 86 1 89 1 99 1 100 1P39eebeeaec27bdbf 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P39fe3a4ddc4e6e91 0 4 0 1 62 1 78 1 79 1P3afef5672436966e 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3b2e5db75209d9ae 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P3b73674cafb306ff 0 6 0 1 35 1 59 1 83 1 99 1 100 1P3c64154a85b998f3 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3d467606e4350e2f 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3dbeed3c92e7ff49 1 1 16 3 0 1 101 1 102 1 4 60 2 100 2 103 2 104 32P3dd087a265989d5b 0 8 0 1 43 1 46 1 48 1 53 1 63 1 78 1 79 1P3e1cf4e61a1f6016 1 1 16 4 1 1 28 1 39 1 79 1 11 42 1 44 1 47 1 49 1 54 1 56 1 64 1 65 1 66 1 80 1 81 16P3e25b652e291fa1f 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P3eace40de0ff602c 0 10 0 1 43 1 46 1 48 1 53 1 63 1 64 1 65 1 78 1 79 1P3ecb6fe6dcb5b591 0 4 0 1 62 1 78 1 79 1P3ed26411d2d785e1 1 2 16 2 0 1 80 1 16 2 1 1 79 1 2 81 1 82 1P3f1b621e86e410cb 0 5 0 1 34 1 62 1 78 1 79 1N01f77bb610372814N034379eeb51bd8c8N0439ca3f6553168dN0489dbeb37912b45N06cd8e5c9f2eb1c4N070249c6ef041e17N09564a2789e40751N095d4827c5472c27N0a27ebb8f70f3254N0a8063dd8fb06524N0b878c6572b9ee71N0c64882fbceaec07N0d04d1f6f634fe21N0d15d075a5a85e79N0daa9dac20b802f9N0e2b526d71f450caN0e6b4098dab19cf7N0e836467364717eeN0eb356413cecbf72N0ebbec87398b2490N0f2a4a6e3703d634N0f4e1df94cae3a21N0ff250588d83a127N1258f8287b189628N1354f2e49b3c7de0N14b9dac3d3871977N15e3560b05c1ae46N15ec1f2ef14f1e37N1631e4605371cd80N17a23cd2b5d60c8cN1904d809360d4a0aN1a90c0f485f7c6bfN1b3bc663158ba05aN1d83e45dc7decabbN1ed8e8237fa8fea7N1f8b746a229c248cN20965b5310e59219N217f05fc8c10ae90N22f41bee454b9fd6N234ab95703d52d77N24f305160ddf20aaN2690a6b646a89b69N27c90743a26ce0c8N2803b909285cc8b1N29253ad5c0ee2394N29e56302b3fdecb4N2a102aab3d2e1848N2a325c684cde1edaN2a4f115f26191f95N2a6d805b955ade34N2b06b2aa9de6e25dN2b81591f66f915ebN2bceb06cfcfec0ccN2ce68e0077cbf8dfN30ae7d923a1b70e1N30d77b4007fc6b91N310e4173a794dfaeN31af07e73588d28bN31bb577913b4d385N31d6b539794c2b9aN321c9878e1591954N323058672c96b996N3287ce587715473bN330eb06b434426beN33f186513040765eN357042e7d5ca851bN357737f91ca5f087N3590f2f21b0e88ebN3613e3b64147807dN3636838f770792b4N3757677913b9fb92N3777ecbdc4a4762aN37c367ef8967be6aN37ce02f0c546dc21N37e74443dd6b2546N38f5dfc23b185a7fN38fe55b9fd813252N39377f243c187c25N3ac1e9dd133ba233N3ad79fc91324f06cN3b0fed645ae759ceN3e55be1241a6371cN3eaa392ede065176N3f7fbbf6267875b8"%lxh.
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
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_SMALLOC_2 : Z := 0x531fc.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WCALLOC : Z := 0x69484.              (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_AMEMCPY_F : Z := 0x67dbc.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WBCMP : Z := 0x58704.                (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASN1_GET_INT_G : Z := 0x099b4c.      (* [comment removed for export] *)
Definition A_ASN1_GET_ALG_NULL_G : Z := 0x09ad70. (* [comment removed for export] *)
Definition A_OID_GET_MD_ALG_G : Z := 0x0a8cc0.    (* [comment removed for export] *)
Definition A_PKCS7_NEXTLEN_G : Z := 0x0980b4.     (* [comment removed for export] *)
Definition A_PKCS7_CINFO_G : Z := 0x098388.       (* [comment removed for export] *)
Definition A_X509_CRT_INIT : Z := 0x0aa030.       (* [comment removed for export] *)
Definition A_PKCS7_GETSIGNERS : Z := 0x098a04.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_OID_P7_DATA : Z := 0x24d20.          (* [comment removed for export] *)
Definition A_OID_P7_SIGNED : Z := 0x24d40.        (* [comment removed for export] *)
Definition A_OID_P7_ENVELOPED : Z := 0x24d60.     (* [comment removed for export] *)
Definition A_OID_P7_SIGNED_ENV : Z := 0x24d80.    (* [comment removed for export] *)
Definition A_OID_P7_DIGESTED : Z := 0x24da0.      (* [comment removed for export] *)
Definition A_OID_P7_ENCRYPTED : Z := 0x24dc0.     (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable PK : pk_class asegs.
  Variable SI : sinv (arl_L R).
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIg : Z -> Z) (FFRg : Z -> Z -> Z) (CNTg : Z -> Z) (STKg : Z).
  Hypothesis GETCERTS : pkcs7_get_certs_stmtA_c asegs R HIA PK SI PHIg FFRg CNTg STKg A_PKCS7_GETCERTS.   (* [comment removed for export] *)
  Variables (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z) (STKs : Z).
  Hypothesis GETSIGNERS : pkcs7_getsigners_stmtA asegs R HIA PHIs FFRs CNTs STKs A_PKCS7_GETSIGNERS.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Variables (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PKFREE : pkcs7_free_stmtA asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIg_mono : forall n n', 0 <= n <= n' -> 0 <= PHIg n <= PHIg n'.
  Hypothesis FFRg_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRg n d <= FFRg n' d.
  Hypothesis CNTg_mono : forall n n', 0 <= n <= n' -> 0 <= CNTg n <= CNTg n'.
  Hypothesis PHIs_mono : forall n n', 0 <= n <= n' -> 0 <= PHIs n <= PHIs n'.
  Hypothesis FFRs_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRs n d <= FFRs n' d.
  Hypothesis CNTs_mono : forall n n', 0 <= n <= n' -> 0 <= CNTs n <= CNTs n'.
  Hypothesis PHIj_mono : forall n n', 0 <= n <= n' -> 0 <= PHIj n <= PHIj n'.
  Hypothesis FFRj_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRj n d <= FFRj n' d.
  Hypothesis CNTj_mono : forall n n', 0 <= n <= n' -> 0 <= CNTj n <= CNTj n'.
  Hypothesis PHIj_joint : forall a b, 0 <= a -> 0 <= b -> PHIg a + PHIs b <= PHIj (a + b).
  Hypothesis FFRj_joint : forall a b d, 0 <= a -> 0 <= b -> FFRg a d + FFRs b d <= FFRj (a + b) d.
  Hypothesis CNTj_joint : forall a b, 0 <= a -> 0 <= b -> CNTg a + CNTs b <= CNTj (a + b).
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis STKg0 : 0 <= STKg. Hypothesis STKs0 : 0 <= STKs. Hypothesis STKf0 : 0 <= STKf.
  (* [comment removed for export] *)
  Definition STKp : Z := 208 + Z.max (Z.max (Z.max STKg STKs) (Z.max STKf 512)) (Z.max (arl_need_smalloc R) (arl_need_rt R))
                         + Z.max 0 (4352 + arl_need_smalloc R + arl_need_rt R + arl_need_bcmp R).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (A DATA n lo slo d : Z) (bs : list byte).
  Hypothesis P7Z : pkcs7_zero asegs m A.
  Hypothesis AAL : A mod 8 = 0.
  Hypothesis A0 : 0 < A.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A PKCS7_SIZE.
  Hypothesis ASTK : A + PKCS7_SIZE <= arl_stklo R.
  Hypothesis AOD : A + PKCS7_SIZE <= hl_data_lo L \/ hl_data_hi L <= A.
  Hypothesis HBY : bytes_at asegs m DATA bs.
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2 ^ 26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CRD : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis DA : n = 0 \/ A + PKCS7_SIZE <= DATA \/ DATA + n <= A.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKp.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 33)%nat.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L15273424461.9900000aS1R2LF2sp1A1n2lo3slo2bs2A03LEN4SLOS4SLOL3LFB1H2H0". (* [comment removed for export] *)
  Let ALO1 : A + PKCS7_SIZE <= lo. Proof. pose proof LOS. pose proof ASTK. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2 in SM2; unfold STKp in SLO; unfold PKCS7_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := fun ms =>
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (w0 w1 w2 : word) (j32 j64 j96 j128 j144 : list byte),
      ms = MS (mkR x1 (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 (-8)) (Z_to_bv 64 DATA) (Z_to_bv 64 n) s6 (Z_to_bv 64 FB) (Z_to_bv 64 A) s9
                   (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
              F (Z_to_bv 64 0x9790c) fc None m1 (seg_rom asegs)
      /\ bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 /\ sp1 mod 32 = 0
      /\ HM asegs R HIA h1 LB ((FB, 256) :: LF) m1 /\ hcs asegs R HIA h1 = CS /\ htop asegs R HIA h1 = htop asegs R HIA h
      /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\ hflag asegs R HIA h1 = hflag asegs R HIA h
      /\ havol asegs R HIA h1 = havol asegs R HIA h /\ hfr asegs R HIA h1 = hfr asegs R HIA h
      /\ (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
      /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 256
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (FB + 32) [CB 8 j32] /\ rw_cells asegs m1 (FB + 64) [CB 8 j64] /\ rw_cells asegs m1 (FB + 96) [CB 8 j96]
      /\ rw_cells asegs m1 (FB + 128) [CB 8 j128] /\ rw_cells asegs m1 (FB + 144) [CB 8 j144] /\ rw_cells asegs m1 (FB + 176) [C8 (Z_to_bv 64 0)]
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHXL
      /\ rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL
      /\ rw_cells asegs m1 (sp1 + 48) [C8 (Z_to_bv 64 FB)] /\ stk asegs m1 sp1 (sp1 + 48) /\ stk asegs m1 (sp1 + 56) (bv_unsigned sp + -104)
      /\ stk asegs m1 lo sp1 /\ mem_inv asegs m1
      /\ pkcs7_zero asegs m1 A /\ bytes_at asegs m1 DATA bs
      /\ aobj asegs AL CS m1 A PKCS7_SIZE /\ (1 <= n -> aobj asegs AL CS m1 DATA n)
      /\ (FB + 256 <= A \/ A + PKCS7_SIZE <= FB) /\ (n = 0 \/ FB + 256 <= DATA \/ DATA + n <= FB)
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m m1
      /\ sshad asegs AL m1 slo (bv_unsigned sp).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 DA; try lx_pin1 HD; try lx_pin1 AOD; try lx_pin1 AAL; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 mo0; try lx_pin1 STKf0; try lx_pin1 STKs0; try lx_pin1 FFRf_mono; try lx_pin1 PHIf_mono; try lx_pin1 CNTj_joint; try lx_pin1 FFRj_joint; try lx_pin1 PHIj_joint; try lx_pin1 CNTj_mono; try lx_pin1 FFRj_mono; try lx_pin1 PHIj_mono; try lx_pin1 CNTs_mono; try lx_pin1 FFRs_mono; try lx_pin1 PHIs_mono; try lx_pin1 CNTg_mono; try lx_pin1 FFRg_mono; try lx_pin1 PHIg_mono; try lx_pin1 PKFREE; try lx_pin1 FFRf; try lx_pin1 PHIf; try lx_pin1 CNTj; try lx_pin1 FFRj; try lx_pin1 PHIj; try lx_pin1 GETSIGNERS; try lx_pin1 CNTs; try lx_pin1 FFRs; try lx_pin1 PHIs; try lx_pin1 GETCERTS; try lx_pin1 CNTg; try lx_pin1 FFRg; try lx_pin1 PHIg; try lx_pin1 GETTAG; try lx_pin1 SI; try lx_pin1 PK; try lx_pin1 HMND; try lx_pin1 DIMG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02A0@D13927008426.195D16049649470.175D18607476203.143D19921221523.195D2457697675.174 D30009943149.175D31762839144.175D32458983504.174D32604263313.176D3375410824.173 D37704033335.175D37706247433.97 D45716866873.173D50254960491.144D54547090218.144D563007111.98   D57793146470.195D60109265004.175D60111245650.97 D62011770186.176D62022258533.98 D66237105966.174D67483720860.145D67483720860.146D68407129291.173D6911780558.173 D8423573803.97  D8425816085.175 L1156686087.1   L11621613575.1  L1272297818.110 L15278480665.187L15822417165.1  L16810015495.1  L1685717371.0   L18021517688.14 L18271036607.155L19548981075.157L19980016842.14 L21866712442.1  L22941438733.1  L26892418956.1  L29738741675.1  L31302595335.1  L32463525127.1  L33472729358.114L33483560980.15 L33485826452.1  L33985112333.1  L3612539911.1   L36316927438.2  L39269760500.1  L40226756952.1  L40228640085.0  L41099742989.1  L43055369633.130L43300649301.0  L48037591002.169L48117620908.86 L48119718060.153L48119718063.152L5067997814.157 L50790731766.13 L50863131871.187L53537894342.3  L54547072822.170L55716550157.1  L57124690773.0  L57355539152.153L57355539152.155L58790154276.14 L59308634497.18 L59578101107.179L60746759833.14 L61437265048.2  L61552013524.11 L62867260193.0  L63405906047.1  L64850595401.0  L65278984349.152L65620441318.132L6910010090.152 L7040749983.111 L7738195705.2   L9356559645.18  P36312780344.195P7750690063.195 Q10533598597.100Q10592386194.180Q11448315440.181Q11452508936.100Q1530342990.144 Q16178749879.180Q23937998252.100Q23937998260.102Q28074340950.192Q31021924279.142Q31760741999.181Q32440833928.179Q35653441506.127Q38248895670.103Q39693285665.191Q40271359350.144Q42439168719.142Q42439382254.104Q42439443119.195Q42441479406.185Q43880146026.103Q47223635094.195Q47241206720.100Q48117620900.180Q48117823211.195Q48132302231.179Q49698585326.193Q50796826103.144Q52116642125.181Q52120837237.100Q52744951088.194Q52747231024.195Q56531220664.180Q59310664043.100Q59310664043.179Q59321150552.180Q59321350679.195Q59323247699.181Q59865321072.195Q59865520177.104Q59867617329.185Q60109315147.127Q6192914196.142 Q62022254700.102Q62022254708.100Q62415448880.191Q64681502663.185Q64683599815.104Q64683667846.195Q65266402725.179Q65266402749.183Q65278984349.181Q67117497828.195Q67119445988.194Q6897428426.183 Q6897428434.179 Q6910010090.181 Q9350548487.125 00000100200301101201301401c02Y02Z03K04004_04`05P06;07907o08[09J09o0:^0:_0:`0:a0;P0<50<f0<j0<n0=i0>X0>\0>`0>a0?30?j0@c0AJ0AN0AR0AV0AZ0A^0Ab0Ac0Ad0Ae0Ai0Am0An0B20B70B80B<0CM0CN0D=0E;0F80G50Gn0H\0IK0IW0JJ0JN0JO0JP0KM0L10LL0M@0MR0MZ0N>0N?0ND0NE0Ni0ON0P20Pa0Pb0Q`0S?0TV0U;0U_0U`0Ua0VM0W10We0XM0Y70Yj0Yk0Yl0Z]0[B0[f0\M0]70]b0^^0_H0`00`10`W0aT0bc0c`0dM0eF0eG0eH0f;0fn0fo0g00g10g20g30g40g50g60g70gZ0h?0ha0iC0ig0j^0kV0l_0mC0mg0nK0o>10110U11911]12JFFFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FB2HB5Ha_st5Hl_stFFFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS1R3HIA4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2h12FBFS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3sp13H284LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H263H284LFB'S1R3HIA4STKg4STKs4STKf1h2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp2lo2bs3LFB3LOS3sp13H284LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2lo2bs3LFB3LOS3ARBS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBFFFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3sp13H284LFB'2FBS2FBS2spS1R4STKg4STKs4STKf2LF2sp2bs3SPA3LFB3SPR3sp13H243H253H263H28S1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS2FBS2FBSS1R4STKg4STKs4STKfS1R4STKg4STKs4STKf2LF2sp3slo2bs4SLOS3LFB3ALO4LFB'2FB2F1S1R4STKg4STKs4STKf2LF2sp2bs3LFB3SPR3sp13H284LFB'2FB2F02F8S1R3HIA4STKg4STKs4STKf1h2sp3TOP3sp13SP1S2FBS2FBS2spS2FBS2FBS2FBFFFS2FBS2FBFS2FBS3sp1SS2FBS1R3NS14STKg4STKs4STKf5STKg02LF2sp1A1n2lo2bs2A04ASTK3LEN3SLO3LFB3LOS4ALO13SPR3ARBSS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO3ARBS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'S1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'S1R4STKg4STKs4STKf2LF2sp2bs3LFB3SPR3sp13H284LFB'2FB2F02F8S1R4STKg4STKs4STKf2sp2lo3slo4SLOS4SLOL3SLO3LOSS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FBS2sp3sp13SP1S1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H263H284LFB'2FBS2FBSFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3ACV3SPR3sp13H284LFB'2FB2F02F1S1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1S1R4STKg4STKs4STKf2FB2F02KbS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H284LFB'2FB1c2HcS1R4STKg4STKs4STKfS2LF3LFBS1R4STKg4STKs4STKf2sp2lo3SLO3sp13SP1SS3sp1SS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2sp2bs3LFB3SPR3sp13H243H28FS1R3NS14STKg4STKs4STKf5STKg02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2F14FBLO2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2F14FBLO2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBFFS1R4STKg4STKs4STKf2LF2sp2bs3LFB3sp13H264LFB'S1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R3HIA4STKg4STKs4STKf1h2LF2sp1A2bs3TOP3LFB4HTOP3ARBS1R3HIA4STKg4STKs4STKf1h2LF1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2F02HBS1R3HIA4STKg4STKs4STKf1h2LF2sp2bs3TOP3LFB4HTOP4LFB'FFS1R3HIA4STKg4STKs4STKf1h2LF2sp2lo2bs3TOP3LFB4HTOPS1R4STKg4STKs4STKf2LF1A2lo2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R3HIA4STKg4STKs4STKf1h2LF2bs3LFB4LFB'S1R4STKg4STKs4STKf2LF3slo2bs4SLOS3LFB4LFB'S1R4STKg4STKs4STKf2LF1A3slo2bs4SLOS3LFB3ARBS1R4STKg4STKs4STKf2LF3slo2bs4SLOS3LFB4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF3slo2bs4SLOS3LFB4LFB'S1R4STKg4STKs4STKf2LF2sp1A2lo2bs3LFB3ARBFS1R4STKg4STKs4STKf2LF1A2bs3LFB3ALO3ARBS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'S1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB3ALO4LFB'S1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2HB5Ha_stS1R4STKg4STKs4STKf2LF2sp2lo3slo2bs4SLOS4SLOL3SLO3LFB4LFB'FFS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2HB5Ha_st5Hl_stFFFFFFFFFS1R4STKg4STKs4STKf2LF2lo2bs3LFB3LOSS1R4STKg4STKs4STKf2LF2bs3LFB3sp14LFB'S1R4STKg4STKs4STKf2LF1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF1A2bs3LFB3ARBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R3HIA4STKg4STKs4STKf1h2LF2sp3slo2bs3TOP3LFB4HTOP4LFB'S1R3HIA4STKg4STKs4STKf1h2LF2sp1A3slo2bs3TOP3LFB4HTOP3ARBS1R3HIA4STKg4STKs4STKf1h2LF2sp3slo2bs3TOP3LFB4HTOP4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FB2HB5Ha_st5Hl_stS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB4LFB'2FBS1R4STKg4STKs4STKf2LF2bs3LFB3sp13H273H284LFB'". (* [comment removed for export] *)
  #[using="ALO1 LOS LFB TPV SPH SPA TOP SLO SLOL SLOS DLO CRD Hn LEN HBY ASTK CWA A0 P7Z STKg0 STKf STKs STKg NS1 SM2 UARG IMG"]
  Lemma pro_walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    HM asegs R HIA h LB LF m ->
    stk asegs m lo (bv_unsigned sp) -> sshad asegs AL m slo (bv_unsigned sp) -> mem_inv asegs m ->
    aobj asegs AL CS m A PKCS7_SIZE -> (1 <= n -> aobj asegs AL CS m DATA n) ->
    evtA asegs AL CS S1P
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 DATA) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_PKCS7_PARSE_DER) fc None m (seg_rom asegs)).
  Proof.
  intros until t6.
  intros HH ST SS MI OA OD.
  unfold A_PKCS7_PARSE_DER.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(first [ clear - LOS SLO NS1 STKg0; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  unfold pkcs7_zero in P7Z.
  pose proof (rw_cells_bound _ _ _ _ P7Z) as ARB.
  cbn [cells_size csize Nat.add length] in ARB.
  (* [comment removed for export] *)
  pose proof (conj HBY (conj P7Z (conj OA (conj OD I)))) as EBOX.
  clear HBY P7Z OA OD.
  carve_frame 192%nat ST.
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
  lx_hide1 EBOX.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 557%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H1 into f).
  lxr_leaf. lx_carry. lx_unhide.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -192) ST ltac:(first [ clear - SP1 SLO NS1 STKg0; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340476) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 224); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP NS1 STKg0; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). kland Kb.
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 2) with 256 in *. change (8 * 2 ^ 2) with 32 in FSH. change (Z.to_nat 256) with 256%nat in FRM. change (Z.to_nat 32) with 32%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ A 1440 FB 256 FRSH CWA ltac:(clear; lia) ltac:(clear; lia) LOS) as APPA.
      pose proof (frame_apart_obj0 R HIA LB LF lo DATA n FB 256 FRSH CRD (proj1 Hn) ltac:(clear; lia) LOS) as APD.
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -192) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -192) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 56) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 56) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 56 - Z.of_nat 8) with (sp1 + 48) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [8; 8; 8; 232]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FREST.
      cb8_to_c8 FHD (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  idtac "HDR-STORES".
  idtac "SB-STORES".
  try (lx_hide1 EBOX). lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x97908] [] 557%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f); try (let f := fresh "lxh" in rename H1 into f).
  lxr_leaf. lx_carry. lx_unhide.
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  try (match goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb _) _ |- _ => rename H into FSHX end).
  (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FRx : rw_cells _ mx (FB + 24) [CB 232 ?jr] |- _ =>
          apply (rw_cells_split_CB asegs mx (FB + 24) [] 232 jr [] [8; 8; 24; 8; 24; 8; 24; 8; 8; 8; 24; 8; 64; 8]%nat) in FRx; [| reflexivity];
          cbn [mk_CB_cells app] in FRx;
          chunk_split FRx 1%nat FLNK FRMb;
          chunk_split FRMb 1%nat G4 FRMc; chunk_split FRMc 1%nat J40 FRMd;
          chunk_split FRMd 1%nat G8 FRMe; chunk_split FRMe 1%nat J72 FRMf;
          chunk_split FRMf 1%nat G12 FRMg; chunk_split FRMg 1%nat J104 FRMh;
          chunk_split FRMh 1%nat G16 FRMi; chunk_split FRMi 1%nat J136 FRMj;
          chunk_split FRMj 1%nat G18 FRMk; chunk_split FRMk 1%nat J152 FRMl;
          chunk_split FRMl 1%nat G22 FRMm; chunk_split FRMm 1%nat J184 FFLAG;
          clear FLNK J40 J72 J104 J136 J152 J184 FFLAG end end.
      lazymatch type of G4 with rw_cells _ _ ?a _ => replace a with (FB + 32) in G4 by (clear; lia) end.
      lazymatch type of G8 with rw_cells _ _ ?a _ => replace a with (FB + 64) in G8 by (clear; lia) end.
      lazymatch type of G12 with rw_cells _ _ ?a _ => replace a with (FB + 96) in G12 by (clear; lia) end.
      lazymatch type of G16 with rw_cells _ _ ?a _ => replace a with (FB + 128) in G16 by (clear; lia) end.
      lazymatch type of G18 with rw_cells _ _ ?a _ => replace a with (FB + 144) in G18 by (clear; lia) end.
      lazymatch type of G22 with rw_cells _ _ ?a _ => replace a with (FB + 176) in G22 by (clear; lia) end.
      cb8_to_c8 G22 (@nil cell).
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      destruct EBOX as (HBY & P7Z & OA & OD & _).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HPF;
        assert (CRDs : client_range L (LB ++ fdata LF) (bv_unsigned sp) DATA n) by (eapply client_range_sep; [exact CRD| intros b Hb; exact Hb| exact DLO]);
        assert (CRAs : client_range L (LB ++ fdata LF) (bv_unsigned sp) A 1440) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWA)| exact ALO1]);
        assert (OD1 : 1 <= n -> aobj asegs AL CS mx DATA n);
        [ intros H1; eapply presA_aobj0;
          [ exact CSOK | exact HPF | exact (OD H1) | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRDs| clear; lia] ] |];
        assert (OA1 : aobj asegs AL CS mx A 1440);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OA | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRAs| clear; lia] ] |];
        assert (HB1 : bytes_at asegs mx DATA bs);
        [ eapply presA_bytes_at0; [exact HPF| exact HBY| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right; split; [rewrite LEN; exact CRDs| exact I]]] |];
        assert (P7m : rw_cells asegs mx A [CB 1440 (zeros 1440)]);
        [ eapply presA_rw_cells; [exact HPF| exact P7Z| exact CRAs| exact I] |];
        clear HPF end.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      repeat match goal with |- _ /\ _ => split end;
        first [ eassumption | exact PRES
              | lazymatch goal with
                | |- 1 <= n -> _ => exact OD1
                | |- pkcs7_zero _ _ _ => unfold pkcs7_zero; eassumption
                | |- _ \/ _ => first [exact APPA | exact APD]
                end
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
