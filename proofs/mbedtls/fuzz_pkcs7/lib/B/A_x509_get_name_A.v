(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts P_x509_get_name_A.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_len A_asn1_free_named_data_list_shallow A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts A_x509_get_name_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00118562864b5d80 0 4 0 1 59 1 76 1 77 1P0016370a90459513 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P001c5f73e1909380 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P00558652ec4976d0 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P0056993fe8b84361 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P0088a9d7b828da99 1 2 32 3 0 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P00a33538b1bb179c 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P00f26abcaa8ef5f4 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P013fbf70522f0718 0 4 0 1 59 1 76 1 77 1P016df93efca1f7ec 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P018209e6bff17586 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P01a50f980fa198a1 0 4 0 1 59 1 76 1 77 1P01cd4fe85ee5f7f6 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P0234d2d726475a8f 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P0258737385ec1a63 0 6 0 1 33 1 61 1 78 1 95 1 96 1P0402dce4e0da576d 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P0456b664d04cd8b0 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P04607c76ec2d37ad 0 6 0 1 48 1 50 1 60 1 76 1 77 1P04a8320209be37d8 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P04c6dad6672aea06 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P04fb866082eb3c62 0 4 0 1 59 1 76 1 77 1P0504a12e45ed3e68 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P051199d1393f180d 0 8 1 1 42 1 68 1 70 1 80 1 83 1 96 1 97 1P054164e7f659c7a9 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P05539c3831e558f5 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P0580a4c3ae33336f 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P05a222a572d09871 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P066c9ef701a7e72c 0 8 1 1 42 1 68 1 70 1 80 1 83 1 96 1 97 1P06c18b35a3a77ad1 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P077c1a432265b95c 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P07cb070113cf0123 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P07cb77bd7928b3f6 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P07ddcf13833b4aca 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P080e42da979a2a44 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P08cb0f7c48dd43ab 0 5 0 1 35 1 59 1 76 1 77 1P08d1967488493e71 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P08d206c80a0c2b61 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P08e90c06d3224a4c 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P09ad6183f5a45248 0 6 0 1 33 1 61 1 78 1 95 1 96 1P09be6140e209ba6b 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P09c1b4d6cb219c1d 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P09f008266995386e 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P09f319e389286a7d 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P0a50514d64fb0730 0 4 0 1 59 1 76 1 77 1P0a7ebb5ca4ca4159 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P0a91dd5bdab176a3 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P0ab559fb6fc8dd21 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P0b292dc2cbd2cab6 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P0b2ece465cb505c8 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P0b2f816c08c7607f 0 2 0 1 35 1P0b6086557f9c215f 0 5 0 1 35 1 59 1 76 1 77 1P0b60cc0a86d9c51b 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P0b663b4a041aa342 0 6 0 1 33 1 61 1 78 1 95 1 96 1P0b8b445cf8331fad 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P0bbc0a032fb88007 0 6 0 1 58 1 61 1 78 1 95 1 96 1P0c1122f865d256ef 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P0c69b3e0195b403d 0 5 0 1 35 1 59 1 76 1 77 1P0ce976894dfcecad 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P0cf070d07d3fb564 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P0d046bcbb803ba39 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P0d174c38064560d7 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P0d1b4aecc6e78758 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P0d563deb2dd278c6 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P0d71051e0590d771 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P0d7ef0b8113b285b 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P0d9a8b172305873b 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P0e2c0e15edeb1b76 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P0e3fb73f4cc8cadb 0 6 0 1 33 1 61 1 78 1 95 1 96 1P0ee456de67ffa4a0 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P0f13153006d32584 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P0f5148d44c223f2c 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P0fb752ce27caf3b5 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P10804ad0543e714a 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P1085dd99b3ed11c9 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P10c35796d8e6641e 0 4 0 1 59 1 76 1 77 1P11493c604da07198 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P1170111224924268 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P119f182921803b96 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P11c57aa2e7ba6b46 1 1 16 3 0 1 97 1 98 1 10 48 1 68 1 70 1 73 1 80 1 81 1 82 1 96 1 99 1 100 16P128b7709773f023e 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P12aeef760cb2e08a 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P12f5e7062508f205 0 4 0 1 59 1 76 1 77 1P132be601acc9f0ab 1 1 16 3 0 1 96 1 97 1 10 47 1 67 1 69 1 72 1 79 1 80 1 81 1 95 1 98 1 99 16P1336858824ce5969 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P137904004090c288 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P13a33d86f66b24d3 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P13ecc2519e21f33b 0 5 0 1 35 1 59 1 76 1 77 1P14786f330d467d5c 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P1491a25bf9d5b2d6 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P14f9555b14cf2d31 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P14fef8e6d6862823 0 6 0 1 58 1 61 1 78 1 95 1 96 1P15467059ba34c9a2 0 6 0 1 48 1 50 1 60 1 76 1 77 1P1569866a4cc03e6f 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P16145e5d5e93a03f 1 1 16 3 0 1 97 1 98 1 10 48 1 68 1 70 1 73 1 80 1 81 1 82 1 96 1 99 1 100 16P1656e5c774cafbf9 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P165a82a5ac98af85 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P168d33d1e56a74c3 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P16af009d83caa62f 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P16b2d288240ddc91 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P16c96b0173bcd219 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P16d2f651451cd742 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P16f6656bc7dc570c 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P174d4153957b7e37 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P17e4f87d4bcc3cfa 0 6 0 1 48 1 50 1 60 1 76 1 77 1P186ccafe7f8d6a7f 0 4 0 1 59 1 76 1 77 1P187e6bf2a57e6a20 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P18812664265769f0 0 4 0 1 59 1 76 1 77 1P18bf609381180f1e 0 6 0 1 33 1 61 1 78 1 95 1 96 1P18e3c704b27d9476 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P1920cdc472f8163f 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P192a906ed2e4384e 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P195c5aa082d5b0ad 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P196320948f1e4c2e 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P19fbe40a631d76bd 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P1a140a51877e667b 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P1a2d2d51bc44f15f 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P1a4f33fb0a30f050 0 6 0 1 67 1 69 1 79 1 95 1 96 1P1abd7ccbce8e193a 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P1b0224ff23fa391c 0 5 0 1 35 1 59 1 76 1 77 1P1b6021fc61b37aea 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P1bbc475922404634 0 5 0 1 35 1 59 1 76 1 77 1P1c318b42b77d2228 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P1ca0844cc9f3da26 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P1cbe552f0311d91c 0 8 1 1 42 1 68 1 70 1 80 1 88 1 96 1 97 1P1d26aaeecfe9131a 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P1d5616173d537d63 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P1d572530ad893b6d 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P1dca29dfb39f2927 0 6 0 1 48 1 50 1 60 1 76 1 77 1P1dcac0b1a1e3d832 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P1dd06240c3ddec49 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P1dea327cbc746f2c 1 1 64 2 0 1 95 1 3 6 1 96 1 97 64P1ded8a75e7ba5a49 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P1df884fe061bab53 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P1e089dc1192887d2 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P1e6dd12a0934d703 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P1e9d9675132d5f26 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P1f4ca63f90aec084 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P1f58db1ede0d3117 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P1f5f0c330891893a 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P1f6a3ca4cc894c0a 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P1f6dc71c332d539a 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P1f724e2b4233bc3a 1 1 16 2 0 1 76 1 3 7 1 77 1 78 16P1f974936d2a3df8c 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P1fdb3087b26e9b98 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P202df3daa308704a 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P2036552e474915ed 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P2059a21cfa6b118a 0 6 0 1 48 1 50 1 60 1 76 1 77 1P208e3287c3e8dac6 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P2096a2f7f1693798 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P20a42d64a9ae19af 0 6 0 1 48 1 50 1 60 1 76 1 77 1P20bcd24f75d93c4b 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P210d7e53c359eb49 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P2189d5b420637acf 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P21a809f7c9e5c9f5 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P2201d85aaba4bf1a 0 6 0 1 58 1 61 1 78 1 95 1 96 1P22725b1debd69671 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P22fedad279266ef8 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P230d4096125a3e2e 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2334c89c12016915 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P23bb7fe4c95dd9c8 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P23e39a1f553a7306 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P23ec0e51e2b8610d 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P243cb7b434de2030 0 6 0 1 33 1 61 1 78 1 95 1 96 1P2498b56624d0a669 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P24cdbd148f349b91 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P25112b443f6eb51f 0 5 0 1 35 1 59 1 76 1 77 1P2534b6a31ed28dd1 0 6 0 1 58 1 61 1 78 1 95 1 96 1P25676041ba51f04c 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P256c141a04997156 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P25855904d2dd3c04 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P259ae4321a35dac1 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P25f497a9ceea69c2 0 5 0 1 35 1 59 1 76 1 77 1P261d28ea517e1b91 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P26359b73d546939a 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P267e6f3c420c5c34 0 6 0 1 33 1 61 1 78 1 95 1 96 1P269f286017088b91 0 6 0 1 48 1 50 1 60 1 76 1 77 1P26fe0cdcd8bd9ad8 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2726868b86ab7783 0 6 0 1 48 1 50 1 60 1 76 1 77 1P2750a0c94121e1c6 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P276a973dc8461797 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P27996b78a77fafaa 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P27bdebc24d02067e 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P27ea5e01093f8219 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P27f84ba23d979ed7 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P282f0734facdef6e 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P2836f0d7bea540c8 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P2841ef58d67d8e3d 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P288a8f5a54f91881 0 4 0 1 59 1 76 1 77 1P28c7f7fdd3f33a67 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P292332166584a2f6 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P293bc991abbe2429 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P296d9f16a8668bcf 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P29b1afab1fd17008 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P2a381411e376f993 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P2a3f5d8b57a1d236 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P2a4034964ea835a3 0 5 0 1 35 1 59 1 76 1 77 1P2a4eb098cc014a25 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P2a55fc038058abe3 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2a7306ab340ad940 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P2a9d4f5efabb2892 0 6 0 1 58 1 61 1 78 1 95 1 96 1P2b2a1016547a3f09 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P2b6feea4b00f76d6 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P2b8e0ebd5edfd7ee 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P2bb9b818b42e5df1 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P2bbf7301309db3b9 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2bd730b063fedf12 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P2bf8b86006c3e596 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P2c0dd8f94ffaa526 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P2c0e31ae9df80c41 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P2c34239a7da754f3 0 3 0 1 46 1 59 1P2c3423b76f94d275 0 4 0 1 59 1 76 1 77 1P2c6601c6e018cb47 1 1 16 3 0 1 97 1 98 1 10 48 1 68 1 70 1 73 1 80 1 81 1 82 1 96 1 99 1 100 16P2c6dada791934bd9 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2c716019555519f4 1 2 32 3 0 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P2c8b35478ce54da3 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P2c927944bd53fa96 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P2d048bfaf1a0935d 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P2d704b9b820a432e 0 5 0 1 35 1 59 1 76 1 77 1P2da17fb8eb963253 1 2 32 3 0 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P2df3ae0837324131 0 6 0 1 58 1 61 1 78 1 95 1 96 1P2e2a8dfedc289aa1 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P2e52046edfde780b 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P2e547a50f2eaf166 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P2e6613d8557515dc 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2e9e39891bc461d2 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P2ea19c5e8af1970b 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P2ef4b6c64a0a7c90 0 8 1 1 42 1 68 1 70 1 80 1 88 1 96 1 97 1P2f0cd817b287e0ce 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P2f920e3ed2612d3e 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P2f947429e5151c9e 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P2faa7bfd6581ad6d 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P2fc10c09a11bdd15 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P2fe096c0b40ccb53 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P2ff6c3d327d76882 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P30663f19efb4c105 0 6 0 1 33 1 61 1 78 1 95 1 96 1P30c36af988990ecc 0 7 0 1 48 1 50 1 60 1 63 1 76 1 77 1P30d5b3df444aa132 1 1 16 2 1 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P30fb5fe71e5e7471 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P312ae3bb6ddad439 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P31b23b774134cf4d 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P31d1e47da564dea3 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P31d5e733a7a0d958 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P31fbb1ae5baf3573 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P3213c74981de6c9f 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P323b99c67945f9a9 1 1 64 2 9 1 95 1 3 0 1 96 1 97 64P3282ba48a458d16b 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P33183941a4f7401a 0 6 0 1 48 1 50 1 60 1 76 1 77 1P333a9d62e1f23106 0 4 0 1 59 1 76 1 77 1P3354ff025b9834ed 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P336c9994698a2950 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P33a4559ed80cfed2 0 6 0 1 48 1 50 1 60 1 76 1 77 1P33bb29b9590d6d07 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P33bd960d8034dac9 0 5 0 1 35 1 59 1 76 1 77 1P33f577d4130cdc35 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P343b4139650bce57 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P3443000544f3b2d5 0 8 1 1 42 1 68 1 70 1 80 1 88 1 96 1 97 1P349c9d2e6b24e831 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P34d6c63ea8f9baf1 0 2 0 1 88 1P34e41bf678150f59 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P35639bfa01d9ff2d 0 8 0 1 41 1 67 1 69 1 79 1 87 1 95 1 96 1P3564e1baff2d40b9 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P356a042f9b56721d 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P3631bc8533b1e42b 0 5 0 1 35 1 59 1 76 1 77 1P36434ae747609c27 0 6 0 1 48 1 50 1 60 1 76 1 77 1P36a5bcb87b71818c 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P36d21564b2361529 0 6 0 1 58 1 61 1 78 1 95 1 96 1P36e38a0e42500121 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P37128e037b8df8fd 1 2 16 3 1 1 27 1 77 1 16 3 0 1 28 1 78 1 2 79 1 80 1P3725488886ab9edc 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P37333b7fed31e384 1 2 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 2 100 2 101 2P3756ca8a7a8c6db4 0 9 0 1 41 1 67 1 69 1 79 1 80 1 81 1 95 1 96 1P37771ca8e2446edf 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P37957b2d7f1d9ab5 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P37d6b798d995dfe2 0 4 0 16 58 16 76 16 77 16P37e174b2d7e316ba 0 5 0 1 35 1 59 1 76 1 77 1P37e908cf3f52fed8 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P3815ec93f92ddea7 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P381de93e5be2b953 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P383b202230e740b7 0 8 0 1 41 1 67 1 69 1 79 1 82 1 95 1 96 1P38550bcff2f69cc9 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P386bc7ea83c8bffd 0 8 0 1 48 1 50 1 60 1 61 1 62 1 76 1 77 1P3872437b6328548b 0 6 0 1 33 1 61 1 78 1 95 1 96 1P3873cda200346d95 0 6 0 1 58 1 61 1 78 1 95 1 96 1P3894a57ce2f25e13 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P38e5181a0fd2b216 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P393d144522db0b64 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P394f2f79cbebf9a6 0 4 0 1 59 1 76 1 77 1P3967b8e57cbaf765 1 1 16 3 1 1 27 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P39880d30b97a72bd 0 6 0 1 48 1 50 1 60 1 76 1 77 1P39f9fd61eb99f447 1 1 16 3 0 1 96 1 97 1 4 61 2 95 2 98 2 99 32P3a3947fc28d44238 1 2 32 3 1 1 96 1 99 1 32 10 42 1 48 1 68 1 70 1 73 1 80 1 81 1 82 1 97 1 98 1 2 100 2 101 2P3a50e0d18d0ba597 0 5 0 1 35 1 59 1 76 1 77 1P3a5c0a748201f9ea 0 7 1 1 49 1 51 1 61 1 64 1 77 1 78 1P3a6237aa36b74654 1 1 16 3 0 1 97 1 98 1 4 62 2 96 2 99 2 100 32P3a71e9790d884172 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P3affd6b90f9c1066 0 6 0 1 48 1 50 1 60 1 76 1 77 1P3b6e60650d1cbc3c 0 7 1 1 49 1 51 1 61 1 69 1 77 1 78 1P3be17e38c620be7d 1 2 32 3 0 1 95 1 98 1 32 10 41 1 47 1 67 1 69 1 72 1 79 1 80 1 81 1 96 1 97 1 2 99 2 100 2P3c9f09d5d3f0cec9 0 6 0 1 33 1 61 1 78 1 95 1 96 1P3caa8f7e92340f62 0 7 0 1 41 1 67 1 69 1 79 1 95 1 96 1P3d118360f5d6c8f3 0 6 0 1 48 1 50 1 60 1 76 1 77 1P3d7861256fe55bf0 1 1 16 4 1 1 29 1 42 1 77 1 9 47 1 49 1 51 1 54 1 61 1 62 1 63 1 78 1 79 16P3e026716ff6fdda9 0 10 2 1 50 1 52 1 53 1 55 1 62 1 63 1 64 1 78 1 79 1P3eab57d9ea8c2a9b 0 7 0 1 48 1 50 1 60 1 68 1 76 1 77 1P3ef7b228fe6ecb92 0 4 0 1 59 1 76 1 77 1P3f2512fae25cc4eb 0 8 1 1 42 1 68 1 70 1 80 1 83 1 96 1 97 1P3f5a5a8dd092d956 0 6 0 1 58 1 61 1 78 1 95 1 96 1P3f95722956620204 0 3 0 1 32 1 45 1P3fecd7db9d120c3d 0 6 0 1 58 1 61 1 78 1 95 1 96 1N00348a179aabf288N003b8d1a7f0719f4N008f51489a4a191bN010f9367d792f29dN0133927b88644160N01366ba7152005f2N015c3520ca343728N021947b2bd07a6a9N024b258b3b9fe8e9N03c4daeeb6c05263N042cbebcca145a00N04d93cfa1e9338dbN053623c42447f9eaN0589e9245ba6c847N06203fe1de302a21N063d1cadf847f9bdN068ca7b16bfdcf1aN074fcebc31c8f165N07d4d8caf419b35aN089c63e293119145N0906258fd7db62d5N0933511008eae9b8N099cbed66b4395e2N0b2a8ff571b12126N0b3b29359c0f35c2N0c54f60539cde67bN0cbed6c5a1823e4eN0cc163115682e542N0ccbb59f0de582c2N0cee5f2c4289282cN0dddb6e31c26a878N0df497c7cd0085d9N0f4c6545f85cb62aN102b83f21e82fb17N107d01f8b97cb2deN108113d7aebc3dffN110e77bea8651fb2N12849d17a22617bdN1296d3bd301b5c17N129932f8b156171eN12b9414318c6239fN12e0bf8e2ec96ffdN132c24f3d3dce00dN133a64952879fc63N139a7caf1a8c15bfN14458e98b5e56343N14541fd21e115ebfN154cfd7624d5afbcN15961a1c0093a05dN1625478d24ee997cN16264b14331eafebN163cd459f6fe6e8bN1686dc47dfb39cecN170e701ae901056dN17df4ec95e32edc4N17f423f2c0a64982N1845eeed083112d3N18eedfdfc1e461bbN18f37ea4be2bb92dN1903db570ec16a84N1a094c6d29fc324cN1a39559607f73e55N1a72c2e91088f8d4N1b3cc46063ae1c72N1b646a5934f109ffN1c2ddd6d07574a59N1c6b7fde8618b5c8N1d5ca150f97d37c4N1d7588d3fdbcbc9aN1d90823e85ee6eb5N1e479f9cf2eb639aN1ec3bdd0f5d4a5f6N1ed99a5971f421f2N1ee2c1889ab52991N1eeaffd10ad8e519N201a2ae17aec7394N2050537e448cdcc4N205966424e7a875bN20e44568c446c20cN2148f05e7c1f5fabN2199e6458fa19ba5N219fae174177dd34N238b41a603434c74N23c9bc38841b224fN24997ed284533dacN24b2e582b3be9c4fN2531eec6bb059e16N256e289f0793da68N25d837a5b1854532N25e4acc85b8d1b4aN25eca7c0d053bdc6N26376979e671a1d6N264ce40c502f071bN26eb91deb12073f3N27b8c3961fbc0804N294b07c2204d53abN2972cba45303aefeN29c382d0d8e408f5N29c77cfb13f2655dN29f356450ffee26fN29fcdb491433e8fdN2a4c9c1cf32fdc55N2acd0b292e11f7a5N2aefc68418eb7365N2b6f984a3d792dceN2d7048213d8a7771N2e30c748a94c24b9N2e39b65065d84062N2e40350416f88c1cN2e664f9824a4791bN2e78fc1485244475N2e875945a83a2ccbN2eac2dab08f19fadN2eb3571991285feeN2ed0d724c19f6fd0N2ed4911e9eda9ff2N2f4787b48540186aN314973e903c39ab3N31c400a41e1f1eb8N325e078a1fa48585N32e4f8cd96a677ddN33c28e6755e6bb43N342571b46cf9c618N346b53edb9d08464N34b57b8144d759d1N34bca83389b47e5eN35a141393da51107N35f47d54d6ad9140N36324eaf1cc92e6eN368e015286d00fe2N36fc3bc1c0221776N37a3f28e370e7846N37b74f0f1de0c27aN382529337a2f0a31N38e24b734fb869eeN398e43bcc91f8059N3a6f9bb5a354be8fN3acdd6eab65f861dN3b01720e8635524dN3b1059964827f4f7N3c08781214ff9c9bN3d2f3fb2873eff81N3de1167dcdb6cb22N3e808863b6148f86N3f4ec1b5edea97f6N3f731d6e9c1e9d38N3f74306268b12842N3f834d3f0e2b18deN3fb6bb0c74a3b0f2N3ffac02dfaed32b8"%lxh.
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
Ltac2 gd_tbl_A_x509_get_name_A () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Walk.Call.rsl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_name_stmt.A_X509_GET_NAME"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_WCALLOC : Z := 0x69484.              (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT : Z := 0x0f5ea8.             (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Hypothesis FREEL : asn1_free_named_data_list_shallow_stmtA asegs R HIA A_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55855578687.12000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKn : Z := 240 + Z.max (Z.max 16 (32 + arl_need_rt R)) (arl_need_smalloc R).

  (* [comment removed for export] *)
  Definition CNTn (n : Z) : Z := n / 6.
  Definition PHIn (n : Z) : Z := (n / 6) * (2 * 64 + AVOL_CALL) + (n / 6) * AVOL_CALL.
  Definition FFRn (n d : Z) : Z := (n / 6) * Z.max 0 (fr_charge (d + 1)) + (n / 6) * fr_charge 0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2431248216.16 L56910101129.16L63969262006.1600000800@00AS1n2n'1HS1n2n'1HS". (* [comment removed for export] *)
  Lemma div6_mono : forall n n', 0 <= n <= n' -> 0 <= n / 6 <= n' / 6.
  Proof. intros n n' H. split; [apply Z.div_pos; lia| apply Z.div_le_mono; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L36691039924.19L63967161564.17L63969262006.1800000@00A00GS1a1b2Ha2Hb1H2H0SS1a2Ha". (* [comment removed for export] *)
  Lemma div6_sadd : forall a b, 0 <= a -> 0 <= b -> a / 6 + b / 6 <= (a + b) / 6.
  Proof.
    intros a b Ha Hb. apply Z.div_le_lower_bound; [lia|].
    pose proof (Z.mul_div_le a 6 ltac:(lia)). pose proof (Z.mul_div_le b 6 ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L44722220398.18L63967151244.1800000=00>S1k1x1n2H12H2S". (* [comment removed for export] *)
  Lemma cnt6_div : forall k x n, 6 * k <= x -> x <= n -> k <= n / 6.
  Proof. intros k x n H1 H2. apply Z.div_le_lower_bound; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma CNTn_mono : forall n n', 0 <= n <= n' -> 0 <= CNTn n <= CNTn n'.
  Proof. intros n n' H; unfold CNTn; exact (div6_mono n n' H). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2257843156.1700000;S1n2n'1H2H0". (* [comment removed for export] *)
  Lemma PHIn_mono : forall n n', 0 <= n <= n' -> 0 <= PHIn n <= PHIn n'.
  Proof. intros n n' H; unfold PHIn, AVOL_CALL; pose proof (div6_mono n n' H); lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma FFRn_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRn n d <= FFRn n' d.
  Proof. intros n n' d H; unfold FFRn, fr_charge. pose proof (Z.le_max_l 0 (d + 1 + 3)). pose proof (div6_mono n n' H). nia. Qed.
  Lemma CNTn_sadd : forall a b, 0 <= a -> 0 <= b -> CNTn a + CNTn b <= CNTn (a + b).
  Proof. intros a b Ha Hb; unfold CNTn; exact (div6_sadd a b Ha Hb). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16482844668.1800000=S1a1b2Ha2Hb1H". (* [comment removed for export] *)
  Lemma PHIn_sadd : forall a b, 0 <= a -> 0 <= b -> PHIn a + PHIn b <= PHIn (a + b).
  Proof. intros a b Ha Hb; unfold PHIn, AVOL_CALL; pose proof (div6_sadd a b Ha Hb); lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma FFRn_sadd : forall a b d, 0 <= a -> 0 <= b -> FFRn a d + FFRn b d <= FFRn (a + b) d.
  Proof. intros a b d Ha Hb; unfold FFRn, fr_charge. pose proof (Z.le_max_l 0 (d + 1 + 3)). pose proof (div6_sadd a b Ha Hb). nia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L61587414154.13000003S1R". (* [comment removed for export] *)
  Lemma STKn0 : 0 <= STKn.
  Proof. unfold STKn. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF CUR lo slo d : Z) (bs : list byte) (j48 : list byte) (mg : byte) (pad7 : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 7)%nat.
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
  Hypothesis HCUR : rw_cells asegs m CUR (name_blob j48 0 mg pad7).
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 64.
  Hypothesis CURLO : CUR + 64 <= lo.
  Hypothesis DCB : CUR + 64 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKn.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_1 in SM1; unfold STKn in SLO; unfold NAME_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Ltac list_eq_lits := first [ reflexivity | apply bv_eq; vm_compute; reflexivity | (progress f_equal); list_eq_lits | idtac ].

  (* [comment removed for export] *)
  Definition rsl (FB : Z) (j0 j96 : list byte) : list cell := [CB 16 j0; C8 (Z_to_bv 64 (-9186)); C8 (Z_to_bv 64 (-9184)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 END); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 (-10368)); C8 (Z_to_bv 64 1347948552); C8 (Z_to_bv 64 (FB + 64)); C8 (Z_to_bv 64 CUR); CB 16 j96; C8 (Z_to_bv 64 FB)]
(* [comment removed for export] *).
  Definition rslr (FB : Z) (j0 j96 : list byte) (r64 : Z) : list cell := [CB 16 j0; C8 (Z_to_bv 64 (-9186)); C8 (Z_to_bv 64 (-9184)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 END); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 r64); C8 (Z_to_bv 64 1347948552); C8 (Z_to_bv 64 (FB + 64)); C8 (Z_to_bv 64 CUR); CB 16 j96; C8 (Z_to_bv 64 FB)].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_A ()) "Lms,$7.(8.$9.LFB,$9.(8.$9.Lsp1,$9.(8.(:.$;.VR,VHIA,)Lh1,(:.$;.VR,VHIA,)(8.P,(<.&40.)(=.(<.&8.))Lm1,P,(<.&40.)(=.(<.&8.))(8.(<.&40.)Lx1,(<.&40.)(8.(<.&40.)Lt0,(<.&40.)(8.(<.&40.)Lt1,(<.&40.)(8.(<.&40.)Lt2,(<.&40.)(8.(<.&40.)La0,(<.&40.)(8.(<.&40.)La1,(<.&40.)(8.(<.&40.)La3,(<.&40.)(8.(<.&40.)La4,(<.&40.)(8.(<.&40.)La5,(<.&40.)(8.(<.&40.)La6,(<.&40.)(8.(<.&40.)La7,(<.&40.)(8.(<.&40.)Lt3,(<.&40.)(8.(<.&40.)Lt4,(<.&40.)(8.(<.&40.)Lt5,(<.&40.)(8.(<.&40.)Lt6,(<.&40.)(8.(<.&40.)Lw0,(<.&40.)(8.(<.&40.)Lw1,(<.&40.)(8.(<.&40.)Lw2,(<.&40.)(8.(<.&40.)Lga,(<.&40.)(8.(<.&40.)Lgb,(<.&40.)(8.(>.(<.&8.))Lj0,(>.(<.&8.))(8.(>.(<.&8.))Lj96,(>.(<.&8.))(?.(10.$7.R1;.(11.(12.R16.(4.&40.R19.)Vgp,Vtp,R15.R14.R13.Vsp,(4.&40.R19.)R12.R11.(4.&40.-23>2.)R10.R?.R>.R=.R<.(4.&40.VEND,)(4.&40.(5.(13.VPP,+3.)(14.(15.VR,))))(4.&40.VPP,)(4.&40.(5.(13.R1:.+3.)(14.(15.VR,))))(4.&40.(5.R1:.+40.))(4.&40.(5.R1:.+20.))(4.&40.(14.(15.VR,)))(4.&40.VCUR,)(4.&40.+1.)(4.&40.-8.)R;.R:.R9.R8.)VF,(4.&40.+:<=>8.)Vfc,(16.(<.&40.))R17.(17.$;.)))(?.(?.(18.(19.(1:.&40.Vsp,)+?0.)R19.)(18.R19.(19.(1:.&40.Vsp,)+>0.)))(?.(10.$9.(1;.R19.+20.)=)(?.(1<.$;.VR,VHIA,R18.VLB,(0.(1=.$9.$9.)(1>.$9.$9.R1:.+80.)VLF,)R17.)(?.(10.P,$9.Sp(1?.$;.VR,VHIA,R18.)(1?.$;.VR,VHIA,Vh,))(?.(10.$9.(20.$;.VR,VHIA,R18.)(20.$;.VR,VHIA,Vh,))(?.(10.$9.(21.$;.VR,VHIA,R18.)(21.$;.VR,VHIA,Vh,))(?.(10.$9.(22.$;.VR,VHIA,R18.)(22.$;.VR,VHIA,Vh,))(?.(10.$9.(23.$;.VR,VHIA,R18.)(23.$;.VR,VHIA,Vh,))(?.(10.$9.(24.$;.VR,VHIA,R18.)(24.$;.VR,VHIA,Vh,))(?.Pmo,$25.(26.(27.$;.VR,VHIA,R19.R1.)(27.$;.VR,VHIA,Vh,R1.))(?.(10.$9.(1;.R1:.+40.)=)(?.(28.VR,VLB,VLF,R1:.+80.)(?.(29.$;.R17.R1:.(0.$1.(3.R7.)(0.$1.(3.R6.)(0.$1.(3.R5.)(6.$1.)))))(?.(29.$;.R17.(5.R1:.+20.)(0.$1.(3.R4.)(6.$1.)))(?.(29.$;.R17.(5.R1:.+40.)(0.$1.(3.R3.)(6.$1.)))(?.(29.$;.R17.(5.(13.R1:.+3.)(14.(15.VR,)))(0.$1.(2:.(4.&8.+?1.))(0.$1.(2:.(4.&8.+?1.))(0.$1.(2:.(4.&8.+?1.))(0.$1.(2:.(4.&8.+?1.))(0.$1.(2:.(4.&8.+?8.))(0.$1.(2:.(4.&8.+?2.))(0.$1.(2:.(4.&8.+?2.))(0.$1.(2:.(4.&8.+?2.))(0.$1.(2:.(4.&8.=))(0.$1.(2:.(4.&8.+?3.))(0.$1.(2:.(4.&8.+?3.))(0.$1.(2:.(4.&8.+?3.))(0.$1.(2:.(4.&8.=))(0.$1.(2:.(4.&8.=))(0.$1.(2:.(4.&8.=))(0.$1.(2:.(4.&8.=))(6.$1.))))))))))))))))))(?.(29.$;.R17.(5.(1:.&40.Vsp,)-68.)(0.$1.(3.Vs11,)(0.$1.(3.Vs10,)(0.$1.(3.Vs9,)(0.$1.(3.Vs8,)(0.$1.(3.Vs7,)(0.$1.(3.Vs6,)(0.$1.(3.Vs5,)(0.$1.(3.Vs4,)(0.$1.(3.Vs3,)(0.$1.(3.Vs2,)(0.$1.(3.Vs1,)(0.$1.(3.Vs0,)(0.$1.(3.Vra,)(6.$1.)))))))))))))))(?.(29.$;.R17.R19.(2;.R1:.R2.R1.))(?.(2<.$;.R17.(5.R19.+78.)(5.(1:.&40.Vsp,)-68.))(?.(2<.$;.R17.Vlo,R19.)(?.(2=.$;.R17.)(?.(29.$;.R17.VPP,(0.$1.(3.(4.&40.VP,))(6.$1.)))(?.(29.$;.R17.VCUR,(2>.Vj48,=Vmg,Vpad7,))(?.(2?.$;.R17.VBUF,Vbs,)(?.(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)R17.VPP,+8.)(?.(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)R17.VCUR,+40.)(?.(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)R17.VBUF,(31.(32.(<.&8.)Vbs,)))(?.(33.(18.(5.R1:.+80.)VPP,)(18.(5.VPP,+8.)R1:.))(?.(33.(18.(5.R1:.+80.)VCUR,)(18.(5.VCUR,+40.)R1:.))(?.(33.(10.$9.(31.(32.(<.&8.)Vbs,))=)(33.(18.(5.R1:.+80.)VBUF,)(18.(5.VBUF,(31.(32.(<.&8.)Vbs,)))R1:.)))(?.(34.$;.VR,VHIA,Vh,VLB,VLF,(1:.&40.Vsp,)(1:.&40.Vsp,)(6.$35.)Vm,R17.)(36.$;.(15.VR,)R17.Vslo,(1:.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 ALC; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 pad7; try lx_pin1 mg; try lx_pin1 j48; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 NRT; try lx_pin1 FREEL; try lx_pin1 GETTAG; try lx_pin1 FREE; try lx_pin1 CALLOC; try lx_pin1 HMND; try lx_pin1 DIMG; try lx_pin1 NS1.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0210@D10637083020.182D10639329459.108D10779914029.181D14196765248.182D18607476203.150D2457697672.181 D29848042131.183D30470095146.151D3162359811.182 D32458983507.181D32467519491.183D32478003747.109D3254889317.149 D32604263327.184D3267764854.150 D3385912464.180 D36106837486.182D45702202657.180D46793042006.108D46795284841.182D50254960491.151D52459714198.183D560907438.110  D60098777666.109D60109264994.183D60109265005.182D60111245650.108D62011770180.184D62011770188.110D62184560053.183D67499905220.183D67506199268.109D68409210579.180D6897083606.180 L10646859417.9  L10837002389.2  L12654381620.1  L13422353012.159L15629616632.9  L19548981073.159L19980016842.9  L2275137097.0   L24133462175.154L24462168006.3  L26892418956.1  L27188209011.187L28987030758.118L29738741675.1  L30470049078.177L32463525127.1  L33472729358.118L33483560980.10 L33485826452.1  L35653441506.8  L36278886100.6  L37156630869.0  L39280637297.0  L39332637397.0  L40228640085.0  L41302442785.0  L42402910215.1  L43055369633.116L45298099350.1  L48117620909.92 L48119718058.155L48119718061.154L50790731766.8  L51609971897.157L5325812058.111 L57355539152.156L57355539152.161L58790154276.9  L59308634497.15 L60098763854.6  L61437265048.2  L68330859864.1  L68345989594.176L6910010088.154 L7040749983.112 L9356559645.13  P1056307012.151 P66690624472.151Q10533598597.112Q10594483354.188Q13345046842.112Q13349241856.189Q1530342990.151 Q23937998252.112Q23937998260.114Q24133462175.189Q24137657765.187Q24137657789.191Q24898543734.112Q24911127884.189Q29850139288.189Q30220990911.188Q31021924279.148Q31599749226.112Q31603944784.189Q32440833928.187Q36104740330.189Q38248895665.115Q40271359350.151Q42439168719.148Q42439382255.116Q42441479404.193Q43880146029.115Q47241206720.112Q48119718060.188Q48132302231.187Q49429114882.189Q49441699128.112Q50796826103.151Q56533317808.188Q59310664043.112Q59310664043.187Q59323247696.188Q59323247697.189Q59865520176.116Q59867617331.193Q6192914196.148 Q62022254700.114Q62022254708.112Q64681502661.193Q64683599814.116Q6897428426.191 Q6897428434.187 Q6910010088.189 Q9350548487.132 00000X01701\01]01^01_01`02F02G02l03U04404504a04b04c04d05I05h06P06Q06R07707]08I09509[0:@0:_0:`0;I0;h0;i0<N0<Q0<Y0<^0=M0=P0>?0>W0>X0?20?>0?B0?l0@K0@O0A80A<0A=0A>0A?0AW0Al0Am0An0Ao0B00B10B50CF0CK0D90Db0EK0E\0FI0G:0G;0Gn0HC0HO0HY0Ha0Hf0IK0Ie0JJ0Jo0KU0L=0L\0M60M70M80MZ0NH0Nj0OD0O^0P80P90P:0P;0PU0Q>0Q?0Q@0QA0QB0Qa0R>0R^0SC0Sc0TE0Te0UN0V70V80V90V^0V_0V`0Va0Vb0Vc0Vd0Ve0W@0W\0X80Xe0YW0Z10ZK0Ze0[HS1R2LF2sp2PP2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBFFFFS1R2LF2sp2bs3LFB4lxHn3sp13H213H234LFB'FS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp3CUR2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS1R3HIA2LF2sp2bs3LFB4lxHn3sp13H234LFB'2h12FBFFFS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBS1R2LF2sp2PP2bs3LFB4lxHn3sp13H234LFB'2FBFFS1R3HIA1h2LF2sp2PP3CUR2bs3LFB3PPB3CUBS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS3PPB3CUBS1R2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H234LFB'2FBS1R2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2lo2bs3LFB3LOS3PPB3CUBS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS1R2LF2sp3CUR2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBFS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBS1RS3BUF2bsS3BUFS1R2LF2sp2bs3LFB3SPR4lxHn3sp13H234LFB'2FB2F02F8S1RS1R2LF2sp2bs3LFB3SPR4lxHn3sp13H234LFB'2FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1SS1R2LF2bs3LFB4lxHn4LFB'2FBS2sp3sp13SP1S2spS1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FB1c2HcS1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBS2FBS1R2LF2sp2bs3LFB4lxHn3sp13H213H234LFB'2FBS2FBFFFS1R3HIA1h2sp2lo3TOP4HTOPS1R2sp2lo3SLO3sp13SP1SSSSSS2spS1R2LF2sp2PP1P3END3BUF3CUR2lo2bs3LFB3PP02B12B22B33DPB4CUR03DCB2D13SLO3SPR3PPB3CUBS3sp1S1R2LF2sp2PP3CUR2lo2bs3LFB3SLO3LOS3ALO3PPB3CUBS1R2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R2sp2lo3SLO3LOSS1R2LF2sp3slo2bs3LFB4SLOS3ALO4lxHn4LFB'2FB2F1S1R2LF2sp2bs3LFB3SPA3SPR4lxHn3sp13H193H203H213H23FS1R2LF2sp2bs3LFB3ACV3SPR4lxHn3sp13H234LFB'2FB2F02F1S1R2sp2lo3SLO3sp13SP1S1R2FB2F02KbS1R2lo3LOSS2LF3LFBS3sp1S1R2LF2sp2bs3LFB4lxHn3sp13H234LFB'2FBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2sp2bs3LFB3SPR4lxHn3sp13H193H23S1R2sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R2LF2PP2lo2bs3LFB4PPLO4lxHn3sp14LFB'S1R2LF3CUR2lo2bs3LFB5CURLO4lxHn3sp14LFB'S1R2LF2sp2PP3CUR2bs3LFB3PPB3CUBS1R2LF2bs3LFB4lxHn4LFB'2FBFFS1R2LF2sp2bs3LFB4lxHn3sp13H214LFB'S1R3HIA1h2LF2sp2PP3CUR2bs3LFB3TOP4HTOP3PPB3CUBS1R3HIA1h2LF2PP3CUR2bs3LFB3PPB3CUBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2bs3LFB4lxHn4LFB'2FBFFFS1R2LF2bs3LFB4lxHn4LFB'2FBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4lxHn4LFB'FFFFS1R2LF2PP3CUR2lo2bs3LFB3PPB3CUBS1R3HIA1h2LF2bs3LFB4lxHn4LFB'S1R2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R2LF2PP3CUR3slo2bs3LFB4SLOS3PPB3CUBS1R2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R2LF2sp2PP3CUR2lo2bs3LFB3PPB3CUBS1R2LF2PP3CUR2bs3LFB3ALO3PPB3CUBS1R2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'FFS1R2LF2sp2lo2bs3LFB3SLO3LOS4lxHn4LFB'FFFFFFFS1R2LF2bs3LFB4lxHn3sp14LFB'S1R2LF2PP3CUR2bs3LFB3PPB3CUBS1R2LF2PP3CUR2bs3LFB3PPB3CUBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn4LFB'S1R3HIA1h2LF2sp2PP3CUR3slo2bs3LFB3TOP4HTOP3PPB3CUBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2bs3LFB4lxHn4LFB'2FBS1R2LF2bs3LFB4lxHn3sp13H223H234LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS D1 DCB CURLO CWC CUR0 HCUR DPB B3 B2 B1 BIN HBY PPLO CWP PP0 ALP HPP LFB SM1 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_name_A ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)P,(1<.$;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2<.$;.Vm,Vlo,(1:.&40.Vsp,))P,(36.$;.(15.VR,)Vm,Vslo,(1:.&40.Vsp,))P,(2=.$;.Vm,)P,(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)Vm,VPP,+8.)P,(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)Vm,VCUR,+40.)P,(30.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)Vm,VBUF,(31.(32.(<.&8.)Vbs,)))(37.$;.(15.VR,)(1?.$;.VR,VHIA,Vh,)$38.(11.(12.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(4.&40.VPP,)(4.&40.VEND,)(4.&40.VCUR,)R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(4.&40.$39.)Vfc,(16.(<.&40.))Vm,(17.$;.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST SS MI OPP OCUR OBUF.
  unfold A_X509_GET_NAME.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO TOP HTOP; lia | lx_side_lia ]]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(first [ clear - LOS SLO; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add length] in PPB.
  pose proof (rw_cells_bound _ _ _ _ HCUR) as CUB.
  cbn [cells_size csize Nat.add length name_blob] in CUB.
  destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _].
  rewrite Forall_forall in BR.
  destruct (BR _ ltac:(apply in_or_app; left; exact BIN)) as (_ & _ & BCE & BIMG).
  cbn [fst snd] in BCE, BIMG.
  clear BR.
  (* [comment removed for export] *)
  pose proof (conj HBY (conj HPP (conj HCUR (conj OPP (conj OCUR (conj OBUF I)))))) as EBOX.
  clear OPP OCUR OBUF.
  carve_frame 224%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0xaccb0] [] 408%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. lx_unhide.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV; lia | lx_side_lia ]).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0x end.
      destruct (stk_split asegs m0x lo sp1 (bv_unsigned sp + -224) ST ltac:(first [ clear - SP1 SLO; lia | lx_side_lia ])) as [ST1 STx]. clear ST.
      lazymatch goal with FRx : rw_cells _ m0x (bv_unsigned sp + -224) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -224 + 120) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      release_frame FRa STx (bv_unsigned sp + -104). rename STx into STJ.
      destruct (stk_split asegs m0x sp1 (sp1 + 120) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m0x sp1 (sp1 + 120) 120 STlo ltac:(clear; lia)) as [_ [jrs RSL]]. clear STlo.
      replace (sp1 + 120 - Z.of_nat 120) with sp1 in RSL by (clear; lia).
      apply (rw_cells_split_CB asegs m0x sp1 [] 120 jrs [] [16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity]. cbn [mk_CB_cells app] in RSL.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 RSL [c1] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 RSL [c1; c2] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 RSL [c1; c2; c3] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7; c8] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7; c8; c9] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12] end.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with HHc : HM _ _ _ h LB LF m0x |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF m0x HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF m0x HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF m0x HHc) as FLIMG
  end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  try (lx_hide1 EBOX). try lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 408%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. lx_unhide.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 340076) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (unfold LFMAX_CRT in LFB; first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP; lia | lx_side_lia ]
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
      zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). kland Kb.
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 128 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ CUR 64 FB 128 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      assert (APB : n = 0 \/ FB + 128 <= BUF \/ BUF + n <= FB).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right]. apply F3. apply in_or_app. left. exact BIN. }
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 24; 8; 56]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat GA FRM3. chunk_split FRM3 1%nat JMC FRM4. chunk_split FRM4 1%nat GB FREST.
      lazymatch type of GA with rw_cells _ _ ?a _ => replace a with (FB + 32) in GA by (clear; lia) end.
      lazymatch type of GB with rw_cells _ _ ?a _ => replace a with (FB + 64) in GB by (clear; lia) end.
      clear FLNK JMC FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      cb8_to_c8 GA (@nil cell). cb8_to_c8 GB (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  idtac "HDR-STORES".
  idtac "SB-STORES".
  try (lx_hide1 EBOX). lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xacde8] [] 408%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry. lx_unhide.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      idtac "STORES-DONE".
      (* [comment removed for export] *)
      lazymatch goal with H : rw_cells _ m9 sp1 _ |- _ => rename H into RSLX end.
      lazymatch type of RSLX with rw_cells _ _ _ (CB 16 ?ja :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 16 ?jb :: _) =>
        assert (RSL9 : rw_cells asegs m9 sp1 (rsl FB ja jb)) end.
      { unfold rsl. lazymatch type of RSLX with rw_cells _ _ _ ?cs => lazymatch goal with |- rw_cells _ _ _ ?cs' =>
          replace cs' with cs; [exact RSLX|] end end.
        list_eq_lits. all: match goal with |- ?g => idtac "RSL-FORM-LEFT:" g; fail end. }
      clear RSLX.
      (* [comment removed for export] *)
      destruct EBOX as (HBY' & HPP' & HCUR' & OPP & OCUR & OBUF & _).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HPF;
        assert (CRP : client_range L (LB ++ fdata LF) (bv_unsigned sp) PP 8) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWP)| exact PPLO]);
        assert (CRC : client_range L (LB ++ fdata LF) (bv_unsigned sp) CUR 64) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWC)| exact CURLO]);
        assert (CRB : client_range L (LB ++ fdata LF) (bv_unsigned sp) BUF n) by (eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]);
        assert (OPP1 : aobj asegs AL CS mx PP 8);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OPP | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRP| clear; lia] ] |];
        assert (OCUR1 : aobj asegs AL CS mx CUR 64);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OCUR | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRC| clear; lia] ] |];
        assert (OBUF1 : aobj asegs AL CS mx BUF n);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OBUF | intros xq Hxq; eapply hcs_below_top; exact Hxq
                              | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right; split; [exact CRB| clear; lia]] ] |];
        assert (HB1 : bytes_at asegs mx BUF bs);
        [ eapply presA_bytes_at0; [exact HPF| exact HBY'| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right; split; [exact CRB| exact I]]] |];
        assert (HPP1 : rw_cells asegs mx PP [C8 (Z_to_bv 64 P)]);
        [ eapply presA_rw_cells; [exact HPF| exact HPP'| exact CRP| exact I] |];
        assert (HCUR1 : rw_cells asegs mx CUR (name_blob j48 0 mg pad7));
        [ eapply presA_rw_cells; [exact HPF| exact HCUR'| cbn [cells_size csize Nat.add length name_blob]; exact CRC| exact I] |];
        clear HPF end.
  apply evtA_done. unfold S1P.
      exists FB, sp1, h1, m9.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      repeat match goal with |- _ /\ _ => split end;
        first [ exact RSL9 | eassumption | exact PRES
              | lazymatch goal with
                | |- _ \/ _ => first [exact APP | exact APC | exact APB]
                end
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
