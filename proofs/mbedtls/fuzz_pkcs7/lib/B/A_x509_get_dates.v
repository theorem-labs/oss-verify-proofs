(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_time P_x509_get_dates.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo A_x509_get_time.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_time_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_dates_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001dcfe2968ed602 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P003745ed24db2774 0 4 0 1 63 1 71 1 72 1P00558643134917e2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0160fb03fe2c14f6 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P01e4d318a17222ab 0 4 0 1 63 1 71 1 72 1P0264d1ea9a918de1 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P02da91dbbffd0a2a 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P02fb581175d6e87c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P036cadb091753fd3 0 4 0 1 63 1 71 1 72 1P0471dcc267469cc1 0 4 0 1 58 1 71 1 72 1P062ad1c3b4881786 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P068bff56bdeef39c 0 4 0 1 58 1 71 1 72 1P070800cf23996707 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P070c82f8fed6551a 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P084f0f02ab66b221 0 6 0 1 59 1 60 1 63 1 71 1 72 1P09e5d8585ed0d0a3 1 2 64 2 0 1 82 1 64 2 36 1 83 1 2 84 1 85 1P0a2e29fc583d9c0a 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0b58414aa45f0afa 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0bc1069a65789060 0 4 0 1 63 1 71 1 72 1P0bd7ab8c2ba7dc91 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0c0e0462927237ac 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0c8e6b3b99b5c5e2 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0ce3dce4c4a9af89 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0d372fee16e78a39 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P0d9656d43486f1d5 0 5 0 1 37 1 58 1 71 1 72 1P0edac2ca9084da64 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0f57a72c7fa31fc8 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0fa5b018ce9fb503 0 4 0 1 63 1 71 1 72 1P1041e650aa46e432 0 4 0 1 63 1 71 1 72 1P10b7b0f3aeff96da 0 4 0 1 63 1 71 1 72 1P136682331b3fc818 0 6 0 1 59 1 60 1 63 1 71 1 72 1P13a770968e3f90c7 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P13cd9157ed67df7b 0 3 0 1 43 1 49 1P13f6d8ec3376b795 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P149c23347c66632c 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P15165802298570d8 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P153ecd671d20ccf4 0 6 0 1 59 1 60 1 63 1 71 1 72 1P15423a32b238682c 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P171ad4921b9a6099 0 4 0 1 63 1 71 1 72 1P17cc8646ae62f97f 0 4 0 1 58 1 71 1 72 1P1976b6935974ff1d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P1984218d44160253 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P199670f40baeea84 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P1997f6191b6e0bbe 0 4 0 64 11 64 82 64 83 64P19c626bce1d71fba 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1b00ece6d7bc6876 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1ba093d3468a1d73 0 5 0 1 37 1 58 1 71 1 72 1P1c5122cf7b3ff7b3 0 4 0 1 63 1 71 1 72 1P1cbe65153e17cd7b 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1d7568a2cf24216f 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P1db9231b351c6393 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1e2c98585f71f098 0 5 0 1 37 1 58 1 71 1 72 1P1e48058a6206a085 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1e651397a9640628 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1eb9f43ee0e9c37d 0 4 0 1 63 1 71 1 72 1P1f29a68c11c73189 0 5 0 1 37 1 58 1 71 1 72 1P1f65046325697b86 0 5 0 1 37 1 58 1 71 1 72 1P1fbe7c347ab43559 0 5 0 1 37 1 58 1 71 1 72 1P20e49b574a2a3627 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P223e5edcaabf496f 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P225009dc108f40e8 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P22741e7be5c669b7 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P22c9f89317139b4e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P24f29bc8a29829c1 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2537c4a3f4eaf494 0 6 0 1 59 1 60 1 63 1 71 1 72 1P259d5e18a2cb5a35 0 5 0 1 37 1 58 1 71 1 72 1P25dc19fb83861abe 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P26d4519eb04524ba 0 6 0 1 59 1 60 1 63 1 71 1 72 1P26e17e5c17825a60 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P27e5efd31b54e201 0 6 0 1 59 1 60 1 63 1 71 1 72 1P28414b57fa7f0a6d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P28494bdaee4253c4 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P285395ab769934a2 0 5 0 1 37 1 58 1 71 1 72 1P28979476c93073e5 0 5 0 1 37 1 58 1 71 1 72 1P290c530089059cb4 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2ab5df304f664039 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2ad62358ecc654e9 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2ae7ad201688feea 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2b6b3b5765dba47e 0 4 0 1 58 1 71 1 72 1P2c5a193ed7ed283a 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P2d798adec51901bf 0 5 0 1 37 1 58 1 71 1 72 1P2db61d80ba97c95e 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2e16309cc5fff19b 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2e61c69478d39ba8 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2f44d704d55e7277 0 4 0 1 58 1 71 1 72 1P2f44d8f7477814df 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2f963a3c35b80d2d 0 5 0 1 37 1 58 1 71 1 72 1P2fd0cd2feb8fd497 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P30dd8d0121ef320b 0 6 0 1 59 1 60 1 63 1 71 1 72 1P30e3d347f0b15e8b 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3103e192750374a7 0 4 0 1 58 1 71 1 72 1P310bdb02e0a60153 0 4 0 1 58 1 71 1 72 1P31702acf76ed8141 0 6 0 1 59 1 60 1 63 1 71 1 72 1P32dd04737f0d1940 0 6 0 1 59 1 60 1 63 1 71 1 72 1P33c53e550bb5ed96 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P345ad8e3c1b56276 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P348bdf55ba0eaf4b 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P34a27615151438b8 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P357bd5981b59200f 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3682b95243680149 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P36d4a81f74cf94c3 0 4 0 1 63 1 71 1 72 1P36e3a559df469bd1 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3769a759fe24254f 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P37ac1de06db64cee 0 4 0 1 58 1 71 1 72 1P382a5ed9852e8371 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P38cf85426b6ed826 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P38deff31a16701a3 0 4 0 1 58 1 71 1 72 1P3a04d9a10d31722e 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3a50f07090c89e6c 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3a9e6c4b34298f13 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3abe1bcb27c0e462 0 3 0 1 44 1 52 1P3b08204b8060f64d 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3bd483d12c7bc106 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3cf59ad338749fbc 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3cfaf6a3970dc00d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3d18cabb376bcef3 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3d19526339bff427 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3dedcdf58524efd2 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3ec4e0f9d898bbb2 0 5 0 1 37 1 58 1 71 1 72 1P3ecf7759a27ca507 0 4 0 1 58 1 71 1 72 1P3ef6eb7a395d80cf 0 4 0 1 58 1 71 1 72 1P3f2534682f27a109 0 4 0 1 58 1 71 1 72 1P3f29d3b6483b5301 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P3f435ce0990077b5 1 1 64 2 36 1 83 1 3 0 1 82 1 84 64P3fadf22645053cd5 0 4 0 1 63 1 71 1 72 1P3fe1088fab5bacb9 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3fe400d1de6b2110 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16N00057a19dd80aba7N00330579923ca216N01b701a81c96428cN01f89c8fff1978edN022fbfe3619c4a87N02fc7b82d44c3887N032b65d6bccf415aN07184979fdde4cd2N0811af94b9a96d3eN081357f9d7dc5768N083479973dd2c974N08c2c6ad5dd54ce8N0a3cde26f2ec7d40N0c65e7fc0d7eb98aN0d912f2c1907be86N0e5dd422a5170861N10f8207c4e6d6fc4N14eb6e86a5fbd968N15adc2ce9868f954N178d0b3677215e3fN191dee07f64d3f01N1b7eafdde2312878N1db88cd219981379N1eb1dfbdf51ba1dfN1f83cd5bb37114e0N20c4a32b3e30366cN240cb3ce270e7c19N248c345203b5935aN27ff258f08692888N29c1b853af756781N29c39bdc06809d51N2b8a2fcacdf113b4N2f94ae37d7ff992aN3014d90cac335646N302040b2208b3963N30297bc686c4c21fN312a866b828fe2ebN315ce88c6848807dN31edd59f63dd6ab8N323803e697df2d13N32d46528b159c06bN3354045b0514b18bN349a6bc94d3dc778N35ceefb51fca006bN36a09b58b4cc61f4N3773aae5d04d9a89N3a2d43ea9aec7f4eN3acae0707d83905eN3af973ef3cb0b46bN3bae17921fac73aeN3bc32573d5ddb3ecN3df4cd1a3eb2ce69N3f9008819d559d9d"%lxh.
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
Ltac2 gd_tbl_A_x509_get_dates () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_dates_A.x509_get_dates_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_dates_A.A_X509_GET_DATES"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_dates_A.x509_get_dates_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis GTIME : A_x509_get_time_A.x509_get_time_stmtA asegs R HIA A_x509_get_time_A.A_X509_GET_TIME.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP TM P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= TM \/ TM + 48 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ TM + 48 <= BUF \/ BUF + Z.of_nat (length bs) <= TM.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : TM mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis TMB : 0 < TM /\ TM + 48 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_GET_DATES_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 288 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : TM + 48 <= lo \/ bv_unsigned sp <= TM.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo TM 48.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) TM 48.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_GET_DATES_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_get_dates_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP TM P END lo slo).
  Local Notation W := [(PP, PP + 8); (TM, TM + 48)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis LFB : (length LF < 511)%nat.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01l0@D10639329459.122D10651912114.171D11651368143.123D11655565030.172D12516027549.172D14207366270.171D18607476203.161D2455714710.196 D27392810573.196D32457002573.196D3254889317.160 D32606360468.173D3373657269.196 D33956323578.162D33956323578.163D33956323578.164D41440366531.196D43132410038.162D43132410038.163D43132410038.164D46793042006.122D46805624663.171D50254960491.162D51880109472.172D51884306313.123D53232575014.162D53232575014.163D53232575014.164D560907438.124  D58077997354.162D60098666067.171D60098777666.123D60111245650.122D60111362155.172D62009673039.173D62011770188.124D68405212918.196D6909863155.196 L13062538913.0  L15756354262.7  L17921795213.188L19013159470.0  L19980016842.7  L29738741675.1  L35228767239.1  L3551623394.2   L35680140202.3  L36180999398.116L38436634709.0  L3876079316.5   L39332637397.0  L39618635427.2  L40228640085.0  L43055370171.114L48117620907.102L48132302231.145L50790731766.8  L52249874585.0  L52255793882.186L56854270298.119L58071656716.187L58790154276.6  L59257759329.3  L60558678699.1  L61437265048.2  L6203936179.1   L63738252715.1  L64009471222.1  L7040749983.120 L9356559645.13  L9873114841.7   P1056307012.160 P1056307012.162 P36462068749.161P36465839390.160P62747542064.160P62747542064.162Q10523111608.128Q10651763882.130Q10651763890.126Q11653467873.131Q11653467876.127Q12660624644.132Q1530342990.162 Q21829627469.196Q23927511185.128Q23927511197.133Q27944911788.196Q31021924279.160Q31805155683.196Q32436491433.196Q32681887700.128Q33196749121.132Q33963892682.196Q35653441506.108Q38248895676.134Q40228749922.196Q40271359350.162Q42437284299.176Q42439168719.160Q42439382240.135Q43880146016.134Q46805771343.130Q46805771351.126Q47230721789.128Q48119867062.196Q49077563264.196Q50796826103.162Q51882206626.127Q51882206631.131Q59865520191.135Q59871812884.176Q60109315147.108Q60740903729.126Q6192914196.160 Q62011770181.133Q62011770185.128Q63018782704.127Q64683599817.135Q64685695714.176Q67026483294.161Q67038703949.160Q6909863155.196 Q9356560156.143 00000D00c01701V01W01X01Y01Z02902X02Y03A03B03i04P04Q05005105205305G05f05g06F06Z06[06\06]07907Y08A08^09;09c0:D0:Z0:[0;:0;;0;I0;J0;K0;c0;g0;k0<20<<0<P0<Q0<d0<e0<o0=00=K0=j0>I0>Z0>[0?:0@20@U0@k0A70A;0AC0AH0AL0AP0B40Bc0C?0D60Dm0EU0EV0FM0GD0GT0Gb0H00H>0HL0H[0I10I?0I^0J10JN0Jm0K\0K]0K^0Km0La0MC0MQ0MR0Me0N;0NQ0Ng0O80OF0OT0Oe0PD0P]0Q80QF0QT0QU0QV0Qj0R;0RJ0RW0Rd0S50SX0T;0T^0UA0UO0UfS2LF2sp2PP2TM2bs3LFBS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3LFBS2LF2sp2PP2TM2bs3LFB3sp13H222FBFFFFS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3LFB3sp13H222FBFS1R3HIA2LF2sp2PP2TM2bs3LFB3sp13H222h12FBFS2LF2sp2PP2TM3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP2TM3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP2TM2bs3LFB3sp13H222FBFFFS2LF2sp2PP2TM2bs3LFBS2LF2sp2PP2TM2bs3LFB3sp13H222FBFS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3LFBFFFS1R3HIA1h2LF2sp2PP2TM2bs3LFBS2LF2sp2PP2TM2bs3LFB3sp13H203H22S1R2LF2sp2PP2TM2lo2bs3LOS3LFB3sp13H222FBS1R2LF2sp2PP2TM2lo2bs3LOS3LFBS1R2LF2sp2PP2TM2lo2bs3LOS3LFBS1R2LF2sp2PP2TM2lo2bs3LOS3LFB3sp13H222FBS1R2LF2sp2PP2TM2bs3LFB3sp13H222FBS1R2LF2sp2PP2TM2bs3LFBFS2LF2sp2PP2TM2bs3LFB3sp13H222FBSS1R2lo3LOS3ALOFSS1R3HIA1h2sp3TOP3sp13SP1S2FBS2spS2bs2EQS2FB2x22HxS2LF2sp2PP2TM2bs3LFBSS2sp2lo3SLO3sp13SP1SS3sp14SP1MSS2LF2sp2PP2TM2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSSS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3PPB3TMB3SPA3LFB3SPR3sp13H183H193H203H22S2LF2sp2PP2TM2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S2sp3sp13SP1S2FBS2LF3LFBS3sp1S2FBS2bsS2LF2sp2PP2TM2bs3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2TM1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2TM1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF2TM2bs3LFBS2LF2TM2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB4Hfr1FFS2LF3BUF2bs3LFBS2LF2sp2PP2TM2bs3PPB3TMB3LFB3SPR3sp13H222FB3F644Hfr0S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LF2bs3LFB3ALO2FB4Hfr1S1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2TM2bs3LFBS2LF2TM2bs3LFBFFS1R2LF2lo2bs3LOS3LFBS2LF2PP2TM2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS2LF2PP2TM2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_dates ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ptb0,(1.(0.&8.))P,(2.$3.VR,VHIA,Vh,VLB,VLF,Vm,)P,(4.$3.Vm,VPP,(5.$6.(7.(8.&40.VP,))(9.$6.)))P,(4.$3.Vm,VTM,(5.$6.(:.#30.R3.)(9.$6.)))P,(;.$3.Vm,VBUF,Vbs,)P,(<.$3.Vm,Vlo,(=.&40.Vsp,))P,(>.$3.(?.VR,)Vm,Vslo,(=.&40.Vsp,))P,(10.$3.Vm,)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VPP,+8.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VTM,+30.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VBUF,(13.(14.(0.&8.)Vbs,)))(15.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)(16.$3.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VTM,VP,VEND,Vlo,Vslo,Vm,)(17.(18.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(8.&40.VPP,)(8.&40.VEND,)(8.&40.VTM,)(8.&40.(19.VTM,+18.))R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(8.&40.$1:.)Vfc,(1;.(0.&40.))Vm,(1<.$3.)))")
(* [comment removed for export] *).
  Proof.
  intros until tb0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_GET_DATES.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
  carve_frame 96%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 166%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64);
                  [ exact HHc | (clear - LFB; lia) | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
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
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaa2f0] [] 166%N). lx_tree.
  lxr_leaf. lx_carry.
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
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 1%nat FRa SPILL end.
      replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -88); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -88) sp1 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo TM 48 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_get_dates_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_dates ()) "PR,$1=.PHIA,(1>.$3.R1.)P,(1?.(?.R2.))P,(20.$21.(22.R3.)$23.)P,(20.$21.(24.R4.=)$25.)(26.$3.R5.R4.$1:.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  pose proof (A_x509_get_time.A_x509_get_time_spec R HIA IMG UARG SM0) as GTIME.
  unfold x509_get_dates_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
