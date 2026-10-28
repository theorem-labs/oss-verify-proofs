(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_x509_crt_ext_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000831140573b83b 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P00327d10a2760274 0 6 0 1 55 1 66 1 67 1 74 1 75 1P00589837cde71a27 0 6 0 1 55 1 66 1 67 1 74 1 75 1P008fb963e086da63 0 5 0 1 35 1 54 1 74 1 75 1P009fec5f08ae5469 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P00ba860918fa9310 0 6 0 1 55 1 66 1 67 1 74 1 75 1P00e582edd81ee20b 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P01a101329988abeb 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P01e2beb41e90a5de 0 5 0 1 35 1 54 1 74 1 75 1P02003664cfdc9ac7 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P0238c3f9259b2b1b 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P02c34bbf93a9f71d 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P030390c7eeab715f 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P03b4da2b9d098dfa 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P0410292d19d0dc55 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P04c7bd89e6f7ecbb 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P04d9e34a8f4e1840 0 6 0 1 55 1 66 1 67 1 74 1 75 1P059a714d1b7f4d38 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P0776764c9657ea4c 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P0777f621d0a508e9 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P07b511002904097d 0 7 0 1 40 1 79 1 90 1 91 1 98 1 99 1P07f8c7192285e623 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P07fd8cfbb241d1b4 0 4 0 1 54 1 74 1 75 1P08a334c1c92d6d8f 0 6 0 1 55 1 66 1 67 1 74 1 75 1P092c650e29985db0 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P09720371fde7ce7d 0 5 0 1 35 1 54 1 74 1 75 1P09e26f4387051868 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P0a301a8516e97742 0 4 0 1 54 1 74 1 75 1P0a4d90486df5bd15 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P0a9d8623dd3fd2fc 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P0ab70abb715a7977 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P0adc31c8f9760f3e 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P0be4b905457c4d51 1 1 8 3 0 1 98 1 101 1 8 40 1 79 1 88 1 90 1 91 1 99 1 100 1 102 8P0cc81ec4750620fa 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P0cc8e7464e00fae0 1 2 8 2 0 1 98 1 8 2 89 1 99 1 2 100 1 101 1P0ccd7a7b807bc7d4 0 3 0 1 41 1 58 1P0d3df1a672bbc013 1 1 16 2 0 1 74 1 3 11 1 75 1 76 16P0da25400d73e6782 0 6 0 1 55 1 66 1 67 1 74 1 75 1P0de47759de6eda1c 0 5 0 1 35 1 54 1 74 1 75 1P0e04e591ef2b9e4c 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P0ecdb77b830ccfee 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P0ef568603baa5fa6 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P0f75431a6d0adefd 1 1 64 2 17 1 98 1 3 0 1 99 1 100 64P10fc9c4129bdb0dd 0 5 0 1 35 1 54 1 74 1 75 1P119621bfac2c5e65 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P1253c50580aeb564 0 4 0 1 54 1 74 1 75 1P1260121e4ce0fd5a 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P1298ce7127e6bf42 0 5 0 1 35 1 54 1 74 1 75 1P12e4a109b979adcc 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P132c8d7811cc1506 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P136f0c8b90f42bc5 0 6 0 1 55 1 66 1 67 1 74 1 75 1P137f4ce2dd422c80 1 2 32 3 0 1 99 1 102 1 32 10 41 1 47 1 68 1 80 1 81 1 82 1 91 1 92 1 100 1 101 1 2 103 2 104 2P13bdfe5c1977c02c 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P13c872bb60e02ebd 0 4 0 1 54 1 74 1 75 1P13d201831ba13b30 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P14091ffa057357ca 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P143228ef32988056 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P147d6faf07a6cdf4 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P14a4fd2ea9a22e8e 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P14c3a3778894de7f 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P15bcf23a6714e3e2 0 3 0 1 40 1 55 1P163ab0dac1d7dc10 0 6 0 1 55 1 66 1 67 1 74 1 75 1P169ed1b44417de91 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P16d383726db0ea3c 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P1736e04423a20f8f 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P1864cd1001f83560 0 4 0 1 54 1 74 1 75 1P1865ffcf050e757e 0 6 0 1 55 1 66 1 67 1 74 1 75 1P18cf53597a1177c3 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P18d07a7d8e8b7aa5 0 5 0 1 35 1 54 1 74 1 75 1P192aa1571090fbba 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P195ff8404ef151ec 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P19a89f0e332c6dc6 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P19b837c218ff0c28 0 6 0 1 55 1 66 1 67 1 74 1 75 1P1a053e31be1b8401 0 4 0 1 54 1 74 1 75 1P1a491cc9ec9dec5d 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P1ad3a6f61d63b8ee 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P1b146a075443f13f 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P1b216c7f3339e431 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P1b7c006628491369 1 2 32 3 0 1 98 1 101 1 32 10 40 1 46 1 67 1 79 1 80 1 81 1 90 1 91 1 99 1 100 1 2 102 2 103 2P1bafabfef4bdee31 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P1bd6c7b1ffc74bfb 0 5 0 1 35 1 54 1 74 1 75 1P1c79efc6281cd591 1 1 16 3 0 1 100 1 101 1 7 46 4 80 4 91 4 92 4 99 4 102 4 103 64P1c8498f767c4d3df 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P1c943ad2aa6c0ab7 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P1ccacf5e2f30aa92 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P1d7f40de19442924 0 5 0 1 35 1 54 1 74 1 75 1P1d7fd950adbfbdbe 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P1db879ee3bacee75 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P1dd4b31cb8248927 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P1e446382b219f754 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P1e59a11eed95b8ac 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P1fa96838cf6879b5 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P203469d98a6e89af 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P20d2b8ec7190225d 1 2 32 3 0 1 98 1 101 1 32 10 40 1 46 1 67 1 79 1 80 1 81 1 90 1 91 1 99 1 100 1 2 102 2 103 2P20feb2b7c44a8967 0 4 0 1 54 1 74 1 75 1P21d14cc8a0245fee 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P21e2b09f00d87b1c 1 2 32 3 1 1 99 1 102 1 32 10 41 1 47 1 68 1 80 1 81 1 82 1 91 1 92 1 100 1 101 1 2 103 2 104 2P223f2bedc6625770 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P225df631e1555db0 0 8 0 1 40 1 79 1 82 1 90 1 91 1 98 1 99 1P22807754c43359d6 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P22838492bf739b3a 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P22bcdd535b8ce291 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P22e3c8a6a7bae7e5 0 6 0 1 57 1 60 1 78 1 98 1 99 1P2327223d26da566b 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P23293969b9ad8631 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P23ad5d26ed49e2c4 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P23b7ede56f111a9f 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P23f16c55b7db5039 0 5 0 1 35 1 54 1 74 1 75 1P2452e3c98ef337ea 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P24d1f6b22334594f 0 4 0 1 54 1 74 1 75 1P25883631a47b0a4b 0 4 0 1 54 1 74 1 75 1P2592dbd7cea075ac 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P25977d3067e152ea 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P25bb29e667cddfd6 0 5 0 1 35 1 54 1 74 1 75 1P25e166c0abe26523 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P25e5411f4d809191 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P25e80b2d7ffe7e0b 0 4 0 1 54 1 74 1 75 1P26338055cf3b12c7 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P2685456e88f4050b 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P268d063df27c3916 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P26d7e02a5b98ee7e 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P26e443cd134c6986 1 1 16 3 0 1 99 1 100 1 4 60 1 98 1 101 1 102 16P276c8f59fb2b57b2 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P27854c2fc229b1e9 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P2799f883ea6b7a3f 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P27d54848a10aa399 1 2 32 3 0 1 98 1 101 1 32 10 40 1 46 1 67 1 79 1 80 1 81 1 90 1 91 1 99 1 100 1 2 102 2 103 2P289b55df34fb1720 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P28e3ab07ce2484a9 0 4 0 8 4 8 98 8 99 8P2977bdae479789a0 0 5 0 1 35 1 54 1 74 1 75 1P2a09a9fd1a4d4c17 0 6 0 1 55 1 66 1 67 1 74 1 75 1P2a725fdfd52ce390 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P2abf0ff8f36cf5ab 1 1 16 3 0 1 100 1 101 1 7 46 4 80 4 91 4 92 4 99 4 102 4 103 64P2b26c6838a9c4e37 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P2b294831ce308dc2 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P2b77680cc16768d5 0 9 0 1 40 1 79 1 80 1 81 1 90 1 91 1 98 1 99 1P2b8d6663bf72f7e4 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P2bdd2391d2ccacc4 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P2be22cd28abe370e 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P2c680b4fdaa6b3ff 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P2c79fbcf9636aa5a 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P2d7720618651c4d8 0 6 0 1 55 1 66 1 67 1 74 1 75 1P2dc0f7c7b81be568 1 1 16 3 0 1 100 1 101 1 7 46 4 80 4 91 4 92 4 99 4 102 4 103 64P2dc8815934c913c8 0 4 0 1 54 1 74 1 75 1P2dd2a2ea86a3f527 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P2ddd364ec1de131f 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P2ddde24778d42176 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P2dec1131f1221aa5 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P2df173070eab42dc 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P2e0aeaf16aaf6b52 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P2e773c90d7305932 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P2ec2c1184e9bec50 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P2f3e1236430f19ef 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P2f6eb80249ccfd20 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P2fa7c0a79d42b707 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P2fe3105b28b75acb 0 7 0 1 40 1 79 1 90 1 91 1 98 1 99 1P3004ab27dbdefc7b 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P30319c99757d8768 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P30655a8b1f600853 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P3076d25baf74bfa6 0 6 0 1 55 1 66 1 67 1 74 1 75 1P30a190987e9c2452 1 2 32 3 1 1 99 1 102 1 32 10 41 1 47 1 68 1 80 1 81 1 82 1 91 1 92 1 100 1 101 1 2 103 2 104 2P30c3b9d09878874f 0 5 0 1 35 1 54 1 74 1 75 1P30d8692eeeabc3ee 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P317a7e50b92c95e8 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P319133bac9d3d74a 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P31fc2b50e001ac99 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P321ae2e0b09a46db 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P32927545cbb4c184 1 2 32 3 0 1 99 1 102 1 32 10 41 1 47 1 68 1 80 1 81 1 82 1 91 1 92 1 100 1 101 1 2 103 2 104 2P3293df77b9af0a57 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P32def30643968a2b 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P335264b5cf520e4a 0 6 0 1 55 1 66 1 67 1 74 1 75 1P336e1e0c0beee8c8 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P33b3cb6581fd65bc 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P33ff8bb553522943 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P3407cecc36f61fd0 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P341b5775bbac44a4 0 11 2 1 42 1 69 1 78 1 81 1 82 1 83 1 92 1 93 1 100 1 101 1P347824f76cca5378 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P34b0336f96090c08 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P35237f355279f6a7 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P3529b61d073d1f95 0 4 0 1 54 1 74 1 75 1P353fde437a120044 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P356ff353d0f49bfe 0 8 1 1 41 1 80 1 83 1 91 1 92 1 99 1 100 1P3573b9462c44e534 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P3592a363cb80dbf9 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P35dbfadc284db6a2 1 1 16 3 1 1 45 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P35fae51367ad4768 1 1 8 3 1 1 76 1 77 1 7 56 1 65 1 67 1 68 1 75 1 78 1 79 8P3621078e57d228fb 0 7 1 1 56 1 59 1 67 1 68 1 75 1 76 1P36736fb04d5eb8a9 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P3722857d9e000961 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P37569113c89043d4 1 1 8 3 0 1 75 1 76 1 7 55 1 64 1 66 1 67 1 74 1 77 1 78 8P375f7ebf6f625357 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P37f0530a7d79daba 0 6 0 1 79 1 90 1 91 1 98 1 99 1P380a77efb2813c85 1 1 16 4 1 1 38 1 47 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P38273318040eaec9 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P3910baec5f34c183 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P399b4e83349e5ed9 1 2 32 3 0 1 99 1 102 1 32 10 41 1 47 1 68 1 80 1 81 1 82 1 91 1 92 1 100 1 101 1 2 103 2 104 2P3a074a49b18753ca 0 7 0 1 55 1 58 1 66 1 67 1 74 1 75 1P3a10b81b926d1739 0 14 0 1 40 1 67 1 76 1 79 1 80 1 81 1 85 1 86 1 87 1 90 1 91 1 98 1 99 1P3a185b4e4ba4190d 1 1 8 3 1 1 99 1 102 1 8 41 1 80 1 89 1 91 1 92 1 100 1 101 1 103 8P3a2d451f03176662 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P3a588670687ccfdf 0 7 2 1 43 1 57 1 68 1 69 1 76 1 77 1P3b92efdee1dc7aee 1 1 16 3 0 1 99 1 100 1 7 45 4 79 4 90 4 91 4 98 4 101 4 102 64P3bc1f9f95d5ae84a 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P3bdfbc1c98c491b9 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P3c4db39f33badb54 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P3c4df204f2a1e762 1 1 64 2 0 1 98 1 3 16 1 99 1 100 64P3c7e372017a8de86 1 2 16 2 0 1 76 1 16 2 1 1 75 1 2 77 1 78 1P3cdb042fd719c2c7 0 8 0 1 55 1 56 1 57 1 66 1 67 1 74 1 75 1P3da1b71c240991a5 0 6 0 1 38 1 60 1 78 1 98 1 99 1P3e8990be2eb6b0fb 0 10 0 1 41 1 55 1 61 1 62 1 63 1 66 1 67 1 74 1 75 1P3e9223a4bfb52e4a 0 4 0 1 54 1 74 1 75 1P3eb749e7fd911db5 1 2 16 3 1 1 45 1 75 1 16 3 0 1 46 1 76 1 2 77 1 78 1P3ec1f829ebb63b65 1 1 16 2 1 1 75 1 9 41 1 44 1 56 1 57 1 58 1 67 1 68 1 76 1 77 16P3f453126155d73bd 0 5 0 1 35 1 54 1 74 1 75 1P3fa563dcb153983a 1 1 16 3 0 1 100 1 101 1 4 61 1 99 1 102 1 103 16P3fb8c3153abfd67f 0 4 0 1 54 1 74 1 75 1P3fc62ab16282e31d 0 4 0 16 53 16 74 16 75 16N0049cebd511f2fcdN0187d30ec1597d96N01b96a58fcd7e2b5N02a74302bc8f7616N03a3545736df8106N048b9a7e5e936265N06d5253dcf28444fN0756ef2d416c5d14N08297e11d709a090N08ae3792cf802108N0a89d0e0d92f54dbN0c10d2585d14498bN0c22231e3c043dabN0d0f75fb0c14175fN0d5d0d8b45db9b3dN0df3772172e8093fN0e335e01f3a55e3fN0f1ac6806f715e7bN0fec87d73312e54fN102075b01e7e6a12N139c47d065a59a2dN14113e3eb6f3dcbdN147dae30492d9040N14bb168dc766bfa0N14e1c627564e4351N17570fc39ce69892N17f9631ee83a2c12N18fd26d3391cd769N193d257814d3b247N19db46d2680cf960N1aff787a72091c7cN1b8a814c08feae2fN1d4df40e3763cf5dN1d66865f36d343baN1d8f2df78d0bc3e9N1d9274ad86fd9ac9N1d9d3f5e0812a386N1db2b6593318808eN1ec5555968d1b597N1ef2ed6f4e12bf2aN1f81a175979843bdN227564c7ddcd1166N23426ae12b57831bN243299723d4acd55N24ca085059b35cc4N250865bb99b25850N25bed397a19e4f3dN26146f5ba0df32f1N2695fd1dae91d9b0N26ae93d50f225999N274ae791423521a7N2865914da71cffe1N2895751ffb33fe76N28ab72117b47808cN29b5c9ce23da9101N29f1c5ef5657bb4bN2aee07a7ec1d6c24N2b297222cc527530N2b99d45311ffda16N2bf8997c7a64a09fN2d7ed8bada6a4522N2dad96398af8e24aN2dcb8e0771c1fbd6N2de517c8b4797236N2e070fc99d1f9a20N2ee459a4a5d9f0deN2f5cc7ea104c7cdbN308f207f89883075N309c4d2d5aa52487N3182db5b582bed6bN31a21054d66a4a83N32e9d33f2234eecbN353d9d71468bcec6N3567fa89afecd6c9N35c46bf31fa85f2cN36031d2cde32313cN37a4a3c3297ae60dN37e2990c34cef499N386c5cd854490119N38c4599177277b65N38fe90ec151eeda7N3946b09472218c6cN39921e7881956874N3b80359cf4b5f335N3ba140cd6e2e13faN3ca7ab54b69ef1d8N3ce8556130811505N3eeee6d5b8f3c8feN3fe390cff11b2795N3feea8ba2cc8d5a6"%lxh.
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
Ltac2 gd_tbl_A_x509_crt_ext_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.zeros"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_X509_CRT_EXT"].


Definition A_X509_CRT_EXT : Z := 0xaa638.       (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = 0x531fc.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  (* [comment removed for export] *)
  Definition STKx : Z := 336 + 48 + STKc + arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CRT P END BUF lo slo : Z) (bs : list byte).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) (CRT + 424) EXT_SIZE.
  Hypothesis CRTLO : CRT + 424 + EXT_SIZE <= lo.
  Hypothesis DXB : CRT + 424 + EXT_SIZE <= BUF \/ BUF + n <= CRT + 424.
  Hypothesis D1 : PP + 8 <= CRT + 424 \/ CRT + 424 + EXT_SIZE <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold STKx, EXT_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CRT + 424, CRT + 424 + 272)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHX := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
                          C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.

  (* [comment removed for export] *)
  Definition S1P (a3e a4e : word) : machine_state -> Prop := (fun (ms : machine_state) => (exists FB, (exists sp1, (exists h1, (exists m1, (exists x5, (exists x6, (exists x7, (exists x10, (exists x11, (exists x12, (exists x13, (exists x14, (exists x15, (exists x16, (exists x17, (exists x28, (exists x29, (exists x30, (exists x31, (exists w0, (exists w1, (exists w2, (exists jloc, (exists ja, (exists k16, (exists k24, (exists k32, (exists k40, (exists k48, (exists k56, (exists k64, (exists k72, (exists k80, (exists k88, (exists k96, (exists k104, (exists k112, (exists k120, (exists k128, (exists k136, (exists k144, (exists k152, (exists k160, (exists k168, ((ms = (MS (mkR (Z_to_bv 64%N 0xaa6b8) (Z_to_bv 64%N sp1) gp tp x5 x6 x7 sp (Z_to_bv 64%N sp1) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64%N FB) (Z_to_bv 64%N PP) (Z_to_bv 64%N END) (Z_to_bv 64%N FB) (Z_to_bv 64%N CRT) (Z_to_bv 64%N (al_sb (arl_AL R))) (Z_to_bv 64%N ((Z.shiftr PP 3) + (al_sb (arl_AL R)))) a4e a3e (Z_to_bv 64%N ((Z.shiftr FB 3) + (al_sb (arl_AL R)))) x28 x29 x30 x31) F (Z_to_bv 64%N 0xaa798) fc (@None (bv 64%N)) m1 (seg_rom asegs))) /\
   (((((bv_unsigned sp) - 304) <= sp1) /\
   (sp1 <= ((bv_unsigned sp) - 288))) /\
   (((sp1 mod 32) = 0) /\
   ((HM asegs R HIA h1 LB ((@pair Z Z FB 256) :: LF) m1) /\
   (((hcs asegs R HIA h1) = (hcs asegs R HIA h)) /\
   (((htop asegs R HIA h1) = (htop asegs R HIA h)) /\
   (((hstkhi asegs R HIA h1) = (hstkhi asegs R HIA h)) /\
   (((hflag asegs R HIA h1) = (hflag asegs R HIA h)) /\
   (((havol asegs R HIA h1) = (havol asegs R HIA h)) /\
   (((hfr asegs R HIA h1) = (hfr asegs R HIA h)) /\
   ((forall (mo : Model),
 (iff (HK asegs R HIA h1 mo) (HK asegs R HIA h mo))) /\
   (((FB mod 64) = 0) /\
   ((fresh_apart R LB LF FB 256) /\
   ((rw_cells asegs m1 FB [(C8 w0); (C8 w1); (C8 w2)]) /\
   ((rw_cells asegs m1 (FB + 32) [(CB 216%nat jloc)]) /\
   ((rw_cells asegs m1 ((Z.shiftr FB 3) + (al_sb (arl_AL R))) [(C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 241)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 242)); (C1 (Z_to_bv 8%N 248)); (C1 (Z_to_bv 8%N 243)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0)); (C1 (Z_to_bv 8%N 0))]) /\
   ((rw_cells asegs m1 ((bv_unsigned sp) + (-104)) [(C8 s11); (C8 s10); (C8 s9); (C8 s8); (C8 s7); (C8 s6); (C8 s5); (C8 s4); (C8 s3); (C8 s2); (C8 s1); (C8 s0); (C8 ra)]) /\
   ((rw_cells asegs m1 sp1 [(C8 k16); (C8 k24); (C8 k32); (C8 k40); (C8 k48); (C8 k56); (C8 k64); (C8 k72); (C8 k80); (C8 k88); (C8 k96); (C8 k104); (C8 k112); (C8 k120); (C8 k128); (C8 k136); (C8 k144); (C8 k152); (C8 k160); (C8 k168); (CB 16%nat ja); (C8 (Z_to_bv 64%N FB))]) /\
   ((stk asegs m1 (sp1 + 184) ((bv_unsigned sp) + (-104))) /\
   ((stk asegs m1 lo sp1) /\
   ((mem_inv asegs m1) /\
   ((rw_cells asegs m1 PP [(C8 (Z_to_bv 64%N P))]) /\
   ((rw_cells asegs m1 (CRT + 424) [(CB 272%nat (zeros 272%nat))]) /\
   ((bytes_at asegs m1 BUF bs) /\
   ((aobj asegs (arl_AL R) (hcs asegs R HIA h) m1 PP 8) /\
   ((aobj asegs (arl_AL R) (hcs asegs R HIA h) m1 (CRT + 424) 272) /\
   ((aobj asegs (arl_AL R) (hcs asegs R HIA h) m1 BUF (Z.of_nat (@length (bv 8%N) bs))) /\
   ((((FB + 256) <= PP) \/ ((PP + 8) <= FB)) /\
   ((((FB + 256) <= (CRT + 424)) \/ (((CRT + 424) + 272) <= FB)) /\
   ((presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [(@pair Z Z PP (PP + 8)); (@pair Z Z (CRT + 424) ((CRT + 424) + 272))] m m1) /\
   ((sshad asegs (arl_AL R) m1 slo sp1) /\
   (sshad asegs (arl_AL R) m1 sp1 (bv_unsigned sp))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 ALC; try lx_pin1 B5.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02]0@D10639180168.191D10651765667.113D10823604468.158D12562369743.189D12658639931.112D12660902694.158D14194668100.191D15662658206.192D18607476203.159D18607476203.163D19295242034.192D19297339191.114D20553579080.160D20553579080.161D20553579080.162D23724182216.192D2455600524.190 D31526457809.112D31538959723.189D3160262663.191 D32456886359.190D3254889317.158 D32606360467.193D33194539134.112D33271305925.189D3386124079.189 D36104740330.191D39411162312.159D39411162312.163D45702483614.189D46793187693.191D46805773126.113D50254960491.160D50254960491.161D50254960491.162D51088045910.189D52056129450.163D54544308936.189D560907437.115  D56900755293.192D56902852440.114D60098680296.189D60098777666.113D60109265003.114D60111362153.191D60111362158.192D6192914196.163 D62009673032.193D62011770191.115D66239203113.190D67824652051.192D68409458028.189D6897397609.189 L18021517688.12 L19548981083.166L19980016842.12 L21664106842.113L22897884290.141L2333531081.151 L2333536794.153 L26163319614.151L26163329773.153L29738741675.1  L33472729358.123L33485826452.1  L33485826452.13 L35488231161.165L35653441506.11 L39332637397.0  L39618635427.2  L40228640085.0  L43044648533.0  L43055154860.106L43300649301.0  L48117620904.97 L48119718052.161L48119718055.160L48132302231.114L49993911730.9  L5067997822.166 L50790731766.11 L53077668502.1  L56380976587.10 L57355539152.167L57355539152.171L58790154276.12 L59308634497.16 L59578101107.196L60098763854.6  L60562890748.140L61437265048.2  L61738609335.163L6302880071.151 L6302890132.153 L64850595401.0  L65278984341.160L65279510758.108L66000499105.0  L66007138311.1  L6910010082.160 L7040749983.114 L7471620488.9   L7755433625.12  L9356559645.16  L9873114841.11  P1056307012.158 P1056307012.163 P19969955661.158P19969955661.163Q10523111609.119Q10594483344.197Q10651763882.121Q10651763890.117Q12660624651.123Q1530342990.163 Q16180847029.197Q19297339185.122Q19297339186.118Q23927511184.119Q23927511196.124Q26032252603.202Q31021924279.158Q32440833928.196Q32679790552.197Q32681887700.118Q32681887701.119Q33196749134.123Q33271078526.196Q34966725149.202Q38248895679.125Q40216052035.196Q40271359350.163Q42437284299.147Q42439168719.158Q42441479401.204Q42441479403.126Q43351262911.117Q43351262911.146Q43351262911.196Q43880146019.125Q46805771343.121Q46805771351.117Q47230721788.119Q47313632828.117Q47313632828.146Q47313632828.196Q48119718054.197Q48132302231.196Q50796826103.163Q5406483567.158 Q56533317818.197Q56902852445.118Q56902852446.122Q59867617332.126Q59867617334.204Q59871812884.147Q60740903729.117Q62011770180.124Q62011770184.119Q64681502658.126Q64685695714.147Q65266402725.196Q65266402749.200Q65278984341.198Q67038703949.158Q67517027822.117Q67517027822.146Q67517027822.196Q6897428426.200 Q6897428434.196 Q6910010082.198 Q8701272495.204 Q9350548487.144 00000Q00b01D01E01Z02<02=02>02?02@02e03:03;03<03=03>03?03@03A03B03c03d04N04c04d04e04f04g04h05I05j06;06<06=06>06?06a06b07;07`08508_09909S0:=0:g0;E0;h0<;0<\0<]0<^0=?0=@0=k0>C0?40@O0@P0@Q0@R0@S0@W0@X0@Y0@Z0AC0A[0A\0Af0Ag0Ah0C@0CA0Co0Db0EU0FC0Fg0GV0H60H;0HT0HU0IJ0Ij0J40JZ0Jd0K=0KE0L@0LA0LB0LC0LV0Lk0Ll0M00MC0Md0NH0NI0O=0Oj0PI0Ph0QI0Qj0R:0RM0R[0Ri0S80SS0Sf0T50TD0Tc0U60UP0V40V50V60VH0VI0VX0VY0WL0WZ0W[0X30XI0Xd0Y?0YU0YV0YW0YX0Yi0Z70ZE0ZV0ZW0ZX0ZY0[L0\?0\n0]B0]C0]R0]a0]b0]c0]d0^60^C0^P0_30_V0_i0`<0`O0aF0aG0aH0aI0a\0ao0bB0c20cNS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBS2LF2sp2PP3BUF2bs3LFB3sp13H224LFB'FS2LF2sp2PP3BUF2bs3LFBS2LF2sp2PP3BUF2bs3LFB3sp13H224LFB'FFFFS2LF2sp2PP3CRT2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP3CRT2bs3LFBFFFFFFFFS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBFS1R3HIA2LF2sp2PP2bs3LFB3sp13H224LFB'2h12FBS2LF2sp2PP3BUF2bs3LFBFFFFFS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBFFFFS2LF2sp2PP2bs3LFB3sp13H203H224LFB'FS1R3HIA1h2LF2sp2PP2bs3LFBS2LF2sp2PP3CRT2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP3CRT2bs3LFBS1R2LF2sp2PP2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2PP2lo2bs3LFB3LOSS1R2LF2sp2PP2lo2bs3LFB3LOSS1R2LF2sp2PP2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2PP2lo2bs3LFB3LOS3sp13H224LFB'2FBS2LF2sp2PP2bs3LFB3sp13H224LFB'S1R2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS1R2LF2sp2PP2bs3LFBS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBFFS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBSS2LF2sp2PP2bs3LFB3SPR3sp13H224LFB'2FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1S2LF2sp2PP2bs3LFB3PP03SPA3SPR3sp13H183H193H203H22S1R3NS14STKc5STKc02LF2sp2PP3CRT1P3END3BUF2lo2bs3LFB3PP02B12B22B33DPB3DXB2D13SLO3SPR3sp13H22FFFFS2FBFFFS1R2LF3slo2bs3LFB4SLOS3ALO3sp14LFB'2FB2F1S1R3HIA1h2sp2lo3TOP4HTOPSS3sp14SP1MSSS1R3NS14STKc5STKc02LF2sp2PP3CRT1P3END3BUF2lo2bs3LFB3PP02B12B22B33DPB4CRT03DXB2D13SLO3SPRSS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1S2LF2sp2PP2bs3LFB3PP03SPR3sp13H224LFB'2FB2F02F8S1R3NS14STKc5STKc02sp2lo3SLO3LOSS3sp1S1R3BUF2lo2bs3LOS3BCE3ALOFS1R2LF2sp2PP2bs3LFB3PP03ACV3SPR3sp13H224LFB'2FB2F02F1S1R4STKc5STKc02sp2lo3SLO3sp13SP1S2FB2F02KbS2LF2sp2PP2bs3LFB3sp13H224LFB'2FB1c2HcS1R2lo3LOSS2LF2sp2PP2bs3LFB3sp13H22S2LF3LFBS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'2FB4FBLOFFSS2LF2bs3LFB4LFB'2FBS2LF2sp2PP3CRT2bs3LFBSS2spS2LF2bs3LFB4LFB'2FBS2LF2sp2PP2bs3LFB3SPR3sp13H183H22S1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1SS1R3NS14STKc5STKc02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R3NS14STKc5STKc02sp2lo3slo4SLOL3SLO3sp13SP1S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF3CRT2lo2bs3LFB5CRTLO3sp14LFB'S2LF3CRT2lo2bs3LFB5CRTLO3sp14LFB'S1R2LF2sp2bs3LFBS2LF2bs3LFB4LFB'2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H204LFB'S2LF2bs3LFB4LFB'2FBS2LF3CRT2bs3LFBS2LF3CRT2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3LFB3sp14LFB'S1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4LFB'FFS2LF2PP3CRT2bs3LFBFS2LF3BUF2bs3LFBFS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'S2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFB4LFB'S1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOSFFFS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOFFFS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS4LFB'S2LF2bs3LFB3sp14LFB'FS2LF3CRT2bs3LFBS2LF3CRT2bs3LFBFFFS2LF2PP3CRT2bs3LFBS1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'FFFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP3sp13SP14LFB'S2LF2bs3LFB3sp13H213H224LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS D1 DXB CRTLO CWX CRT0 DPB B47 B3 B2 B1 BIN PPLO CWP PP0 ALP LFB STKc0 STKc NS1 SM2 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_ext_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(25.$4.Vm,VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))P,(25.$4.Vm,(=.VCRT,+1:8.)(18.$26.(29.#110.(2=.#110.))(28.$26.)))P,(2>.$4.Vm,VBUF,Vbs,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(34.$4.(10.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)Vm,(=.VCRT,+1:8.)+110.)P,(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VBUF,(30.(31.(5.&8.)Vbs,)))(35.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)(36.R13.R12.)(:.(;.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VCRT,)R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(<.&40.$37.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH HPP HEXT HBUF ST SS MI OPP OEXT OBUF.
  unfold A_X509_CRT_EXT.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  rt_facts.
  assert (BUFLO : BUF + n <= lo) by (first [ clear - BCE ALO LOS; lia | lx_side_lia ]).
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKc0 TOP HTOP; lia | lx_side_lia ]]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  carve_frame 288%nat ST.
  (* [comment removed for export] *)
  idtac "T-SAVED".
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaa67c] [] 543%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).   (* [comment removed for export] *)
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 304 <= sp1 <= bv_unsigned sp - 288) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKc0; lia | lx_side_lia ]).
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
  lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -288) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
  replace (bv_unsigned sp + -288 + 184) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
  lazymatch goal with STx : stk _ m0 lo (bv_unsigned sp + -288) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
  destruct (stk_split asegs m0 lo (sp1 + 184) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as [STlo SThi].
  destruct (stk_carve asegs m0 lo (sp1 + 184) 184 STlo ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as [ST1 [jrs RSL]].
  replace (sp1 + 184 - Z.of_nat 184) with sp1 in RSL, ST1 by (clear; lia).
  apply (rw_cells_split_CB asegs m0 sp1 [] 184 jrs [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity].
  cbn [mk_CB_cells app] in RSL.
  cb8_at RSL 0%nat.
  cb8_at RSL 1%nat.
  cb8_at RSL 2%nat.
  cb8_at RSL 3%nat.
  cb8_at RSL 4%nat.
  cb8_at RSL 5%nat.
  cb8_at RSL 6%nat.
  cb8_at RSL 7%nat.
  cb8_at RSL 8%nat.
  cb8_at RSL 9%nat.
  cb8_at RSL 10%nat.
  cb8_at RSL 11%nat.
  cb8_at RSL 12%nat.
  cb8_at RSL 13%nat.
  cb8_at RSL 14%nat.
  cb8_at RSL 15%nat.
  cb8_at RSL 16%nat.
  cb8_at RSL 17%nat.
  cb8_at RSL 18%nat.
  cb8_at RSL 19%nat.
  cb8_at RSL 21%nat.
  idtac "T-RSL".
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 543%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try clear STJ.
  try clear STlo.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 340476 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 160); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP NS1 STKc0; lia | lx_side_lia ]
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
      replace (Z.to_nat (8 * 2 ^ 2)) with 32%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 2)) with 256%nat in FRM by reflexivity.
      replace (64 * 2 ^ 2) with 256 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      idtac "T-SMALLOC".
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). try kland Kb.
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 256 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (256 / 8) with 32 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 256 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ (CRT + 424) 272 FB 256 FRSH CWX ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      assert (APB : FB + 256 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [8; 8; 8; 8; 216; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat HLOC FREST.
      lazymatch type of HLOC with rw_cells _ _ ?a _ => replace a with (FB + 32) in HLOC by (clear; lia) end.
      clear FLNK FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(first [ clear - SP1 SLO SLOL NS1 STKc0; lia | lx_side_lia ]) ltac:(first [ clear - SP1M; lia | lx_side_lia ])) as [SS1 SS2]; clear SSx end.
      idtac "T-FRAME".
      (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with HHc : HM _ _ _ h1 _ _ mc |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mc HHc) as AB1 end end.
  (* [comment removed for export] *)
  idtac "S1P".
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xaa798] [] 543%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]. spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
