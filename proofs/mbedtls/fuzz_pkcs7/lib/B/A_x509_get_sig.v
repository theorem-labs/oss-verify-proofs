(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_bitstring_null A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_sig_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P009452490d564e64 0 4 0 1 58 1 71 1 72 1P00aa5e89c1d81878 0 6 0 1 59 1 60 1 63 1 71 1 72 1P012aa1b32852667b 0 4 0 1 63 1 71 1 72 1P01af16c74ddffffe 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0266796a62e3c683 0 5 0 1 37 1 58 1 71 1 72 1P026f582c75fbe4c8 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0273b7ac989dd056 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0275364ae50442bf 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P02c38e4e7320d248 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P02c4f8657b5c22d6 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P03138e879373200c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0347d93685b5c677 0 3 0 1 43 1 49 1P03edfb167a3dff2d 0 5 0 1 37 1 58 1 71 1 72 1P0412e9c9a449c442 0 4 0 1 63 1 71 1 72 1P045e42cfe157bc95 0 6 0 1 59 1 60 1 63 1 71 1 72 1P04b59b569be7181a 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P04fe872dbc39969e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P05b2e1b72ee78de5 0 4 0 1 58 1 71 1 72 1P0688b6495d7aea81 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P06a46d1f8a48ba29 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P06bbad134fd3cdb9 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P06c765e831ac1338 0 6 0 1 59 1 60 1 63 1 71 1 72 1P07c95a47904c8113 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P07df9d5bfeabd730 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0916755ef0ae6efd 0 4 0 1 58 1 71 1 72 1P091cc55207f60d7d 0 5 0 1 37 1 58 1 71 1 72 1P0ac463e93ce99d15 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0bab78807192918c 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0c4d5fd5cf88349a 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0cfe6d215c20dd23 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0d3bb667e637a02d 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0db1cdd65e28d662 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0e01ba09f32cee3a 0 5 0 1 37 1 58 1 71 1 72 1P0e4c65cb890f6d1d 0 5 0 1 37 1 58 1 71 1 72 1P0e79d5fc9c69123a 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0ec91674ca2aca0f 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0ed6eb33303a0336 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0f29e97f5711c814 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P103d397b4025ebc4 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P10e6ef6543acdfb6 0 4 0 1 63 1 71 1 72 1P10f66d2ba7ab1ae8 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P11257743ea1627d3 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P11874c902f89c4f9 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P11f93f7dcbdcc338 0 4 0 1 58 1 71 1 72 1P12e9b31c96cf2b6e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P132cdd09e4250aa6 0 4 0 1 63 1 71 1 72 1P135d45236aa54006 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P13db07d40521b218 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P148889cf7cdd56df 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P149ba9c3c274614b 0 4 0 1 63 1 71 1 72 1P149ebc5ef92d60e4 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P14e17c9514a8159d 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P14ffb003899990c0 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P15a7a5a2da903453 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1786719ae89a1da0 0 5 0 1 37 1 58 1 71 1 72 1P1789e82162ac8aa9 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P17e8ec261414701c 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1a473ea825227a28 0 4 0 1 63 1 71 1 72 1P1a9d716a5e611501 0 5 0 1 37 1 58 1 71 1 72 1P1b6ad8dc37c19198 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P1b9abdba53b5464a 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P1c3e8ca4a96b1edd 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1c693253ee6bdc9d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P1cd1e62684a1936f 0 4 0 1 58 1 71 1 72 1P1e19184c7acb60cc 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1f2ff92df75bb1d4 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P20544bc1f0b2aa04 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2060439ecc45bad0 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P21d2b2226b38c3bf 0 4 0 1 63 1 71 1 72 1P21e5b8a8933db3cc 0 4 0 1 58 1 71 1 72 1P22c7a7262ccc97c8 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P23245e3571103d0b 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P23ae64f15618a30c 0 5 0 1 37 1 58 1 71 1 72 1P23cab529ef578dfa 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2401459b253914b4 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P24358ea0efeff87a 0 5 0 1 37 1 58 1 71 1 72 1P249a4d8e662cded6 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P24ece0321afde5bf 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P25add8730df63ee9 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2603dba86488abe6 0 4 0 1 63 1 71 1 72 1P26440f6f772eaa9f 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P26fb7eb4917221f4 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P286a356e67562d3f 0 4 0 1 63 1 71 1 72 1P290bef2c3dc1cfa0 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P293d98742d5684bb 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P29fc9e161058d3c4 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P2a546136bc509bd6 0 4 0 1 58 1 71 1 72 1P2aa01d8c52cc8fc3 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2ab95c7caa19b2a4 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2b7ab24143873b8b 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2bb889fb43e142ae 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2c1a0c0a426f8857 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2c7b75a5cef0e685 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P2cd1614d4a4aa45f 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2dda52ed1eaf7ec8 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2fa904aa28385d79 0 4 0 1 63 1 71 1 72 1P2fc5db8577641fce 0 4 0 1 63 1 71 1 72 1P307fbc2d1fe34b20 0 4 0 1 58 1 71 1 72 1P30d03473aa0327dc 0 5 0 1 37 1 58 1 71 1 72 1P30da2e2fdb5a40b2 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P30e1fbd51734d783 0 4 0 1 58 1 71 1 72 1P312340957d25f63b 0 6 0 1 59 1 60 1 63 1 71 1 72 1P318d0ad102f573a0 0 4 0 1 58 1 71 1 72 1P31a29d7c26a49aed 0 5 0 1 37 1 58 1 71 1 72 1P32bfef195cd82b02 0 6 0 1 59 1 60 1 63 1 71 1 72 1P33ddafacb12e4e6c 0 6 0 1 59 1 60 1 63 1 71 1 72 1P33e0179dcffc9114 0 5 0 1 37 1 58 1 71 1 72 1P33ffea240549aec1 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P351a4441a1533011 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P354d739e3bc03edb 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P35601e9338cc61ea 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3597a8390be02fec 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P36628da6dc73e0f7 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P36d4e9e67d72690f 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P36f06d3349a90219 0 4 0 1 63 1 71 1 72 1P374255a192b7efad 0 4 0 1 63 1 71 1 72 1P3748773d7854e3e0 0 4 0 1 63 1 71 1 72 1P3799476772cd7d88 0 4 0 1 58 1 71 1 72 1P3814f6ac5a96cd21 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P38d2eba55c707051 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P392576b7c2871c71 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3938aade5b26d17a 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P39cf2fb957033894 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3a576e00c219620b 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3a5f2466db5782b5 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3a67d38ebd68ad8c 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P3b3d129439289096 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3b62ddbbea9f7206 0 5 0 1 37 1 58 1 71 1 72 1P3bd3f209201d043e 0 4 0 1 58 1 71 1 72 1P3bd76c44819bc514 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3bea3c8a6cb75b50 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3c053d633c3110b0 0 5 0 1 37 1 58 1 71 1 72 1P3c082dd2b22a3e8e 0 4 0 1 58 1 71 1 72 1P3cc4218dda1f6afb 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3ccc20c15a5bb687 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3d4098f29cd96fe6 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P3dedb2c9d2209c0e 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3e4de520a5c39ed0 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3e98809979a1e6ef 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3e98834718ab5b99 0 3 0 1 44 1 52 1P3ed6dd368cc08e59 0 4 0 1 58 1 71 1 72 1P3f35fde1438781aa 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P3fbb9a26af488e03 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3ffe415a61f10346 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16N0098360fa9281a32N00f5dd19ee6bcc45N01500654e74f1ce9N02a07318ff660ddaN02e277dc98eb0847N03e1776a49d46c9cN049a51fc546c95baN0630803ceebb7af0N06da6258cd81ff3fN082c597533fa0bf6N087e4305189f0341N089c19829a7de686N09834f05d985f818N0ab35048281033e9N0b5620903ffd76e0N0c4ec168b1c91b78N0efef39e3ca4b444N10025101b0eb7014N110cb74f30f75cebN11d2593ab4fa3afdN13f280b3f3d251adN14f9b630854a00f3N15c7ba7ccb1dca8eN1652f95c35ba4d54N16c21de0726970b3N1a01bbc4b5fa6932N1a18ee2a5cf2fcb4N1a5dde40d4417ca8N1a9e4b7b233a6fc4N1d781ed011ef12bfN1dd97f5b220642d0N1deb6305f62be1baN1f3c1cb8aa6db8c8N1fb20e8f81cb88d2N20aa8133d80535fcN2211128e7586febfN246c211a6613c6fcN265a08630ef3cc93N29ef38d9429ca177N2ac80c165a76a0feN2df11163672934f4N2e17d56ce4a1a1eaN2e96550ac07b1bccN2f5fe3a7b263f478N344a7b584abeaa47N3476c47851bf8825N34feb77c5375cb4bN36358e47d0b519edN36937a8931f70278N378d633ca5a29526N3931fd6f3fa6c0f0N39529a9bdc0b39f0N3a56f5878e502c92N3b56929246df3f34N3bced68bd65e3ea2N3e1e9f0c282ac929N3f6eb74083dcd8af"%lxh.
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
Ltac2 gd_tbl_A_x509_get_sig () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_sig_A.x509_get_sig_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_sig_A.A_X509_GET_SIG"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_sig_A.x509_get_sig_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GBN : asn1_get_bitstring_null_stmtA asegs AL A_ASN1_GET_BITSTRING_NULL.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP SIGB P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SIGB \/ SIGB + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ SIGB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SIGB.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SIGB mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SGB : 0 < SIGB /\ SIGB + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_GET_SIG_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 144 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SIGB + 24 <= lo \/ bv_unsigned sp <= SIGB.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo SIGB 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIGB 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_GET_SIG_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_get_sig_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SIGB P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (SIGB, SIGB + 24)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01a0@D10639329459.125D10692844218.165D10692844218.166D10692844218.167D18607476203.164D2459889674.191 D27388597713.191D32452855249.191D3254889317.163 D3386124073.191 D33956323578.165D33956323578.166D33956323578.167D41452831839.191D46793042006.125D50254960491.165D53232575014.165D53232575014.166D53232575014.167D560907438.127  D59942523331.126D60098777666.126D60111245650.125D62011770188.127D62960757940.126D6395731754.165 D68409458026.191D6897397615.191 L10989370580.5  L12583145818.122L15756354262.7  L17921795213.184L19013159470.0  L19959024712.1  L19980016842.7  L29738741675.1  L3551623394.2   L35680140202.3  L38996969702.119L39076636629.0  L39332637397.0  L39618635427.2  L40228640085.0  L40753528314.3  L43055370171.117L48117620907.105L50790731766.8  L52249874585.0  L53342260001.0  L57355539152.169L58790154276.6  L59308677456.15 L59922446343.1  L60558678699.1  L63738252715.1  L64009471222.1  L6406266636.181 L7040749983.123 L7422344154.180 L9356559645.13  L9873114841.7   P1056307012.163 P1056307012.165 P36462068749.164P36465839390.163P53499894264.163P53499894264.165Q10523111608.131Q10651763882.133Q10651763890.129Q12660624644.135Q1530342990.165 Q21842126289.191Q23927511185.131Q23927511197.136Q27940636720.191Q31021924279.163Q31801074431.191Q32440606517.191Q32681887700.131Q33196749121.135Q33967969366.191Q3482560409.191 Q35653441506.111Q38248895676.137Q40216283646.191Q40271359350.165Q42439168719.163Q42439382240.138Q43880146016.137Q46805771343.133Q46805771351.129Q47230721789.131Q48132468010.191Q49081869340.191Q50796826103.165Q59865520191.138Q59932040168.130Q59932040173.134Q60109315147.111Q60740903729.129Q6192914196.163 Q62011770181.136Q62011770185.131Q62950270618.134Q62950270623.130Q64683599817.138Q67026483294.164Q67038703949.163Q6897397615.191 Q7166002681.130 Q9356560156.146 Q9633850153.191 00000F00G00H00I00J00K00l01M01N01O02802a02b03C03Y03Z03[03\03]04;04Q05005O05g06=06_06`07A07T08N08\08]08^08c09;09?09F09P09f09g09h0:20:30:?0:\0;;0;L0;M0;N0;O0;e0<80<<0<@0<D0<H0<m0=S0>40>c0??0@60@m0AU0AV0BO0CH0CX0Cf0D40DC0DY0Dg0EF0EY0F60FU0GH0GI0GJ0GY0HJ0I<0I^0Il0Im0J@0JV0Jl0K=0KK0KY0Kj0LI0Lf0MA0MB0MR0Mb0N60NI0NX0Ne0O20OB0OR0P50PX0Q;0QI0Q\0R30RLS2LF2sp2PP4SIGB2bs3LFBFFFFFS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBFFS2LF2sp2PP4SIGB3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP4SIGB3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS2LF2sp2PP4SIGB2bs3LFBFFFFS1R3HIA1h2LF2sp2PP4SIGB2bs3LFBS2LF2sp2PP4SIGB2bs3LFBS1R2LF2sp2PP4SIGB2lo2bs3LOS3LFBS1R2LF2sp2PP4SIGB2lo2bs3LOS3LFBS1R2LF2sp2PP4SIGB2bs3LFBS2LF2sp2PP4SIGB2bs3LFBS2LF2sp2PP4SIGB2bs3LFB3sp13H203H22FS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS2sp2lo3SLO3sp13SP1S2LF2sp2PP4SIGB2bs3PPB3SGB3SPA3LFB3SPR3sp13H183H193H203H22S1R2lo3LOS3ALOFSS3sp1S1R3HIA1h2sp3TOP3sp13SP1S2FBS2bs2EQS2FB2x22HxS2LF2sp2PP4SIGB2bs3LFBSSS3sp14SP1MSS2sp3sp13SP1S2LF2sp2PP4SIGB2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSSSFS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2spS2FBS2FBS2bsS2LF2sp2PP4SIGB2bs3LFB3sp13H203H222FBS2LF2sp2PP4SIGB2bs3LFB3SPR3sp13H183H22S2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp4SIGB1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp4SIGB1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'FFS2LF3BUF2bs3LFBS2LF2sp2PP4SIGB2bs3PPB3SGB3LFB3SPR3sp13H222FB3F64S2LF2sp2PP4SIGB2bs3PPB3SGB3LFB3SPR3sp13H224SP1M2FBS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R2LF2sp2lo2bs3SLO3LOS3LFBFS2LF4SIGB2bs3LFBS2LF4SIGB2bs3LFBS1R2LF2lo2bs3LOS3LFBS2LF2PP4SIGB2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS2LF4SIGB2bs3LFBS2LF4SIGB2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2PP4SIGB2bs3LFBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ptg0,(0.&40.)Plen0,$1.Pq0,$1.P,(2.$3.VR,VHIA,Vh,VLB,VLF,Vm,)P,(4.$3.Vm,VPP,(5.$6.(7.(8.&40.VP,))(9.$6.)))P,(4.$3.Vm,VSIGB,(:.R5.Vpad,R4.R3.))P,(;.$3.Vm,VBUF,Vbs,)P,(<.$3.Vm,Vlo,(=.&40.Vsp,))P,(>.$3.(?.VR,)Vm,Vslo,(=.&40.Vsp,))P,(10.$3.Vm,)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VPP,+8.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VSIGB,+18.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VBUF,(13.(14.(0.&8.)Vbs,)))(15.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)(16.$3.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSIGB,VP,VEND,Vlo,Vslo,Vpad,Vm,)(17.(18.Vra,Vsp,Vgp,Vtp,R19.R18.R17.Vs0,Vs1,(8.&40.VPP,)(8.&40.VEND,)(8.&40.VSIGB,)R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(8.&40.$19.)Vfc,(1:.(0.&40.))Vm,(1;.$3.)))")
(* [comment removed for export] *).
  Proof.
  intros until q0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_GET_SIG.
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
      pose proof (fresh_apart_client _ LB LF lo SIGB 24 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      pose proof (hm_abase asegs R HIA h1 LB _ m3 ltac:(eassumption)) as AB3.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_get_sig_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_sig ()) "PR,$1<.PHIA,(1=.$3.R1.)P,(1>.(?.R2.))P,(1?.$1.(20.R3.)$21.)P,(1?.$1.(22.R4.=)$23.)(24.$3.R5.R4.$19.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_bitstring_null_spec (L := arl_L R) (arl_AL R) IMG) as GBN.
  unfold x509_get_sig_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
