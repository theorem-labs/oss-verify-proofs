(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt HeapIface CellsX Cells Mem Step Frame Tac AStep Asn1Aux Asn1AuxA X509Aux X509AuxB MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts CrtFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_x509_get_name_A U_asn1_free_named_data_list_shallow U_x509_get_san_ext_A U_x509_get_san_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac is_arith_goal :=
  lazymatch goal with
  | |- @eq Z _ _ => idtac | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- _ <> _ => idtac | |- False => idtac | |- True => idtac
  | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac | |- Z.divide _ _ => idtac
  end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002b97b7b6a86b7a 2 18 0 5 0 1 3 1 21 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P00793efc7d746fa0 1 1 8 3 0 1 44 1 47 1 4 21 1 45 1 46 1 48 8P009ee74eba60aa2e 0 2 0 1 42 1P010d4a4ebed3937c 0 2 0 1 27 1P011d6df3ce7adba7 1 1 8 3 0 1 64 1 67 1 4 38 2 65 2 66 2 68 16P01709a23f8ffb48b 0 4 0 1 27 1 54 1 55 1P01b1a26df759cc8c 0 2 0 1 7 1P02195dad05037173 0 4 0 1 3 1 58 1 59 1P02c770ac2dfbe05a 0 5 0 1 25 1 27 1 50 1 51 1P03222bc068ee4698 0 4 0 1 53 1 82 1 83 1P036941aa93a69881 1 1 16 2 0 1 45 1 3 4 1 46 1 47 16P03bc85c3acdb83cf 0 4 0 1 53 1 82 1 83 1P04130f103e91aab9 0 4 0 1 50 1 77 1 78 1P041577789f16aa9a 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P0425b3ceb9694183 0 4 0 1 39 1 68 1 69 1P04a5eafb0fd0fc7e 0 6 0 1 13 1 14 1 15 1 48 1 54 1P05dfd7d593627cfd 0 6 0 8 44 8 70 8 71 8 72 8 73 8P05fac8367e309963 0 2 0 1 1 1P0685a45f62c22db3 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P069fa49e8d04776c 0 4 0 1 35 1 62 1 63 1P06ae591910d5adb8 1 1 8 2 41 1 56 1 3 0 1 55 1 57 8P0707b25fada8ff0d 0 4 0 1 35 1 62 1 63 1P0721c7e15cd02b62 0 2 0 1 7 1P0736f0ca51f5ed60 0 2 0 1 5 1P0752777cd15d5e1d 1 1 8 3 1 1 45 1 46 1 4 21 1 44 1 47 1 48 8P0787eafc80d883e3 0 4 0 1 35 1 62 1 63 1P07b9bb2e5c72e979 1 1 8 3 0 1 64 1 67 1 4 38 2 65 2 66 2 68 16P08a14c4c4f082b11 0 3 0 1 8 1 35 1P090802e96ab98625 0 4 0 1 2 1 57 1 58 1P091ecb71b73ed667 0 6 0 8 21 8 45 8 46 8 47 8 48 8P092086bc4ff10acc 0 6 0 8 44 8 70 8 71 8 72 8 73 8P0937bb6dc2770a0c 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P09c1845b55c3ce26 1 1 8 3 1 1 44 1 47 1 4 21 1 45 1 46 1 48 8P09faa072af023e39 1 1 8 3 1 1 65 1 68 1 4 40 1 66 1 67 1 69 8P0a4ceb44a4d8c6b5 0 2 0 1 1 1P0adff41a7bfb6854 0 4 0 1 39 1 68 1 69 1P0b1e1eafb76b99a5 0 4 0 1 39 1 68 1 69 1P0b608c858e26f793 1 1 8 3 1 1 71 1 74 1 4 46 1 72 1 73 1 75 8P0b75bd6ab0f8a826 0 4 0 1 53 1 82 1 83 1P0b7d43483d7eae4a 0 2 0 1 5 1P0bc61373f8ac6aee 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P0bf33660de2ec102 0 5 0 1 43 1 44 1 68 1 69 1P0c04a94ef223086d 0 4 0 1 28 1 55 1 56 1P0c5fcd3ac3443180 0 4 0 1 39 1 68 1 69 1P0c865cb3cd51728c 1 1 8 3 1 1 47 1 48 1 4 23 1 46 1 49 1 50 8P0d365f8d08e4388f 1 1 8 3 0 1 44 1 47 1 4 21 1 45 1 46 1 48 8P0e182dfbfdb8bd2c 0 6 0 8 44 8 70 8 71 8 72 8 73 8P0e4b6e44f53cbad9 1 1 8 2 31 1 46 1 3 0 1 45 1 47 8P0e9d41ebc4321fd7 1 1 8 3 0 1 56 1 59 1 4 30 2 57 2 58 2 60 16P0f4de5cb6ad9cd4c 1 1 8 3 0 1 79 1 82 1 4 53 1 80 1 81 1 83 8P0f634999ed24c48e 0 1 1 1P0f75cfc246a021cf 1 1 8 3 1 1 44 1 47 1 4 21 1 45 1 46 1 48 8P0f9a00db3082cde5 0 4 0 1 39 1 68 1 69 1P0ff720df99388d63 0 2 0 1 5 1P1024d3a6e8a2cc3b 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P107756f38966487c 0 4 0 1 4 1 41 1 42 1P10ac18222742ac45 1 1 8 3 0 1 71 1 74 1 4 45 1 72 1 73 1 75 8P10fe3072246efe96 0 2 0 1 1 1P11613d5e40a77998 0 4 0 1 53 1 82 1 83 1P11904aa754132a30 1 1 16 2 0 1 55 1 3 16 1 56 1 57 16P11fa54da70aa906d 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P120344d97cd46167 2 18 0 5 0 1 3 1 21 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P120be7a50ff95803 0 2 0 1 39 1P12376394e9c87dcf 1 1 8 2 29 1 44 1 3 0 1 43 1 45 8P124c3e0b8de54ae4 0 5 0 1 24 1 26 1 49 1 50 1P1284e31bf4720d30 0 2 0 1 32 1P12a3dc4bddaf7048 0 2 0 1 29 1P12ca65f273d3f2de 1 1 8 3 1 1 80 1 83 1 4 55 1 81 1 82 1 84 8P12e2774fc354213c 0 2 0 1 7 1P12f1f763533c7e5f 1 1 8 3 0 1 71 1 74 1 4 45 1 72 1 73 1 75 8P12f71319a693d851 0 2 0 1 32 1P1425c641d435341e 0 5 1 1 3 1 31 1 58 1 59 1P142da345dd41ab40 0 4 0 1 39 1 68 1 69 1P14704d5e4863cf70 0 5 0 1 43 1 45 1 68 1 69 1P14b74d47648ff443 0 4 0 1 4 1 51 1 52 1P1502e3bb0504e627 0 4 0 1 39 1 68 1 69 1P15211f23c4646248 0 4 0 1 27 1 54 1 55 1P1553dc0fa0e3e91d 0 2 0 1 1 1P15c706f19730a840 0 2 0 1 6 1P160eae115dc22ad0 0 3 0 1 22 1 33 1P165766f0507e22d7 1 1 8 2 56 1 71 1 3 0 1 70 1 72 8P16b22ecac05f2666 0 2 0 1 19 1P16e63fc26d3f5f9f 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P16ea615103d54f31 0 2 0 1 1 1P16f5fb644faf1962 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P171f3ac8f7ff6edb 1 1 8 3 1 1 72 1 73 1 4 46 1 71 1 74 1 75 8P181e750b795ab00b 1 1 8 3 1 1 80 1 83 1 4 55 1 81 1 82 1 84 8P1843b199f8f3be33 0 2 0 1 7 1P187dbe11b9574b25 0 4 0 1 53 1 82 1 83 1P18964e7e132f5e6b 0 2 0 1 43 1P18c00b25a49e6484 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P18cde60f42925802 0 5 0 1 24 1 25 1 49 1 50 1P18e37f1a5f0eede4 1 1 8 3 1 1 46 1 49 1 4 23 1 47 1 48 1 50 8P1927664b5d3e77c2 0 2 0 1 33 1P19c16a7a81201618 1 1 8 3 0 1 44 1 47 1 4 21 1 45 1 46 1 48 8P19d0480d9cc2e50a 0 6 0 1 3 1 4 1 5 1 38 1 44 1P1a0969076208feb3 0 4 0 1 4 1 41 1 42 1P1a5dc8fc92f5a391 0 3 0 1 51 1 52 1P1a720bfbd6be77af 0 2 0 1 5 1P1aa97a578b767e75 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P1b06816a45d0799b 0 2 0 1 4 1P1c1f3789da7e5ae3 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P1c5ab6fa35bd03f8 0 6 0 1 3 1 5 1 15 1 48 1 54 1P1c6d7d4f1f7a770e 0 2 0 1 33 1P1d01aad18d944409 0 4 0 1 25 1 52 1 53 1P1d1128f757b0b110 2 18 0 5 0 1 3 1 21 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P1d4515ae044c93a7 0 2 0 1 5 1P1d6d34edea0e94ee 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P1d7ca044b47d08c7 0 4 0 1 39 1 68 1 69 1P1d959736699898b1 0 5 1 1 3 1 46 1 73 1 74 1P1db3f4b4e800c256 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P1e503f37f9d2edfe 1 1 8 3 0 1 46 1 49 1 4 22 1 47 1 48 1 50 8P1e857eb1fb2e249f 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P1eada689a00c4c5b 0 2 0 1 7 1P1eaf7ef15e8dbb8e 0 3 0 1 41 1 42 1P1f660a07a39145fb 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P20442cf28085aa13 0 4 0 1 3 1 46 1 47 1P204d9d9a79a0fedd 0 6 0 1 3 1 4 1 5 1 38 1 44 1P2069dc78ca88bf75 0 2 0 1 4 1P20aad89c39924232 0 4 0 1 39 1 68 1 69 1P20d9576682dc7074 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P20ef052a729cef09 0 4 0 1 3 1 48 1 49 1P213672533eff6d55 0 4 0 1 43 1 70 1 71 1P215c647e42c06b74 0 5 0 1 25 1 26 1 50 1 51 1P222b1858bc9afdf4 0 2 0 1 6 1P22f0ddfc755ad199 1 1 8 3 1 1 80 1 83 1 4 55 1 81 1 82 1 84 8P23974c82d93e4c6e 0 2 0 1 5 1P2408f55a9e31d5c7 1 1 16 2 0 1 70 1 3 7 1 71 1 72 16P24375aeed78c65c8 0 2 0 1 20 1P24388904e52b9a8f 0 1 1 1P243f6f53c12b486f 0 1 1 1P246fe38f48d99e6e 0 5 0 1 26 1 28 1 51 1 52 1P254d4d1d85d86fa1 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P25517e82cbc7a1e9 0 2 0 1 19 1P2574eca4b03da59d 0 1 1 1P25c2574d490dbf3a 0 4 0 1 28 1 55 1 56 1P25cace44b7737f2d 0 5 0 1 13 1 23 1 32 1 60 1P25cf767bfbbeb612 1 1 8 3 0 1 79 1 82 1 4 53 1 80 1 81 1 83 8P25d3f588339aab75 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P25d69df21cc49f94 0 4 0 1 25 1 52 1 53 1P26c92b34ef8d7557 0 2 0 1 1 1P271bdc5ed231ed45 0 2 0 1 6 1P27da2fec3634635c 0 4 0 1 25 1 52 1 53 1P27fffdf74d808831 1 1 8 3 1 1 71 1 74 1 4 46 1 72 1 73 1 75 8P281be59f15fea616 0 4 0 1 53 1 82 1 83 1P286b0f3e8549167b 0 4 0 1 50 1 77 1 78 1P28e0f1386b46a930 1 1 8 3 1 1 57 1 58 1 4 31 1 56 1 59 1 60 8P28e49cc6ea9b8c87 0 5 1 1 2 1 22 1 47 1 48 1P29166c8061df6fcc 2 18 0 5 0 1 3 1 21 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P2950c694348401fb 1 1 8 3 0 1 44 1 47 1 4 20 2 45 2 46 2 48 16P2b74e64eec4da735 0 2 0 1 1 1P2c1f4766d08d0967 0 2 0 1 5 1P2c4dd96812314f1a 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P2c56dc0ade9d2ab3 0 2 0 1 1 1P2c679c682053b108 1 1 8 3 1 1 65 1 68 1 4 39 2 66 2 67 2 69 16P2dad9b479becd163 1 1 8 3 1 1 56 1 59 1 4 31 1 57 1 58 1 60 8P2db9d28b6f94630e 0 2 0 1 57 1P2e046609eb8fa6c6 0 2 0 1 6 1P2e5176b874d8c504 1 1 16 2 0 1 43 1 3 6 1 44 1 45 16P2e619fdae6b3ee32 0 2 0 1 19 1P2e8df355377b0fee 0 4 0 1 2 1 45 1 46 1P2f15d93a323f16ef 0 2 0 1 1 1P2f81f5c33bc39440 0 2 0 1 54 1P2fd3d2be8062e571 0 2 0 1 1 1P2fd41d117138c564 0 5 0 1 42 1 44 1 67 1 68 1P304454a85e6055b5 1 1 8 3 1 1 65 1 68 1 4 40 1 66 1 67 1 69 8P316f05beb1dfab80 0 2 0 1 5 1P318f7cda0cbe1c0f 0 5 1 1 3 1 21 1 46 1 47 1P319ec1837bd885e1 0 5 1 1 2 1 20 1 45 1 46 1P3200e8975f57a801 0 5 1 1 2 1 45 1 72 1 73 1P323297be7c7c7474 1 1 8 3 1 1 80 1 83 1 4 54 1 81 1 82 1 84 8P3291fc0a758a7c23 0 3 0 1 6 1 45 1P32e58ea9c9eb9010 0 2 0 1 5 1P32f277f3945b9c3f 0 2 0 1 5 1P338ebaee44339687 0 4 0 1 2 1 72 1 73 1P33bdd1882fe733ac 0 5 0 1 3 1 5 1 38 1 44 1P33cb33432c1e63b1 1 1 8 3 1 1 71 1 74 1 4 46 1 72 1 73 1 75 8P33cc6f3b6686fc8c 1 1 8 3 0 1 71 1 74 1 4 45 1 72 1 73 1 75 8P33d3ca266d8654ab 0 4 0 1 3 1 73 1 74 1P34c892b08deb8760 0 5 0 1 26 1 27 1 51 1 52 1P34e5262fcf49af9d 0 3 0 1 41 1 42 1P35598c31d5181178 0 6 0 16 29 16 55 16 56 16 57 16 58 16P358c9b582e80f39f 1 1 8 3 1 1 46 1 49 1 4 23 1 47 1 48 1 50 8P35d788ae7222a03f 0 5 0 1 42 1 43 1 67 1 68 1P3626ed9725c27cb5 0 5 0 1 3 1 5 1 38 1 44 1P3630170f9afff83b 0 2 0 1 31 1P363309ebeb469ece 0 2 0 1 30 1P36b33d5b93f98fb2 2 18 0 5 0 1 3 1 21 1 46 1 47 1 0 4 0 1 2 1 46 1 47 1P36bb3037a8d5c869 0 2 0 1 5 1P36ed69cca6dc1cef 0 4 0 1 28 1 55 1 56 1P36fe4968798b0669 0 4 0 1 2 1 47 1 48 1P372c2e18dcafd5a3 0 3 0 1 51 1 52 1P373026fa5e405e80 0 4 0 1 6 1 51 1 52 1P375229a03656daec 0 2 0 1 5 1P37e072f16d8d6f8b 0 5 1 1 3 1 23 1 48 1 49 1P38311050bd12716c 0 5 0 1 27 1 29 1 52 1 53 1P3849a5aa5f1786b7 0 4 0 1 39 1 68 1 69 1P3886950c2f8f302d 0 6 0 16 19 16 43 16 44 16 45 16 46 16P38cc41a3993cabfe 0 4 0 1 39 1 68 1 69 1P39461076363358d2 1 1 8 3 1 1 46 1 49 1 4 23 1 47 1 48 1 50 8P398d2f789e5bee10 0 4 0 1 39 1 68 1 69 1P39956f9b003a095a 0 4 0 1 50 1 77 1 78 1P3a55b1921cea78bc 1 1 8 3 1 1 65 1 68 1 4 40 1 66 1 67 1 69 8P3a802bd8475ee09e 1 1 8 3 0 1 44 1 47 1 4 21 1 45 1 46 1 48 8P3ac61a4bdc91a692 0 5 0 1 27 1 28 1 52 1 53 1P3b54ec1f0839ab5b 1 1 8 3 0 1 43 1 46 1 4 20 1 44 1 45 1 47 8P3b8d4c294a67ee2c 1 1 8 3 1 1 56 1 59 1 4 31 1 57 1 58 1 60 8P3c583e9b6c364ae3 0 2 0 1 58 1P3c672d66560760fe 1 1 8 3 1 1 56 1 59 1 4 31 1 57 1 58 1 60 8P3cfd1b1aa7be6b3d 1 1 8 3 0 1 64 1 67 1 4 39 1 65 1 66 1 68 8P3d24b1791ff8e685 0 7 0 1 3 1 4 1 5 1 15 1 48 1 54 1P3d730ed31b47d14c 0 4 0 1 27 1 54 1 55 1P3dfc8e287ea08fbd 0 5 1 1 2 1 30 1 57 1 58 1P3e25cf72a07bb3ac 0 5 0 1 7 1 15 1 48 1 54 1P3e54934da9ae9b83 0 2 0 1 7 1P3ed07b4ea1813607 0 2 0 1 7 1P3ed9313e9882f4b5 1 1 8 3 1 1 44 1 47 1 4 21 1 45 1 46 1 48 8P3ee6cb1f8739bd4a 1 1 8 3 0 1 79 1 82 1 4 53 1 80 1 81 1 83 8P3f3fc75d6b78e6ff 1 1 8 3 0 1 44 1 47 1 4 21 1 45 1 46 1 48 8P3f836f0ee4427371 1 1 8 3 0 1 55 1 58 1 4 30 1 56 1 57 1 59 8P3fa2a20042b0a329 1 1 8 3 0 1 64 1 67 1 4 38 2 65 2 66 2 68 16N000b0b90f00ef79cN0026eaa0db7d2b93N00348e440a7936ccN0038aa96dfa6aeabN003af18f0a6b8015N004f5a264c78f69fN00a2604bb81b905fN00b12ea1557c03a8N00d6a20797692c87N01428d5a14679094N014aaedf95a625dcN0163e834cd00f9a2N01dc0714bec1a551N03053f60c1b30a67N032b609e3e7431ebN034e87b2effd590eN03729a1b4405aee3N03cf084d61547c74N03f4766c5786dec7N045849e32f021590N04747ce5ef66f408N048af78218feb4ebN04b1d26f38e2ddbfN0507e15de784ac39N05509548a506c003N062c182b50d34dc4N0636834149e19891N06699b31d10481bbN06a754bcf2580238N06ad405b8e2ac20eN0754d9f43bd199c7N075f9d8029800563N07cec21a9c5f4817N07dd784013bffe49N07f9bc1d20582f76N09207cd1b8265df4N09b3c3609338991dN0a0e6408d57f0b84N0a190371f65aab4eN0a1d0b392b66a33fN0a347ae952a8f553N0a9e41a629607defN0b0859c8fb5e4261N0b0a42cb85a4bdacN0b226f128e71663fN0b62a5992f6eef90N0ba2fa4be4d059c5N0ba9036219c07083N0bba508d29af1a38N0c57f1808bc21ca6N0c8b08778fd3eb4bN0c97823401434c53N0cd3e2fd371867a2N0cf447957e1d27acN0d32b36067ed2de1N0d4a0da7625091ecN0d8e107e5c676f45N0da0443474d9cf94N0da58692ab6ba493N0de5767c52bec2dcN0df179ea767d7882N0df4bcde2ec6d8eaN0dfcdd8ed34cf819N0e1012be256193e1N0e1eca3ac140c348N0e76b19d1714e8d8N0e95bc24e939afc4N10f328c4780f8c8aN1107cdf6223847beN115f6f9a98f6959fN1160dfbf11ae9d13N117d11e97ccea4a5N11b3d489895d3bf6N11bc315467469568N11bce2805d7d93dcN11c80ddbb2ae6001N11ef82286bf57593N12021657df3c5563N1281e2769bcda266N12a4c71d39b2be1cN12b425de52b5f166N12e6613c577a7fd4N12ee2fc9f4fbab7eN13a20236a80ad5b8N13c304460552d370N13ff7a0d6ded1b67N1428f3bde55934b4N145de0d14db7b71dN14eca88b2fdf2699N15113b1a35fae0ecN151ce1604d97e4dbN152a7b80ad6f6b7fN1539dc91e9854f82N157866e763b3e726N15b41a3c9aef7263N162531cb152f7b5aN163ed337daff458dN164e6ea690098723N1663f41f6c2fdce1N170bfc7189b19172N17605bb9b6b805eaN1765ca9dcbed74d4N185819fa28afa1b8N194053660116174bN19479bf30c47221fN195ca9180acbd9efN196c4f7336fe0ef9N197d0bc0828d4e22N199d1ca9e4766607N19a0ddce5eeebe00N19b340378e5fc9f9N19c893ebfb6b48d5N19f1a712dc90c7b9N1a18b5c27e446cc8N1a295919cb5bcd24N1a552add5628c16eN1af30e625c8447caN1b4bad2a1cc40bfdN1b56ed8d2e3a67b6N1c07dbe92069d004N1c31d3dda8208433N1c384908278094d4N1c8c74f22cb568bfN1caf6d11a8e621bdN1d0244964e294442N1d035ca31012a009N1d161257d5ee9b36N1d1c7bebbe0f2225N1d7182b4a46351c1N1d8f790fd52ea9d0N1dbeab902e553db7N1e25f928319a0f5dN1e77eb6b2106f22eN1e785f1c589fd949N1ece97003894b74dN1eeb04490be0a1ceN1f403a36b8a636afN1f4ebada43823f7fN1febcc0641a44e4eN1ff43ebe1ecae510N1ffde27670ac0f62N204efc2c73208383N20d114520bef81e6N20f1f168301ed5aaN211ce84f2217271dN21493852513f5e73N217d635c8125a3a7N2242b05c47a465d7N226873e9afd60758N22b7d789b0294b85N22c71417354a3a34N22cf82220a3cb06cN230d87422e45d3dfN231c730463eb67cdN23403c47387cf157N234981b4a245ad4dN236b0997d2d1ee65N23f9a68055d07368N242afdd35095ab79N244698aeae3f4c1cN247a1df99fe17ee6N24de2e97ac1a8fc5N25117f1bc260860fN25577f3ac848c2ffN25a6160038eee313N2600e34027d6f323N26b8b425d0f48026N27bdfd1e52eeded2N27d270047ee4c2a4N27ece45d2eff13b3N287adf77f9db9e7dN28b438e847a7c231N28c05ed83d0f3842N28e3ba12482c2b58N290b161a06af70c8N290cbb5fc6741924N297741301842b082N29bc480ff200194aN29cc284def22cf21N29e88383f48f04c9N2a0248e6eccf2fffN2a0351cd93cef461N2ac7a88d4470b3ebN2ae15a2e0d5a5accN2b1963855549471dN2b42161380388534N2bb9df6b23ff444bN2bbbae4b241e232fN2bcfbeaab56497eaN2c0aecdc25fd8ef1N2c2026818a68c7c5N2c2324a3383da437N2c864fc846fcfdf0N2cb7223043c7efe0N2e562015ce2b59ecN2e5b562ed87448fdN2e630edb1188d90aN2ed2d4f01e9103c5N2eec65e8edee15acN2f30f472395a462fN2f720c05c832c895N2fb8ad338314e2beN2fb929f108d10228N302dfc8166ce66e0N3032c3b4268c17e8N30dfe2ebff23a186N30e61a05b977017dN310c7ea495098d77N314ced4f0b4f3309N31688b07b097d359N31afcd2ebff08acdN31c4d4f0dd3f1bb8N3227d8ba81d40654N3238e2da23222aa7N3294272307852c88N32a6b05feb435920N338e51091f307687N3414c73ab0a8e457N34b0fd24e704bd97N34ccbf6ea4917421N354b25d02fd373e0N360c30ad8e4be547N369689c65f8de464N36d6009a8d823018N3713c92737eff974N37525d5f8a4344fbN37865d5f9d7a215dN37b60d21082a5d0aN37f578a2c788f7d3N3801012659a58ba6N38438a3d67423413N38595cef8973683aN38ad2251449e1c11N38d8ad5ff58ddc4fN38f47292da3d186eN394d560c89d88de9N3a1bcc5266aa1ef3N3a55e995c885ea28N3a97115b3c2cc370N3ab0839d94dcc93dN3afb14b3a0769b9fN3b7816e29016a550N3b91c1d0cf2e47d7N3bd0e59cb7331353N3cbfe4d1483f5fb9N3cc9045b69d7a665N3cca1d7b508f54ddN3cf16023bf35bff0N3d503c815a09f19fN3d90179df9b7cb78N3d9d55e561bff972N3da763e1d8892457N3e20ecee2820b959N3e22d7863bf2d74fN3e45158c94c01583N3eee53fcdef000dfN3f24ad1965325bc8N3f3f3bff53a2396aN3f6e510b606a532bN3f8e64896b73fcb9N3fa8a5f282092105"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_akid () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.land"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Walk.Body.wfp"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.USpec.CrtExtStmts.akid_cells"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.hd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.seq_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.map"; "Stdlib.Lists.List.rev"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.USpec.CrtExtStmts.x509_akid_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"].


Definition U_X509_AKID : Z := 0x27358.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L11601612111.4L29010614818.4L33965486918.4L35495549846.3L66151426826.400000300<00E00F00NS1rS1r2Hr2H0S1r2Hr2H0SS1r2Hr1H". (* [comment removed for export] *)
Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma land64_nonzero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13201759935.4L18926759668.4L66151426826.4L67182092283.400000900<00D00MS1r2Hr2H0S1rS1r2Hr1HS1r2Hr2H0". (* [comment removed for export] *)
Lemma mod64_zero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 = 0 -> r = 0.
Proof.
  intros r Hr H. destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 18446744073709551616) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma mod64_nonzero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L35497643387.4L43090583504.4L58031153122.400000100700=SS1r2HrS1c2Hc". (* [comment removed for export] *)
Lemma swrap32_land_errsum : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "Pr,$0.Pc,$0.P,(1.(2.-10000.R2.)(3.R2.=))P,(1.(3.(4.(5.+2.+40.)+10000.)R2.)(2.R2.(5.+2.+40.)))(6.$0.(7.&20.(8.(9.R4.+????????????????.)R3.))(8.R4.(4.R3.(5.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros r c Hr Hc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply swrap32_errsum; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.

  Let SANEXT : x509_get_san_ext_stmt usegs L HI U_X509_GET_SAN_EXT := U_x509_get_san_ext_spec L HI HCALLOC HFREE HLS.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (PP AK P END BUF lo : Z) (bs : list byte)
              (k1 k2 k3 k4 ct cpad r1 r2 r3 r4 : word).
    Hypothesis HH : HEAP usegs L HI h LB m mo.
    Hypothesis HPP : rw_cells usegs m PP [C8 (Z_to_bv 64 P)].
    Hypothesis HAK : rw_cells usegs m AK (akid_cells k1 k2 k3 k4 ct cpad 0 0 0 r1 r2 r3 r4).
    Hypothesis BY : bytes_at usegs m BUF bs.
    Hypothesis B1 : BUF <= P.  Hypothesis B2 : P <= END.  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
    Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
    Hypothesis D1 : PP + 8 <= AK \/ AK + 80 <= PP.
    Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
    Hypothesis D3 : AK + 80 <= BUF \/ BUF + Z.of_nat (length bs) <= AK.
    Hypothesis AL1 : PP mod 8 = 0. Hypothesis AL2 : AK mod 8 = 0.
    Hypothesis NZ1 : 0 < PP. Hypothesis NZ2 : 0 < AK. Hypothesis NZ3 : 0 < BUF.
    Hypothesis ST : stk usegs m lo (bv_unsigned sp).
    Hypothesis SLO : lo <= bv_unsigned sp - X509_AKID_STACK - hl_stack L.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L. Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
    Hypothesis SPP : bv_unsigned sp <= PP. Hypothesis SAK : bv_unsigned sp <= AK.
    Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
    Hypothesis DS2 : AK + 80 <= lo \/ bv_unsigned sp <= AK.
    Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
    Hypothesis CW1 : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
    Hypothesis CW2 : client_wrange L LB lo (heap_top usegs L HI h) AK 80.
    Hypothesis CRB : client_range L LB lo BUF (Z.of_nat (length bs)).
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis MI : mem_inv usegs m.
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L27904922626.80000017S1L3HLS2sp2PP2AK3BUF2lo2bs2D12D22D33NZ13NZ23SLO3SPP3SAK3DS13DS23DS33SPR". (* [comment removed for export] *)
    Let LOSP : lo <= bv_unsigned sp + -48. Proof. unfold X509_AKID_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L3476874875.8100000FS1L2sp2PP2AK2lo2bs3SLO". (* [comment removed for export] *)
    Let SLO2 : lo <= bv_unsigned sp + -48 - 480 - hl_stack L. Proof. unfold X509_AKID_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L12990621327.8300000CS2sp2PP2AK2bs3NZ11B". (* [comment removed for export] *)
    Let PPB : 0 <= PP /\ PP + 8 <= 2 ^ 64.
    Proof. pose proof (rw_cells_bound usegs m PP _ HPP) as B. cbn [cells_size csize Nat.add] in B. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L165920857.8400000?S2sp2PP2AK2bs1B". (* [comment removed for export] *)
    Let AKB : AK + 80 <= 2 ^ 64.
    Proof. pose proof (rw_cells_bound usegs m AK _ HAK) as B. unfold akid_cells, seq_cells in B. cbn [cells_size csize Nat.add app] in B. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Notation POST := (x509_akid_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP AK P END BUF lo m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
    Notation X0 := [(PP, PP + 8); (AK, AK + 80)].

    Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
      repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
      repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    Ltac spine_firstn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
      | Datatypes.S ?k' => lazymatch cs with
                 | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
                 | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
                 end
      end.
    Ltac spine_skipn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => cs
      | Datatypes.S ?k' => lazymatch cs with
                 | _ :: ?cs' => spine_skipn k' cs'
                 | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
                 end
      end.
    Ltac splitat H k H2 :=
      lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
        let l1 := spine_firstn k cs in
        let l2 := spine_skipn k cs in
        change (rw_cells sg mm A0 (l1 ++ l2)) in H;
        let H1 := fresh "SP" in
        (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
      end.

    (* [comment removed for export] *)
    Definition wfp (W : list ivl) : Prop := forall a, ~ outside W a -> (lo <= a < bv_unsigned sp) \/ (PP <= a < PP + 8) \/ (AK <= a < AK + 80).
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L28249930155.100L44370643720.100L54398282304.10100000B00T027S2sp2PP2AK2bs1a2H3S2sp2PP2AK2bs1a2H2S1L2HI3HLS2sp1h2PP2AK1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ25SPTOP3SPP3SAK3DS13DS23SPR4SLO21a2H1". (* [comment removed for export] *)
    Lemma HEAPm : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "PW,(:.$;.)PLx,(:.$<.)Phc,(=.$>.VL,VHI,)PmA,P,(?.&40.)(10.(?.&8.))PmB,P,(?.&40.)(10.(?.&8.))Pmoc,$11.P,(12.$>.VL,VHI,R4.R5.R3.R1.)P,(6.$0.(13.$>.VL,VHI,R5.)(13.$>.VL,VHI,Vh,))P,Pb,$<.P,(14.$<.R1.VLB,)(14.$<.R2.R9.)P,(15.R9.R6.R5.)P,(16.$>.R7.R6.)P,(17.R;.)(12.$>.VL,VHI,R:.R;.R8.R7.)")
(* [comment removed for export] *).
    Proof.
      intros W Lx hc mA mB moc HHc HTc HS MU WM HW.
      eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact CEIL | exact MU | exact WM |].
      intros a Ha Hna. destruct (HW a Hna) as [H1|[H2|H3]]; [left; rewrite HTc; pose proof LOSP; lia| |].
      - destruct (CW1 a ltac:(lia)) as [C|[C|(b & Hb & Hr)]]; [left; rewrite HTc; exact C| right; left; exact C| right; right; exists b; split; [apply HS; exact Hb| exact Hr]].
      - destruct (CW2 a ltac:(lia)) as [C|[C|(b & Hb & Hr)]]; [left; rewrite HTc; exact C| right; left; exact C| right; right; exists b; split; [apply HS; exact Hb| exact Hr]].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L56759324319.99 L59308579281.100L59308579414.100L59308730611.102L59310846468.105L59314873579.10400000B00W00l01C02^04FS2sp2PP2AK2bs1a2HaS2sp2PP2AK2bs1a2Ho2H2S2sp2PP2AK2bs1a2Ho2H3S2sp2PP2AK2lo2bs1a1C2H1S1L3HLS2sp2PP2AK3BUF2lo2bs2D12D22D33NZ13NZ24CEIL3SPP3SAK3DS13DS23DS33SPR4SLO21a1b2Hr2H13BceS1L3HLS2sp2PP2AK1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ24CEIL3DHI3SPP3SAK3DS13DS23DS33SPR4SLO21a2C12H1". (* [comment removed for export] *)
    Lemma HPXm : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "PW,(:.$;.)PLx,(:.$<.)Phc,(=.$>.VL,VHI,)PmA,P,(?.&40.)(10.(?.&8.))PmB,P,(?.&40.)(10.(?.&8.))Pmoc,$11.P,(12.$>.VL,VHI,R4.R5.R3.R1.)P,(15.R7.R4.R3.)P,(16.$>.R5.R4.)P,(17.R9.)(18.$>.VL,R9.(19.&40.Vsp,)(1:.(1;.$0.$0.)(1<.$0.$0.VPP,(8.VPP,+8.))(1:.(1;.$0.$0.)(1<.$0.$0.VAK,(8.VAK,+50.))(1=.(1;.$0.$0.))))R7.R6.)")
(* [comment removed for export] *).
    Proof.
      intros W Lx hc mA mB moc HHc MU WM HW a Ha Hc Ho. split; [| apply WM].
      destruct (outside_dec W a) as [O|NO]; [apply MU; rewrite wa_unsigned by lia; exact O|]. exfalso.
      destruct (HW a NO) as [H1|[H2|H3]]; cbn [outside app] in Ho; [| lia| lia].
      flat constr:((heap_blocks usegs L HI _ _ _ _ HHc)) 2%nat. intros BR AP. rewrite Forall_forall in BR.
      destruct Hc as [C|[[C1 C2]|(b & Hb & Hr)]]; [lia| pose proof alloc_ceiling_pos; lia|].
      flat constr:((BR b Hb)) 5%nat. intros _ _ _ Bce _. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26892266857.8900000=S2sp2PP2AK2bs". (* [comment removed for export] *)
    Lemma HPXsub : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "PLx,(:.$<.)PmA,P,(?.&40.)(10.(?.&8.))PmB,P,(?.&40.)(10.(?.&8.))P,(18.$>.VL,R3.(19.&40.Vsp,)(1:.(1;.$0.$0.)(1<.$0.$0.VPP,(8.VPP,+8.))(1:.(1;.$0.$0.)(1<.$0.$0.VAK,(8.VAK,+50.))(1=.(1;.$0.$0.))))R2.R1.)P,Pb,$<.P,(14.$<.R1.VLB,)(14.$<.R2.R6.)(18.$>.VL,VLB,(19.&40.Vsp,)(1:.(1;.$0.$0.)(1<.$0.$0.VPP,(8.VPP,+8.))(1:.(1;.$0.$0.)(1<.$0.$0.VAK,(8.VAK,+50.))(1=.(1;.$0.$0.))))R4.R3.)")
(* [comment removed for export] *).
    Proof. intros Lx mA mB HP HS. eapply heap_presx_weaken; [exact HP| exact HS| lia| intros x Hx; exact Hx]. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2415983207.88 L56401084062.88000011022S1L3HLS2sp2PP2AK3BUF2lo2bs2D12D22D33NZ13NZ23DS33SPR4SLO22H02H12H2S1L3HLS2sp2PP2AK3BUF2lo2bs2D12D22D33NZ13NZ23DS33SPR4SLO22H02H12H2". (* [comment removed for export] *)
    Lemma X0_above : fp_above X0 alloc_ceiling.
    Proof. pose proof LOSP. pose proof SPP. pose proof SAK. pose proof CEIL. unfold fp_above. constructor; [cbn; lia| constructor; [cbn; lia| constructor]]. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma L_RETP : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "Pmx,P,(?.&40.)(10.(?.&8.))Pmox,$11.Phx,(=.$>.VL,VHI,)Pnodes,(:.$0.)Pr,$0.Pp',$0.Pk1',(?.&40.)Pk2',(?.&40.)Pk3',(?.&40.)Pk4',(?.&40.)Pct',(?.&40.)Pcp',(?.&40.)Pcl,$0.Pcq,$0.Pcn,$0.Pr1',(?.&40.)Pr2',(?.&40.)Pr3',(?.&40.)Pr4',(?.&40.)Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa1,(?.&40.)Pa2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)P,(1>.$>.R21.)P,(1?.$>.R22.Vlo,(19.&40.Vsp,))P,(20.Vmo,R22.)P,(6.$0.(13.$>.VL,VHI,R22.)(13.$>.VL,VHI,Vh,))P,(1.(2.-3000.R21.)(3.R21.=))P,(21.$>.R26.VPP,(1:.$22.(23.(24.&40.R21.))(1=.$22.)))P,(1.(3.VP,R22.)(3.R22.VEND,))P,(21.$>.R28.VAK,(25.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.))P,(26.(1.(6.$0.R1<.=)(1.(6.$0.R1=.=)(6.(:.$0.)R26.(1=.$0.))))(1.(3.VBUF,R1<.)(1.(3.=R1=.)(3.(8.R1<.R1=.)VEND,))))P,(6.$0.R1<.(27.$0.=R27.))P,(28.$>.L,(:.$22.)$29.R2;.(2:.(1;.$0.$0.)(2;.$0.(1;.$0.$0.)La,$0.(1<.$0.$0.R1.+20.)(2<.$0.R28.))VLB,)R1=.R28.)P,(2=.$0.R29.)P,Px,$0.P,(14.$0.R1.R2;.)PB,$0.Pk,$0.P,(14.(1;.$0.$0.)(1<.$0.$0.R2.R1.)VLB,)(26.(3.(8.R5.+20.)R3.)(3.(8.R3.R2.)R5.))P,(12.$>.VL,VHI,R2<.(2:.(1;.$0.$0.)(2;.$0.(1;.$0.$0.)La,$0.(1<.$0.$0.R1.+20.)(2<.$0.R2;.))VLB,)R2>.R2=.)P,(18.$>.VL,VLB,(19.&40.Vsp,)(1:.(1;.$0.$0.)(1<.$0.$0.VPP,(8.VPP,+8.))(1:.(1;.$0.$0.)(1<.$0.$0.VAK,(8.VAK,+50.))(1=.(1;.$0.$0.))))Vm,R2?.)(2>.$>.R2?.(2?.$>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VAK,VP,VEND,VBUF,Vlo,Vm,Vmo,)(30.(31.Vra,Vsp,Vgp,Vtp,R1=.R1<.R1;.Vs0,Vs1,(24.&40.R2<.)R1:.R19.R18.R17.R16.R15.R14.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(32.Vra,)Vfc,(33.(?.&40.))R30.(34.$>.)))")
(* [comment removed for export] *).
    Proof.
      intros until t6. intros MIx STx MFx HTx Hr HP Hp HA RNG Hcn CH ND APART HHx HPX.
      apply aevtM_done. unfold x509_akid_post. flexi 15%nat. exists mx, mox, hx, r, p', k1', k2', k3', k4', ct', cp', cl, cq, cn, r1', r2', r3', r4', nodes.
      split; [reflexivity|]. split; [exact MIx|]. split; [exact STx|]. split; [exact MFx|]. split; [exact HTx|]. split; [reflexivity|]. split; [exact Hr|].
      split; [exact HP|]. split; [exact Hp|]. split; [exact HA|]. split; [exact RNG|]. split; [exact Hcn|]. split; [exact CH|].
      split; [exact ND|]. split; [exact APART|]. split; [exact HHx|]. exact HPX.
    Qed.

    (* [comment removed for export] *)
    Ltac lxjoin H1 H2 :=
      lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
      lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
        let v := eval vm_compute in (Z.of_nat (cells_size cs1)) in
        let Hj := fresh "J" in
        pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2)) as Hj;
        let He := fresh "E" in
        assert (He : Z.of_nat (cells_size cs1) = v) by reflexivity; rewrite He in Hj; clear He;
        replace A2 with (A1 + v) in H2 by lia;
        specialize (Hj (conj H1 H2)); clear H1 H2; rename Hj into H1; cbn [app] in H1
      end end.
    Ltac join_frame mx := repeat (
      lazymatch goal with Hf0 : rw_cells usegs mx (bv_unsigned sp + -48) ?cs0 |- _ =>
        let v := eval vm_compute in (-48 + Z.of_nat (cells_size cs0)) in
        match goal with Hf1 : rw_cells usegs mx (bv_unsigned sp + v) _ |- _ => lxjoin Hf0 Hf1 end end).
    Ltac join_ak mx := repeat (
      lazymatch goal with Hf0 : rw_cells usegs mx AK ?cs0 |- _ =>
        let v := eval vm_compute in (Z.of_nat (cells_size cs0)) in
        match goal with Hf1 : rw_cells usegs mx (AK + v) _ |- _ => lxjoin Hf0 Hf1 end end).
    (* [comment removed for export] *)
    Ltac ak_fold H :=
      lazymatch type of H with rw_cells ?sg ?mx ?A [C4 ?a1; C4 ?a2; C8 ?a3; C8 ?a4; C4 ?ct; C4 ?cpad; C8 (Z_to_bv 64 ?cl); C8 (Z_to_bv 64 ?cp); C8 (Z_to_bv 64 ?cn); C4 ?b1; C4 ?b2; C8 ?b3; C8 ?b4] =>
        change (rw_cells sg mx A (akid_cells a1 a2 a3 a4 ct cpad cl cp cn b1 b2 b3 b4)) in H end.
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.88L18926747689.88L18926759668.8800001A01N01_S1L3HLS2sp2PP2AK3BUF2lo2bs2D12D22D33NZ13NZ23SPP3SAK3DS13DS23DS33SPR4SLO21a1b1k2HkS2sp2PP2AK2bsS2sp2PP2AK2bs1a1b". (* [comment removed for export] *)
    Lemma zbv_mod : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
    Proof.
      intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
      apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Ltac fix_a0 :=
      lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        lazymatch z with
        | Zpos _ => lazymatch eval compute in (Z.leb (2^63) z) with
                    | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod; reflexivity)
                    | false => idtac end
        | _ => idtac end
      | |- _ => idtac end.
    Ltac flia := first [clear_disj; lia | lia].

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@L1334695741.179 L1334695741.183 L1334695741.224 L1334695741.248 L1334695741.252 L14789088687.154L1482099654.226 L17441117620.227L19031124518.177L19646181967.229L21764763469.176L23235990545.176L23235990545.188L24810705786.226L26014308813.231L2664553326.188 L27162391167.226L2780795112.226 L31956457296.251L34333716422.237L34333716422.263L35814450096.227L38871691206.238L38871691206.264L41498569876.226L42013446918.176L42383770312.176L42383770312.188L43778690714.188L43820278021.187L44010972587.239L44010972587.265L44010972587.267L44401527573.226L45755922349.223L46887374246.223L47571814464.251L48819652978.176L49628145290.227L52310249682.247L53534961806.251L538471885.176  L5647117268.247 L56701504768.223L56899556562.176L56899556562.188L57628698881.229L60842137433.195L60941357179.176L62798430481.176L63288216409.194L63527981816.176L67040211335.226L68130805597.176L68297732052.177L7423311438.226 L808409681.176  L9869200376.226 00000i01b02803103j04]04n05E06407g08;08<08T08d09D09Q09a09n0:;0:H0:U0:b0:o0;<0;I0<;0<<0<L0<Y0<f0=30=@0=M0=Z0?P0@L0@Y0A70AD0BK0C\0Cm0DG0D\0D]0E10EJ0EW0Ek0F`0Fm0GG0GX0H20HJ0H[0IT0IeS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS2sp2PP2AK2lo2bs1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR3ACP5SLO2'4HLS'5CEIL'S2sp2PP2AK2bs3SPPS2sp2PP2AK3BUF2bs2D22D3S2sp2PP2AK1P3END2bs3NZ13NZ23SPR1p2Hp4lxv02H82H9S1L2sp2PP2AK1P3END3BUF2lo2bs2D12D33NZ13NZ23DS33SPR1p2Hp3B1'3B3'5SLO2'4HLS'4SPP'4SAK'4lxv04lxv12H93H102p23Hp21a2Ha1CS2sp2PP2AK2lo2bs3SAKFS2sp2PP2AK3BUF2lo2bs3DS3S2sp2PP2AK2bs2D1S2sp2PP2AK2bs2D13D1'2A02kk2Y12Y2S2sp2PP2AK2bsS2sp2PP2AK2bs2D1S2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK3END3BUF2bs3NZ13NZ23SPR3B3'4lxv04lxv12H9FS2sp2PP2AK2bs2D1S2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS1L2sp2PP2AK1P3END3BUF2lo2bs2D12D22D33NZ13NZ23SPR1p2Hp3B1'3B2'3B3'5SLO2'4HLS'4SPP'4SAK'4lxv04lxv12H93H103H113cl23cq21HS2sp2PP2AK1P3END2bs3NZ13NZ23SPR1p2Hp4lxv04lxv12H93H102p23Hp2S2sp2PP2AK2bsS2sp2PP2AK2bs3NZ13NZ23SPR4AL2'S2sp2PP2AK2bsS2sp2PP2AK1P3END2bs3NZ13NZ23SPR1p2Hp4lxv04lxv13H102p23Hp25lxv173H193H20S2sp2PP2AK1P3END2bs3NZ13NZ23SPR1p2Hp4lxv04lxv13H102p23Hp25lxv175lxv183H153H163H17S2sp2PP2AK2bs3NZ2S2sp2PP2AK2bs5lxv162H53H22S2sp2PP2AK2bs3rv23Hr2FS2sp2PP2AK3BUF2bs2D3S2sp2PP2AK2bs2D13D1'1a2HoS2sp2PP2AK2bsS2sp2PP2AK2lo2bs3SPPS2sp2PP2AK1P3END3BUF2bs3NZ13NZ23SPR1p2Hp3B1'4lxv03H10S2sp2PP2AK2bsS1L2HI2sp1h2PP2AK2bs5SPTOPS2sp2PP2AK2bs3SAKS2sp2PP2AK2bs4lxv04lxv12H8S2sp2PP2AK2bs3lxv2H33H11S2sp2PP2AK2bs3SAKS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR3ACP5SLO2'4HLS'5SP16'5CEIL'S2sp2PP2AK2bs3SAK". (* [comment removed for export] *)
    Lemma L_ISS : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "Pmc,P,(?.&40.)(10.(?.&8.))Pln,(?.&40.)Pk1',(?.&40.)Pk2',(?.&40.)Pk3',(?.&40.)Pk4',(?.&40.)Pct',(?.&40.)Pcp',(?.&40.)Pr1',(?.&40.)Pr2',(?.&40.)Pr3',(?.&40.)Pr4',(?.&40.)Pp,$0.Pj8,(:.(?.&8.))Px1,(?.&40.)Px5,(?.&40.)Px6,(?.&40.)Px7,(?.&40.)Px10,(?.&40.)Px11,(?.&40.)Px12,(?.&40.)Px13,(?.&40.)Px14,(?.&40.)Px15,(?.&40.)Px16,(?.&40.)Px17,(?.&40.)Px28,(?.&40.)Px29,(?.&40.)Px30,(?.&40.)Px31,(?.&40.)P,(12.$>.VL,VHI,Vh,VLB,R1>.Vmo,)P,(18.$>.VL,VLB,(19.&40.Vsp,)(1:.(1;.$0.$0.)(1<.$0.$0.VPP,(8.VPP,+8.))(1:.(1;.$0.$0.)(1<.$0.$0.VAK,(8.VAK,+50.))(1=.(1;.$0.$0.))))Vm,R1?.)P,(1>.$>.R20.)P,(1?.$>.R21.Vlo,(8.(19.&40.Vsp,)-30.))P,(21.$>.R22.(8.(19.&40.Vsp,)-30.)(1:.$22.(35.#8.R15.)(1:.$22.(23.R21.)(1:.$22.(23.Vs2,)(1:.$22.(23.Vs1,)(1:.$22.(23.Vs0,)(1:.$22.(23.Vra,)(1=.$22.))))))))P,(21.$>.R23.VPP,(1:.$22.(23.(24.&40.R17.))(1=.$22.)))P,(1.(3.VP,R18.)(3.R18.VEND,))P,(21.$>.R25.VAK,(25.R23.R22.R21.R20.R1?.R1>.===R1=.R1<.R1;.R1:.))P,(36.$>.R26.VBUF,Vbs,)(2>.$>.Vmo,(2?.$>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VAK,VP,VEND,VBUF,Vlo,Vm,Vmo,)(30.(31.R19.(24.&40.(8.(19.&40.Vsp,)-30.))Vgp,Vtp,R18.R17.R16.(24.&40.VEND,)(24.&40.VPP,)R15.R14.R13.R12.R11.R10.R?.R>.(24.&40.VAK,)Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(24.&40.+2745<.)Vfc,(33.(?.&40.))R27.(34.$>.)))")
(* [comment removed for export] *).
    Proof.
      intros mc ln k1' k2' k3' k4' ct' cp' r1' r2' r3' r4' p j8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HHc HPXc MIc STc FR PPc Hp AKc BYc.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP.
      pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof D1 as D1'. pose proof D2 as D2'. pose proof D3 as D3'. pose proof AL1 as AL1'. pose proof AL2 as AL2'.
      pose proof NZ1 as NZ1'. pose proof NZ2 as NZ2'. pose proof NZ3 as NZ3'. pose proof PPB as PPB'. pose proof AKB as AKB'. pose proof SLO2 as SLO2'. pose proof HLS as HLS'.
      pose proof DHI as DHI'. pose proof DIM1 as DIM1'. pose proof DIM2 as DIM2'. pose proof SP16 as SP16'. pose proof SPTOP as SPTOP'. pose proof SPR as SPR'. pose proof CEIL as CEIL'.
      pose proof SPP as SPP'. pose proof SAK as SAK'. pose proof DS1 as DS1'. pose proof DS2 as DS2'. pose proof DS3 as DS3'.
      pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      pose proof (bytes_at_bound _ _ _ _ BYc) as BB.
      clear MI ST. change (lx_hidden (rw_cells usegs m PP [C8 (Z_to_bv 64 P)])) in HPP.
      change (lx_hidden (rw_cells usegs m AK (akid_cells k1 k2 k3 k4 ct cpad 0 0 0 r1 r2 r3 r4))) in HAK. change (lx_hidden (bytes_at usegs m BUF bs)) in BY.
      unfold akid_cells, seq_cells in AKc. cbn [app] in AKc.
      (* [comment removed for export] *)
      assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
        by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
      lx_run_tac (PLANS [0x28790] [] 80%N [SUM_gettagP]); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      (* [comment removed for export] *)
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) =>
           join_ak mx;
           lazymatch goal with Hm1 : munch ?W1 _ mx, Hw1 : wmono _ _ mx |- _ =>
             let WF1 := fresh "WF" in
             assert (WF1 : wfp W1) by (intros a Hna; cbn [outside] in Hna; flia);
             pose proof (HEAPm _ _ _ _ _ _ HHc eq_refl ltac:(intros b Hb; exact Hb) Hm1 Hw1 WF1) as HH3;
             pose proof (HPXm _ _ _ _ _ _ HHc Hm1 Hw1 WF1) as HPXW;
             assert (HPX3 : heap_presx usegs L LB (bv_unsigned sp) X0 m mx) by (eapply heap_presx_trans; [exact HPXc| exact HPXW]);
             clear Hm1 Hw1 WF1 HPXW
           end;
           lazymatch goal with HA : rw_cells _ mx AK _, HP : rw_cells _ mx PP _, STx : stk _ mx lo (bv_unsigned sp), MIx : mem_inv _ mx |- _ =>
             ak_fold HA; fix_a0;
             eapply (L_RETP mx mo h (@nil Z)); [exact MIx| exact STx| apply mo_frame_refl| reflexivity| flia| exact HP| flia| exact HA
                                               | left; (flsplit; repeat split); reflexivity| reflexivity| reflexivity| constructor| intros x Hx; inversion Hx| exact HH3| exact HPX3]
           end
         | |- _ => idtac end.
      (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => join_frame mx; join_ak mx; set (m1 := mx) in * end.
      lazymatch goal with Hm1 : munch ?W1 _ m1, Hw1 : wmono _ _ m1 |- _ =>
        assert (WF1 : wfp W1) by (intros a Hna; cbn [outside] in Hna; flia);
        pose proof (HEAPm _ _ _ _ _ _ HHc eq_refl ltac:(intros b Hb; exact Hb) Hm1 Hw1 WF1) as HH1;
        pose proof (HPXm _ _ _ _ _ _ HHc Hm1 Hw1 WF1) as HPXW;
        assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) X0 m m1) by (eapply heap_presx_trans; [exact HPXc| exact HPXW]);
        clear Hm1 Hw1 WF1 HPXW HHc HPXc MK BYc PPc AKc STc MIc FR; rename HH1 into HHc; rename HPX1 into HPXc;
        pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK
      end.
      lazymatch goal with HA : rw_cells _ m1 AK _ |- _ => rename HA into AKc end.
      lazymatch goal with HF : rw_cells _ m1 (bv_unsigned sp + -48) _ |- _ => rename HF into FR end.
      lazymatch goal with HP : rw_cells _ m1 PP _ |- _ => rename HP into PPc end.
      lazymatch goal with HX : stk _ m1 lo _ |- _ => rename HX into STc end.
      lazymatch goal with HX : mem_inv _ m1 |- _ => rename HX into MIc end.
      lazymatch goal with HX : bytes_at _ m1 BUF bs |- _ => rename HX into BYc end.
      splitat AKc 4%nat AKS. splitat AKS 5%nat AKR. rename AKc into AK1.
      pose proof SANEXT as SPS. unfold x509_get_san_ext_stmt, U_X509_GET_SAN_EXT in SPS.
      lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (?p1 + ?l1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply aevtM_cut;
      [ eapply SPS with (LB := LB) (PP := PP) (CUR := AK + 24) (P := p1) (END := p1 + l1) (BUF := BUF) (bs := bs) (lo := lo) (h := h);
          rewrite ?USP; try eassumption; try reflexivity; try (is_arith_goal; flia); try (clear - AL1' AL2' SP16' SPR'; Z.div_mod_to_equations; is_arith_goal; lia); try (lazymatch goal with |- _ = _ => f_equal; lia end)
      | ] end.
      all: try (eapply client_wrange_inside; [exact CW2| intros b Hb; exact Hb| lia| lia]).
      all: try (eapply client_wrange_inside; [exact CW1| intros b Hb; exact Hb| lia| lia]).
      clear SPS. intros ms' mo'x PO.
      destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m2 & mo2 & h2 & rv2 & p2 & ct2 & cp2 & cl2 & cq2 & cn2 & nodes
                      & E0 & MI2 & ST2 & MF2 & HT2 & -> & Hr2 & PPc2 & Hp2 & AKS2 & RNG2 & Hcn2 & CH2 & ND2 & APART2 & HH2 & HPX2).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite ?USP in ST2. rewrite ?USP in HPX2. fix_ret 0x274a8.
      assert (XD : forall A0 kk, (A0 + kk <= PP \/ PP + 8 <= A0) -> (A0 + kk <= AK + 24 \/ AK + 56 <= A0) -> disjoint_from [(PP, PP + 8); (AK + 24, AK + 24 + 32)] A0 kk)
        by (intros A0 kk Y1 Y2; cbn; lia).
      clear PPc AKS.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 FR ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as FR'. clear FR. rename FR' into FR.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 AK1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as AK1'. clear AK1. rename AK1' into AK1.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 AKR ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as AKR'. clear AKR. rename AKR' into AKR.
      assert (CRB' : client_range L LB (bv_unsigned sp + -48) BUF (Z.of_nat (length bs))).
      { intros a Ha. destruct (CRB a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      pose proof (heap_presx_bytes_at usegs L _ _ _ _ _ _ _ HPX2 BYc CRB' ltac:(cbn; lia)) as BY2. clear BYc.
      assert (HPXn : heap_presx usegs L LB (bv_unsigned sp) X0 m m2).
      { eapply heap_presx_trans; [exact HPXc|]. eapply heap_presx_weaken; [exact HPX2| intros b Hb; exact Hb| lia|]. intros a Ho. cbn [outside] in Ho |- *. lia. }
      clear HPXc HPX2 HHc MK STc MIc. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      rename HT2 into HTn.
      assert (RNG2' : (cq2 = 0 /\ cl2 = 0 /\ nodes = []) \/ (BUF <= cq2 /\ 0 <= cl2 /\ cq2 + cl2 <= END)) by (destruct RNG2; [left; assumption| right; lia]). clear RNG2. rename RNG2' into RNG2.
      unfold seq_cells in AKS2.
      (* [comment removed for export] *)
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
      lx_run_tac (PLANS (@nil Z) [(0x27500, DSplit)] 80%N [SUM_gettagP]); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      (* [comment removed for export] *)
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) =>
           join_ak mx;
           lazymatch goal with Hm1 : munch ?W1 _ mx, Hw1 : wmono _ _ mx |- _ =>
             let WF1 := fresh "WF" in
             assert (WF1 : wfp W1) by (intros a Hna; cbn [outside] in Hna; flia);
             pose proof (HEAPm _ _ _ _ _ _ HH2 HTn ltac:(intros b Hb; apply in_or_app; right; exact Hb) Hm1 Hw1 WF1) as HH3;
             pose proof (HPXm _ _ _ _ _ _ HH2 Hm1 Hw1 WF1) as HPXW;
             assert (HPX3 : heap_presx usegs L LB (bv_unsigned sp) X0 m mx)
               by (eapply heap_presx_trans; [exact HPXn| eapply HPXsub; [exact HPXW| intros b Hb; apply in_or_app; right; exact Hb]]);
             assert (CH3 : seq_chain usegs (fun _ => True) mx (map (fun a => (a, 32)) (rev nodes) ++ LB) cn2 nodes)
               by exact (chain_presx' usegs L _ _ _ _ _ _ _ _ _ alloc_ceiling _ _ CH2 ltac:(intros x Hx; eapply chain_nodes_in; [exact CH2| exact Hx]) HPXW
                          ltac:(unfold SEQ_SIZE; lia) ltac:(eapply blocks_below_of_HEAP; exact HH2) X0_above);
             clear Hm1 Hw1 WF1 HPXW
           end;
           lazymatch goal with HA : rw_cells _ mx AK _, HP : rw_cells _ mx PP _, STx : stk _ mx lo (bv_unsigned sp), MIx : mem_inv _ mx |- _ =>
             ak_fold HA; fix_a0;
             eapply (L_RETP mx mo2 h2 nodes); [exact MIx| exact STx| exact MF2| exact HTn| flia| exact HP| flia| exact HA
                                               | exact RNG2| exact Hcn2| exact CH3| exact ND2| exact APART2| exact HH3| exact HPX3]
           end end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00K0@L1334695741.162 L1334695741.166 L1334695741.192 L1334695741.196 L1334695741.197 L1334695741.198 L14789088687.127L19031124518.160L19031124518.164L31378308326.137L31946055504.195L31946055504.196L43059577915.135L47569862720.164L47569862720.195L47569862720.196L52295489746.190L52295489746.195L52295489746.196L53520136334.194L53520136334.195L5645198292.190 L60842137433.209L60842137433.212L63288216409.208L63288216409.211L68297732052.16000000i01b02[03T04M05F06906W07507B07O07\08108>08K08X09M0:B0;80<60=30=M0=Z0=g0>40>A0>YS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR5SLO2'4HLS'4SPP'4SAK'1a3HnaS1L2sp2PP2AK2lo2bs3NZ13NZ23SPR3ACP5SLO2'4HLS'5CEIL'S2sp2PP2AK1P3END2bs4lxv02H82H9S2sp2PP2AK1P3END2bs4lxv02H82H9S2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2lo2bs4LOSPS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK1P3END2bs3NZ13NZ23SPR4lxv05lxv172H93H103H18S2sp2PP2AK1P3END2bs3NZ13NZ23SPR4lxv05lxv172H63H153H23S2sp2PP2AK1P3END2bs3NZ13NZ23SPR4lxv05lxv173H123H133H21S2sp2PP2AK1P3END2bs3NZ13NZ23SPR4lxv05lxv175lxv182H62H93H113H21S2sp2PP2AK1P3END2bs3NZ13NZ23SPR4lxv05lxv175lxv182H72H82H93H19S2sp2PP2AK2bs5lxv162H43H12S2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bsS2sp2PP2AK2bs3lxv2H33H11". (* [comment removed for export] *)
    Lemma ENTRY : ltac2:(CDefT.buildp (gd_tbl_P_x509_akid ()) "Pt0,(?.&40.)Pt1,(?.&40.)Pt2,(?.&40.)Pa3,(?.&40.)Pa4,(?.&40.)Pa5,(?.&40.)Pa6,(?.&40.)Pa7,(?.&40.)Pt3,(?.&40.)Pt4,(?.&40.)Pt5,(?.&40.)Pt6,(?.&40.)(2>.$>.Vmo,(2?.$>.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VAK,VP,VEND,VBUF,Vlo,Vm,Vmo,)(30.(31.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(24.&40.VPP,)(24.&40.VEND,)(24.&40.VAK,)R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(24.&40.+27358.)Vfc,(33.(?.&40.))Vm,(34.$>.)))")
(* [comment removed for export] *).
    Proof.
      intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP.
      pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof D1 as D1'. pose proof D2 as D2'. pose proof D3 as D3'. pose proof AL1 as AL1'. pose proof AL2 as AL2'.
      pose proof NZ1 as NZ1'. pose proof NZ2 as NZ2'. pose proof NZ3 as NZ3'. pose proof PPB as PPB'. pose proof AKB as AKB'. pose proof SLO2 as SLO2'. pose proof HLS as HLS'.
      pose proof DHI as DHI'. pose proof DIM1 as DIM1'. pose proof DIM2 as DIM2'. pose proof SP16 as SP16'. pose proof SPTOP as SPTOP'. pose proof SPR as SPR'. pose proof CEIL as CEIL'.
      pose proof SPP as SPP'. pose proof SAK as SAK'. pose proof DS1 as DS1'. pose proof DS2 as DS2'. pose proof DS3 as DS3'.
      pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as USP.
      pose proof BY as BYc. pose proof HH as HHc. pose proof ST as STc. pose proof MI as MIc. pose proof HPP as PPc. pose proof HAK as AKc.
      pose proof (bytes_at_bound _ _ _ _ BYc) as BB.
      change (lx_hidden (rw_cells usegs m PP [C8 (Z_to_bv 64 P)])) in HPP.
      change (lx_hidden (rw_cells usegs m AK (akid_cells k1 k2 k3 k4 ct cpad 0 0 0 r1 r2 r3 r4))) in HAK. change (lx_hidden (bytes_at usegs m BUF bs)) in BY.
      change (lx_hidden (stk usegs m lo (bv_unsigned sp))) in ST. change (lx_hidden (mem_inv usegs m)) in MI.
      unfold akid_cells, seq_cells in AKc. cbn [app] in AKc.
      (* [comment removed for export] *)
      carve_frame 48%nat STc.
      (* [comment removed for export] *)
      assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
        by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
      lx_run_tac (PLANS [0x2745c] [(0x27500, DSplit)] 100%N [SUM_gettagP]); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      (* [comment removed for export] *)
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) =>
           join_ak mx;
           lazymatch goal with Hm1 : munch ?W1 _ mx, Hw1 : wmono _ _ mx |- _ =>
             let WF1 := fresh "WF" in
             assert (WF1 : wfp W1) by (intros a Hna; cbn [outside] in Hna; flia);
             pose proof (HEAPm _ _ _ _ _ _ HHc eq_refl ltac:(intros b Hb; exact Hb) Hm1 Hw1 WF1) as HH3;
             pose proof (HPXm _ _ _ _ _ _ HHc Hm1 Hw1 WF1) as HPX3;
             clear Hm1 Hw1 WF1
           end;
           lazymatch goal with HA : rw_cells _ mx AK _, HP : rw_cells _ mx PP _, STx : stk _ mx lo (bv_unsigned sp), MIx : mem_inv _ mx |- _ =>
             ak_fold HA; fix_a0;
             eapply (L_RETP mx mo h (@nil Z)); [exact MIx| exact STx| apply mo_frame_refl| reflexivity| flia| exact HP| flia| exact HA
                                               | left; (flsplit; repeat split); reflexivity| reflexivity| reflexivity| constructor| intros x Hx; inversion Hx| exact HH3| exact HPX3]
           end
         | |- _ => idtac end.
      (* [comment removed for export] *)
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x2745c) _ _ ?mx _) =>
           join_frame mx; join_ak mx;
           lazymatch goal with Hm1 : munch ?W1 _ mx, Hw1 : wmono _ _ mx |- _ =>
             let WF1 := fresh "WF" in
             assert (WF1 : wfp W1) by (intros a Hna; cbn [outside] in Hna; flia);
             pose proof (HEAPm _ _ _ _ _ _ HHc eq_refl ltac:(intros b Hb; exact Hb) Hm1 Hw1 WF1) as HH3;
             pose proof (HPXm _ _ _ _ _ _ HHc Hm1 Hw1 WF1) as HPX3;
             clear Hm1 Hw1 WF1
           end;
           lazymatch goal with HA : rw_cells _ mx AK _, HF : rw_cells _ mx (bv_unsigned sp + -48) _, HP : rw_cells _ mx PP _, STx : stk _ mx lo _, MIx : mem_inv _ mx, HB : bytes_at _ mx BUF bs |- _ =>
             ak_fold HA;
             eapply L_ISS; [exact HH3| exact HPX3| exact MIx| exact STx| exact HF| exact HP| flia| exact HA| exact HB]
           end
         | |- _ => idtac end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  Theorem U_x509_akid_spec : x509_akid_stmt usegs L HI U_X509_AKID.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB PP AK P END BUF lo bs
           k1 k2 k3 k4 ct cpad r1 r2 r3 r4
           HH HPP HAK BY B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO CEIL SPTOP SP16 DHI DIM1 DIM2 SPP SAK DS1 DS2 DS3 CW1 CW2 CRB TP MI -> -> ->.
    unfold U_X509_AKID.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    eapply ENTRY; try eassumption.
  Qed.
End Walk.
