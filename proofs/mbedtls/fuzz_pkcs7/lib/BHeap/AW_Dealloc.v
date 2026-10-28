(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AW_HdrBits.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P005ba81eec080ab4 0 2 0 1 22 1P00a5bcbac5b1668e 0 4 0 16 47 16 56 16 57 16P00b55d2037f6e91c 0 2 0 1 22 1P00d161f852cc6ad1 0 4 0 16 55 16 56 16 57 16P0126f87e07ac121e 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P01609fe97d061707 2 49 0 4 0 16 1 16 60 16 61 16 0 5 0 16 2 16 51 16 60 16 61 16P02e7dd83226b0110 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P030091c86925fc28 0 4 0 1 49 1 58 1 59 1P030179315326295d 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P03074ad05887a351 0 2 0 1 22 1P0350e390f7e487a3 0 4 0 1 49 1 58 1 59 1P03510b7b87d1fbf8 0 4 0 16 47 16 56 16 57 16P0376dc319d27b1a2 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P03d95ca2bf15b415 0 4 0 16 47 16 56 16 57 16P047be231a86555e8 0 2 0 1 22 1P04b331b5068d526e 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P04de950c4562da0f 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P04e7cd610e08ce90 0 2 0 1 53 1P052f6910371853be 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P0530ab26a0579168 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P05c9dcbd9636aea4 0 2 0 1 22 1P05deedc648a6ce84 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P05f7412588b1c713 0 4 0 16 47 16 56 16 57 16P07015ff69cb9693a 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P072e11e3bb00363c 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P07d36b8fb11237a9 0 2 0 1 22 1P07d83d11439734f6 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P07e958744fec149e 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P081398dc9e77130e 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P0878e7846a335cad 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P087dce45faa6f348 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P089d7e7dbb2d474d 1 1 16 2 1 1 59 1 5 48 1 50 1 51 1 60 1 61 16P094a2ab3ee7ea969 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P09afb24ece3c1598 0 4 0 16 47 16 56 16 57 16P0a1173d9522a7009 0 2 0 1 22 1P0a32bd38e1f90635 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P0a4cbbe754597e88 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P0af414c359d25db5 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P0b47ae86ea373c0a 0 2 0 1 40 1P0b7bf41b6ae2dc33 2 51 1 1 16 3 1 1 61 1 62 1 4 0 1 60 1 63 1 64 16 1 2 16 3 2 1 60 1 63 1 16 4 0 1 51 1 61 1 62 1 2 64 1 65 1P0b9267d69abbd551 1 1 16 2 0 1 56 1 3 55 1 57 1 58 16P0bb44fe8bf4d7643 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P0be30d14c771b5bf 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P0c020ed8480dc4ac 0 4 0 16 47 16 56 16 57 16P0c6bb7f0b19ef6b6 0 4 0 16 47 16 56 16 57 16P0c932d86757a8f1b 2 51 1 1 16 3 1 1 61 1 62 1 4 0 1 60 1 63 1 64 16 1 2 16 3 2 1 60 1 63 1 16 4 0 1 51 1 61 1 62 1 2 64 1 65 1P0dbeb6d5d3238e7c 0 4 0 16 47 16 56 16 57 16P0e0dea53f55099e0 0 2 0 1 22 1P0ef054eb540ecf4c 0 2 0 1 32 1P0f76f59c636eeb56 2 50 0 4 0 16 2 16 60 16 61 16 0 5 0 16 1 16 51 16 60 16 61 16P101cd43a4b7b4d83 1 2 16 3 0 1 60 1 61 1 16 3 1 1 59 1 62 1 2 63 1 64 1P101d09a6528084ae 0 4 0 16 47 16 56 16 57 16P104ee04b1bf6f1b8 0 4 0 16 47 16 56 16 57 16P10e5110675dc879c 0 4 0 1 49 1 58 1 59 1P115bf128d42a5612 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1175fdd9e86a35c6 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P12151c00764173e8 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1245a9a51ca42517 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P12f30a579e0ebde5 0 2 0 1 22 1P136e8b22ff519022 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P13c8547803c233ae 0 4 0 1 49 1 58 1 59 1P1404019c5f5cbe33 0 2 0 1 22 1P1512440c40d0ca06 0 4 0 16 47 16 56 16 57 16P1573f0b07947cfb2 0 4 0 1 49 1 58 1 59 1P1589607571d9429a 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P158b6d3827aaa32b 0 4 0 1 49 1 58 1 59 1P15cfc8d26a7fb4e2 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P15d5eec79fe6b747 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P16146daac57d9a7a 0 2 0 1 51 1P166eac5fdf391de4 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P16de15066a52f367 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P16f03d011a349deb 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P17048ea57caa0f3d 0 2 0 1 22 1P1713aab47c76cee5 0 4 0 16 47 16 56 16 57 16P1761da251dee73b6 0 2 0 1 22 1P177ff6d9f6f54dc8 0 4 0 16 47 16 56 16 57 16P17af0147ed093bb8 0 2 0 1 22 1P1813f7e891c22bd8 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P1827c64cd3997a7f 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1836d41a427e4f1a 0 4 0 16 47 16 56 16 57 16P18aec27925b01b00 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P19024dc2e8e1041a 2 50 0 4 0 16 2 16 60 16 61 16 0 5 0 16 1 16 51 16 60 16 61 16P1a4665104a3962ed 0 2 0 1 22 1P1aa710e2de00142c 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P1aaba25573cd6032 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P1b1de049bb1bee11 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P1b7b38d28996a248 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1b7b3bb819c113fd 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1b9a15e40d423c1f 0 2 0 1 22 1P1be7fb015b934aaa 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P1d672f554e6f6925 2 50 0 4 0 16 2 16 60 16 61 16 0 5 0 16 1 16 51 16 60 16 61 16P1d9340ae5b325bfc 0 2 0 1 22 1P1e2921aa09feb24b 0 4 0 16 47 16 56 16 57 16P1f663acc1202698d 2 50 0 4 0 16 1 16 60 16 61 16 0 5 0 16 2 16 51 16 60 16 61 16P1f829586a090804c 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P2048cfa6444dd0f3 0 4 0 1 49 1 58 1 59 1P204ab770967fc53d 0 4 0 16 47 16 56 16 57 16P2139e0e5db335675 0 4 0 16 47 16 56 16 57 16P219c4684c4bfb2e6 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P219ec34511785697 0 4 0 16 47 16 56 16 57 16P21a5f32956650cce 0 2 0 1 22 1P21c735a529ff1609 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P2240137f30177665 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2272a769b7e29690 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P22ac3ef302726be1 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P22ec4501a286447f 0 4 0 1 49 1 58 1 59 1P23258059ae7e3479 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P234e9aec6b6354cf 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P239d96a47ba367e9 0 2 0 1 22 1P23c928cbc288a5d8 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P23d55f0c2c502ae8 2 50 0 4 0 16 2 16 60 16 61 16 0 5 0 16 1 16 51 16 60 16 61 16P243e8c4588d7ca26 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P247010049b6ce2ba 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P24ae8330b8c114fd 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P24f3190a201689ec 0 4 0 16 47 16 56 16 57 16P25113642714ff43c 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P25b63b03cd0fbfd9 0 4 0 16 47 16 56 16 57 16P260e3f5744fd1ecb 0 4 0 16 47 16 56 16 57 16P26848cefa5ffec10 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P2719d159f3665996 1 2 16 2 0 1 60 1 16 2 1 1 59 1 2 61 1 62 1P27580729a32c42fd 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P27ab70a8995833f9 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P2a60d82c3a79d448 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P2a83fc9ebeccfb65 0 2 0 1 22 1P2a97ac166f9ee900 0 4 0 16 47 16 56 16 57 16P2b567239c83a937e 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P2b660f0a303c5a39 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P2b80b4f7dbea5a3a 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P2b8f096d53f8b966 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2c292943cc69c48e 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P2c9ef90664634b01 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P2cc0b233dfd507bc 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P2d4a7b65eb51251e 1 1 16 2 1 1 59 1 5 48 1 50 1 51 1 60 1 61 16P2dbc231d2c875f07 0 2 0 1 22 1P2e7c3285a8b87f7c 0 4 0 1 49 1 58 1 59 1P2e8a597e4846debc 0 4 0 16 47 16 56 16 57 16P2ecff859d4f3d486 0 4 0 1 49 1 58 1 59 1P2ee5e46d5e9202a6 0 2 0 1 52 1P3000a65a60b1ff8f 1 2 16 3 0 1 60 1 61 1 16 3 1 1 59 1 62 1 2 63 1 64 1P303e31a9d3d556cf 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P304551d1c9b019dd 0 2 0 1 22 1P306f50b6efe45b0c 0 4 0 16 47 16 56 16 57 16P3090bdddb274e94e 0 4 0 16 47 16 56 16 57 16P31a6bbbb9ea3105d 2 50 0 4 0 16 1 16 60 16 61 16 0 5 0 16 2 16 51 16 60 16 61 16P31f20c9a32b5ea67 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P320a4b139cb35293 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P3212ff2d56673a9c 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P322fc80fdbff91e6 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P3286ceafdaca1b6b 0 4 0 16 47 16 56 16 57 16P3331103124a2624a 1 1 16 2 54 1 56 1 3 0 1 57 1 58 16P346a35ea6e0613d8 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P34833b4de8e6eca8 0 2 0 1 33 1P3529d81080562819 0 4 0 1 49 1 58 1 59 1P35346c410bc452d6 0 2 0 1 40 1P35681768b4058477 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P35a61eef1350bb15 0 2 0 1 52 1P35c1b7cecf074cc5 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P35d7001a234e874d 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P363ea3a56f346507 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P367c8437f978c35b 0 2 0 1 22 1P36f77ec0e7d61677 0 2 0 1 22 1P3715c6c70431574b 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P3776ac5082cf6594 1 1 16 2 1 1 59 1 5 48 1 50 1 51 1 60 1 61 16P3796a6e8c58e68ec 0 4 0 1 49 1 58 1 59 1P3895da7def592ca1 2 49 0 4 0 16 1 16 60 16 61 16 0 5 0 16 2 16 51 16 60 16 61 16P38a7efb639a7199f 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3955d51c18fe793d 0 2 0 1 22 1P398944cf1f724885 2 49 1 1 16 3 1 1 59 1 60 1 4 0 1 58 1 61 1 62 16 1 2 16 3 2 1 58 1 61 1 16 4 0 1 49 1 59 1 60 1 2 62 1 63 1P398c5f7746176dc5 2 47 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P39d0af93f548e2de 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3a9a99539d3e8370 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3ad612f5ab4ca985 0 4 0 1 49 1 58 1 59 1P3b28ee676ab53e88 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3b4f36574e432719 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3ba65da91f80d16f 0 4 0 16 47 16 56 16 57 16P3bc44d9d032995a3 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3bc5d75a578c90dd 0 4 0 16 47 16 56 16 57 16P3bcd1cbcd296d36a 0 4 0 16 47 16 56 16 57 16P3bd6efda9c19bb81 0 4 0 1 49 1 58 1 59 1P3c0f1a7ee2d5ff97 0 4 0 16 47 16 56 16 57 16P3cdded390a1d04e2 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3d0c3d20f5e08e73 0 4 0 16 47 16 56 16 57 16P3d2c8fa0aaef0479 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3dd62b2d4e81e3e1 2 48 0 4 0 16 1 16 58 16 59 16 0 5 0 16 2 16 49 16 58 16 59 16P3e29e97474b1658f 1 1 16 2 1 1 59 1 5 48 1 50 1 51 1 60 1 61 16P3e306770801840e1 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3e428eeb613b1c6d 1 2 16 3 0 1 58 1 59 1 16 3 1 1 57 1 60 1 2 61 1 62 1P3f71d1c0b2f16b7c 1 1 16 2 1 1 57 1 5 46 1 48 1 49 1 58 1 59 16P3f9dd1a0de4a4a9c 0 4 0 16 47 16 56 16 57 16P3fd02a8985a2916b 0 4 0 16 47 16 56 16 57 16N001a3d4936f0c437N09a193b5d317ad56N0dd6d7a29e61e63cN105f958847aa6af3N1c116f0e4a7c9a20N1d2973b69985df5dN1d2c300c067a53e1N3f3957d8dcf5c619"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Dealloc () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "ARUN_1.A_MFHOOKS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "ARUN_1.Dealloc.dealloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.A_QCHUNK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "ARUN_1.Dealloc.hdr_w0"; "ARUN_1.Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Dealloc.dealloc_post"; "ARUN_1.A_ASAN_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Definition A_ASAN_FREE : Z := 0x47758.       (* [comment removed for export] *)
Definition A_DEALLOCATE : Z := 0x47780.      (* [comment removed for export] *)
Definition A_QCHUNK : Z := 0x4bafc.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_MFHOOKS : Z := 0x19b4c0.        (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L17543612044.5L24890855979.4L29784460545.4L37157878596.400000800;00>00DS1q2Hq1ES1qS1qS1q2Hq". (* [comment removed for export] *)
#[using="Type"] Lemma shl3_mod32 : ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "Pq,$0.P,(1.(2.+10.R1.)(3.R1.(4.+2.+3<.)))P,(5.$0.(6.R2.+10.)=)(5.$0.(6.(6.(7.(8.R3.-10.)+3.)+10000000000000000.)+20.)=)")
(* [comment removed for export] *).
Proof.
  intros q Hq Hm. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  rewrite (Z.mod_small ((q + -16) * 8) 18446744073709551616) by lia.
  pose proof (Z.div_mod q 16 ltac:(lia)) as E. rewrite Hm, Z.add_0_r in E.
  replace ((q + -16) * 8) with ((q / 16 * 4 - 4) * 32) by lia.
  apply Z_mod_mult.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L13078707876.5L20391215652.5L23947859748.5L27302457625.5L41891555196.5L50653792827.5L53519162560.5L63368326780.5L65502422012.500000=00J00W00^00_00f00g00h00iS2st2b12Hs2HbS2st2b12Hs2HbS2st2b12Hs2HbS2st2HsSS2b12HbSSS". (* [comment removed for export] *)
#[using="Type"] Lemma w0_bytes : ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "Pst,$0.Pb1,$0.P,(1.(2.=R2.)(3.R2.+100.))P,(1.(2.=R2.)(3.R2.+100.))(5.(9.(:.&8.))(;.(<.$=.(>.(?.&40.(8.R4.(10.+100.R3.))))(11.$=.)))(;.(<.$=.(12.(?.&8.R4.))(<.$=.(12.(?.&8.R3.))(<.$=.(13.(?.&40.=))(11.$=.))))))")
(* [comment removed for export] *).
Proof.
  intros st b1 Hs Hb. cbn -[Z_to_bv Z.shiftr bv_unsigned Z.add Z.mul]. unfold le4, le2. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia.
  replace (8 + 8 + 8) with 24 by reflexivity. replace (8 + 8) with 16 by reflexivity.
  rewrite (w0_shiftr8 st b1) by lia.
  replace (Z.shiftr (st + 256 * b1) 16) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  replace (Z.shiftr (st + 256 * b1) 24) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  try change (Z.shiftr 0 8) with 0.
  f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mul_comm, Z_mod_plus_full. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Dealloc.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Ltac bytes_eq := vm_compute; repeat (first [reflexivity | apply f_equal2; [apply bv_eq; vm_compute; reflexivity|] ]).

  (* [comment removed for export] *)
  Definition dealloc_statics (m : mem) (T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "(1.(14.$15.O3.(8.$16.+8.)(<.$=.(17.(?.&40.=))(11.$=.)))(1.(14.$15.O3.$18.(<.$=.(12.(?.&8.+1.))(<.$=.(19.#3.(<.(:.&8.)(?.&8.=)(<.(:.&8.)(?.&8.=)(<.(:.&8.)(?.&8.=)(11.(:.&8.))))))(<.$=.(>.(?.&40.=))(11.$=.)))))(1.(14.$15.O3.$1:.(<.$=.(17.(?.&40.$1;.))(11.$=.)))(1.(14.$15.O3.$1;.(<.$=.(17.(?.&40.O1.))(11.$=.)))(14.$15.O3.(8.O1.+98.)(<.$=.(17.(?.&40.O2.))(11.$=.)))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1865422044.18 L44183453586.18L47891561692.18L65686408412.1800000500:00?00DS3CTXS3CTXS3CTXS3CTX". (* [comment removed for export] *)
  #[using="Type"] Lemma dealloc_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "PW,(9.$1<.)Pm,P,(:.&40.)(1=.(:.&8.))Pm',P,(:.&40.)(1=.(:.&8.))PT,$0.PCTX,$0.P,(1>.R4.R2.R1.)P,(1?.R6.R5.R4.)P,PA,$0.Pn,$0.P,(20.(1.(2.+10000.R2.)(2.(8.R2.R1.)+65?000.))(1.(2.R5.R2.)(2.(8.R2.R1.)(8.R5.+10000.))))(21.R:.R3.R2.)(1>.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' T CTX (H1 & H2 & H3 & H4 & H5) MU HW. unfold dealloc_statics.
    unfold A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply HW; cbn; lia]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hdr_w0 (b1 st : Z) : list cell := [C1 (Z_to_bv 8 st); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0)].
  Definition hdr_rest (n ctx : Z) : list cell := [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 ctx); C4 (Z_to_bv 64 0)].

  Definition dealloc_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (p b1 n ctx STK T CTX lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "Lms',$22.(23.(:.&40.)La4,(:.&40.)(23.(:.&40.)La5,(:.&40.)(23.(:.&40.)La6,(:.&40.)(23.(:.&40.)La7,(:.&40.)(23.P,(:.&40.)(1=.(:.&8.))Lm',P,(:.&40.)(1=.(:.&8.))(23.(:.&40.)Lfr,(:.&40.)(23.(:.&40.)Lfd,(:.&40.)(1.(5.$22.R8.(24.(25.O21.(?.&40.O22.)O20.O1?.O1>.O1=.O1<.O1;.O1:.(?.&40.$26.)(?.&40.(8.O;.-10.))(?.&40.O;.)(?.&40.O7.)R7.R6.R5.R4.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.)O3.(?.&40.$27.)O2.(28.(:.&40.))R3.(29.$15.)))(1.(1?.(<.(2:.$0.$0.)(2;.$0.$0.O4.O22.)(<.(2:.$0.$0.)(2;.$0.$0.(8.O;.-10.)(8.O;.-<.))(<.(2:.$0.$0.)(2;.$0.$0.O;.(8.O;.+8.))(<.(2:.$0.$0.)(2;.$0.$0.(8.O6.+;08.)(8.O6.+;18.))(11.(2:.$0.$0.))))))O1.R3.)(1.(2<.$15.O1.R3.)(1.(2=.$15.R3.)(1.(2>.$15.R3.(8.O;.-10.)(2?.O:.+3.))(1.(2>.$15.R3.(8.O;.-<.)(30.O9.O8.))(1.(31.$15.R3.O;.+8.)(1.(2>.$15.R3.(8.O6.+;08.)(<.$=.(17.R2.)(<.$=.(17.R1.)(11.$=.))))(1.(1>.R3.O6.O5.)(32.$15.R3.O4.O22.)))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01B0?L1056275518.94 L10784698996.95L11445324318.2 L12589264321.86L12695979950.2 L12805155708.2 L14741499711.92L15224599902.2 L1555683342.1  L1606347861.3  L1606357609.84 L1606357609.86 L17121661550.1 L21974834876.2 L22226590958.2 L22507260528.84L22849952430.2 L22976972249.2 L24483416543.94L26611325086.88L27261505630.2 L27845984990.1 L27978445922.4 L28305712366.1 L28725181897.94L3101466734.2  L32380043246.2 L33279717086.2 L33440425483.69L35345641229.86L36393577245.86L3678621114.93 L36948825479.3 L37062834750.94L37503361981.0 L38910744638.94L39280637297.0 L39571770052.86L39661134997.1 L40470627348.69L40941630867.84L41108346172.2 L44257990206.94L46505744276.69L47283722713.2 L47537723752.2 L48014437652.92L48028616681.4 L49225653524.92L49675611225.2 L49698585326.91L50651538139.2 L51190348121.95L51261130812.2 L51597325913.86L52617098601.92L52630056116.93L52722919865.96L53973597772.2 L5427150238.2  L54956670810.86L55606901317.2 L55715368077.86L56958148372.92L57009295037.85L57329752985.94L58334071645.94L58525224084.69L58527319883.67L61000445529.94L61663247420.87L62282468142.2 L62426986254.1 L6333114222.1  L63832040221.4 L66494272637.86L668819343.96  L68127895326.2 L7990672400.86 L8187326371.96 L9407832852.92 L9999919166.85 00000=00J00K00l00m01501Q01R01V01_01l02<02@02A02B02I02J02K03Y03c03d03e03n03o04R04S04T04U04f05005105A05D05Q05R05_05`05g05k06<06C06D06Q06b06c06d07C07L07k07l08B08J08T08U09609C09P0:L0:T0:U0:_0:g0;10;P0;W0;a0<B0<S0<d0<n0=?0=@0=D0=H0=Q0=X0=i0=j0>40>C0>b0>iS3hAR2SP1p2P0S3hAR2SP1p2P0FS3hAR2SP1p2b12lo2P03B1B5LOIMG3SPLFS2b13B1BS3hAR2SP1p2b12HB5Ha_st5Hl_stFS2SPS1p2P02P1S3hAR1p2P02P1S3hAR2SP1p2P02P1S2SPFFS3hAR1pFSS3hAR2SP1p2b11T3CTX2lo2P02PA2TP2CP5LOIMG3SPL3SPA4SEP14SEP24SEP32HB5Ha_st5Hl_stS3hAR2SP1pFFS1p2P02PAFS3hAR2SP1p2b13CTX2CP2HB5Ha_st5Hl_stFFFS3hAR2SP1p2lo3SPLS3hAR2SP1pFS3hAR2SP1p2P02HBS1pS3hAR2SP1p2P0SS3hAR2SP1p2P0SS3hAR1pS2SPS3hAR2SP1p2lo3SPLS3hAR1pFS3hAR2SP1p2P0S3hAR2SP1p2lo3SPLSFS3hAR2SP1p2b12P02HB5Ha_st5Hl_stS1p2P02PAS3hAR2SP1p2b12P02HB5Ha_st5Hl_stSS3hAR2SP1p2P12HB5Ha_stS2b13B1BS3hAR2SP1pFS3hAR2SP1p2lo2P02PA5LOIMG3SPL3SPAS3hAR2SP1p2P1S3hAR2SP1p2P1S3hAR2SP1p1T3CTX2lo2P02PA2TP2CP5LOIMG3SPL3SPA4SEP14SEP24SEP3S2b13B1BFS3hAR2SP1pS2b13B1BS3hAR2SP1pS3hAR2SP1p2b12P02HB5Ha_st5Hl_stS3hAR1pS3hAR2SP1pS3hAR2SP1p2b11T2TP2HB5Ha_st5Hl_stS3hAR2SP1p2lo3SPLS3hAR2SP1p2lo3SPLS3hAR2SP1pS3hAR2SP1p2b13B1BFS2SPS2SPS1p2P02P1S3hAR1pS3hAR2SP1p3CTX2CPFS3hAR2SP1pS3hAR2SP1p1T2TPS3hAR2SP1p2b12P02HB5Ha_st5Hl_stS3hAR1p". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dealloc_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "Pra,(:.&40.)Pgp,(:.&40.)Ptp,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Ps0,(:.&40.)Ps1,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Ps2,(:.&40.)Ps3,(:.&40.)Ps4,(:.&40.)Ps5,(:.&40.)Ps6,(:.&40.)Ps7,(:.&40.)Ps8,(:.&40.)Ps9,(:.&40.)Ps10,(:.&40.)Ps11,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)PSP,$0.Pp,$0.Pb1,$0.Pn,$0.Pctx,$0.PSTK,$0.PT,$0.PCTX,$0.Plo,$0.Pfr,(:.&40.)Pfd,(:.&40.)PF,(33.&5.(:.&40.))Pfc,(:.&20.)Pm,P,(:.&40.)(1=.(:.&8.))P,(2.(8.+65?000.+10.)R=.)P,(2.(8.R>.+8.)(4.+2.+2?.))P,(5.$0.(6.R?.+10.)=)P,(1.(2.=R>.)(3.R>.(4.+2.+20.)))P,(1.(2.=R>.)(3.R>.(4.+2.+20.)))P,(1.(2.=R>.)(3.R>.(4.+2.+40.)))P,(1.(2.=R12.)(3.R12.+100.))P,(5.$0.(34.R13.+3.)+1.)P,(2>.$15.R9.(8.R15.-10.)(2?.R14.+2.))P,(2>.$15.R:.(8.R16.-<.)(30.R14.R13.))P,(31.$15.R;.R17.+8.)P,(35.VCS,(8.R18.-10.)+18.)P,(2>.$15.R=.(8.R14.+;08.)(<.$=.(17.R11.)(<.$=.(17.R10.)(11.$=.))))P,(1>.R>.R15.R14.)P,(35.VCS,R16.+1000.)P,(35.VCS,R16.+10000.)P,(1.(2.+1000.R18.)(20.(2.(8.R18.+1000.)+10000.)(2.+65?000.R18.)))P,(2.(8.R19.+1000.)(4.+2.+2?.))P,(2.+65?000.R19.)P,(2.(8.R1:.+10000.)(4.+2.+2?.))P,(20.(2.(8.R1<.+1000.)(36.R21.+10.))(2.(8.R21.+8.)R1<.))P,(20.(2.(8.R1<.+10000.)(36.R22.+10.))(2.(8.R22.+8.)R1<.))P,(20.(2.(8.R1>.+1000.)R1=.)(2.(8.R1=.+10000.)R1>.))P,(32.$15.R18.R1=.R25.)P,(2.(37.VhAR,)R1>.)P,(2.R1?.(36.R27.+60.))P,(2.R28.(4.+2.+3>.))P,(5.$0.(6.R29.+10.)=)P,(20.(2.R2:.(36.R29.+10.))(2.(8.R29.+8.)R22.))P,(20.(2.R2;.R25.)(2.(8.R25.+1000.)R23.))P,(20.(2.R2<.R25.)(2.(8.R25.+10000.)R24.))P,(35.VCS,R25.(36.R2=.R25.))P,(2=.$15.R21.)P,(5.(:.&40.)R48.(?.&40.$38.))(39.$15.VAL,VCS,(3:.R30.R4;.R4:.R49.R48.R47.R46.R45.R44.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R25.R24.R23.)(24.(25.R4;.(?.&40.R30.)R4:.R49.R48.R47.R46.R45.R44.(?.&40.R2?.)(?.&40.R2;.)(?.&40.+1.)R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R25.(?.&40.$3;.)R24.(28.(:.&40.))R23.(29.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx STK T CTX lo fr fd F fc m
      P0 P1 PA NB CB STKB B1B B13 HW0 HW1 WR PCS TST (HK & TSD & TPC & TSA & CTH) TCS CTXCS TB1 TB2 CB1 CB2 TP CP TC ST LOIMG SPL SPH SPA
      SEP1 SEP2 SEP3 SCS MI ->.
    facts. unfold hdr_w0, hdr_rest in *.
    unfold A_ASAN_FREE, A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    change (1684672 + 8) with 1684680 in HK.
    pose proof (munch_refl [(lo, SP); (p + -16, p + -12); (p, p + 8); (T + 2824, T + 2840)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MUp. pose proof (wmono_refl asegs m) as WMp.
    lx_c1_norm. lx_aceil.
    lx_run (PLAN [0x47808] [] 60%N). lx_unhide.
    (* [comment removed for export] *)
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ ?mx lo (SP + -88), FRl : rw_cells _ ?mx (SP + -88) _,
                        H0l : rw_cells _ ?mx (p + -16) _ |- _ =>
      chunk_split FRl 3%nat FRx FR; replace (SP + -88 + 24) with (SP + -64) in FR by (clear; lia);
      lx_release STl FRx ST2; clear FRx STl ST; rename ST2 into ST; replace (SP + -88 + Z.of_nat 24) with (SP + -64) in ST by (clear; lia);
      pose proof (wr_at_transport _ _ _ _ _ WR WMl) as WRl; clear WR; rename WRl into WR;
      assert (MU2 : munch [(lo, SP); (p + -16, p + -12); (p, p + 8); (T + 2824, T + 2840)] m mx) by (eapply munch_weaken; [| exact MUl]; lx_subfp);
      clear MU WM MUl HW0 HW1 TST HK TSD TPC TSA CTH MI; try clear WMp; rename MU2 into MU; rename WMl into WM0; rename H0l into HW0;
      pose proof (wmono_refl asegs mx) as WM
    end.
    zstep. rewrite land_align2 by (clear -P0 P1; lia).
    replace ((p + -16) / 4 * 4) with (p + -16) by (clear -PA P0; pose proof (Z.div_mod (p + -16) 4 ltac:(lia)); lia).
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite !(shl3_mod32 p) by (clear -P0 P1 PA; lia).
    change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 2 0)) with 2. change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
    (* [comment removed for export] *)
    apply (rw_cells_reshape asegs _ (p + -16) _ [C4 (Z_to_bv 64 (2 + 256 * b1))]) in HW0; [| cbn; tauto | apply w0_bytes; clear -B1B; lia].
    zstep. rewrite (sx32_small (2 + 256 * b1)) by (clear -B1B; lia).
    (* [comment removed for export] *)
    zstep. rewrite (w0_land255 2 b1) by (clear -B1B; lia).
    zstep. zstep. zstep. zstep.
    rewrite (w0_lxor 2 b1 3) by (clear -B1B; lia). change (Z.lxor 2 3) with 1.
    rewrite ?Z.mod_small by (clear -B1B; lia). rewrite (w0_land255 1 b1) by (clear -B1B; lia).
    rewrite (w0_lxor 2 b1 1) by (clear -B1B; lia). change (Z.lxor 2 1) with 3.
    match goal with |- context [Z_to_bv 64 ?v] => idtac end.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (wr_at_store_ok asegs _ p 8 0 8 WR ltac:(clear; lia) ltac:(clear; lia)) as SOK.
    zstep.
    change (Z_to_le_bytes 8 18446744069414584320) with (le8 (Z_to_bv 64 18446744069414584320)).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) => pose proof (wr_at_write asegs mx p 8 a bs WR) as WR' end.
    store_done. clear WR. rename WR' into WR.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mx (p + -16) [C4 ?v] |- _ => idtac "HDRW0" v;
      apply (rw_cells_reshape asegs mx (p + -16) _ [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | symmetry; apply w0_bytes; clear -B1B; lia] end.
    zstep. cbv beta. replace (bv_unsigned (Z_to_bv 8 b1)) with b1 by (rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; unfold bv_modulus; clear -B1B; lia).
    zstep. rewrite B13. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with WRx : wr_at _ ?mx p 8 |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx' _) =>
      match goal with MUx : munch _ ?ma mx, WMx : wmono _ ?ma' mx |- _ => lx_hide MUx; lx_hide WMx end;
      pose proof (munch_refl [(lo, SP)] mx) as MUq; pose proof (wmono_refl asegs mx) as WMq end.
    lx_run (PLAN [0x4bafc] [] 80%N). lx_unhide.
    lx_stk_grow lo.
    apply evtA_done. unfold dealloc_post.
    lazymatch goal with MUl : munch _ ?mc ?mx, WMl : wmono _ ?mc' ?mx', WRx : wr_at _ ?mc p 8 |- _ =>
      lx_exs; lx_ands;
      [ lx_mseq
      | eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUl]; lx_subfp]
      | first [ eapply wmono_trans; [exact WM0| exact WMl] | eapply wmono_trans; [exact WM0| eapply wmono_trans; [exact WM| exact WMl]] ]
      | assumption
      | unfold hdr_w0; assumption | unfold hdr_rest; assumption
      | exact (wr_at_transport _ _ _ _ _ WRx WMl)
      | eassumption
      | unfold dealloc_statics, A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; change (1684672 + 8) with 1684680;
        split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption
      | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dealloc_null : ltac2:(CDefT.buildp (gd_tbl_AW_Dealloc ()) "Pra,(:.&40.)Pgp,(:.&40.)Ptp,(:.&40.)Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Ps0,(:.&40.)Ps1,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Ps2,(:.&40.)Ps3,(:.&40.)Ps4,(:.&40.)Ps5,(:.&40.)Ps6,(:.&40.)Ps7,(:.&40.)Ps8,(:.&40.)Ps9,(:.&40.)Ps10,(:.&40.)Ps11,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)PSP,$0.PSTK,$0.Plo,$0.PF,(33.&5.(:.&40.))Pfc,(:.&20.)Pm,P,(:.&40.)(1=.(:.&8.))P,(1.(2.=R5.)(3.R5.(4.+2.+40.)))P,(32.$15.R2.R5.R7.)P,(2.+65?000.R6.)P,(2.R7.(36.R9.+40.))P,(2.R:.(4.+2.+3>.))P,(35.VCS,R9.(36.R;.R9.))P,(2=.$15.R7.)(39.$15.VAL,VCS,Lms',$22.(23.(:.&40.)La0,(:.&40.)(23.(:.&40.)La1,(:.&40.)(23.(:.&40.)La2,(:.&40.)(23.P,(:.&40.)(1=.(:.&8.))Lm',P,(:.&40.)(1=.(:.&8.))(1.(5.$22.R5.(24.(25.R2=.(?.&40.R12.)R2<.R2;.R2:.R29.R28.R27.R26.R4.R3.R2.(?.&40.=)(?.&40.R11.)(?.&40.+1.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R?.(3<.R2=.)R>.(28.(:.&40.))R1.(29.$15.)))(1.(1?.(<.(2:.$0.$0.)(2;.$0.$0.R10.R12.)(11.(2:.$0.$0.)))R=.R1.)(1.(2<.$15.R=.R1.)(1.(2=.$15.R1.)(32.$15.R1.R10.R12.)))))))))(24.(25.R28.(?.&40.R=.)R27.R26.R25.R24.R23.R22.R21.(?.&40.=)(?.&40.R<.)(?.&40.+1.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R:.(?.&40.$3;.)R9.(28.(:.&40.))R8.(29.$15.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP STK lo F fc m
      STKB ST LOIMG SPL SPH SCS MI.
    facts. unfold A_ASAN_FREE.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_post.
  Qed.
End Dealloc.

End ARUN_1.
