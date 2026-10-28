(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_core_mla U_mpi_core_add U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr LxU_SumsEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0021fe3144b4cd0b 1 1 8 3 0 1 56 1 57 1 5 2 1 19 4 55 1 58 1 59 8P0054ec707fd136bc 1 1 4 1 0 1 2 19 1 55 1P00b209c4a7e45903 0 5 0 1 45 1 46 1 53 1 54 1P00e90783f0f5d137 0 3 0 1 19 4 26 4P00e98b9892c8c3f1 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P019d388c28c5113b 1 1 4 4 2 1 27 4 58 1 59 1 7 23 1 48 1 49 1 50 1 57 1 60 1 61 4P01eb63a429ea101d 0 5 0 1 45 1 46 1 53 1 54 1P01f0a5c65e21aad7 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P033d0fb5fc37e685 0 2 0 1 36 1P03fa77c9e1cdc261 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P046fd78ee9a619e7 1 1 8 3 1 1 55 1 58 1 4 2 2 56 2 57 2 59 16P05133d598d513882 0 6 0 1 18 4 20 1 45 1 56 1 57 1P06373143350fb863 1 2 16 2 0 1 55 1 16 2 7 1 56 1 2 57 1 58 1P0662bf64b8c5f35d 0 2 0 1 34 1P066aaa1553ae4617 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P072252db681573bd 0 4 0 16 8 16 55 16 56 16P078b3f9cedf9c24e 0 5 0 1 47 1 48 1 55 1 56 1P07c51f8a028d9408 0 10 0 16 19 64 21 16 46 16 47 16 48 16 55 16 56 16 57 16 58 16P08bc6f7b26c478fd 0 5 0 1 47 1 48 1 55 1 56 1P0919fc757c575bb6 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P09849b7f9f0aafc6 1 1 4 1 0 1 2 19 1 55 1P0996e65992c382bf 0 5 0 1 45 1 46 1 53 1 54 1P0998430e6103a316 0 3 0 1 19 1 26 1P0a51bb7a4c9cd2c6 0 2 0 1 36 4P0af204bf84ef4ed2 0 5 0 1 47 1 48 1 55 1 56 1P0bbf0496550265c6 0 3 0 1 19 1 26 1P0bd7c8f6f6c77de6 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P0d377ec36c69a631 1 1 8 3 1 1 56 1 57 1 6 2 1 47 1 48 1 55 1 58 1 59 8P0d6b125b823d0aa5 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P0d73a5f42b55eb49 1 1 8 3 0 1 55 1 58 1 4 2 1 56 1 57 1 59 8P0e1dc3f02808a12b 1 2 16 3 0 1 57 1 58 1 16 3 1 1 56 1 59 1 2 60 1 61 1P0e7d9422268a058a 0 5 0 1 45 1 46 1 53 1 54 1P0e8f3799d867d67d 1 1 16 3 0 1 55 1 56 1 8 18 4 20 1 45 1 46 1 47 1 54 1 57 1 58 16P0eca5609ab74f2dd 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P0ef35b3e013e61b1 0 5 0 1 45 1 46 1 53 1 54 1P0f4b2c688f3fc7b2 0 2 0 1 34 1P0f83ccef06106aa5 1 1 8 3 1 1 58 1 59 1 6 2 1 49 1 50 1 57 1 60 1 61 8P0fc7a94000d427f9 0 4 0 16 6 16 53 16 54 16P109a03e5f7b125f2 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P119f0d350f39a9d1 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P119f5bc54b13ab64 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P11d8ec951b9698ee 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P1215c7ac5110c7af 0 2 0 1 34 1P1219573984b388d2 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P12204ed25e5a2872 0 3 0 1 19 1 26 1P12e709d665809356 1 1 4 4 1 1 26 4 57 1 58 1 7 22 1 47 1 48 1 49 1 56 1 59 1 60 4P12f0f2842e483e73 1 1 16 3 0 1 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P137fdff0f66d127c 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P13cfcb0fa6865c99 1 2 16 3 0 1 57 1 58 1 16 3 1 1 56 1 59 1 2 60 1 61 1P13d6a29c2ecae6a4 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P1414b569a3e6025b 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P149dfdbc7671eeb0 0 5 0 1 47 1 48 1 55 1 56 1P14da40c0bd89e0f9 0 5 0 1 45 1 46 1 53 1 54 1P1550cca8f294dea7 0 1 1 1P1589a622bdac8f6b 0 5 0 1 45 1 46 1 53 1 54 1P15fbde442815363c 1 1 4 1 0 1 2 17 1 53 1P15fda8b55e43f7ae 1 1 4 1 0 1 2 19 1 55 1P163eccecba67950f 1 1 4 1 0 1 2 19 1 55 1P1660d3d249a613b6 0 2 0 1 34 1P17d9a8c384199172 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P18cbb7d1820cb457 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P18e1b6d67722416a 1 1 4 6 13 1 19 1 44 1 45 1 46 1 53 1 4 0 1 23 4 54 1 55 4P1928bb07ab9f1fb8 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P193332e7a49d7330 1 1 16 4 0 1 34 4 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P1a16d18a120f2aa9 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P1a3040593090e161 0 5 0 1 45 1 46 1 53 1 54 1P1a35b31912b0e18d 0 5 0 1 47 1 48 1 55 1 56 1P1af179ea0b736454 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P1b362635a6042a6e 0 10 0 16 17 64 19 16 44 16 45 16 46 16 53 16 54 16 55 16 56 16P1b9f320937ba82cd 0 8 0 16 17 16 19 4 44 4 45 4 46 4 53 4 56 4P1c9b0a3cfda4891f 1 1 4 1 0 1 3 17 1 24 1 53 1P1d508bd8f180bc26 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P1e7f3da2b4dd261b 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P1ea6c1bba80aaee5 1 1 4 1 0 1 2 19 1 55 1P1eb9b903ead31e68 0 3 0 1 19 1 26 1P1ec572ad2fb7229e 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P1f02c4099544ee2c 0 8 0 16 17 16 19 4 44 4 45 4 46 4 53 4 56 4P1fa81cf6469efefb 0 2 0 1 34 1P203df2c585a6d2bb 0 5 0 1 45 1 46 1 53 1 54 1P20c768d6aef9a884 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P20fb943ea2dec40b 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P216abdb0fcac0da0 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P229711946bdd1724 0 2 0 1 34 4P22a95c44f1df9a73 1 2 16 2 0 1 53 1 16 2 5 1 54 1 2 55 1 56 1P22ad710ad1e76691 0 5 0 1 45 1 46 1 53 1 54 1P22e93890e7acf66c 1 1 4 1 0 1 2 19 1 55 1P239cdedcd6724096 1 1 16 4 0 1 36 4 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P2475aa5bae7a0999 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P24ff681401bcd7bb 0 2 0 1 36 1P2521b9c034f2c549 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P25220eb4acbc9e4b 1 1 16 3 0 1 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P2531de3133fe5cfe 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P25825db2a73f5eb8 0 6 0 1 20 4 22 1 47 1 58 1 59 1P265c12f19e670fd5 1 1 16 3 0 1 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P266ef6de2fac84c9 0 3 0 1 19 1 26 1P267a39356ec3b3ee 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P268ef0336ec2e39d 1 2 16 3 0 1 57 1 58 1 16 3 1 1 56 1 59 1 2 60 1 61 1P26d736d6f5316279 0 3 0 1 17 1 24 1P27e23b4cae871b82 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P281b7ec95c150def 0 3 0 1 19 1 26 1P282c80eae5966b08 0 3 0 1 17 4 24 4P28dd9fb9c3c3fde0 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P293a07358fbe14d4 0 5 0 1 47 1 48 1 55 1 56 1P29a1eda3d243730f 0 10 0 16 17 64 19 16 44 16 45 16 46 16 53 16 54 16 55 16 56 16P29b2637647412a60 1 2 16 3 0 1 57 1 58 1 16 3 1 1 56 1 59 1 2 60 1 61 1P29f4c72f357c738b 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2a38f1b2f7d4e15a 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P2acf386af97b5efe 0 2 0 1 34 1P2aef90398388b469 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P2badb273e0ab27da 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2bb48320916b6aee 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P2c031e2211b40547 0 10 0 16 19 64 21 16 46 16 47 16 48 16 55 16 56 16 57 16 58 16P2d1dba748476a237 1 1 16 2 22 1 56 1 3 0 1 55 1 57 16P2dcc47763c7c17a5 1 1 16 3 0 1 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P2dee1a17e9eb25fd 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P2e584d43d6308377 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P2edf1f59d24f0bd2 1 1 8 3 0 1 57 1 60 1 4 2 1 58 1 59 1 61 8P2effd2dfa69ef435 1 1 4 1 0 1 2 19 1 55 1P2f75b60d65a82710 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P3104817aad869516 0 5 0 1 49 1 50 1 57 1 58 1P31149300d0e2795f 0 3 0 1 19 1 26 1P3158d9a581264417 2 39 1 1 8 3 2 1 56 1 57 1 6 0 1 47 1 48 1 55 1 58 1 59 8 1 1 8 3 1 1 55 1 58 1 4 0 1 56 1 57 1 59 8P315f97eb10a02b31 1 1 16 2 20 1 54 1 3 0 1 53 1 55 16P31f98977c6220662 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P322f11cba0d5ebf2 0 6 0 1 22 1 26 4 47 1 58 1 59 1P3284367e0d20566b 0 6 0 1 20 1 24 4 45 1 56 1 57 1P33e8345c35192b9f 0 8 0 16 19 16 21 4 46 4 47 4 48 4 55 4 58 4P346a2fa35880c758 1 1 16 3 0 1 55 1 56 1 8 18 4 20 1 45 1 46 1 47 1 54 1 57 1 58 16P34fac83c4e221c62 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P361040ff31378779 0 2 0 1 34 1P36595f7e7b8efef5 0 5 0 1 45 1 46 1 53 1 54 1P37822b8892a811e7 1 1 4 1 0 1 2 19 1 55 1P385199b82e88d949 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P3868ec141ad8dbbf 1 1 16 3 0 1 56 1 57 1 8 19 4 21 1 46 1 47 1 48 1 55 1 58 1 59 16P387708d43701637a 2 41 1 1 8 3 2 1 58 1 59 1 6 0 1 49 1 50 1 57 1 60 1 61 8 1 1 8 3 1 1 57 1 60 1 4 0 1 58 1 59 1 61 8P393eafdbe9a20f47 1 2 16 3 0 1 57 1 58 1 16 3 1 1 56 1 59 1 2 60 1 61 1P394558dca78f0d72 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P3945853089180439 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P399877b3ee367b62 1 1 16 3 0 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P3b174c46a4394428 0 3 0 1 19 1 26 1P3b26f4f8af6269b8 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16P3b296d33342a13e3 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P3b70c91f0972d01e 2 20 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16 1 1 8 3 1 1 58 1 59 1 5 0 1 21 4 57 1 60 1 61 8P3b7a09e6a23646c5 1 1 4 4 2 1 25 4 56 1 57 1 7 21 1 46 1 47 1 48 1 55 1 58 1 59 4P3c241b413327af4d 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P3c7c495f49affc33 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P3c9c775cbaa2898f 1 1 8 3 0 1 58 1 59 1 5 2 1 21 4 57 1 60 1 61 8P3cf9d129fe5d7784 0 5 0 1 45 1 46 1 53 1 54 1P3d23d777ff69454f 1 1 8 3 1 1 57 1 60 1 4 2 2 58 2 59 2 61 16P3d39ed422487c92b 1 1 16 3 1 1 58 1 59 1 8 21 4 23 1 48 1 49 1 50 1 57 1 60 1 61 16P3d90b15595586a3d 1 1 4 1 0 1 2 19 1 55 1P3d9dac2bc2f43b54 0 8 0 16 19 16 21 4 46 4 47 4 48 4 55 4 58 4P3db2425e25eb2406 1 1 16 3 0 1 54 1 55 1 8 17 4 19 1 44 1 45 1 46 1 53 1 56 1 57 16P3ea89ff06876bf98 1 2 16 2 0 1 55 1 16 2 7 1 56 1 2 57 1 58 1P3eba029d3a1a1a16 0 3 0 1 19 1 26 1P3fd4a01dcfa64fd1 1 1 16 3 0 1 57 1 58 1 8 20 4 22 1 47 1 48 1 49 1 56 1 59 1 60 16N0059684bff72c839N0640dcc74197fac5N085b42b5c0d490f4N0a4dae6d778af2d9N0a614d38244cf11aN0c88ce9f3ec74df5N0cc380f1459e1786N142758bd8df0604cN169bd6e6fc9f5172N177aadbe2266b7adN1a49d91d75cbfa67N1a671ccd11e92e26N1da134ae73e2a793N25acdcac02f9dc52N261faf7416a34cf7N2760674db86acf73N2925fda591676089N29c79fb701dda7fbN2b45143b5a02a3cdN2e2e6c047921dbbaN2f39ac4dc89518e1N2ff98b3e08ca85ebN319c00fd824af6ebN3374a93ba0f7e304N33d20abcbbabce99N3657242b54e29641N3990283a22458536N3a3295db70fc8451N3a4074f57b777c2eN3b735bd4279cbe76N3d53a32fa6c68d83N3dd4b4d0750cfe68N3ea79c5a70024b9aN3eda642519c64c90N3f9a00f688ca299aN3fe68a406ce331a1"%lxh.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_ECP_MOD_P255 : Z := 0x3d610.

(* [comment removed for export] *)
Ltac ecp_leaf_gc :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | u32arr _ _ _ _ => fail | rw_cells _ _ _ _ => fail | bytes_at _ _ _ _ => fail
    | context [zlow _ _] => clear H | context [zswrap _ _] => clear H | context [Z.b2z _] => clear H
    end end;
  repeat match goal with
  | H : 0 <= ?v + 2147483648 |- _ => is_var v; clear H
  | H : 0 <= - ?v + 2147483647 |- _ => is_var v; clear H
  | H : 0 <= ?v, H' : 0 <= - ?v + 18446744073709551615 |- _ => is_var v; clear H H'
  end;
  repeat match goal with v : Z |- _ => clear v end.

Section RED.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01X0@L10311464405.87 L10754041658.119L11803550370.88 L11805629605.91 L12281286362.116L12295654977.82 L12729394630.120L12738676067.3  L16439777795.87 L16629840431.89 L16629840431.90 L17646078182.80 L19026695374.129L20178898145.114L2129949374.114 L21877859746.116L2211492706.87  L23277783028.86 L24167279349.87 L24354829172.83 L2766785880.117 L2766785880.86  L28689697126.161L28692136132.74 L29012665503.116L30700280390.120L30985055127.108L30985070479.87 L33635213816.117L33637411160.161L3477245036.2   L35170042299.115L36427895709.117L36586472463.89 L36586472463.90 L36926271692.89 L37074418654.1  L38017522480.135L3818668784.87  L3820734411.161 L39026997197.87 L39776992186.119L40357717490.4  L40742132661.120L42548926102.90 L43061838089.78 L44321724939.87 L44622288685.89 L44622288685.90 L46943456961.83 L4742244590.167 L4742244590.168 L4742244590.169 L4742244590.170 L47759495350.167L47759495350.168L47759495350.169L47759495350.170L48268199486.85 L49698585326.89 L49698585326.90 L52102261165.167L52102261165.168L52102261165.169L52102261165.170L5211131508.87  L52616107219.132L52637787608.117L52637787608.87 L53540292277.2  L54179152186.119L54391891673.90 L54392444536.168L54392444536.169L54392444923.169L54392444923.170L54398396379.168L54398396379.169L55569326197.2  L56167005126.120L57628696595.14 L57628700040.8  L59314873579.170L59314873579.171L60092477410.1  L61152579772.83 L61998749328.117L63559401084.120L65346195812.87 L65502165646.74 L65502251305.129L65699637964.166L66523984802.115L67984247860.118L67996633777.87 L68616792782.161L7024252226.167 L7024252226.168 L7922115252.1   L9144264913.87  L921574835.117  L921574835.87   M21892540706.164M8551682078.163 00000N01E02<02o03G03Z04L04M04e05O06906C07:07R07j08V09709O09g0:A0:Y0;10;k0<I0<J0=<0>00>d0?<0?_0?l0@R0A>0B60C10Ca0Cb0Df0EG0F30Fk0Gb0H00HO0I90IW0Io0K50L>0LQ0M90N<0O?0P=0Pm0Q`0RS0SC0Sj0TX0UI0V30V`0WM0X70XO0Y60YN0Yf0Yg0Ze0[`0\c0]f0^j0_n0a10b40b50bg0cS0cl0eF0f\0f`0g30gK0gk0hO0hY0i50i`0jL0jd0k<0k_0lI0m30m70mO0mg0n?0o9103S1L2sp2dX3DHI2XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SX4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SX4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR2I4S2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRLS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR1HFS2sp2dX2XB4junk3FRL4wCARS2ra2sp2dX2XB4junk3FRL4wCAR2HB5Ha_st5Hl_stS2sp2s02dX2XB4junk3FRL4wCAR2HB5Ha_st5Hl_stS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR3dX22B0S2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL4wCARS1L2sp2dX2lo3SLO2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX3SPB2X02XB4junk3FRLS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR1HS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsfS4wCAR6LENCARS2sp2dX3SPB2X02XB4junk3FRL4wCAR6LENCARS1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL4wCARS2ra2sp2dX3SPB2X02XB4junk3FRL4wCAR6LENCAR2HB5Ha_st5Hl_stS2sp2s02dX3SPB2X02XB4junk3FRL4wCAR6LENCAR2HB5Ha_st5Hl_st2s1S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCARFS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XB4junk3FRL4wCARS1L2sp2dX2lo3ACL2XB4junk3FRL3dX22n22P'5lxwsfS1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SX4junk3FRL4wCARS2dX3dX22n22N2S2sp2dX2XB4junk3FRL4wCAR2xx3HxxS2sp2s12dX2XB4junk3FRL4wCAR2HB5Ha_st5Hl_stS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2sp2dX2XB4junk3FRL4wCARS1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB4junk3FRL4wCAR2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB4junk3FRL4wCAR2HB5Ha_st5Hl_st2s1S2sp2dX2XB4junk3FRLS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C1S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB4junk3FRL3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2lo2XB4junk3FRL3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB4junk3FRL3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB4junk3FRL3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB4junk3FRL3dX22n22P'5lxwsf1a2C21n2n0S2sp2dX3SPB2X02XB4junk3FRL4wCAR7LENCAR0S2ra2sp2dX3SPB2XB4junk3FRL4wCAR2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB4junk3FRL4wCAR2HB5Ha_st5Hl_st2s1S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C21nS2sp2dX2XB4junk3FRL4wCARS1L2HI2sp1h2dX2XB4junk3FRL4wCAR3dX21a1CS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARFS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SX4junk3FRL4wCAR6LENCARS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB4junk3FRL4wCAR1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf1a1QFS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB4junk3FRL4wCAR1HS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX4junk3FRL3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX4junk3FRL3dX22n22N22P'2B02B45lxwsf1a2C21l2l02Rb1HS2spS2sp2dX2XB4junk3FRLS2sp2dX2XB4junk3FRL4wCARS1L2sp2dX2XB4junk3FRL4wCAR2I32I4S1L2HI2sp1h2dX4HTOP2XB4junk3FRL4wCARS2sp2dX2XBS2sp2dX2XB4junk3FRL4wCAR3dX2S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a2C12C2S1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsfS2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB4junk3FRL3dX22n22P'5lxwsf1a1l2l0S2spS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS2sp2dX2XB4junk3FRL4wCARS1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XB4junk3FRL3dX22n22P'2B05lxwsf". (* [comment removed for export] *)
  Lemma U_ecp_mod_p255_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P255 U_MEMSET_FUNC 16 128.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P255. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(MA) 2%nat. intros FLt1 _. flat constr:(FLt1) 4%nat. flclear FLt1. intros CH XAL X0 _. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add mpi_cells length] in XB. clear CH.
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 64%nat ST.
    pose proof (proj1 (proj1 FR)) as FRWF. cbn in FRWF. flat constr:(FRWF) 2%nat. flclear FRWF. intros FRL _.
    pose proof (rw_cells_split_CB usegs _ _ [] 64 _ [] [8;32;24]%nat FR eq_refl) as FRS. cbn [mk_CB_cells app] in FRS. clear FR.
    flat constr:((proj1 (rw_cells_app usegs _ _ [CB 8 _] _) FRS)) 2%nat. intros FRg0 FRS'. clear FRS. cbn [cells_size csize Nat.add] in FRS'.
    match type of FRS' with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -56) in FRS' by lia end. rename FRS' into FRS.
    flat constr:((proj1 (rw_cells_app usegs _ _ [CB 32 _] _) FRS)) 2%nat. intros CARc FRS'. clear FRS. cbn [cells_size csize Nat.add] in FRS'.
    match type of FRS' with rw_cells _ _ ?aa _ => replace aa with (bv_unsigned sp + -24) in FRS' by lia end. rename FRS' into FR.
    match type of CARc with rw_cells _ _ ?aa _ => try replace aa with (bv_unsigned sp + -56) in CARc by lia end.
    apply u8arr_of_rw_cells in CARc. destruct (u32arr_of_u8arr usegs _ _ _ 8 CARc ltac:(rewrite ?firstn_length, ?skipn_length; lia)) as (wCAR & UCAR & LENCAR0). clear CARc.
    assert (LENCAR : Z.of_nat (length wCAR) = 8) by lia. clear LENCAR0. pose proof (same_from_refl 8 wCAR) as FSCAR.
    do 7 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (MA1 : mpd_at usegs m1 LB dX).
    { eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; lia|].
      intros O. flat constr:((mpdr_blk_facts usegs L m LB dX (proj1 MA) O HBR)) 5%nat. intros _ _ I3 I4 _. cbn. lia. }
    assert (PX1 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1) by (eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]).
    clear HH MA MU WM.
    (* [comment removed for export] *)
    pose proof (U_mpi_grow_spec L HI HFREE HCALLOC HLS SW DIMG HND) as SG. unfold mpi_grow_stmt, U_MPI_GROW in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 16); rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3d62c)) with (Z_to_bv 64 0x3d62c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OLDL : md_own dX = LHeap -> 0 < md_p dX /\ md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros O. flat constr:((mpdr_blk_facts usegs L m1 LB dX (proj1 MA1) O HBR)) 5%nat. intros _ _ I3 I4 _. lia. }
    presx_stack usegs L PXg ltac:(unfold mpd_ivs; destruct (md_own dX) eqn:?; cbn;
                                 [ split; [lia| exact I] | split; [lia|]; split; [pose proof (OLDL eq_refl); lia| exact I] | exfalso; apply NST; reflexivity ]).
    assert (PX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply (heap_presx_weaken usegs L); [exact PXg| lia| intros x Hx; exact Hx]. }
    clear PX1 ST MI SOK MK HH1 MA1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 _.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & _)|[Er EdX]] FRr]; [exfalso; subst r; apply K; reflexivity|]. subst dX2.
      zstep. zstep. zstep. release_frame FRg0 ST2 (bv_unsigned sp + -56). apply u32arr_cells in UCAR. release_frame UCAR ST2 (bv_unsigned sp + -24). release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 16 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
      flat constr:((grow_ok_facts _ _ _ _ _ _ _ MA2 OUT2 GR ltac:(lia))) 9%nat. intros O2 N2 S2 P2 EA2 LEN IN2 PAL2 U.
      flat constr:((proj1 (Forall_forall _ _) HBR2 _ IN2)) 5%nat. intros B0 _ _ B4 B5. cbn in B0, B4, B5.
      assert (APX : md_addr dX + 16 <= md_p dX2 \/ md_p dX2 + 4 * md_n dX2 <= md_addr dX).
      { eapply (new_limbs_apart_range usegs L HI) with (SP := bv_unsigned sp); [exact HH2| exact MA2| exact OUT2| exact FRr| lia| exact DI1| exact DI2| | lia| exact XP| exact O2].
        intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      flat constr:(MA2) 2%nat. intros (CH2 & _) _. rewrite EA2, S2, P2 in CH2. unfold mpi_cells in CH2.
      set (P' := md_p dX2) in *. set (n2 := md_n dX2) in *. set (ws0 := md_limbs dX2) in *.
      pose proof (u32arr_bound _ _ _ _ U) as UB. assert (PB : P' + 4 * n2 <= 2 ^ 64) by lia. clear UB.
      pose proof (same_from_refl (Z.to_nat n2) ws0) as FS.
      clear MU WM. pose proof (munch_refl [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH0. clear HH2. pose proof (conj MA2 I) as MA0. clear MA2.
      clearbody ws0.
      (* [comment removed for export] *)
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 16 <= n2) by (clear -N2; lia).
      clear MU. pose proof (munch_refl [(P', P' + 4 * n2); (lo, bv_unsigned sp)] m2) as MU.
      pose proof (sumsecp_ok [P']) as LXSUMS.
      apply (lxp_aevtM_of_evt _ _ _ _ MK). lx_mkR.
      lx_run_tac (PLANS [] [] 400%N SUMSECP); lx_tree.
      (* [comment removed for export] *)
      all: try (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
             tryif lx_is_zlit e then fail else
             match goal with H1 : 0 <= e, H2 : 0 <= - e |- _ => replace e with 0 by (clear -H1 H2; lia) end end).
      all: lx_gen_regs; apply evt_done; try clear U; try clear LEN; try clear MU; try clear WM;
        let mx := lx_cur_mem in let xP := constr:(P') in let xm := constr:(m2) in let xlo := constr:(lo) in let xsp := constr:(sp) in
        lazymatch goal with Hu : u32arr _ mx xP ?l |- _ => rename Hu into U;
          assert (LEN : Z.of_nat (length l) = n2)
            by (first [ rewrite ?upd_length; exact (unlock _ LEN0)
                      | lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ => rewrite Hl end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption]
                      | rewrite ?upd_length;
                        lazymatch goal with |- Z.of_nat (length ?l2) = _ => lazymatch goal with Hl : Z.of_nat (length l2) = _ |- _ => rewrite Hl end end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption] ]);
          (* [comment removed for export] *)
          repeat match goal with Hl : Z.of_nat (length _) = Z.of_nat (length _) |- _ => clear Hl end;
          set (lxwsf := l) in U, LEN; clearbody lxwsf; ecp_leaf_gc
        end;
        lazymatch goal with Hm : munch _ xm mx |- _ =>
          assert (MU : munch [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2 mx)
            by (eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia);
          match goal with SO : statics_ok _ _ xm |- _ =>
            eapply (statics_ok_munch usegs L) in SO; [| exact Hm| intros aa Ha _; cbn; clear -Ha B5 DI1 DI2 ACL DHI LO0; lia] end;
          clear Hm end;
        lazymatch goal with Hw : wmono _ xm mx |- _ => rename Hw into WM end;
        try clear ST2; lx_release_frame; lazymatch goal with Hs : stk _ mx xlo ?h |- _ => (tryif constr_eq h (bv_unsigned sp) then idtac else replace h with (bv_unsigned sp) in Hs by (clear; lia)); rename Hs into ST2 end;
        let xa := constr:(md_addr dX) in
        try clear CH2; lazymatch goal with Hc : rw_cells _ mx xa _ |- _ => rename Hc into CH2 end;
        repeat match goal with H : lx_opq _ _ _ _ _ _ _ |- _ => clear H end.
      all: (flat constr:(HH0) 2%nat; flclear HH0; intros HH2 _). all: (flat constr:(MA0) 2%nat; flclear MA0; intros MA2 _).
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mfin end.
      apply aevtM_done. unfold mpi_binop_post.
      try match goal with Kz : bv_unsigned ?v = 0 |- _ => is_var v; replace v with (Z_to_bv 64 0) in * by (apply bv_eq; rewrite Kz; reflexivity) end.
      lazymatch type of U with u32arr _ _ _ ?wsf =>
        (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] => lazymatch xa0 with Z_to_bv 64 0 => flexi 17%nat; exists LB2, (relimb dX2 wsf), 0 | _ => flexi 17%nat; exists LB2, (relimb dX2 wsf), MBEDTLS_ERR_ECP_BAD_INPUT_DATA end end) end.
      split; [first [reflexivity| do 2 f_equal; apply bv_eq; vm_compute; reflexivity]|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split. { apply (@HEAP_munch usegs L HI h2 _ m2 mfin mo2 _ lo HH2 MU WM ACL).
               intros a Ha NO. cbn in NO. rewrite HT2.
               destruct (Z_le_dec P' a) as [C1|C1]; [destruct (Z_lt_dec a (P' + 4 * n2)) as [C2|C2]|].
               - right. right. exists (P', 4 * n2). split; [exact IN2| cbn; lia].
               - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                 + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                   exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                   unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
               - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                 + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                   exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                   unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..]. }
      split. { eapply relimb_at; [exact MA2| exact O2| rewrite EA2, S2, P2; unfold mpi_cells; exact CH2| exact U| rewrite LEN; reflexivity]. }
      split. { eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; rewrite O2; discriminate| reflexivity]. }
      split. { eapply (reducer_presx usegs L HI) with (lo' := lo); [exact HH2| exact MA2| exact OUT2| exact FRr| exact O2| exact EA2| exact PX2| | exact WM| lia| lia| exact DHI| exact DI1| exact DI2].
               rewrite EA2. exact MU. }
      split; [assumption|].
      eapply reducer_R_ok; [exact MA2| exact OUT2| exact GR| lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_ECP_BAD_INPUT_DATA; lia].
  all: match goal with |- ?gg => idtac "REDLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

