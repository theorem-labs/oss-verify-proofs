(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_DepotA AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P004662d7c554388a 0 4 0 16 30 16 37 16 38 16P00c1f544f651abbb 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P0105d2be833efe47 0 2 0 1 10 1P01686bcfab420751 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P01c9e8db40bbd569 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P01efcf7092253a60 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P0200ab2e73f70d4a 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P02597e27480c3c0a 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P029f257a1617cbd1 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P02a1ce2c8e6c393b 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P02b72697fbd63cfc 0 4 0 16 30 16 37 16 38 16P02c7e55e6e4c1b30 0 4 0 16 30 16 37 16 38 16P02d86236f51d5109 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P02f546115bd33f34 0 2 0 1 17 1P0352d625ee24bd99 0 4 0 16 30 16 37 16 38 16P038986de735e1acb 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P03ae6f5be707608a 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P04bfe71aa9bb4375 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P04dcad438d8bf006 0 2 0 1 10 1P053ac6fd7783104b 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P0562b4e924c02313 0 4 0 16 30 16 39 16 40 16P05b9328cc1d814d3 0 2 0 1 26 1P061236fbfee43112 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P067640df844baf8a 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P06bf2d8bb1e871a4 0 2 0 1 10 1P06f5b20896f29633 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P07e5d835b0ed5309 0 2 0 1 17 1P080688dee989e865 0 4 0 16 30 16 39 16 40 16P0860b7350d8bad88 0 2 0 1 33 1P08727f9915de38c8 0 4 0 16 30 16 37 16 38 16P087cd738598dec58 0 4 0 16 30 16 39 16 40 16P088adc1e843f5aaa 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P08b0dc541545600c 0 2 0 1 33 1P08c49e15fa8d7f14 0 4 0 16 30 16 37 16 38 16P093c8281baea43ac 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P096cd7c5bc75203e 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P09c4895a8382b6b4 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P0a1a8f7954246fa1 0 4 0 16 30 16 37 16 38 16P0a5b7391c3ff290f 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P0a8ac970bd740a3d 0 4 0 16 30 16 37 16 38 16P0a8f067c5c86dd48 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P0b4e81e1938e8111 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P0bd481c87e3a5c36 0 2 0 1 33 1P0c02e50038b280d2 0 2 0 1 10 1P0caf6becc64d26f4 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P0cc0437cccd4c420 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P0ccb7789c18f0876 1 2 16 2 0 1 39 1 16 2 1 1 38 1 2 40 1 41 1P0ce40b615b180555 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P0dd647caad485f55 0 2 0 1 10 1P0f36fe2da4cf9787 0 2 0 1 33 1P0f38d183c08cb295 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P0f6fc251fbe52ec5 0 2 0 1 17 1P0f8277881c3057bc 0 4 0 16 30 16 39 16 40 16P0f96a3ecdcfa6aac 0 2 0 1 21 1P0fd60cf2d3b63bfa 0 4 0 16 30 16 37 16 38 16P1015bdb585a5365a 0 4 0 16 30 16 39 16 40 16P10e5ae4742c0bb91 0 2 0 1 15 1P11111034cf3c8c42 0 2 0 1 15 1P11ad1d8f4dd0fc5a 0 4 0 16 30 16 39 16 40 16P11d50a9ba94fc441 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P1267606c1a06dcae 0 4 0 16 30 16 39 16 40 16P1285850ca2bd0e7d 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P12a48e453acf1ff6 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P12f26b564aa080c0 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P132191346665fb97 1 2 16 2 0 1 39 1 16 2 1 1 38 1 2 40 1 41 1P135ce0ddfe56f555 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1386cade97d2c2f8 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P13c90711f1b2b9df 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P142660e1bfc99dd3 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P14898f7370615be8 0 4 0 16 30 16 37 16 38 16P14ceb77ac84b8a7d 0 4 0 16 30 16 37 16 38 16P15251a7fcf8562ac 0 4 0 16 30 16 37 16 38 16P15385356b9076bdd 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P15fecfb5e455ddb4 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P16bbbf78e711d471 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P16c9b466a864f21e 0 4 0 16 30 16 39 16 40 16P16ed86c8251eabda 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1742333a9e0d4b9c 0 4 0 16 30 16 39 16 40 16P1744fa5777f641f2 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P178f75fb08a28b29 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P17a8ec2c094769c9 1 2 16 3 0 1 39 1 40 1 16 3 1 1 38 1 41 1 2 42 1 43 1P1887ff57d5081f61 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P18c443319b426767 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P198a12829ed4a0c8 0 2 0 1 18 1P1a079cacdeeb769d 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1a74dc3185ea019c 0 4 0 16 30 16 39 16 40 16P1a7897d63aad4aca 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P1ad2c53a7987d447 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1adc25db7b48fc3f 0 4 0 16 30 16 37 16 38 16P1b09888526c98896 0 2 0 1 17 1P1b55ee1f9220b1c4 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P1be1517173d86e30 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1c05cad33bc033f4 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P1c5bd65167a1f37b 1 2 16 2 0 1 39 1 16 2 1 1 38 1 2 40 1 41 1P1cb783a599a5243b 0 2 0 1 15 1P1dca3ff57217b393 0 2 0 1 33 1P1dd0c30214c930c6 0 2 0 1 10 1P1e59d15303d0243f 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P1f175496c8bcd1bf 1 2 16 2 0 1 39 1 16 2 1 1 38 1 2 40 1 41 1P1f639d36492e712c 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P1fc8471ced5fcb88 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P1fdb39b8610b77c7 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P205a5708d618a1e0 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P212aef3467612eb5 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P214e119da95e0d78 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P21d25f73f3e6f67e 0 2 0 1 26 1P21daea38b3b7ebbe 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P2206f42fb5559140 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P225d2bbddff411ed 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P2292b7f178944d12 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P229574c7310b1741 0 4 0 16 30 16 37 16 38 16P22a190be1712782a 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P22ed536ed2c34c21 1 2 16 3 0 1 39 1 40 1 16 3 1 1 38 1 41 1 2 42 1 43 1P232cee9fb95cc117 0 4 0 16 30 16 37 16 38 16P2395f85bf164ed73 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P24536efb3627ff95 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P245abe0273f58b4c 0 4 0 16 30 16 37 16 38 16P247637e957657713 0 4 0 16 30 16 37 16 38 16P24c78eef0fa5d504 0 4 0 16 30 16 39 16 40 16P24e226f2c2f69b8f 1 2 16 3 0 1 39 1 40 1 16 3 1 1 38 1 41 1 2 42 1 43 1P2502a2551a5e85a9 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P264bd860ee9c21e3 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P266966846418bd20 1 2 16 3 0 1 39 1 40 1 16 3 1 1 38 1 41 1 2 42 1 43 1P266c7d1d5843e9cf 0 4 0 16 30 16 37 16 38 16P266f86599c14d90f 0 2 0 1 15 1P2671df2ef942cc64 0 4 0 16 30 16 39 16 40 16P2688d8dc5a139d9b 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P26a2f919815321a9 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P26ae72819d278ad6 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P2714e6bf815de9df 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P2769801d18a2049b 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P277a36a8b4e0c650 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P27a6b6dfc2f27b1f 0 4 0 16 30 16 37 16 38 16P27e17eec9fb6ca6f 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P28d76ec5016ac273 0 4 0 16 30 16 39 16 40 16P29502018c25c60d0 0 2 0 1 9 1P2a116ee342c727df 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P2a1a80e8861faf7d 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P2ac38e010dea5031 0 2 0 1 15 1P2b8dac81fba69552 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P2c4312328c11ef46 0 2 0 1 33 1P2c96338741ffcd20 0 2 0 1 15 1P2d89e0bcc7c23240 0 2 0 1 10 1P2db637cd88ac94ca 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P2dca874a3fa7cf6c 0 4 0 16 30 16 39 16 40 16P2e3155c7190f0bf9 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P2e42ff89ed50aebd 0 4 0 16 30 16 37 16 38 16P2e5dfd8707f8b22d 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P2ed64ec79bf9500e 2 32 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P2ffb3b97fa30b6f8 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P3033e62c8a25cab6 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P305b1fbbe6186bdf 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P30c1ddc6ca133180 0 4 0 16 30 16 37 16 38 16P310856c5111424e6 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P3146ab9731ccfba5 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P31782e056778a9d0 0 2 0 1 20 1P31b2ce3ba7b2e644 0 4 0 16 30 16 37 16 38 16P31b64f4e46f018f0 0 2 0 1 33 1P31d4f8d3392eb59b 0 4 0 16 30 16 37 16 38 16P31f6315bb0359809 2 30 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P31fc3e7aff2a932b 0 2 0 1 10 1P324dd01413304fc6 0 4 0 16 30 16 39 16 40 16P329309ea3ac5eddd 0 2 0 1 15 1P332bc2a98ef1bfcb 0 4 0 16 30 16 37 16 38 16P3346939243eb0ff0 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P33478b456444a80e 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P3452bf92b7263cd8 0 4 0 16 30 16 37 16 38 16P347a9341d735773f 0 2 0 1 33 1P34b3f0321ed6569a 0 2 0 1 9 1P34d6c6f91aa576c3 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P34e75ebd33f633ab 0 4 0 16 30 16 39 16 40 16P35338ae7a22d1f37 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P3538611aa3cca841 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P35d5ae75205c34e9 0 2 0 1 10 1P362f802fdc79e3d4 1 2 16 2 0 1 39 1 16 2 1 1 38 1 2 40 1 41 1P367fc33849245825 0 4 0 16 30 16 39 16 40 16P3694780ae08d5a34 2 31 1 1 16 3 1 1 40 1 41 1 4 0 1 39 1 42 1 43 16 1 1 16 3 2 1 39 1 42 1 6 0 1 24 8 32 1 40 1 41 1 43 16P36ecbf10ea897036 2 33 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P3702124cf05f1d04 0 4 0 16 30 16 37 16 38 16P37699bd7583f73b6 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P37a639e2fa5b5d9c 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P37d3a2ab29fe80ef 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P38739288d12aebb7 0 4 0 16 30 16 37 16 38 16P38e129190b26aa30 0 2 0 1 15 1P38e91e1de8af6fea 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P39c9fc28513d22f3 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P39f34a3b3b7f4b29 0 4 0 16 30 16 39 16 40 16P3ab22e87848f7159 0 4 0 16 30 16 39 16 40 16P3ab5afb194a12f7b 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P3b607f6ba954bec1 0 2 0 1 34 1P3b76a9e7654836d4 0 4 0 16 30 16 39 16 40 16P3b87c0d9ec5d0185 0 4 0 16 30 16 37 16 38 16P3ba978e44100d23a 0 2 0 1 18 1P3c13c5dacbab9b67 0 2 0 1 32 1P3c43922f5e707268 0 4 0 16 30 16 39 16 40 16P3ca9e70bc425a886 0 4 0 16 30 16 37 16 38 16P3d89b4966b3d9431 0 4 0 16 30 16 37 16 38 16P3de61fe9792db1e1 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P3df0409ccf2858cf 0 2 0 1 10 1P3e1e7236d042f978 1 2 16 2 0 1 41 1 16 2 1 1 40 1 2 42 1 43 1P3ed3af6877ed1614 2 31 0 4 0 16 1 16 41 16 42 16 0 5 0 16 2 16 32 16 41 16 42 16P3f0debec929ed5c3 1 1 16 2 1 1 38 1 5 25 1 31 1 32 1 39 1 40 16P3f410aa42ccd03a2 0 4 0 16 30 16 37 16 38 16P3f6f0b7b44836789 0 2 0 1 15 1P3fca3280695dbb1c 1 1 16 2 1 1 40 1 5 29 1 31 1 32 1 41 1 42 16P3ff5177e3ebe9f72 1 2 16 3 0 1 39 1 40 1 16 3 1 1 38 1 41 1 2 42 1 43 1N00aa655a543f0be3N03a8b980d3838b08N0ad3e01e8e743b25N0b9255d46c48461aN0e26ae1914dc4d84N0ef4b241a2e57e57N0fb6960b146119f0N11a4afc204f89cc9N11dc1ee6d55d3097N12c8684157563a49N144e466d7afbe965N186dbc11966c31ebN18ad90181a54f064N1a68164c78773ff9N1aeb5993d5d4f5e3N1bb5cdbe07296f6fN1eda26c440e3fb18N1ee36888c64d0cedN1f1a2174962756dfN2053fd2197e8af2eN2546e68be5cbe212N2603e11c34de6d6cN261280376aa8f3f8N293a3159a627aac3N29a847e85cd8f7bcN2b2af81051ba808eN2fa199010a0da294N304a68cacadac6baN30f4830387a229fdN32b7aaea2d7bc9c5N334125ac494f7938N374918d6ec43d4e4N3910b87782ff549bN3adc5ac431ce0f3d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_QPut () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.shiftl"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zx16"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zx32"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "ARUN_1.A_QC_RA1"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.dealloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.QPut.qcA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.A_QCHUNK"; "ARUN_1.A_QPUT"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "ARUN_1.QPut.qcB_post"; "Stdlib.ZArith.BinInt.Z.div"; "ARUN_1.A_QPUT_RA1"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "ARUN_1.A_ENQUEUE"; "ARUN_1.QPut.put_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMin"; "ARUN_1.A_GOT_FLAGS_"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kMaxMallocFill"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kMallocFillByte"; "ARUN_1.QPut.putA_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_QPUT_RA2"; "ARUN_1.A_DRAIN"].

Section ARUN_1. Context {hAR : arun}.
Definition A_QC_RA1 : Z := 0x4bb54.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_QPUT : Z := 0x4bc74.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ENQUEUE : Z := 0x4be24.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_QPUT_RA1 : Z := 0x4be18.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_QPUT_RA2 : Z := 0x4bd50.        (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_DRAIN : Z := 0x4957c.           (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GOT_FLAGS_ : Z := 0x0f5e48.     (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36646331050.3L61927656618.300000500:S1n1HS1n1H". (* [comment removed for export] *)
#[using="Type"] Lemma zx32_lit : forall n, 0 <= n < 2^32 -> zx32 (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof. intros n H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L33089697706.3L61927656618.300000500:S1n1HS1n1H". (* [comment removed for export] *)
#[using="Type"] Lemma zx16_lit : forall n, 0 <= n < 2^16 -> zx16 (Z_to_bv 64 n) = Z_to_bv 64 n.
Proof. intros n H. unfold zx16. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13629548202.3L36646331050.3L53512866218.3L61927656618.300000100600700<SS1n1HSS1n1H". (* [comment removed for export] *)
#[using="Type"] Lemma hi0_lor : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pn,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+20.)))(5.$0.(6.(7.(8.&40.(9.(:.&40.=)))+20.)(8.&40.(;.(:.&40.R2.))))R2.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros n H. rewrite zx16_lit, zx32_lit by lia. rewrite !unsigned_lit by lia. cbn [Z.shiftl]. apply Z.lor_0_l.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section QPut.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition qcA_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (p STK TR size T CTX lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Lms',$<.(=.(>.&40.)La4,(>.&40.)(=.(>.&40.)La5,(>.&40.)(=.(>.&40.)La6,(>.&40.)(=.(>.&40.)La7,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(1.(5.$<.R6.(10.(11.(:.&40.$12.)(:.&40.(13.O21.-30.))O1?.O1>.O1=.O1<.O1;.(:.&40.(13.O:.-10.))(:.&40.O9.)(:.&40.O8.)(:.&40.O7.)(:.&40.O8.)(:.&40.O5.)R5.R4.R3.R2.(:.&40.$14.)(:.&40.=)(:.&40.O6.)O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.)O3.(:.&40.$15.)O2.(16.(>.&40.))R1.(17.$18.)))(1.(19.(1:.(1;.$0.$0.)(1<.$0.$0.O4.O21.)(1=.(1;.$0.$0.)))O1.R1.)(1.(1>.$18.O1.R1.)(1.(1?.$18.R1.)(1.(20.$18.R1.(13.O21.-30.)(1:.$21.(22.O16.)(1:.$21.(22.O17.)(1:.$21.(22.O18.)(1:.$21.(22.O19.)(1:.$21.(22.O1:.)(1:.$21.(22.O20.)(1=.$21.))))))))(1.(23.R1.O6.O5.)(24.$18.R1.O4.(13.O21.-30.)))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13180411502.1 L13898861899.62L57147504277.1 00000400C00GS2SPS3hAR2SP2lo3SPLS2SP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma qc_A : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)PSP,$0.Pp,$0.Pb1,$0.Pn,$0.Pctx,$0.PSTK,$0.PTR,$0.Psize,$0.PT,$0.PCTX,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))P,(2.(13.+65?000.+10.)R=.)P,(2.(13.R>.+8.)(4.+2.+2?.))P,(2.=R;.)P,(2.(13.R<.+10.)(4.+2.+3?.))P,(1.(2.=R<.)(3.R<.(4.+2.+40.)))P,(1.(2.=R<.)(3.R<.(4.+2.+40.)))P,(20.$18.R7.(13.R13.-10.)(26.R12.+3.))P,(27.VCS,(13.R14.-10.)+18.)P,(20.$18.R9.R11.(1:.$21.(22.(:.&40.R10.))(1:.$21.(22.(:.&40.R?.))(1=.$21.))))P,(27.VCS,R12.+10.)P,(28.$18.R;.R10.(1:.$21.(22.(:.&40.R?.))(1=.$21.)))P,(28.$18.R<.(13.R10.+8.)(1:.$21.(29.(:.&40.=))(1=.$21.)))P,(23.R=.R12.R11.)P,(27.VCS,R13.+1000.)P,(27.VCS,R13.+10000.)P,(1.(2.+1000.R15.)(2:.(2.(13.R15.+1000.)+10000.)(2.+65?000.R15.)))P,(2.(13.R16.+1000.)(4.+2.+2?.))P,(2.+65?000.R16.)P,(2.(13.R17.+10000.)(4.+2.+2?.))P,(24.$18.R14.R17.R21.)P,(2.(2;.VhAR,)R18.)P,(2.R19.(2<.R23.+40.))P,(2.R24.(4.+2.+3>.))P,(5.$0.(2=.R25.+10.)=)P,(2:.(2.R26.(2<.R25.+10.))(2.(13.R25.+8.)R1<.))P,(2:.(2.R27.R1?.)(2.(13.R1?.+1000.)R1=.))P,(2:.(2.R28.R1?.)(2.(13.R1?.+10000.)R1>.))P,(2:.(2.R29.R24.)(2.(13.R24.+10.)R1?.))P,(27.VCS,R20.(2<.R2:.R20.))P,(1?.$18.R1>.)P,(5.(>.&40.)R44.(:.&40.$2>.))(2?.$18.VAL,VCS,(30.R2=.R47.R46.R45.R44.R43.R42.R41.R40.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2<.R28.R27.R26.R25.R24.R23.R22.R21.R20.)(10.(11.R47.(:.&40.R2=.)R46.R45.R44.R43.R42.R41.R40.(:.&40.$14.)(:.&40.(13.R2<.-10.))(:.&40.R2<.)(:.&40.R28.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R22.(:.&40.$31.)R21.(16.(>.&40.))R20.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx STK TR size T CTX lo F fc m
      P0 P1 K0 K1 TRB SZB HW0 PCS HSTK KCS TH0 CT8 (HK & TSD & TPC & TSA & CTH) TCS CTXCS TB1 TB2 CB1 CB2
      ST LOIMG SPL SPH SPA SEP1 SEP2 SEP3 SEP4 SCS MI ->.
    unfold hdr_w0 in HW0.
    unfold A_QCHUNK, A_QC_RA1, A_INSTANCE, A_STACK_DEPOT_PUT, A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    change (1684672 + 8) with 1684680 in HK.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_c1_norm. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x0895a0] [] 60%N).
    lazymatch goal with STl : stk _ ?mx lo (SP + -56), FRl : rw_cells _ _ (SP + -56) _ |- _ =>
      chunk_split FRl 1%nat FRx FRb; replace (SP + -56 + 8) with (SP + -48) in FRb by (clear; lia);
      lx_release STl FRx STl2; clear FRx STl; replace (SP + -56 + Z.of_nat 8) with (SP + -48) in STl2 by (clear; lia) end.
    apply evtA_done; unfold qcA_post; lx_exs; lx_ands;
      [ lx_mseq | assumption | assumption | assumption | assumption
      | unfold dealloc_statics, A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; change (1684672 + 8) with 1684680;
        split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption
      | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition qcB_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (p n STK T lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Lms',$<.(=.(>.&40.)La6,(>.&40.)(=.(>.&40.)La7,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(1.(5.$<.R4.(10.(11.O1>.(:.&40.O1?.)O1=.O1<.O1;.O1:.O19.O18.O17.(:.&40.(13.$14.+2=8.))(:.&40.(13.O5.+50.))(:.&40.(13.O5.+=0.))(:.&40.O6.)(:.&40.(13.O8.-10.))(:.&40.O7.)R3.R2.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O3.(:.&40.$32.)O2.(16.(>.&40.))R1.(17.$18.)))(1.(19.(1:.(1;.$0.$0.)(1<.$0.$0.O4.O1?.)(1:.(1;.$0.$0.)(1<.$0.$0.O8.(13.O8.+8.))(1=.(1;.$0.$0.))))O1.R1.)(1.(1>.$18.O1.R1.)(1.(1?.$18.R1.)(1.(33.$18.R1.O8.+8.)(24.$18.R1.O4.O1?.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L10784698996.74L14628904265.72L2593744242.72 L35209531419.71L37503361981.0 L39280637297.0 L39571770052.72L42303277901.1 L51190348121.74L52617098601.74L52630056116.75L56281136313.76L57329752985.76L59589536811.71L61000445529.76L66494272637.72L7872035019.61 00000:00;00@00A00B00C00J00N00U00_00i01C01N01S01^01e024S3hAR1p2P0FS3hARFSSS3hAR1pS2SPS3hAR1pS3hAR1p2P1S3hAR1p2P1S3hAR3idw2SP1p2lo3SPL4SEP1S3hAR3idw1pS3hARS3hAR3idw1pS3hAR1pS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma qc_B : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pra,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pidw,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)PSP,$0.Pp,$0.Pb1,$0.Pn,$0.Pctx,$0.PSTK,$0.PT,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm0,P,(>.&40.)(?.(>.&8.))Pm,P,(>.&40.)(?.(>.&8.))P,(2.(13.+65?000.+10.)R;.)P,(2.(13.R<.+8.)(4.+2.+2?.))P,(1.(2.=R;.)(3.R;.(4.+2.+20.)))P,(1.(2.=R:.)(3.R:.(4.+2.+40.)))P,(1.(2.+1000.R:.)(2:.(2.(13.R:.+1000.)+10000.)(2.+65?000.R:.)))P,(2.(13.R;.+1000.)(4.+2.+2?.))P,(20.$18.R7.(13.R11.-10.)(26.R10.+3.))P,(20.$18.R8.(13.R12.-<.)(34.R10.R?.))P,(33.$18.R9.R13.+8.)P,(27.VCS,(13.R14.-10.)+18.)P,(20.$18.R;.(13.R16.-30.)(1:.$21.(22.R2:.)(1:.$21.(22.R2;.)(1:.$21.(22.R2<.)(1:.$21.(22.R2=.)(1:.$21.(22.R2>.)(1:.$21.(22.R2?.)(1=.$21.))))))))P,(24.$18.R<.R10.(13.R17.-30.))P,(2.(2;.VhAR,)R11.)P,(2.R12.(2<.R19.+40.))P,(2.R1:.(4.+2.+3>.))P,(2:.(2.R1;.(2<.R1:.+10.))(2.(13.R1:.+8.)R14.))P,(19.(1:.(1;.$0.$0.)(1<.$0.$0.R15.R1<.)(1:.(1;.$0.$0.)(1<.$0.$0.R1;.(13.R1;.+8.))(1=.(1;.$0.$0.))))R12.R11.)P,(1>.$18.R13.R12.)P,(1?.$18.R13.)P,(27.VCS,R18.(2<.R1?.R18.))(2?.$18.VAL,VCS,(35.R20.R39.R3>.R3=.R3<.R3;.R3:.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R1?.R1=.R1;.R1:.R19.R18.R17.R16.)(10.(11.(:.&40.$12.)(:.&40.(13.R20.-30.))R3>.R3=.R3<.R3;.R3:.(:.&40.(13.R1?.-10.))(:.&40.R1;.)R28.R27.R26.R25.R24.R23.R22.R21.(:.&40.$14.)(:.&40.=)(:.&40.R1:.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R18.(:.&40.$12.)R17.(16.(>.&40.))R15.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 idw a1 a2 a3 a4 a5 a6 a7 SP p b1 n ctx STK T lo F fc m0 m
      P0 P1 NB STKB TB1 TB2 HW0 HW1 WR PCS FR ST LOIMG SPL SPH SEP1 MU WM MI SCS.
    facts. unfold hdr_w0, hdr_rest in *. unfold A_QC_RA1, A_INSTANCE, A_QPUT in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    pose proof (wr_at_store_ok asegs _ p 8 0 8 WR ltac:(clear; lia) ltac:(clear; lia)) as SOK.
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      first [ change bs with (le8 (Z_to_bv 64 (bv_unsigned (bv_or (Z_to_bv 64 0) idw)))) | idtac ];
      lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem mx a ?bs2) _) => pose proof (wr_at_write asegs mx p 8 a bs2 WR) as WR' end
    end.
    store_done. clear WR. rename WR' into WR.
    lx_aceil.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      pose proof (munch_refl [(lo, SP); (p, p + 8)] m1) as MU1; pose proof (wmono_refl asegs m1) as WM1 end.
    lx_run (PLAN [0x4bc74] [] 30%N). lx_unhide.
    lazymatch goal with MUl : munch _ ?m1 ?mx, WMl : wmono _ ?m1' ?mx', STl : stk _ _ lo (SP + -48), FRl : rw_cells _ _ (SP + -48) _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx'' _) =>
      lx_release STl FRl STl2; replace (SP + -48 + Z.of_nat 48) with SP in STl2 by (clear; lia);
      apply evtA_done; unfold qcB_post, A_QPUT, A_INSTANCE; change (1074072 + 728) with 1074800; lx_exs; lx_ands;
      [ lx_mseq | lx_munch MU MUl | lx_wmono WM WMl | assumption
      | exact (wr_at_transport _ _ _ _ _ WR WMl)
      | exact STl2 ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition put_frame (m : mem) (SP T STK : Z) (s6 s5 s4 s3 s2 s1 s0 ra : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "(20.$18.O<.(13.O;.-50.)(1:.$21.(22.(:.&40.(13.O:.+=0.)))(1:.$21.(22.(:.&40.O9.))(1:.$21.(22.O8.)(1:.$21.(22.O7.)(1:.$21.(22.O6.)(1:.$21.(22.O5.)(1:.$21.(22.O4.)(1:.$21.(22.O3.)(1:.$21.(22.O2.)(1:.$21.(22.O1.)(1=.$21.))))))))))))")
(* [comment removed for export] *).

  Definition putA_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (p n STK T lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Lms',$<.(=.(>.&40.)Lt0,(>.&40.)(=.(>.&40.)Lt1,(>.&40.)(=.(>.&40.)Lt2,(>.&40.)(=.(>.&40.)La5,(>.&40.)(=.(>.&40.)La6,(>.&40.)(=.(>.&40.)La7,(>.&40.)(=.(>.&40.)Lt3,(>.&40.)(=.(>.&40.)Lt4,(>.&40.)(=.(>.&40.)Lt5,(>.&40.)(=.(>.&40.)Lt6,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))ZS,$0.(13.+7???8000.(36.O8.+8.))Zk,$0.(36.(13.O7.+7.)+8.)(1.(5.$<.R>.(10.(11.(:.&40.$37.)(:.&40.(13.O18.-50.))O16.O15.R=.R<.R;.(:.&40.(13.$14.+2=8.))(:.&40.(13.O5.+50.))(:.&40.(13.O5.+50.))(:.&40.(13.O5.+=0.))(:.&40.O6.)(:.&40.(13.O8.-10.))(:.&40.O7.)R:.R9.R8.(:.&40.O7.)(:.&40.O6.)(:.&40.(13.O5.+=0.))(:.&40.(13.O8.-10.))(:.&40.$38.)O=.O<.O;.O:.O9.R7.R6.R5.R4.)O3.(:.&40.$39.)O2.(16.(>.&40.))R3.(17.$18.)))(1.(19.(1:.(1;.$0.$0.)(1<.$0.$0.O4.O18.)(1:.(1;.$0.$0.)(1<.$0.$0.R2.(13.R2.R1.))(1=.(1;.$0.$0.))))O1.R3.)(1.(1>.$18.O1.R3.)(1.(1?.$18.R3.)(1.(3:.R3.O18.O5.O6.O>.O?.O10.O11.O12.O13.O14.O17.)(1.(20.$18.R3.R2.(1:.$21.(3;.(3<.R1.)(3=.(>.&8.)(:.&8.+?=.)(3<.R1.)))(1=.$21.)))(1.(3>.R3.)(24.$18.R3.O4.(13.O18.-50.))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L11330106339.76 L17120848823.0  L17463680011.109L19520188026.3  L21753913141.2  L22375555030.2  L27846297964.3  L28034335414.7  L28688805159.0  L35080720211.3  L35450344195.4  L35539854113.0  L36949723459.4  L38235734261.1  L39575460409.1  L40797741474.1  L40938924652.1  L44671073410.67 L46559860800.4  L46595273239.108L47413478169.64 L51797172194.1  L52627017202.14 L5363753020.108 L54789358972.108L57628690499.109L58817773446.108L59367596220.108L60559473378.2  L61028791505.69 L61844504062.0  L62872289555.12 L63374621462.70 L66516586114.107L66551147714.10900000R00S00T00\00d00l01301G01H01S01^01_01d01h01k01l01o02g02l02m03V03W04>04_05@06@07@07a07g08308408U08a08b09KS3hAR2SP1p1n2lo2P02P12NB5LOIMG3H11SFS1n1k2KBS2SP3SPAS2SP3SPHS2SP2loS1p1n1k2P02P13RNG2KBSS2SP2lo3SPLS1n2NB1H2H0SS1p1kS2loS1pFS1pS3hAR2SP1p1n2lo1k2P02NB5LOIMG3SPL2HK2KB3lxv2H82H93H112DvS1p1kFS3hAR2SP1p1n2lo1S1k2P02P12NB5LOIMG2HS3H11FS3hAR2SP1p2lo1S1k2P05LOIMG2HS2A'2n'3HA'S3hAR2SP1p1n2lo1k2P02NB5LOIMG3H11S3hAR2SP1p1n2lo1k2P02NB5LOIMG3H11S3hAR2SP1p1n2lo1S1k2P02P12NB5LOIMG3SPL3SPA4SEP12HS2HK3H113x152H1S3hAR2SP1p1n2lo1S1k2P02PA2NB3RNG5LOIMG3SPL3SPA4SEP12HS2HK3H112P1S3hAR2SP1p1n2lo1k2P02NB5LOIMG3H11S1p2PAS3hAR2SP1p1nSS3hAR2SP1p1n2lo2P05LOIMG2A02n02HAS3hAR2SP1p1nFS3hAR2SP1p1n2lo1S1k2P02P12NB5LOIMG2HS3H11". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma put_A : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)PSP,$0.Pp,$0.Pb1,$0.Pn,$0.Pctx,$0.PSTK,$0.PT,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(?.(>.&8.))Pjunk,(3?.(>.&8.))ZS,$0.(13.+7???8000.(36.R;.+8.))Zk,$0.(36.(13.R:.+7.)+8.)P,(2.(13.+65?000.+10.)R=.)P,(2.(13.R>.(40.+8.R2.))(4.+2.+2?.))P,(5.$0.(2=.R?.+10.)=)P,(1.(2.=R>.)(2.R>.(4.+2.+1<.)))P,(1.(2.=R=.)(3.R=.(4.+2.+40.)))P,(1.(2.+1000.R=.)(2:.(2.(13.R=.+1000.)+10000.)(2.+65?000.R=.)))P,(2.(13.R>.+1000.)(4.+2.+2?.))P,(2:.(1.(2.(13.R14.+8.)+7???8000.)(2.(13.R14.(40.+8.R8.))+7???8000.))(1.(2.+10007???8008.R14.)(2.(13.R14.+8.)(4.+2.+2?.))))P,(20.$18.R<.(13.R15.-10.)(26.R14.+3.))P,(20.$18.R=.(13.R16.-<.)(34.R14.R13.))P,(27.VCS,(13.R17.-10.)(13.+10.(40.+8.(41.R;.+1.))))P,(20.$18.R?.R=.(1:.$21.(3;.(3<.R<.)R>.)(1=.$21.)))P,(28.$18.R10.$42.(1:.$21.(22.(:.&40.$43.))(1:.$21.(22.(:.&40.$44.))(1:.$21.(22.(:.&40.$38.))(1=.$21.)))))P,(28.$18.R11.$45.(1:.$21.(22.(:.&40.$46.))(1=.$21.)))P,(28.$18.R12.(13.$46.+2<.)(1:.$21.(29.(:.&40.$47.))(1:.$21.(29.(:.&40.=))(1:.$21.(29.(:.&40.$48.))(1=.$21.)))))P,(3>.R13.)P,(24.$18.R14.R17.R1>.)P,(2.(2;.VhAR,)R18.)P,(2.R19.(2<.R20.+90.))P,(2.R21.(4.+2.+3>.))P,(5.$0.(2=.R22.+10.)=)P,(2:.(2.R23.(2<.R22.+10.))(2.(13.R22.(40.+8.R16.))R1<.))P,(27.VCS,R1=.(2<.R24.R1=.))P,(1?.$18.R1;.)(2?.$18.VAL,VCS,(49.R26.R3>.R3=.R3<.R38.R37.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R25.R23.R21.R20.R1?.R1>.R1=.R1<.)(10.(11.R3>.(:.&40.R26.)R3=.R3<.R3;.R3:.R39.R38.R37.(:.&40.(13.$14.+2=8.))(:.&40.(13.R20.+50.))(:.&40.(13.R20.+=0.))(:.&40.R21.)(:.&40.(13.R25.-10.))(:.&40.R23.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R1>.(:.&40.$32.)R1=.(16.(>.&40.))R1<.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx STK T lo F fc m junk S k
      P0 P1 PA NB STKB TB1 TB2 RNG HW0 HW1 PCS SH QMX GOTF FL PS ST LOIMG SPL SPH SPA SEP1 SCS MI.
    unfold hdr_w0, hdr_rest in *.
    unfold A_QPUT, A_Q_MAX, A_INSTANCE, A_GOT_FLAGS_, A_FLAGS, kQuarantineMax, kQuarantineMin, kQuarantineCache, kMaxMallocFill, kMallocFillByte in *.
    change (1074072 + 792) with 1074864 in QMX. change (1074072 + 728) with 1074800. change (1077752 + 44) with 1077796 in FL.
    assert (HS : S = 0x7fff8000 + p / 8) by reflexivity. assert (HK : k = (n + 7) / 8) by reflexivity. clearbody S k.
    assert (KB : 0 <= k /\ n <= 8 * k < n + 8).
    { subst k. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). clear -NB H H0. lia. }
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    assert (PCS24 : crange CS (p + -16) 24) by (eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]).
    lx_hide SH. lx_hide PS. lx_c1_norm. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x6a55c] [] 60%N). lx_unhide.
    (* [comment removed for export] *)
    first [ lazymatch goal with |- context [Z_to_bv 64 (Z.land ?e ?msk)] =>
              replace (Z.land e msk) with (k * 8) by (rewrite HK, lxw_land_m8 by (clear -NB; lia); clear; lia) end
          | match goal with AL8 : ?v mod ?q = 0 |- _ =>
              is_var v; let qv := eval cbv in q in change q with qv in AL8; let EV := fresh "EV" in let Dv := fresh "Dv" in
              assert (EV : v = k * 8) by (pose proof (Z.div_mod v qv ltac:(clear; lia)) as Dv; rewrite AL8, Z.add_0_r in Dv; lx_arith);
              subst v; clear AL8 end ].
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -80) |- _ =>
    assert (SHl : rw_cells asegs mx S [CB (Z.to_nat k) junk]) by (lx_tr_rw SH MUl WMl);
    assert (MUW : munch [(lo, SP); (S, S + k)] m mx) by (eapply munch_weaken; [| exact MUl]; lx_subfp);
    clear SH MUl;
    callxA (eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (lo := lo) (junk := junk);
      [ clear -PA; lia
      | clear; apply Z_mod_mult
      | clear -KB; lia
      | clear; lia
      | clear -RNG P0 P1 KB; lia
      | left; clear; lia
      | eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]
      | rewrite Z.div_mul by (clear; lia); rewrite <- HS; exact SHl
      | eapply (poison_statics_transport _ _ _ PS MUW); intros A' n' HA'; cbn [disjoint_from]; clear -HA' HS P0 P1 LOIMG H; lia
      | exact STl
      | exact LOIMG
      | clear -SPL; lia
      | clear -SPH; lia
      | clear -SPA; lia
      | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia]
      | apply munch_refl
      | apply wmono_refl
      | assumption ]) end.
    rewrite Z.div_mul in * by (clear; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with MUW : munch _ m ?mx, WMW : wmono _ m ?mx' |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx'' _) =>
      lx_hide MUW; lx_hide WMW; pose proof (munch_refl [(lo, SP)] mx) as MU2; pose proof (wmono_refl asegs mx) as WM2 end.
    lx_run (PLAN [0x4be24] [] 10%N). lx_unhide.
    apply evtA_done. unfold putA_post, put_frame, A_QPUT_RA1, A_ENQUEUE, A_INSTANCE, kQuarantineCache. cbv zeta.
    change (1074072 + 728) with 1074800. subst S k.
    lazymatch goal with MUl : munch _ ?mc ?mx, WMl : wmono _ ?mc' ?mx', MUW : munch _ m ?mc'', WMW : wmono _ m _,
                        SHc : rw_cells _ _ (2147450880 + p / 8) _ |- _ =>
      lx_exs; lx_ands;
      [ lx_mseq
      | lx_munch MUW MUl
      | lx_wmono WMW WMl
      | assumption | assumption
      | lx_tr_rw SHc MUl WMl
      | eapply (poison_statics_transport _ _ _ PS); [lx_munch MUW MUl|]; intros A0 n0 HA; cbn [disjoint_from]; clear -HA P0 P1 LOIMG H; lia
      | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma put_B_ret : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Ps6,(>.&40.)Ps5,(>.&40.)Ps4,(>.&40.)Ps3,(>.&40.)Ps2,(>.&40.)Ps1,(>.&40.)Ps0,(>.&40.)Pra,(>.&40.)Plen,(>.&40.)Pfirst,(>.&40.)Plast,(>.&40.)PSP,$0.Pp,$0.Pn,$0.PSTK,$0.PT,$0.Pbytes,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm0,P,(>.&40.)(?.(>.&8.))Pm,P,(>.&40.)(?.(>.&8.))PW,(3?.(1;.$0.$0.))P,(1.(2.=R7.)(2.R7.$38.))P,(1.(2.+1000.R9.)(2:.(2.(13.R9.+1000.)+10000.)(2.+65?000.R9.)))P,(2.(13.R:.+1000.)(4.+2.+2?.))P,(20.$18.R5.(13.R;.+50.)(1:.$21.(22.R12.)(1:.$21.(22.R11.)(1:.$21.(22.R10.)(1:.$21.(22.(:.&40.R:.))(1=.$21.))))))P,(27.VCS,R<.+1000.)P,(3:.R7.R11.R=.R>.R1<.R1;.R1:.R19.R18.R17.R16.R15.)P,(24.$18.R8.R<.(13.R12.-50.))P,(2.(2;.VhAR,)R=.)P,(2.R>.(2<.R14.+50.))P,(2.R15.(4.+2.+3>.))P,(19.(1:.(1;.$0.$0.)(1<.$0.$0.R10.R16.)R;.)R=.R<.)P,(1>.$18.R>.R=.)P,(1?.$18.R>.)P,(27.VCS,R13.(2<.R19.R13.))(2?.$18.VAL,VCS,Lms',$<.(=.(>.&40.)Lx10,(>.&40.)(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(1.(5.$<.R3.(10.(11.R21.(:.&40.R1=.)R3>.R3=.R3<.R3;.R3:.R22.R23.R2.R38.R37.R36.R35.R34.R33.R32.R24.R25.R26.R27.R28.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R16.(4:.R21.)R15.(16.(>.&40.))R1.(17.$18.)))(1.(19.(1:.(1;.$0.$0.)(1<.$0.$0.R17.R1=.)R12.)R14.R1.)(1.(1>.$18.R14.R1.)(1.(1?.$18.R1.)(1.(20.$18.R1.(13.R19.+50.)(1:.$21.(22.R20.)(1:.$21.(22.R1?.)(1:.$21.(22.R1>.)(1:.$21.(22.(:.&40.R18.))(1=.$21.))))))(24.$18.R1.R17.R1=.))))))))(10.(11.(:.&40.$37.)(:.&40.(13.R1:.-50.))R3;.R3:.R39.R38.R37.(:.&40.(13.$14.+2=8.))(:.&40.(13.R16.+50.))R36.R35.R34.R33.R32.R31.R30.R2?.(:.&40.R18.)(:.&40.R17.)(:.&40.(13.R16.+=0.))(:.&40.(13.R19.-10.))(:.&40.$38.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R13.(:.&40.$37.)R12.(16.(>.&40.))R10.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 s6 s5 s4 s3 s2 s1 s0 ra len first last
      SP p n STK T bytes lo F fc m0 m W BY TB1 TB2 QC TCS FR ST LOIMG SPL SPH MU WM MI SCS.
    unfold put_frame in FR. unfold A_QPUT_RA1, A_INSTANCE, kQuarantineCache in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ => lx_post; [lx_munch MU MUl | lx_wmono WM WMl] end.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L10128865365.70L1053909285.72 L13607354964.71L28932364874.71L35440445713.71L46493634886.71L49686112913.71L52519387078.71L59308634497.3 L67750724942.72L9273682244.70 00000700?00M00T00_00n01901H01U01]01dS3hAR1TS3hAR2SPS3hAR5bytes2BYS3hAR1TS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPLS5bytes2BY2KbS3hAR2SPS3hAR1T". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma put_B_drain : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Ps6,(>.&40.)Ps5,(>.&40.)Ps4,(>.&40.)Ps3,(>.&40.)Ps2,(>.&40.)Ps1,(>.&40.)Ps0,(>.&40.)Pra,(>.&40.)Plen,(>.&40.)Pfirst,(>.&40.)Plast,(>.&40.)PSP,$0.Pp,$0.Pn,$0.PSTK,$0.PT,$0.Pbytes,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm0,P,(>.&40.)(?.(>.&8.))Pm,P,(>.&40.)(?.(>.&8.))PW,(3?.(1;.$0.$0.))P,(1.(3.$38.R7.)(3.R7.(4.+2.+40.)))P,(1.(2.+1000.R9.)(2:.(2.(13.R9.+1000.)+10000.)(2.+65?000.R9.)))P,(2.(13.R:.+1000.)(4.+2.+2?.))P,(1.(2.=R<.)(3.R<.(4.+2.+40.)))P,(20.$18.R6.(13.R<.+50.)(1:.$21.(22.R13.)(1:.$21.(22.R12.)(1:.$21.(22.R11.)(1:.$21.(22.(:.&40.R;.))(1=.$21.))))))P,(27.VCS,R=.+1000.)P,(3:.R8.R12.R>.R?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)P,(24.$18.R9.R=.(13.R13.-50.))P,(2.(2;.VhAR,)R>.)P,(2.R?.(2<.R15.+50.))P,(2.R16.(4.+2.+3>.))P,(19.(1:.(1;.$0.$0.)(1<.$0.$0.R11.R17.)R<.)R>.R=.)P,(1>.$18.R?.R>.)P,(1?.$18.R?.)P,(27.VCS,R14.(2<.R1:.R14.))(2?.$18.VAL,VCS,Lms',$<.(5.$<.R1.(10.(11.(:.&40.$4;.)(:.&40.(13.R1<.-50.))R3=.R3<.R3;.R3:.R39.(:.&40.(13.$14.+2=8.))(:.&40.(13.R18.+50.))(:.&40.(13.$14.+2=8.))(:.&40.(13.R18.+50.))(:.&40.(13.R18.+=0.))(:.&40.R19.)R34.R33.R32.R31.(:.&40.R1:.)(:.&40.R19.)(:.&40.(13.R18.+=0.))(:.&40.(13.R1;.-10.))(:.&40.$38.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R15.(:.&40.$4<.)R14.(16.(>.&40.))R12.(17.$18.)))(10.(11.(:.&40.$37.)(:.&40.(13.R1;.-50.))R3<.R3;.R3:.R39.R38.(:.&40.(13.$14.+2=8.))(:.&40.(13.R17.+50.))R37.R36.R35.R34.R33.R32.R31.R30.(:.&40.R19.)(:.&40.R18.)(:.&40.(13.R17.+=0.))(:.&40.(13.R1:.-10.))(:.&40.$38.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R14.(:.&40.$37.)R13.(16.(>.&40.))R11.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 s6 s5 s4 s3 s2 s1 s0 ra len first last
      SP p n STK T bytes lo F fc m0 m W BY TB1 TB2 STKB QC TCS FR ST LOIMG SPL SPH MU WM MI SCS.
    facts. unfold put_frame in FR. unfold A_QPUT_RA1, A_QPUT_RA2, A_DRAIN, A_INSTANCE, kQuarantineCache in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. clear -Kb BY. lia. }
    zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG ALWF CSOK"] Lemma put_C : ltac2:(CDefT.buildp (gd_tbl_AW_QPut ()) "Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Pa0,(>.&40.)Pa1,(>.&40.)Pa2,(>.&40.)Pa3,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Px8,(>.&40.)Px9,(>.&40.)Px18,(>.&40.)Px19,(>.&40.)Px20,(>.&40.)Px21,(>.&40.)Px22,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Ps6,(>.&40.)Ps5,(>.&40.)Ps4,(>.&40.)Ps3,(>.&40.)Ps2,(>.&40.)Ps1,(>.&40.)Ps0,(>.&40.)Pra,(>.&40.)PSP,$0.PSTK,$0.PT,$0.Plo,$0.PF,(25.&5.(>.&40.))Pfc,(>.&20.)Pm0,P,(>.&40.)(?.(>.&8.))Pm,P,(>.&40.)(?.(>.&8.))PW,(3?.(1;.$0.$0.))P,(3:.R2.R9.R7.R8.R11.R10.R?.R>.R=.R<.R;.R:.)P,(24.$18.R3.R7.(13.R:.-50.))P,(2.(2;.VhAR,)R8.)P,(2.R9.(2<.R<.+50.))P,(2.R=.(4.+2.+3>.))P,(19.(1:.(1;.$0.$0.)(1<.$0.$0.R;.R>.)R6.)R8.R7.)P,(1>.$18.R9.R8.)P,(1?.$18.R9.)P,(27.VCS,R>.(2<.R11.R>.))(2?.$18.VAL,VCS,Lms',$<.(=.P,(>.&40.)(?.(>.&8.))Lm',P,(>.&40.)(?.(>.&8.))(1.(5.$<.R2.(10.(11.R15.(:.&40.R14.)R39.R38.R37.R36.R35.R16.R17.R34.R33.R32.R31.R30.R2?.R2>.R2=.R18.R19.R1:.R1;.R1<.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R10.(4:.R15.)R?.(16.(>.&40.))R1.(17.$18.)))(1.(19.(1:.(1;.$0.$0.)(1<.$0.$0.R11.R14.)R<.)R>.R1.)(1.(1>.$18.R>.R1.)(1.(1?.$18.R1.)(24.$18.R1.R11.R14.))))))(10.(11.(:.&40.$4;.)(:.&40.(13.R12.-50.))R37.R36.R35.R34.R33.R2:.R29.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R>.(:.&40.$4;.)R=.(16.(>.&40.))R;.(17.$18.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x9 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 s6 s5 s4 s3 s2 s1 s0 ra
      SP STK T lo F fc m0 m W FR ST LOIMG SPL SPH MU WM MI SCS.
    unfold put_frame in FR. unfold A_QPUT_RA2 in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ => lx_post; [lx_munch MU MUl | lx_wmono WM WMl] end.
  Qed.
End QPut.

End ARUN_1.
