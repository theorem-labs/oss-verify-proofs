(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_len U_asn1_get_tag U_asn1_get_sequence_of_A U_asn1_get_sequence_of_B U_asn1_get_sequence_of_C U_asn1_get_sequence_of_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0004f388ec1dfc98 0 3 0 1 34 1 35 1P003ac7487e22a200 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P021784410ae20beb 0 2 0 1 12 1P021dd105d7afdf35 0 5 0 1 30 1 33 1 34 1 35 1P029071e3f835ea84 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P0331d5446885e571 2 15 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P036ed5536867e869 0 5 0 1 2 1 19 1 34 1 35 1P0371d0bf0b86020e 0 5 0 1 12 1 13 1 30 1 35 1P0383c1050f6b3438 2 15 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P0516c595cba07a12 0 2 0 1 2 1P053295e4847d969d 0 4 0 1 13 1 30 1 35 1P0885927301ae33a7 0 4 0 1 1 1 33 1 34 1P08b6fbbd55dffa8d 0 2 0 1 1 1P08c5f79fc4c95c9b 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P09afd7a2c2da3fc8 2 14 0 6 0 1 3 1 23 1 31 1 36 1 37 1 0 4 0 1 2 1 36 1 37 1P09ed36b90948461f 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P0a06bcaf14b8fe28 0 4 0 1 13 1 30 1 35 1P0bc0fdc9fceed6b7 2 15 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P0c10206a605de5ec 2 16 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P0cb6185f24ca6db1 0 3 0 1 4 1 34 1P0dea5578f5f8a920 0 2 0 1 16 1P0fb8e9d7c539097e 0 2 0 1 43 1P105d6ab88fa8e034 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P10a9aa42a184a06b 0 4 0 1 20 1 33 1 34 1P10ad9dd1db812d11 2 14 0 6 0 1 3 1 23 1 31 1 36 1 37 1 0 4 0 1 2 1 36 1 37 1P113a5821d75fd929 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P113e02c983225adf 0 4 0 1 1 1 33 1 34 1P122e537fb5f038c0 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P123268beb1b8617f 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P130de5cba3ea4df6 2 14 0 6 0 1 3 1 23 1 31 1 36 1 37 1 0 4 0 1 2 1 36 1 37 1P133f6d15d2cfcf49 0 4 0 1 10 1 18 1 32 1P14339c4aed151c91 0 3 0 1 1 1 30 1P14b8d8fefdbbc07e 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P1539fb92d2c82354 0 2 0 1 35 1P15ef0108354fe17c 0 2 0 1 5 1P19814184c1eeb817 0 2 0 1 2 1P1c4c869518e85646 2 23 1 1 8 3 1 1 43 1 44 1 6 0 1 30 1 31 1 42 1 45 1 46 8 1 1 8 3 2 1 42 1 45 1 4 0 1 43 1 44 1 46 8P1c66864059161d71 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P1c788a786c0ba51f 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P1d204a6bb5fc40d0 2 16 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P1e333b448fff3e95 0 2 0 1 1 1P1fee7cc7091e7101 0 2 0 1 12 1P204c807b52408939 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P20a617c6474c2c62 0 2 0 1 5 1P20b29b3592e50cc1 0 3 0 1 33 1 34 1P21d52bac293dde26 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P2264c1c9749b2dec 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P226e1f4f6d3bc237 0 2 0 1 31 1P230afb92aad56b6f 0 6 0 1 1 1 14 1 18 1 30 1 35 1P2319e4b22625c0bc 0 2 0 1 36 1P244e6d54d0cf461a 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P2458e82b8cdc6e71 0 2 0 1 1 1P24f047fe927e855f 0 5 0 1 24 1 25 1 36 1 37 1P256152e977a22113 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P25fb2ad125342ce5 2 15 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P26ec41f2140440d1 0 5 0 1 31 1 34 1 35 1 36 1P27395262c86130ef 0 2 0 1 40 1P2a0b8240d3383350 0 3 0 1 1 1 35 1P2a0c93726b6d15fb 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P2a0ed2565145ca04 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P2a3ad37846f944c6 0 2 0 1 12 1P2ad6d6a515d76c9a 0 2 0 1 1 1P2b4201449cc19873 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P2b6bd4c720e74cb9 0 5 0 1 14 1 18 1 30 1 35 1P2c5b7188434ee059 2 23 1 1 8 3 1 1 43 1 44 1 6 0 1 30 1 31 1 42 1 45 1 46 8 1 1 8 3 2 1 42 1 45 1 4 0 1 43 1 44 1 46 8P2d6d336462cc6009 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P2d847d481b8aa00c 2 15 1 1 8 3 1 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P2e9aff1baaef4873 2 23 1 1 8 3 1 1 43 1 44 1 6 0 1 30 1 31 1 42 1 45 1 46 8 1 1 8 3 2 1 42 1 45 1 4 0 1 43 1 44 1 46 8P2f1cf61340a25704 0 3 0 1 33 1 34 1P2f276effcb3d52ab 0 5 0 1 24 1 25 1 36 1 37 1P2f2c6824ad0c5fe2 0 2 0 1 17 1P301da9d36ec069aa 2 16 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P30a7206b9c3b5f21 0 2 0 1 44 1P30eaa2e5db35fc3c 0 5 0 1 12 1 20 1 33 1 34 1P30f9e06303cd547e 2 23 1 1 8 3 1 1 43 1 44 1 6 0 1 30 1 31 1 42 1 45 1 46 8 1 1 8 3 2 1 42 1 45 1 4 0 1 43 1 44 1 46 8P3269bce0d7605c10 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P33355c06c1775496 0 6 0 1 1 1 14 1 18 1 30 1 35 1P337d582257dfbb96 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3388eab202bf1c36 0 4 0 1 15 1 31 1 36 1P338efbe667a1ff9b 0 5 0 1 12 1 13 1 30 1 35 1P33a6317196798821 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P3508aaac767336bc 0 5 0 1 25 1 28 1 29 1 30 1P3555823defde25cf 0 6 0 1 2 1 15 1 19 1 31 1 36 1P369dde6e54d44aea 2 15 1 1 8 3 1 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P375eef28ec614bbd 0 6 0 1 13 1 29 1 32 1 33 1 34 1P3786e670709ff213 2 15 1 1 8 3 1 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P37af98bc139c6da4 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P37d377e55a8b13e2 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P37fd4bbd8670190d 2 16 1 1 8 3 2 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 1 36 1 37 1 39 8P38bd5c22bc033831 0 5 0 1 12 1 20 1 33 1 34 1P38f9512209718fd5 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P398d42f049015113 0 5 0 1 14 1 18 1 30 1 35 1P3a10ece65b73d753 0 3 0 1 11 1 33 1P3a812fae72e8b655 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3a8c122c357e254b 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3a9f2d1245c7187b 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3abd95c892cc97ea 2 25 1 1 8 3 1 1 49 1 50 1 6 0 1 32 1 33 1 48 1 51 1 52 8 1 1 8 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 8P3b1897b1765e0c9a 2 15 1 1 8 3 1 1 36 1 37 1 6 0 1 22 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P3b5c7f4643df88a9 2 19 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3c74c714b1da00b5 0 2 0 1 15 1P3cf7d4683fdc6fc5 2 14 0 6 0 1 3 1 23 1 31 1 36 1 37 1 0 4 0 1 2 1 36 1 37 1P3d27accf96ea63db 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P3d9df6f2da68e4f0 2 18 1 1 8 3 2 1 39 1 40 1 6 0 1 26 1 27 1 38 1 41 1 42 8 1 1 8 3 1 1 38 1 41 1 4 0 1 39 1 40 1 42 8P3efd337db4ce709b 0 4 0 1 20 1 33 1 34 1P3f58c884fea66e77 2 17 0 6 0 1 3 1 27 1 28 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P3f83ab71afc0c863 0 2 0 1 1 1P3ff3670a7d9fe954 0 2 0 1 2 1N001c1a5f9ca43c9dN0034800db8c3dd06N0065c73f84e891feN00676ca957a2633eN0067f7a1f6dd37ebN00caae445e82605bN00ee5f4aaa739f91N0102aa41f6829ef7N012beac2ccda8d54N0143e5e11c34529dN0147244e5eb6095eN014948f7f47ff91eN017a95f658978bacN01e28e201c712eccN01f4ae5d934926f9N01f7afe8850a8c78N025511ce44a429aeN02909c8fcb0d6dc0N029f5c29b973376eN0301fb5cfa539602N03120181e027424aN032998390c75ae5cN034d5c538471718aN0385d0f338648251N039034b4a504dad8N0402032049116ef4N04091acbb1b08cfaN04126481a95c8d09N0498f2898ce9fbaeN049cdb434b1d9946N04fe42dae69290b8N055f6b0486f12f3bN055fd0f939f4464cN0560e09ac048e8aaN05915c15db498e11N05a9709fb8e3b532N05c6c8163c07b036N06070067dfa15964N0613eecd5921046eN0644f3b670ffd5a4N066bc4b6f976a748N06bfe0b1c551f2ccN06cc3a0f4d61c374N079c084fd95296cbN07e0a25741ce9312N08411b3775f31606N0850571cf3a74c47N08936f6051dfcd69N08d388e912314aa2N0916973a53b5a390N09541605c79dbd23N0959602283e59e15N0970156c8f42b43eN0972cd029d9484dbN09baf14a1c52f85cN0a29277e38f8e656N0a2a6d200a82ea1dN0ab8be651a73f677N0ac85167ad3c05dfN0afebd9353489b2eN0b5afb7aa5cf7d01N0b65a000819b7e63N0bbbadef12f14e64N0bf5d5e46dafea64N0c36c9090d6499c8N0c4faefcd9e038eaN0cee4fdff5e06942N0cfc6b803430b055N0d3590284eace51cN0d7ff3f5b59a1597N0d8a2d98159d9594N0e3047e4cba6acbbN0e7247b7bca0d7eeN0ecead2aefe839f5N0eda56545ec54680N0f10349008018776N0f13856bfc50661dN0f7398bc16afee8bN0f982e6103ce8040N10d11661f9d3331fN111b28433350b42cN111b2babe083814cN112c1d9cc52adb3fN11306aaacf4ec46cN1194577e38aa562dN11bc061fafd0c430N11e71e9a1986fb10N11f1cf1e0b2e16feN12229adf38704984N1230c451fc444a2dN12388431bd7dded4N12e18ba11d39e27fN130c8beb17174aeaN132384d10c866b9fN13300ae3b967a9e2N14a71539803a0b50N14b907e42c5bfa13N14bd4517ac2d0734N14dfb73710970af0N151cb6caa880799aN154de4501d8ad93fN156e29a5872db06cN15728c50a7279295N157321311a9e3604N159a06e2b4b5db03N162b4f49a840de36N166cbbc6bd027a38N16775d786ec164e8N16c6d773ee1e5c7dN16caa81fce2e4f21N1712207d84a3dd54N175bc8011e17ab9eN1768d3dd63c35912N1794188cd52c5731N179710127e23fbb3N17d37dd75cc872cdN1811cdd1465557d8N185173f8f8f0b4b8N1865adfef52bae9cN186cc13fc9d1ac6dN18896a4a91a3cc9bN18bf9b868031a9f4N19022e09df43d9a9N19028bf3441cb1ceN193a1a1294f184a0N195a000d029e7445N195fd94994845108N197e5ab0ecb3979dN19a496a1a4f9a7baN19dc7f674c6adb28N1a1f986572af144aN1a269f6d723cb5adN1a9be3d0efbbe0f0N1af513920033a8ddN1b0e0be338f9eb9aN1b18fa0294924372N1b9134bb74079ff6N1b9c23aff580b5f8N1bb706c8aafa4f06N1bc3438d42f3dec5N1beaf5c11def0dc9N1c19df68ca6f69e6N1c3e0a9e2776912fN1c3e636e8f2e5091N1c62af083f342a27N1c72d2de27e1d02cN1c74bf0b5101925aN1c7e2c031e4e54ffN1c9128c9a5bb883fN1c9338b7294e88e0N1c9e730c90b309c4N1d0f512ef1aee361N1d2438d4f83fed82N1d7dc51664d869fdN1db76f24810c7c23N1e0ae62585b009d4N1e5967f905c119f5N1e948087b69a7017N1ed267bd9ba44384N1f1ba0a8f3871706N1f4c32bd408c3f59N1f58a22b91c91aa2N1f86cc70b0239a1fN1fe640a8b8bd19d0N204f8fd0959ac6cfN20545e089d2fba92N207bc5ffe5973c32N20ce2b6c58d88680N20e1bf5d49956482N2156333ee70797fdN21992b093086236fN219b943704ed175fN21ae141396d7d805N21ae5114e748ea31N21c741aa73a31a2cN229cd8a2c8cb1ff5N22d3b1e601954f7bN230eba7d98dff7dcN232a5863bf5ad8faN233b30d0c147a1daN23996a12f823cefdN24469c9266198c57N2469512702b34ee7N247abbc839b7ddc0N249a15c945f0cc34N24dbb47be628b6c3N2533fa4ed633b69aN253ad38ea7bce403N254bf040d3557206N2573435c37ebf7b6N25e8f7ef0ec906bbN25fe839120b10a12N260c995a51c6fc88N261457eecf9d2dbfN263b8b1e8e86b139N26434cfe3cd203fbN264e61ba74b4db32N2674dbabce0703e0N267b0d4b38bb2cdcN268d0b517f2805a6N26ce26fe12e8e98fN2737386e38c7f6d5N274dd92f8c00db2fN2764baf17696d956N28044e9c8d44c504N280d9007e0e0b79dN28227de6059d316cN2832eb5ee10643c1N284c457855c34112N2893004d3916a4aaN29038e3f50ba6602N296fc86d1c62a884N2b2b964d371af835N2ba27e3e45471b90N2bb9d1069cddf8ccN2bd4356b15564595N2c52a1a728522a32N2c7ee31e24cb7fa9N2cd2559ff4829897N2cee692f1f7f8548N2d0402e536e35601N2d58fcf281435822N2d87228ed46d2f27N2defed45255d5440N2e8465b1084a84b6N2e9db192df033c78N2eb9d4d8690779f5N2ec476f1479c4f95N2ed0bc96af847635N2ed2badd4ad9c07aN2f1503cc3528f60aN2fc712cbc2ed55caN3026c6998ce8307dN307accc8add648d4N30cbdc238695f383N30ecea886ee25ce0N31a26091fd772b41N31c8d441a0474e97N3278c292ec9862e2N332e263b876ac74cN337d240590c0b031N33ae278e80bc1972N33c7df4fcf4350a4N340e01208f4edd45N346414684790ae03N347f9342fbb0c181N34c9185d49637cddN3512f41b255f6cf0N355d3bf9cfb3e181N35657d4ca65ebcf3N35e44279fb79972aN3628e90865929714N36c141b4a373e6e3N37603e893835c683N37988d9ab8b29251N37ffce93f9c6a575N386b5945f3a6135fN3a35d21793eacdfeN3a5546f58d833193N3a6e71ad51417617N3a75925d2e0011d7N3a8907de6f901695N3a8f2f7351605521N3aa844163071be00N3aecb30e1b5a5dcbN3b6bfb285e3ce81cN3b6cf8d5b9da0ab4N3b9919dbdf80263dN3baf198904a19ca1N3c0b21276347e28eN3c71122fe303c0a7N3cc1904bc9844f5cN3d305dd8052597b1N3d6a4eb0f1ce6361N3d8f89b7cdc8327fN3de974091061223aN3e8476501671e950N3e8bd8820474ebe3N3edb1f6006bf9f3cN3f4f9164f24f52d1N3fb9cd4664b9799d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_asn1_get_sequence_of () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.LBof"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.fresh"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Walk.W3"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_D.LoopOblig"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.asn1_get_sequence_of_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.asn1_get_sequence_of_stmt"; "U_ASN1_GET_SEQUENCE_OF"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo tag : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 32 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 176 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 32.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (asn1_get_sequence_of_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation CTX := (bv_unsigned sp + -24).
  (* [comment removed for export] *)
  Notation SPG := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Notation INV := (inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs).
  Notation CBPOST := (cb_post L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR END BUF lo bs).
  (* [comment removed for export] *)
  Definition W3 : list ivl := [(PP, PP + 8); (CUR, CUR + 32); (bv_unsigned sp - 128, bv_unsigned sp)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L1224094474.47 L24089274786.12L28573890933.50L28575982988.51L32795543516.51L36324901792.5 L44010973198.54L44017149326.55L44370725769.50L54391871354.51L63380913806.5400000Y01C02102W02j03=03H03S03_04^04iS1L2sp2PP3CUR3BUF2lo2bs2D22D33SLO3HLS3DS3S1L2sp2PP3CUR2lo3SLO3HLS3ACL1y3HXC3AXP3AXCS2sp2PP3CUR2bs1a2Hs2Ho1L2lo3SLO3HLS3ACL3DHI2HdS1L2sp2PP3CUR2lo2bs3SLO3HLS3ACL1a2Ho1HS2PP3CUR2bs1a2O12O2S1L4DIM14DIM21y3HXDS2bs2cs3HszS2bs2cs3HszS2PP2bs1a2O1S1L2HI2sp1h2PP3CUR3BUF2lo2bs2D22D33SLO3HLS4HTOP3DS31a3Hin2O12O2S2bs2cs3Hsz". (* [comment removed for export] *)
  Lemma sync_T : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of ()) "Pnodes,(0.$1.)Phc,(2.$3.VL,VHI,)Pmm,P,(4.&40.)(5.(4.&8.))Pm1,P,(4.&40.)(5.(4.&8.))Pmoc,$6.P,(7.$3.VL,VHI,R4.(8.VLB,R5.)R3.R1.)P,(9.$1.(:.$3.VL,VHI,R5.)(:.$3.VL,VHI,Vh,))P,(;.VL,VLB,R7.)P,(<.$3.R6.(8.VLB,R8.)VBUF,VEND,R8.=)P,(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R7.)P,(14.$3.R8.VBUF,Vbs,)P,(15.$16.R9.R8.)P,(17.$3.R:.R9.)(18.(7.$3.VL,VHI,R<.(8.VLB,R=.)R:.R9.)(18.(<.$3.R:.(8.VLB,R=.)VBUF,VEND,R=.=)(18.(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R:.)(14.$3.R:.VBUF,Vbs,))))")
(* [comment removed for export] *).
  Proof.
    clear - ACL CWPP CWCUR CRBUF DIM1 DIM2 DHI HBR0 PPB CURB SLO HLS HTOP D2 D3 DS3 B1 B3 B4.
    intros nodes hc mm m1 moc HHx HT HFR HLS' HPX HBY MU WM.
    assert (HSUB : forall b, In b LB -> In b (LBof LB nodes)) by (intros b Hb; unfold LBof; apply in_or_app; right; exact Hb).
    split; [| split; [| split]].
    - eapply HEAP_munch; [exact HHx| exact ACL| exact MU| exact WM|].
      intros a Ha Hin. cbn [outside W3] in Hin. rewrite HT.
      destruct (outside_dec [(PP, PP + 8)] a) as [O1|O1]; cbn [outside] in O1.
      2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWPP HSUB a ltac:(lia)). }
      destruct (outside_dec [(CUR, CUR + 32)] a) as [O2|O2]; cbn [outside] in O2.
      2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWCUR HSUB a ltac:(lia)). }
      left. lia.
    - eapply seq_lseg_mem; [exact HLS'| intros y Hy; eapply seq_lseg_in; [exact HLS'| exact Hy] |].
      intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
      flat constr:((HFR y Hy)) 3%nat. intros HXC HXD HXAP.
      assert (AXP : y + 32 <= PP \/ PP + 8 <= y)
        by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP]).
      assert (AXC : y + 32 <= CUR \/ CUR + 32 <= y)
        by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP]).
      cbn [disjoint_from W3]. clear - AXP AXC HXC ACL SLO HLS. lia.
    - eapply heap_presx_trans; [exact HPX|]. eapply presx_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn [outside W3] in Ho |- *.
      destruct Hc as [Hs|[Hd|Hb]]; [lia| lia| pose proof (in_block_below L LB HBR0 a Hb); lia].
    - eapply bytes_at_transport; [exact HBY| exact MU|]. pose proof (bytes_at_bound _ _ _ _ HBY). cbn [disjoint_from W3]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Ltac tsync mx :=
    repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end;
    first [ lazymatch goal with Hm : munch _ _ mx |- _ => idtac end
          | pose proof (munch_refl (@nil ivl) mx); pose proof (wmono_refl usegs mx) ];
    lazymatch goal with Hm1 : munch ?W1 ?mA mx |- _ =>
    lazymatch goal with Hw1 : wmono _ mA mx |- _ =>
      let MUW := fresh "MUW" in
      assert (MUW : munch W3 mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W3] in Hxw |- *; lia);
      lazymatch goal with HHc : HEAP _ _ _ ?hc (LBof LB ?nodes) mA ?moc, HTc : heap_top _ _ _ ?hc' = heap_top _ _ _ h, HPXc : heap_presx _ _ LB (bv_unsigned sp) _ m mA,
                          HFR : fresh L LB ?nodes', HSG : seq_lseg _ mA _ BUF END _ 0, BYc : bytes_at _ mA BUF bs |- _ =>
        let A := fresh "HH" in let C := fresh "HLS" in let D := fresh "HPX" in let E := fresh "HBUF" in
        (flat constr:((sync_T nodes hc mA mx moc HHc HTc HFR HSG HPXc BYc MUW Hw1)) 4%nat; intros A C D E);
        clear HHc HSG HPXc MUW Hm1 Hw1; try clear BYc;
        try match goal with H : bytes_at _ mx BUF bs, H' : bytes_at _ mx BUF bs |- _ => clear H' end
      end end end.

  (* [comment removed for export] *)
  Ltac rebuild_inv INV mm' :=
    lazymatch goal with
    | HH : HEAP _ _ _ ?hc (LBof LB ?nodes) mm' ?moc, HCUR : rw_cells _ mm' CUR [C4 ?ct; C4 ?cpad; C8 (Z_to_bv 64 ?cl); C8 (Z_to_bv 64 ?cp); _],
      FRG : rw_cells _ mm' (bv_unsigned sp + -32) [CB 8 ?j0; C4 ?tagw; C4 ?zpad; _; _],
      FRT : rw_cells _ mm' (bv_unsigned sp + -128) (CB 8 ?j1 :: _) |- _ =>
        assert (INV : inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs mm' moc hc nodes ct cpad cl cp tagw zpad j0 j1);
        [ unfold inv; unfold seq_cells; (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try (eapply mo_frame_trans; eassumption) | ]
    end.
  Ltac flia := first [clear_disj; lia | lia].
  Ltac joinr H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
      let Hj := fresh "J" in
      pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
      cbn [app] in H1
    end end.
  Ltac lenslot mx :=
    lazymatch goal with HL : rw_cells _ mx (bv_unsigned sp + -128) [C8 _], HR : rw_cells _ mx _ (C8 s9 :: _) |- _ =>
      apply lxp_cell_to_CB in HL; cbn [csize] in HL; joinr HL HR
    end.


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
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
    end.
  (* [comment removed for export] *)
  Ltac cut_frames mx :=
    lazymatch goal with HF : rw_cells _ mx (bv_unsigned sp + -128) ?cs |- _ =>
      lazymatch eval compute in (length cs) with
      | 17%nat => let HG := fresh "FRG" in splitat HF 12%nat HG
      | _ => idtac end end.

  Notation CBA := 126228 (only parsing).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0@L1522838471.141 L1522838471.144 L1522838471.145 L1522838471.147 L1522838471.149 L16882270386.109L1815122797.109 L1815122797.122 L19615206823.123L19615206823.136L22704459656.5  L23643007576.123L23643007576.136L24793115312.133L27668654086.120L2936365656.109 L34924923261.123L38892891850.139L42802377143.132L42802377143.137L47203022477.123L47844901431.135L48148060671.139L49917522021.132L49917522021.135L49917522021.137L52757608417.128L57626602889.5  L60925704695.128L65761178213.122L68356205778.3  L68473235704.123L68473235704.136L6974890779.123 L7889758911.123 L7889758911.136 00000>00L00Z00h01602502602702802902K02L02M02d04>04[04i05E05S05a06106?06W06o07F07^08508G08U08c08l08m08n09<09=09>S2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR2bsS1L2sp2PP3CUR1P3END2lo2bs3PPB4CURB3ACP4ACL'4SLO'5HLS'02p'2H12H2FFFFS2sp2PP3CUR2xw3HxwFFS2sp2PP3CUR1P3END2bs2H7S1L2sp2PP3CUR1P3END3BUF2lo2bs2D12D22D33PPB4CURB3ACP3DS13DS23DS32B24ACL'4SLO'5HLS'03B1'3B3'S2sp2PP3CUR1P3END2bs2p'2H12H2S2sp2PP3CUR2bsS2sp2PP3CUR1P3END2bs4lxv02H5S2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR1P2bsS2sp2PP3CUR2bsS2sp2PP3CUR1P2bs4lxv02HNS2sp2PP3CUR1P3END2bs3H10S2sp2PP3CUR1P3END2bs2H9S2sp2PP3CUR1P3END2bs3H10S2sp2PP3CUR1P3END2bs2B2S2sp2PP3CUR2xw3HxwS2sp2PP3CUR2bsS2sp2PP3CUR2bsS4lxv02H6FFS2sp2PP3CUR2bsFF". (* [comment removed for export] *)
  Lemma traverse_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of ()) "Ptgw,(4.&40.)Ptagw,(4.&40.)Pj0,(0.(4.&8.))Px5,(4.&40.)Px6,(4.&40.)Px7,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))P,(7.$3.VL,VHI,Vh,VLB,R1.Vmo,)P,(1?.$3.R2.VCUR,(2=.(22.&40.=)(22.&40.=)===))P,(1?.$3.R3.(12.(>.&40.Vsp,)-20.)(?.$20.(2>.#8.R;.)(?.$20.(2?.R<.)(?.$20.(2?.(22.&40.=))(?.$20.(21.(22.&40.VCUR,))(?.$20.(21.Vra,)(13.$20.)))))))P,(30.$3.R4.Vlo,(12.(>.&40.Vsp,)-20.))P,(31.$3.R5.)P,(14.$3.R6.VBUF,Vbs,)P,(1?.$3.R7.VPP,(?.$20.(21.(22.&40.VP,))(13.$20.)))P,(19.VP,VEND,)P,(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R9.)(25.$3.Vmo,(26.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(27.(28.(22.&40.+1>=08.)(22.&40.(12.(>.&40.Vsp,)-20.))Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(22.&40.VPP,)(22.&40.VEND,)(22.&40.+??.)R14.(22.&40.=)(22.&40.=)(22.&40.+1>=14.)(22.&40.(12.(>.&40.Vsp,)-18.))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(22.&40.+1>:24.)Vfc,(29.(4.&40.))R:.(2:.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros tgw tagw j0 x5 x6 x7 x28 x29 x30 x31 mm HH HCUR FRG ST MI HBUF HPP B2 HPX.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof ACL as ACL'. pose proof SLO as SLO'. pose proof HLS as HLS'0. pose proof SPB as SPB'. pose proof SPA as SPA'.
    pose proof B1 as B1'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'. pose proof CURB as CURB'. pose proof D1 as D1'. pose proof D2 as D2'. pose proof D3 as D3'.
    pose proof DS1 as DS1'. pose proof DS2 as DS2'. pose proof DS3 as DS3'. pose proof HTOP as HTOP'.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    unfold seq_cells in HCUR.
    (* [comment removed for export] *)
    pose proof HH as HHc. change (HEAP usegs L HI h (LBof LB []) mm mo) in HHc.
    assert (HTc : heap_top usegs L HI h = heap_top usegs L HI h) by reflexivity.
    assert (HFR : fresh L LB []) by (intros x Hx; destruct Hx).
    assert (HND : List.NoDup (@nil Z)) by constructor.
    assert (HSG : seq_lseg usegs mm (LBof LB []) BUF END [] 0) by exact I.
    assert (HBUFOK : (0 = 0 /\ 0 = 0 /\ (@nil Z) = []) \/ (BUF <= 0 /\ 0 <= 0 /\ 0 + 0 <= END)) by (left; (flsplit; repeat split); reflexivity).
    pose proof HPX as HPXc. pose proof HBUF as BYc. pose proof (mo_frame_refl mo) as MF.
    (* [comment removed for export] *)
    carve_frame 96%nat ST.
    lazymatch type of FR with rw_cells usegs ?mx ?A [CB 96 ?j] =>
      set (JJ := j) in FR; clearbody JJ;
      change (rw_cells usegs mx A ([] ++ CB 96 JJ :: [])) in FR;
      apply (rw_cells_split_CB usegs mx A [] 96 JJ [] [8; 88]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR end.
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1e4e4; 0x1eb80; 0x1ebbc] [] 100%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch pc with
         | 0x1e4e4 => idtac
         | 0x1eb80 => tsync mx; cut_frames mx; rebuild_inv INV2 mx; eapply exit_walk; try exact INV2; try eassumption; flia
         end end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => set (m1 := mx) in *; clearbody m1 end.
    lazymatch goal with FRx : rw_cells _ m1 (bv_unsigned sp + -128) _ |- _ =>
      apply (rw_cells_CB8_C8 usegs _ _ []) in FRx; cbn [app] in FRx;
      lazymatch type of FRx with rw_cells _ _ _ (?c :: ?rest) => destruct (proj1 (rw_cells_app usegs m1 (bv_unsigned sp + -128) [c] rest) FRx) as [FRL FRR] end end.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRR.
    replace (bv_unsigned sp + -128 + 8) with (bv_unsigned sp + -120) in FRR by lia.
    pose proof U_asn1_get_len_spec as SPL. unfold asn1_get_len_stmt, U_ASN1_GET_LEN in SPL.
    eapply aevtM_cut_evt; [exact MK| eapply SPL with (PP := PP) (LENP := bv_unsigned sp + -128) (P := P + 1) (END := END) (BUF := BUF) (bs := bs); try eassumption; try reflexivity; try lia |].
    clear SPL. intros ms' PO. unfold asn1_get_len_post in PO.
    destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & rl & p2 & Ll & -> & MU2 & WM2 & MI2 & EA0 & HRL & HPP2 & HLEN2 & HP2 & HOK).
    subst ya0.
    rewrite ret_pc_even by first [lia | reflexivity].
    lazymatch goal with BYx : bytes_at _ m1 BUF bs |- _ => pose proof (bytes_at_transport usegs _ _ _ _ _ BYx MU2 ltac:(cbn; repeat split; try exact I; lia)) as BY2 end.
    lazymatch goal with CUx : rw_cells _ m1 CUR _ |- _ => pose proof (rw_cells_transport usegs _ _ _ _ _ CUx MU2 WM2 ltac:(cbn; repeat split; try exact I; lia)) as CU2 end.
    pose proof (rw_cells_transport usegs _ _ _ _ _ FRR MU2 WM2 ltac:(cbn; repeat split; try exact I; lia)) as FRR2.
    lazymatch goal with STx : stk _ m1 lo _ |- _ => pose proof (stk_transport_disjoint usegs _ _ _ _ _ STx MU2 WM2 ltac:(cbn; repeat split; try exact I; lia)) as ST2 end.
    lazymatch goal with MUx : munch _ mm m1, WMx : wmono _ mm m1 |- _ =>
      assert (MUc : munch W3 mm m2) by (eapply munch_trans; [eapply munch_weaken; [| exact MUx] | eapply munch_weaken; [| exact MU2]]; intros xw Hxw; cbn [outside W3] in Hxw |- *; lia);
      assert (WMc : wmono usegs mm m2) by (eapply wmono_trans; [exact WMx| exact WM2]) end.
    repeat match goal with Hx : context [m1] |- _ => clear Hx end. clear m1.
    clear HH HCUR FRG MI HBUF HPP HPX ST FR.
    tsync m2.
    repeat match goal with Hx : context [mm] |- _ => clear Hx end.
    destruct (Z.eq_dec rl 0) as [E|E].
    2:{ rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
        lx_run_tac (PLANS [0x1eb80; 0x1eac0; 0x1ebbc] [] 4%N (@nil summary)); lx_tree.
        all: apply evt_done; cbv beta; rewrite <- TP.
        all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
             lazymatch pc with
             | 0x1eb80 => tsync mx; lenslot mx; cut_frames mx; rebuild_inv INV2 mx; eapply exit_walk; try exact INV2; try eassumption; flia
             | _ => exfalso; flia
             end end. }
    subst rl. destruct (HOK eq_refl) as [HOK1 HOK2].
    pose proof (bv_unsigned_in_range 64 Ll) as LLR. unfold bv_modulus in LLR. cbn in LLR.
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1eafc; 0x1eb80; 0x1ebbc] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         tsync mx; lenslot mx; cut_frames mx; rebuild_inv INV2 mx;
         lazymatch pc with
         | 0x1eafc => eapply loop_head; try exact INV2; try eassumption; flia
         | 0x1eb80 => eapply exit_walk; try exact INV2; try eassumption; flia
         end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Definition U_ASN1_GET_SEQUENCE_OF : Z := 0x1ecc4.

Local Ltac2 Set LiaOrc.tbl := fun () => "0070@D28573890933.104D39822696399.105D43777662812.102L32795543389.3  L34290115814.87 L43055549449.85 L54391871483.14 00000j01Z01l02602M03=03eS2sp2PP3CUR2bs1a2Hs2Ho1L3HLS2lo3NZ13NZ23SLO3ACL3DHI3SPB2HdS1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3ACL3SPB1a2HoS2sp2PP3CUR2bs3SPBS3CUR1a2O1S2sp2PP3CUR2bs3PPB4CURBS1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3SPB3PPB4CURBS1L2HI3HLS2sp1h3CUR2lo3SLO4HTOP1a3Hin2O1". (* [comment removed for export] *)
Lemma U_asn1_get_sequence_of_spec : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of ()) "PL,$32.PHI,(33.$3.R1.)P,(9.$1.(34.R2.)$35.)P,(19.=(36.R3.))(37.$3.R4.R3.$38.)")
(* [comment removed for export] *).
Proof.
  intros L HI HCALLOC HLS. unfold asn1_get_sequence_of_stmt, U_ASN1_GET_SEQUENCE_OF.
  intros until cjunk. intros HH HPP HCUR HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3
    CWPP CWCUR CRBUF TP MI -> -> -> ->.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. pose proof (proj1 ST) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HCUR) as CURB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, CURB.
  flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
  carve_frame 32%nat ST.
  change (Z.of_nat 32) with 32 in CURB. change (Z.of_nat 8) with 8 in PPB.
  pose proof (bytes_at_bound _ _ _ _ HBUF) as BB. unfold seq_cells in HCUR.
  (* [comment removed for export] *)
  assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
  rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
  lx_run_tac (PLANS [0x1ea24] [] 60%N (@nil summary)); lx_tree.
  all: apply evt_done; cbv beta; rewrite <- TP.
  lazymatch goal with Hm1 : munch ?W1 m ?mx, Hw1 : wmono _ m ?mx', HC : rw_cells _ ?mx'' CUR _ |- aevtM _ _ _ (MS _ _ _ _ _ ?mx3 _) =>
    assert (HH1 : HEAP usegs L HI h LB mx mo);
    [ eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact ACL| exact Hm1| exact Hw1|];
      intros a Ha Hin; cbn [outside] in Hin;
      destruct (outside_dec [(CUR, CUR + 32)] a) as [O1|O1]; cbn [outside] in O1;
      [ left; clear - Hin O1 LO0 SLO HLS HTOP Ha; lia | exact (CWCUR a ltac:(clear - O1; lia)) ]
    | ];
    assert (HPX : heap_presx usegs L LB (bv_unsigned sp) [(PP, PP + 8); (CUR, CUR + 32)] m mx);
    [ eapply presx_munch; [exact Hm1| exact Hw1|];
      intros a Ha Hc Ho; cbn [outside] in Ho |- *;
      destruct Hc as [Hs|[Hd|Hb]]; [dlia| dlia| pose proof (in_block_below L LB HBR0 a Hb) as HY; generalize HY; dlia]
    | ];
    pose proof (rw_cells_reshape usegs mx CUR _ (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0) HC ltac:(cbn; (flsplit; repeat split); reflexivity) eq_refl) as HCUR2
  end.
  eapply traverse_walk; try exact HCUR2; try eassumption; try dlia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
