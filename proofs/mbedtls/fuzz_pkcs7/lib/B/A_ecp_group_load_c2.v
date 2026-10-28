(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_copy A_mpi_bitlen A_ecp_defs A_ecp_statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAEcpSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_ecp_group_load.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0085f75601846fe0 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P00b4f8b981352b30 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P00d4c20f7ccc9b3d 0 2 0 1 2 1P013414eca02d29e5 0 2 0 1 2 1P013761c6893dd17c 0 4 0 1 53 1 58 1 59 1P018f9edbbc1f23f7 0 2 0 1 2 1P01dd4a70d5b3f698 0 2 0 1 1 1P01de316cac87d439 0 4 0 1 53 1 58 1 59 1P020de39018d75771 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P0266f5f47232ab4a 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P02753471e266964c 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P02c7d241ba734e4d 2 52 1 1 8 3 2 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 1 1 59 1 62 1 4 0 2 60 2 61 2 63 16P03027584fa5b95ed 0 2 0 1 2 1P030ef6cb8f3865b8 0 2 0 1 2 1P032d5d4198cf1b7c 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P033d523a72195065 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P0344f027846b50a3 0 4 0 8 43 8 57 8 58 8P037df9c5288f9f3f 0 2 0 1 1 1P03afe031a74f695b 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P04102c220dec7d97 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P0442a46dad66e149 0 4 0 8 44 8 58 8 59 8P045bf1f4674696cd 0 2 0 1 1 1P04f6778c1f2cf81b 0 4 0 8 42 8 58 8 59 8P051b9c29eb7af2c6 0 2 0 1 2 1P0545f3a30ae2e625 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P05ad79e45c2ca638 0 2 0 1 2 1P05b40914f3d5e0f8 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P061acf3110d83723 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P062dd92e48c1f442 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P0635f8c164d885ed 0 2 0 1 2 1P065b3dd22f050a8d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P06a4e5a86cb505a3 0 2 0 1 1 1P06c71cfaa70c20f2 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P06d0023487d45dfc 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P06d713604144811f 1 1 8 2 0 1 59 1 3 5 1 60 1 61 8P071fca0c35357303 0 5 0 1 50 1 51 1 57 1 58 1P0734adec2c57b984 2 48 1 1 8 3 1 1 55 1 56 1 5 0 1 49 1 54 1 57 1 58 8 1 1 8 3 2 1 54 1 57 1 4 0 2 55 2 56 2 58 16P075ffdd3cc446347 0 2 0 1 1 1P07646d4404b33a31 0 4 0 8 42 8 58 8 59 8P0774d1819418d3e9 0 4 0 8 42 8 56 8 57 8P080c3abf244258d2 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P0811ef7653fa64b6 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P0812dc500ccf4fc2 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P083263cc770c5119 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P083298e0ee40cabe 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P08d61bdf5e2f0956 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P08ea6649e456093e 0 4 0 1 50 1 55 1 56 1P08f22af633cf33c6 0 4 0 1 53 1 58 1 59 1P091558efc94c082c 0 2 0 1 1 1P095f1904a4997ad2 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P09651a57867af443 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P09726dd225251d8c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0990ff65e77a4724 1 1 8 2 0 1 59 1 3 5 1 60 1 61 8P09b7ed6182a208b0 0 2 0 1 1 1P09c307aede7573f5 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0a0cd412a7ad6214 0 4 0 8 42 8 56 8 57 8P0a0ee511b7da940e 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P0a109296453a59b2 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0a793fb95bca024d 0 2 0 1 1 1P0a84c59ac78b70a4 0 4 0 8 42 8 56 8 57 8P0b62e0d6b767a7ff 0 4 0 1 50 1 57 1 58 1P0ba04f7e26259bcb 1 1 8 2 0 1 59 1 3 42 1 58 1 60 8P0bd45bb9f5b9a868 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P0c122962009cab9a 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P0c4a0142bf7ca398 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P0c64e059d49aa217 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0c776bb07c352479 0 2 0 1 2 1P0c99b87b1d837657 0 2 0 1 1 1P0cb9473f645fc4d2 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P0cd6f848227ff66d 0 2 0 1 1 1P0d2ee20ba4bd8cea 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P0d6d336b0b27a482 0 2 0 1 1 1P0da0a56ac3043761 0 4 0 8 43 8 59 8 60 8P0da179b1b33995d5 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0e6059688e845df5 0 2 0 1 2 1P0e72052c47bcfc63 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P0ea096b3ec1d3bee 0 4 0 8 43 8 55 8 56 8P0eb3572acb39d1d9 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0ebd22dc1f326681 0 2 0 1 2 1P0f200510ca792827 0 2 0 1 1 1P0fad4eb7abc64fc0 0 4 0 8 42 8 56 8 57 8P0ff3324611185ae2 0 2 0 1 1 1P1017aee5e9de6b2b 0 4 0 8 40 8 52 8 53 8P1031dd4ea997839a 0 2 0 1 2 1P106ef45efe30f632 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P10cb3caf3a417005 0 2 0 1 1 1P10eb543817c7c3b0 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P11351bd61a15bc91 0 2 0 1 2 1P1143dabe7c96da22 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P115a409ea51b8775 0 2 0 1 2 1P1184cac4a6183e8a 0 4 0 1 50 1 57 1 58 1P1198afbe34693558 0 2 0 1 2 1P11ef8bf3e562ebe8 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P120c5ad6500ee9b0 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P1223e489848b11e3 0 4 0 8 43 8 55 8 56 8P125bd36e1355dc2c 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P12df92102d239ccc 2 52 1 1 8 3 2 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 1 1 57 1 60 1 4 0 2 58 2 59 2 61 16P13317a637157ef0c 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P13c90364291824fa 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P141ba639a9222b0f 0 4 0 1 49 1 55 1 56 1P14f72b5c7f575a7c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1519b19eccdd7f27 0 2 0 1 1 1P15204c4982c60efd 0 4 0 8 42 8 56 8 57 8P15661586dcc4c7ad 0 4 0 8 42 8 56 8 57 8P1578bfc1008f4dab 0 4 0 1 49 1 57 1 58 1P15e9c9d156275e37 0 4 0 8 43 8 55 8 56 8P1611fc8a8497bb0b 1 1 8 2 0 1 59 1 3 5 1 60 1 61 8P1645b5781eb06f57 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P164b24a71af09f6b 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1729ff5f695aa29f 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P1736b9c202d51b43 0 2 0 1 1 1P1765283a4dd5b1cc 0 2 0 1 2 1P17824a7d67d1eff9 0 4 0 8 42 8 58 8 59 8P17f6ce432877bd78 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P17fd0b08f2a62ead 0 2 0 1 2 1P18106f39784f22b5 0 4 0 8 44 8 58 8 59 8P1853973989d347e2 0 2 0 1 2 1P18971981d6424608 0 4 0 8 43 8 57 8 58 8P18a6adbb8010c5e1 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P18cace87a0386baa 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P18dd29dc0f1359fb 2 48 1 1 8 3 1 1 55 1 56 1 5 0 1 49 1 54 1 57 1 58 8 1 1 8 3 2 1 54 1 57 1 4 0 2 55 2 56 2 58 16P196d536284a6eb58 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1990bb368a490504 0 4 0 8 42 8 56 8 57 8P19a053475b0ecee3 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P19e860652f8638bc 0 2 0 1 1 1P1a1e566d16f42fa5 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P1a4e24bee915742e 0 2 0 1 2 1P1a6e8efb230854c8 0 4 0 8 43 8 57 8 58 8P1a70dbe42ef64d22 0 2 0 1 1 1P1ad3ce37d4501d7e 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P1b3ee2de453488eb 0 4 0 1 53 1 58 1 59 1P1b46479b409d9f2c 0 2 0 1 1 1P1b5b8e9685c9b777 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P1c1bbe37db99dbc5 0 2 0 1 1 1P1c2bb2bc076c2a16 0 2 0 1 1 1P1c59432e47c2db1f 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P1c6e5a87947c9445 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P1d8720aa5735d480 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1dbd0a8ffe18f523 0 2 0 1 2 1P1e20743a542de6dc 0 4 0 1 50 1 55 1 56 1P1e39681b73e41735 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1e57ad5dda5421fa 0 4 0 8 43 8 55 8 56 8P1ed78904bd572bf9 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P1edfa4dcbf67d9d0 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P1efa0c79ce2583ce 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P1efb95667b60ce7a 0 4 0 8 42 8 56 8 57 8P1f17a01d2a0578a2 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P20123166c00276de 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P202a074d5a2ad691 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P215db95a818ba59e 0 2 0 1 1 1P218dc04ada0b1e1f 0 4 0 8 42 8 58 8 59 8P219dc68ed8f82a7c 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P21aa238b3b3e8ac8 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P21dab49684b30c8a 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P21f37f11f47b307e 0 2 0 1 2 1P222112a20e4a6e3a 0 4 0 8 43 8 55 8 56 8P2248f3b62789a6d6 0 4 0 8 44 8 58 8 59 8P22785b29a0961f51 0 4 0 8 42 8 58 8 59 8P22de13c379872f7d 0 4 0 1 50 1 55 1 56 1P23242d1dfde04d82 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2374f910d3c7a9f8 0 2 0 1 1 1P2377402dddb705b5 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P23c1cd9997bbfb80 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P23f3cd98c2af400b 0 4 0 8 43 8 55 8 56 8P2433e75f6bc5a098 0 2 0 1 1 1P24738ecd0b2b7335 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P24a652bcba7a46aa 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P24b1c2154ef4d530 0 2 0 1 1 1P254b3c10e699b90f 0 4 0 8 43 8 55 8 56 8P257b4362e24837a0 0 2 0 1 2 1P258057695933c65c 0 4 0 8 44 8 58 8 59 8P25d898891f5fbabf 0 2 0 1 2 1P25df5fe9b293f993 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P26b7147b10822ead 1 1 8 2 0 1 59 1 3 42 1 58 1 60 8P2792a30baea96079 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P27adf9975880f408 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P27d3757e939d24c6 0 4 0 8 43 8 59 8 60 8P280237197372902d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P280480d0e4b176f7 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2872756dcc0aa35d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P288333f18fac356b 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P28d35dd0c390221f 1 1 8 2 0 1 58 1 3 2 1 59 1 60 8P291c410659c1f24f 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P29323133738fc0c9 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2959bf830d02c4ae 0 4 0 8 43 8 57 8 58 8P2996fbc211de94bb 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P29ad6ee54bf0cd36 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P2a01b091b82b56bd 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P2a5bb560be4d4844 0 2 0 1 1 1P2a680426b95b556c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P2a989930b9183167 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P2ab8f2d0966848cb 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2b3d110940b2f9db 0 5 0 1 50 1 51 1 55 1 56 1P2b6e51fba58ba48a 0 4 0 8 43 8 57 8 58 8P2b7e22a3510933e9 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P2bd989872c81fbde 0 2 0 1 1 1P2bfb9c7e6abc08d4 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P2bff8077df524151 0 2 0 1 1 1P2c22cc01851fde06 0 2 0 1 2 1P2c49476a903600b9 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P2c6e3acb0c8dc518 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P2d63c1afc5e0b49a 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P2d9acdcc79167982 2 51 1 1 8 3 1 1 61 1 62 1 5 0 1 51 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P2de60cbb4ac4f7cd 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2e0379a460581e08 0 2 0 1 2 1P2ec2cecad54e04d7 0 4 0 8 43 8 55 8 56 8P2ef2709eaebd36e6 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P2f0a31caf39b55c7 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P2f9d00987c494fe1 0 2 0 1 2 1P2f9e55c8fc7f6deb 0 2 0 1 1 1P2fa2c386f78b997c 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P2fb5508a9c7f9cfb 0 4 0 1 53 1 58 1 59 1P2fd363575db65489 0 2 0 1 2 1P2fff4276bfb230e9 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P30069fc6e7e5f8ef 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P30421c36ddc0a78f 0 2 0 1 2 1P305f91ce1ea2bc06 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P30b5977579361862 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P31956961f34a040c 0 4 0 8 43 8 57 8 58 8P31a8d248107e37fc 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P31bf86dd25ba8b5d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3237e234a84227a9 0 2 0 1 2 1P325573ac971800b9 0 4 0 8 42 8 56 8 57 8P3279fe33b3cb8dfd 0 4 0 8 43 8 57 8 58 8P32f14ad207db209c 0 2 0 1 1 1P332b8e864b36198c 0 2 0 1 2 1P33723066be998086 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P33efa64091bf8b3d 0 2 0 1 1 1P340459c0c3279299 0 2 0 1 2 1P347c51a7e3b6b516 1 1 8 2 0 1 59 1 3 42 1 58 1 60 8P3487341c33e55ff3 0 2 0 1 2 1P34999498ff6e1045 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P34c9eec3216a4b99 0 2 0 1 1 1P350fc69a240a7b46 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P3538e9dcd8efa9a1 0 2 0 1 1 1P35ad1e97f8fdb26b 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P35f985a71b09d1b7 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P361eaff91c6c69ce 0 2 0 1 2 1P36fbcd3553d6046c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P37ceb342207a1919 0 4 0 8 43 8 57 8 58 8P38d7cc60b96711f4 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P38f94595431055c6 0 2 0 1 1 1P390e6740951161a1 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P390f1e9ad6607dd0 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P394e6a416b705b08 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P399e03b56d74e2bd 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P39a16561eb9fa82a 0 4 0 8 40 8 52 8 53 8P3a5a1ded14d14584 0 4 0 8 44 8 58 8 59 8P3a5dfead04d2f504 0 4 0 8 42 8 56 8 57 8P3a5ed728b06eb3f6 0 4 0 8 43 8 57 8 58 8P3a94aded77606a48 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3ab7cb3ef6b842c2 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3af5614457bd243d 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P3b0e7d1a72d99413 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P3b229df87eee6f81 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P3b76904d7d1e2f37 0 4 0 8 43 8 55 8 56 8P3ba870a9b9465560 0 2 0 1 2 1P3bc4370e5beb0c2c 1 1 8 2 0 1 58 1 3 4 1 59 1 60 8P3c00802c6f0d1951 0 2 0 1 2 1P3c35ca8506a5a606 0 2 0 1 1 1P3c4b5181ee20499c 0 4 0 8 43 8 55 8 56 8P3c927fd92996b8b0 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3d91a588b8c5f559 0 2 0 1 2 1P3dad385b7f531e3e 1 1 8 2 0 1 53 1 3 40 1 52 1 54 8P3dd61b163465fac7 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3df149daed9b1367 0 4 0 8 42 8 56 8 57 8P3e093d3b4f7b6674 0 4 0 8 42 8 58 8 59 8P3e0d3b6a2b22c660 0 4 0 8 42 8 56 8 57 8P3e5afeca2543a072 0 4 0 8 43 8 55 8 56 8P3ea64f357ee3c348 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P3eae66898f568bd8 2 52 1 1 8 3 1 1 62 1 63 1 5 0 1 52 1 61 1 64 1 65 8 1 1 8 3 2 1 61 1 64 1 4 0 2 62 2 63 2 65 16P3efa6a5607a3f013 0 4 0 8 42 8 56 8 57 8P3f67ad7cfaf8603f 0 2 0 1 1 1P3f786ee70a093982 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3f8c978a4e4cc1a6 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P3f9a22f5e041d13a 0 4 0 1 50 1 57 1 58 1P3fb27c2a46cb0500 2 52 1 1 8 3 1 1 62 1 63 1 5 0 1 52 1 61 1 64 1 65 8 1 1 8 3 2 1 61 1 64 1 4 0 2 62 2 63 2 65 16N00dfd9de6405ff97N01483f81191c1552N02b57d6e77ee8c39N030b3e501bdbb1bdN032309da10e3e1aaN0490ddcdbc03edf7N050d4bc494632890N06cca66162ac8358N084fce7adcbc8986N091f5813c56922c0N0958bb0421ab0ea3N0a3b35a876fd7143N0a6e5a6c28c9a50bN0a734ec20310b6f3N0b32951e2089f450N0b912fda1226f9f1N0c87aee437d20f54N0e376fb2c8c7672eN0f218863c36bd8cfN0fa82ffeaa7cd09dN1027512673cfe26dN110b06043554e425N1231c8d4851fd785N12512db52564f391N12df446d8b7988d6N135e843f4003e86aN1361d50aeaf52dcfN136fca1838ff750cN13835ca2660aa4a8N13dfa92cd2262641N148f30e44ad5be5fN151e597a0760349cN15a95e21c749c261N160db78bae233011N161ecb9b9cd5a8bcN164eb20d2de51151N187e1a25bae253d3N193ef663d9044e98N1b79b14125eb759eN1c088ca82ccb89caN1c3eeae10fe343deN1d541f5e6f9bd671N1db92681907a55f1N1dcd991577055c35N1e915b8880e78af8N1f21a855f9383768N1f657362fac487b2N1fe74cf3ef244bfeN2086d97590c9ed59N20b1763768143f9dN213c790a531930c5N214d63cf2cb01984N2186cc487b6177efN21a72d2470d0fe72N21a7a2ae475f97ecN222bd40ac3ceaef7N22886f020a48a17bN233337b17f419d1dN23713b0ffc927987N24809fc5a3914fe0N26218c7cbf3f9751N267055fa42af4c99N2829992bb35837a5N286e723c650f7866N28791dcc0c692e4dN2939d6a3cc456b68N2aede7f3c66fdf4aN2b3fab6ba7741e06N2bb561ef0a7e3512N2bb94c279b4da11aN2bcd6dd26771700bN2c2cdce4892c55f6N2e27b82e5792ffa5N2eecaa769a6ed037N2f8a73f359ffd732N304ac5fcbb6b997bN30a517378bc08b8aN31cfbc07b987f91fN325ea49b5a70c126N330c370a39091f49N33710681561154d3N33dce459aa3bd5adN34393f1d07a4d801N34a0d6f142ef1f27N352c28f466ca269fN35aebe9136e1dcbeN35ca9e1833637696N36898aa8bee242baN37531dcac2d24fc9N377e5d8f9a5018edN378d582dc68be725N388a688e88bde2b2N38c2e592478f529cN38c8f65f484436a4N391675366bcfe05cN3965df61707e450eN3a054620a0a899e7N3aa74f58e270d985N3ab43d39a5813bf0N3b4f19ee600fdbeaN3c086dd4d83ed5bbN3c372dfc8d465750N3c38c6388970b13aN3cc71674f02ce15fN3db62636b1cb0073N3e80633d53e88f61N3f3bdb883745382dN3f9daa387c256b84N3fe51b33f76cb697"%lxh.
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
Ltac2 gd_tbl_A_ecp_group_load_c2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_init_cells"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_sw_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section GLC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Notation gl_sw_post := (gl_sw_post R HIA).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25296973522.0  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46982844833.0  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L49455700789.14 L50597913045.3  L53835837837.6  L54937175313.3  L56803381133.6  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L62867260193.0  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05c05f05g05h06406506<06=06H06K06N06Q06c06d06e06h07@07C07D07H07K07L07O07V07W07X07Y07Z07[07\07]07^07j07k07l07m07n08>08?08O08P08S08V08`08a08d08g08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFS1AS1AFFS2sp1A2lo2DSFS2sp2loSS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1AFS1AS2sp2loFFFFFFSFS2sp1A2lo2DSFFFFS1R2lo3LOS3ALO1HFS1R2lo3LOS3ALO1HFS1AS1AS1R2lo3LOSFS1AS1ASS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case7 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c2 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+7.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+7.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+7.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=28?<.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros HH (HD & HP & HA & HB & HX & HY & HZ & HN & HT) AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 7 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd290c, DJoin); (0xd292c, DJoin); (0xd294c, DJoin); (0xd2970, DJoin); (0xd2990, DJoin); (0xd29b0, DJoin); (0xd29d4, DJoin); (0xd29f4, DJoin); (0xd2a14, DJoin); (0xd2a38, DJoin); (0xd2a58, DJoin); (0xd2a78, DJoin); (0xd2a9c, DJoin); (0xd2abc, DJoin); (0xd2adc, DJoin); (0xd2b00, DJoin); (0xd2b20, DJoin); (0xd2b40, DJoin); (0xd2b64, DJoin); (0xd2b84, DJoin); (0xd2ba0, DJoin); (0xd2bc8, DJoin); (0xd2bec, DJoin); (0xd2c08, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 7)) (cP 7) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 7)) (4 * Z.of_nat (length (cP 7))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 7)) (cP 7) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 7)); vm_compute (Z.of_nat (length (cP 7))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd290c, DJoin); (0xd292c, DJoin); (0xd294c, DJoin); (0xd2970, DJoin); (0xd2990, DJoin); (0xd29b0, DJoin); (0xd29d4, DJoin); (0xd29f4, DJoin); (0xd2a14, DJoin); (0xd2a38, DJoin); (0xd2a58, DJoin); (0xd2a78, DJoin); (0xd2a9c, DJoin); (0xd2abc, DJoin); (0xd2adc, DJoin); (0xd2b00, DJoin); (0xd2b20, DJoin); (0xd2b40, DJoin); (0xd2b64, DJoin); (0xd2b84, DJoin); (0xd2ba0, DJoin); (0xd2bc8, DJoin); (0xd2bec, DJoin); (0xd2c08, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_N end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_N, MIc : mem_inv _ mq_N |- _ =>
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 7)) (cN 7) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 7)) (4 * Z.of_nat (length (cN 7))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 7)) (cN 7) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 7)); vm_compute (Z.of_nat (length (cN 7))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd290c, DJoin); (0xd292c, DJoin); (0xd294c, DJoin); (0xd2970, DJoin); (0xd2990, DJoin); (0xd29b0, DJoin); (0xd29d4, DJoin); (0xd29f4, DJoin); (0xd2a14, DJoin); (0xd2a38, DJoin); (0xd2a58, DJoin); (0xd2a78, DJoin); (0xd2a9c, DJoin); (0xd2abc, DJoin); (0xd2adc, DJoin); (0xd2b00, DJoin); (0xd2b20, DJoin); (0xd2b40, DJoin); (0xd2b64, DJoin); (0xd2b84, DJoin); (0xd2ba0, DJoin); (0xd2bc8, DJoin); (0xd2bec, DJoin); (0xd2c08, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    try match goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp) end.   (* [comment removed for export] *)
    finish; try eassumption; try (clear - SLO; lia).
    unfold gl_sw_cells; cbv zeta; do 8 (split; [assumption|]); assumption.
    all: match goal with |- ?g => idtac "CASE7-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L10897409697.0  L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L12808385313.0  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27669281997.6  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36311508685.6  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46243424357.14 L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L7262368338.0   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05P05W05X05Y05Z05a05b05e05h05i05j06606706>06I06L06\06_06b07407507607907Q07T07d07e07i07l07m08008708808908:08;08<08=08>08?08K08L08M08N08O08P08S08V08`08a08d08g08j09J09M09N09a09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSSFFFS1A3POSFFSS1A3POSFS1AS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1R2lo3LOS3ALO1HS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AS1R2lo3LOS3ALO1HFS2loS1AFS1AS2sp2loFFFFFFFFS2sp1A2lo2DSFFFFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0SS1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case8 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c2 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+8.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+8.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+8.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=1?0<.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros HH (HD & HP & HA & HB & HX & HY & HZ & HN & HT) AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 8 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1efc, DJoin); (0xd1f1c, DJoin); (0xd1f3c, DJoin); (0xd1f5c, DJoin); (0xd1f80, DJoin); (0xd1fa0, DJoin); (0xd1fc0, DJoin); (0xd1fe4, DJoin); (0xd2004, DJoin); (0xd2024, DJoin); (0xd2048, DJoin); (0xd2068, DJoin); (0xd2088, DJoin); (0xd20ac, DJoin); (0xd20cc, DJoin); (0xd20ec, DJoin); (0xd2110, DJoin); (0xd2130, DJoin); (0xd2150, DJoin); (0xd2174, DJoin); (0xd2194, DJoin); (0xd21b0, DJoin); (0xd21d8, DJoin); (0xd21fc, DJoin); (0xd2218, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 8)) (cP 8) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 8)) (4 * Z.of_nat (length (cP 8))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 8)) (cP 8) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 8)); vm_compute (Z.of_nat (length (cP 8))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1efc, DJoin); (0xd1f1c, DJoin); (0xd1f3c, DJoin); (0xd1f5c, DJoin); (0xd1f80, DJoin); (0xd1fa0, DJoin); (0xd1fc0, DJoin); (0xd1fe4, DJoin); (0xd2004, DJoin); (0xd2024, DJoin); (0xd2048, DJoin); (0xd2068, DJoin); (0xd2088, DJoin); (0xd20ac, DJoin); (0xd20cc, DJoin); (0xd20ec, DJoin); (0xd2110, DJoin); (0xd2130, DJoin); (0xd2150, DJoin); (0xd2174, DJoin); (0xd2194, DJoin); (0xd21b0, DJoin); (0xd21d8, DJoin); (0xd21fc, DJoin); (0xd2218, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_N end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_N, MIc : mem_inv _ mq_N |- _ =>
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 8)) (cN 8) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 8)) (4 * Z.of_nat (length (cN 8))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 8)) (cN 8) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 8)); vm_compute (Z.of_nat (length (cN 8))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd1efc, DJoin); (0xd1f1c, DJoin); (0xd1f3c, DJoin); (0xd1f5c, DJoin); (0xd1f80, DJoin); (0xd1fa0, DJoin); (0xd1fc0, DJoin); (0xd1fe4, DJoin); (0xd2004, DJoin); (0xd2024, DJoin); (0xd2048, DJoin); (0xd2068, DJoin); (0xd2088, DJoin); (0xd20ac, DJoin); (0xd20cc, DJoin); (0xd20ec, DJoin); (0xd2110, DJoin); (0xd2130, DJoin); (0xd2150, DJoin); (0xd2174, DJoin); (0xd2194, DJoin); (0xd21b0, DJoin); (0xd21d8, DJoin); (0xd21fc, DJoin); (0xd2218, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    try match goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp) end.   (* [comment removed for export] *)
    finish; try eassumption; try (clear - SLO; lia).
    unfold gl_sw_cells; cbv zeta; do 8 (split; [assumption|]); assumption.
    all: match goal with |- ?g => idtac "CASE8-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L29902896109.6  L33226651153.3  L33565347303.1  L33720279442.0  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L47868799981.6  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L49858401057.0  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L64024914437.14 L65357366945.0  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05c05f05g05h06406506<06G06J06M06P06b06c07307407707807P07S07T07X07[07\07_07f07g07h07i07j07k07l08<08=08I08J08K08L08M08N08O08R08U08_08`08c08f08i08j08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFS1AS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFS1R2lo3LOS3ALO1HFS1ASS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1AFS1AS2sp2loFFFFFFS1R2lo3LOS3ALO1HFS2sp1A2lo2DSFFSFFFS1AS1AS1R2lo3LOSFS1AS1AS1AFSS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case10 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c2 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+:.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+:.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+:.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=1550.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros HH (HD & HP & HA & HB & HX & HY & HZ & HN & HT) AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 10 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1560, DJoin); (0xd1584, DJoin); (0xd15a4, DJoin); (0xd15c4, DJoin); (0xd15e8, DJoin); (0xd1608, DJoin); (0xd1624, DJoin); (0xd1648, DJoin); (0xd1668, DJoin); (0xd1684, DJoin); (0xd16a8, DJoin); (0xd16c8, DJoin); (0xd16e8, DJoin); (0xd170c, DJoin); (0xd172c, DJoin); (0xd174c, DJoin); (0xd1770, DJoin); (0xd1790, DJoin); (0xd17b0, DJoin); (0xd17d4, DJoin); (0xd17f4, DJoin); (0xd1810, DJoin); (0xd1838, DJoin); (0xd185c, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 10)) (cP 10) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 10)) (4 * Z.of_nat (length (cP 10))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 10)) (cP 10) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 10)); vm_compute (Z.of_nat (length (cP 10))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1560, DJoin); (0xd1584, DJoin); (0xd15a4, DJoin); (0xd15c4, DJoin); (0xd15e8, DJoin); (0xd1608, DJoin); (0xd1624, DJoin); (0xd1648, DJoin); (0xd1668, DJoin); (0xd1684, DJoin); (0xd16a8, DJoin); (0xd16c8, DJoin); (0xd16e8, DJoin); (0xd170c, DJoin); (0xd172c, DJoin); (0xd174c, DJoin); (0xd1770, DJoin); (0xd1790, DJoin); (0xd17b0, DJoin); (0xd17d4, DJoin); (0xd17f4, DJoin); (0xd1810, DJoin); (0xd1838, DJoin); (0xd185c, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_N end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_N, MIc : mem_inv _ mq_N |- _ =>
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 10)) (cN 10) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 10)) (4 * Z.of_nat (length (cN 10))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 10)) (cN 10) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 10)); vm_compute (Z.of_nat (length (cN 10))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd1560, DJoin); (0xd1584, DJoin); (0xd15a4, DJoin); (0xd15c4, DJoin); (0xd15e8, DJoin); (0xd1608, DJoin); (0xd1624, DJoin); (0xd1648, DJoin); (0xd1668, DJoin); (0xd1684, DJoin); (0xd16a8, DJoin); (0xd16c8, DJoin); (0xd16e8, DJoin); (0xd170c, DJoin); (0xd172c, DJoin); (0xd174c, DJoin); (0xd1770, DJoin); (0xd1790, DJoin); (0xd17b0, DJoin); (0xd17d4, DJoin); (0xd17f4, DJoin); (0xd1810, DJoin); (0xd1838, DJoin); (0xd185c, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    try match goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp) end.   (* [comment removed for export] *)
    finish; try eassumption; try (clear - SLO; lia).
    unfold gl_sw_cells; cbv zeta; do 8 (split; [assumption|]); assumption.
    all: match goal with |- ?g => idtac "CASE10-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L2442511693.6   L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L28572447521.0  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L3983061409.0   L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50219795154.0  L50597913045.3  L50959441853.6  L5490983925.14  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05c05f05g05h06406506E06L06W06Z06]06^06a07307407507807P07S07T07X07[07\07]07`07g07h07i07j07k07l07m07n08:08;08<08=08>08N08O08P08Q08T08W08a08b08e08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFS1AS1AFFS2sp1A2lo2DSFS1R2lo3LOS3ALO1HS2sp2loS2sp2lo3SLOS1AS1ASS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1ASFS1AS2sp2loFFFFFFFS2sp1A2lo2DSFFSFS1R2lo3LOS3ALO1HFFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case11 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c2 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+;.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+;.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=2<58.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros HH (HD & HP & HA & HB & HX & HY & HZ & HN & HT) AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 11 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd2c4c, DJoin); (0xd2c68, DJoin); (0xd2c8c, DJoin); (0xd2cac, DJoin); (0xd2ccc, DJoin); (0xd2cf0, DJoin); (0xd2d10, DJoin); (0xd2d2c, DJoin); (0xd2d50, DJoin); (0xd2d70, DJoin); (0xd2d8c, DJoin); (0xd2db0, DJoin); (0xd2dd0, DJoin); (0xd2df0, DJoin); (0xd2e14, DJoin); (0xd2e34, DJoin); (0xd2e54, DJoin); (0xd2e78, DJoin); (0xd2e98, DJoin); (0xd2eb8, DJoin); (0xd2edc, DJoin); (0xd2efc, DJoin); (0xd2f18, DJoin); (0xd2f40, DJoin); (0xd2f64, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 11)) (cP 11) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 11)) (4 * Z.of_nat (length (cP 11))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 11)) (cP 11) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 11)); vm_compute (Z.of_nat (length (cP 11))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd2c4c, DJoin); (0xd2c68, DJoin); (0xd2c8c, DJoin); (0xd2cac, DJoin); (0xd2ccc, DJoin); (0xd2cf0, DJoin); (0xd2d10, DJoin); (0xd2d2c, DJoin); (0xd2d50, DJoin); (0xd2d70, DJoin); (0xd2d8c, DJoin); (0xd2db0, DJoin); (0xd2dd0, DJoin); (0xd2df0, DJoin); (0xd2e14, DJoin); (0xd2e34, DJoin); (0xd2e54, DJoin); (0xd2e78, DJoin); (0xd2e98, DJoin); (0xd2eb8, DJoin); (0xd2edc, DJoin); (0xd2efc, DJoin); (0xd2f18, DJoin); (0xd2f40, DJoin); (0xd2f64, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_N end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_N, MIc : mem_inv _ mq_N |- _ =>
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 11)) (cN 11) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 11)) (4 * Z.of_nat (length (cN 11))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 11)) (cN 11) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 11)); vm_compute (Z.of_nat (length (cN 11))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd2c4c, DJoin); (0xd2c68, DJoin); (0xd2c8c, DJoin); (0xd2cac, DJoin); (0xd2ccc, DJoin); (0xd2cf0, DJoin); (0xd2d10, DJoin); (0xd2d2c, DJoin); (0xd2d50, DJoin); (0xd2d70, DJoin); (0xd2d8c, DJoin); (0xd2db0, DJoin); (0xd2dd0, DJoin); (0xd2df0, DJoin); (0xd2e14, DJoin); (0xd2e34, DJoin); (0xd2e54, DJoin); (0xd2e78, DJoin); (0xd2e98, DJoin); (0xd2eb8, DJoin); (0xd2edc, DJoin); (0xd2efc, DJoin); (0xd2f18, DJoin); (0xd2f40, DJoin); (0xd2f64, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    try match goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp) end.   (* [comment removed for export] *)
    finish; try eassumption; try (clear - SLO; lia).
    unfold gl_sw_cells; cbv zeta; do 8 (split; [assumption|]); assumption.
    all: match goal with |- ?g => idtac "CASE11-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L29200941389.6  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35558650189.6  L35653441506.7  L36216445415.1  L36783814929.3  L38224815777.0  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L44767745618.0  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50037441829.14 L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L62799502113.0  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05c05f05g05h06406506<06G06J06M06]06`07207307407707G07_07b07c07d07h07k07l07o08608708808908:08;08<08=08>08J08K08L08M08N08O08P08S08V08`08a08d08g08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFS1AS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1R2lo3LOS3ALO1HS1AS1R2lo3LOS3ALO3ACPFFS1AS1R2lo3LOS3ALO1HS1R3HIA1h2sp2lo3TOP4HTOPS1AFSS2loS1AFS1AS2sp2loSFFFFFFFS2sp1A2lo2DSFFFFFFS1AS1AS1R2lo3LOSFS1AS1ASS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case12 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c2 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+<.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+<.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+<.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=0=34.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until hpad. intros HH (HD & HP & HA & HB & HX & HY & HZ & HN & HT) AL8 POS FR ST LOS SLO TOP SPA DS MI OA CWA RAE.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    pose proof (munch_refl [(A, A + 192); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (lock MI) as MI00.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (A_curve_statics m 12 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd0d24, DJoin); (0xd0d44, DJoin); (0xd0d68, DJoin); (0xd0d88, DJoin); (0xd0da8, DJoin); (0xd0dcc, DJoin); (0xd0dec, DJoin); (0xd0e08, DJoin); (0xd0e2c, DJoin); (0xd0e4c, DJoin); (0xd0e68, DJoin); (0xd0e8c, DJoin); (0xd0eac, DJoin); (0xd0ecc, DJoin); (0xd0ef0, DJoin); (0xd0f10, DJoin); (0xd0f30, DJoin); (0xd0f54, DJoin); (0xd0f74, DJoin); (0xd0f94, DJoin); (0xd0fb8, DJoin); (0xd0fd8, DJoin); (0xd0ff4, DJoin); (0xd101c, DJoin); (0xd1040, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_P end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_P, MIc : mem_inv _ mq_P |- _ =>
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 12)) (cP 12) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 12)) (4 * Z.of_nat (length (cP 12))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 12)) (cP 12) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 12)); vm_compute (Z.of_nat (length (cP 12))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd0d24, DJoin); (0xd0d44, DJoin); (0xd0d68, DJoin); (0xd0d88, DJoin); (0xd0da8, DJoin); (0xd0dcc, DJoin); (0xd0dec, DJoin); (0xd0e08, DJoin); (0xd0e2c, DJoin); (0xd0e4c, DJoin); (0xd0e68, DJoin); (0xd0e8c, DJoin); (0xd0eac, DJoin); (0xd0ecc, DJoin); (0xd0ef0, DJoin); (0xd0f10, DJoin); (0xd0f30, DJoin); (0xd0f54, DJoin); (0xd0f74, DJoin); (0xd0f94, DJoin); (0xd0fb8, DJoin); (0xd0fd8, DJoin); (0xd0ff4, DJoin); (0xd101c, DJoin); (0xd1040, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq_N end.
    lazymatch goal with HHc : HM _ _ _ h _ _ mq_N, MIc : mem_inv _ mq_N |- _ =>
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 12)) (cN 12) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 12)) (4 * Z.of_nat (length (cN 12))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 12)) (cN 12) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 12)); vm_compute (Z.of_nat (length (cN 12))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd0d24, DJoin); (0xd0d44, DJoin); (0xd0d68, DJoin); (0xd0d88, DJoin); (0xd0da8, DJoin); (0xd0dcc, DJoin); (0xd0dec, DJoin); (0xd0e08, DJoin); (0xd0e2c, DJoin); (0xd0e4c, DJoin); (0xd0e68, DJoin); (0xd0e8c, DJoin); (0xd0eac, DJoin); (0xd0ecc, DJoin); (0xd0ef0, DJoin); (0xd0f10, DJoin); (0xd0f30, DJoin); (0xd0f54, DJoin); (0xd0f74, DJoin); (0xd0f94, DJoin); (0xd0fb8, DJoin); (0xd0fd8, DJoin); (0xd0ff4, DJoin); (0xd101c, DJoin); (0xd1040, DJoin)] 260%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    try match goal with FRx : rw_cells _ _ (bv_unsigned sp + -32) _, STx : stk _ _ lo (bv_unsigned sp + -32) |- _ => release_frame FRx STx (bv_unsigned sp) end.   (* [comment removed for export] *)
    finish; try eassumption; try (clear - SLO; lia).
    unfold gl_sw_cells; cbv zeta; do 8 (split; [assumption|]); assumption.
    all: match goal with |- ?g => idtac "CASE12-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End GLC.
