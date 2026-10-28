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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001178444d7125ac 0 2 0 1 2 1P0041b1f24e353a55 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P0085f75601846fe0 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P00b4f8b981352b30 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P013414eca02d29e5 0 2 0 1 2 1P013761c6893dd17c 0 4 0 1 53 1 58 1 59 1P018f9edbbc1f23f7 0 2 0 1 2 1P01de316cac87d439 0 4 0 1 53 1 58 1 59 1P020de39018d75771 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P02369fe9c58e7dfc 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P023fd5ef8a263099 0 4 0 8 42 8 56 8 57 8P0266f5f47232ab4a 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P02753471e266964c 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P02aa93cdfe70d2ab 0 4 0 8 42 8 56 8 57 8P03027584fa5b95ed 0 2 0 1 2 1P032d5d4198cf1b7c 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P033d523a72195065 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P036db1fa29f45689 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P036df3aee15d8a8a 0 2 0 1 2 1P037df9c5288f9f3f 0 2 0 1 1 1P03ab82b0e02faa2b 2 52 1 1 8 3 2 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 1 1 57 1 60 1 4 0 2 58 2 59 2 61 16P03afe031a74f695b 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P03c699499e3591cd 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P04102c220dec7d97 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P0442a46dad66e149 0 4 0 8 44 8 58 8 59 8P045bf1f4674696cd 0 2 0 1 1 1P051b9c29eb7af2c6 0 2 0 1 2 1P05b40914f3d5e0f8 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P05b6dd1c9c43a28d 0 2 0 1 1 1P061acf3110d83723 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0657f0a9736e71d3 0 4 0 1 49 1 55 1 56 1P065b3dd22f050a8d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P06a4e5a86cb505a3 0 2 0 1 1 1P06c71cfaa70c20f2 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P06d0023487d45dfc 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P06f880a43062d13c 0 2 0 1 2 1P0734adec2c57b984 2 48 1 1 8 3 1 1 55 1 56 1 5 0 1 49 1 54 1 57 1 58 8 1 1 8 3 2 1 54 1 57 1 4 0 2 55 2 56 2 58 16P074795528c4a9124 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0774d1819418d3e9 0 4 0 8 42 8 56 8 57 8P079bc141b769b301 0 2 0 1 2 1P080c3abf244258d2 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P080fcd6ed57df7e9 0 4 0 8 42 8 56 8 57 8P0811ef7653fa64b6 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P0812dc500ccf4fc2 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0878b5aa83e95c06 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P08c1c05a941ad416 0 2 0 1 2 1P08d61bdf5e2f0956 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P08ea6649e456093e 0 4 0 1 50 1 55 1 56 1P08f22af633cf33c6 0 4 0 1 53 1 58 1 59 1P095f1904a4997ad2 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P09651a57867af443 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0967fff29e7914db 0 2 0 1 2 1P09726dd225251d8c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P09b7ed6182a208b0 0 2 0 1 1 1P09c307aede7573f5 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0a0cd412a7ad6214 0 4 0 8 42 8 56 8 57 8P0a109296453a59b2 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0a82ccc530e1fb1a 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P0a84c59ac78b70a4 0 4 0 8 42 8 56 8 57 8P0ad0cfe8f3f098a4 0 2 0 1 1 1P0ad38144b60e371e 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0af50ce2bc9d4d8f 0 4 0 1 50 1 55 1 56 1P0b1044309b98ed6d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0b23e0bbc98df423 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0b3d94fd3a6cfcef 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0bd45bb9f5b9a868 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P0be03183860b93a1 0 4 0 1 50 1 55 1 56 1P0be0f0b6bbb1c668 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0c122962009cab9a 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P0c2dd859d0549dff 0 2 0 1 2 1P0c3dee6192a7b2b2 0 2 0 1 1 1P0c64e059d49aa217 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0cd6f848227ff66d 0 2 0 1 1 1P0d6d336b0b27a482 0 2 0 1 1 1P0d78eba436456826 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0da179b1b33995d5 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0e1895d0b4bafbaa 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0e6059688e845df5 0 2 0 1 2 1P0e7232df9cf8e9c6 0 4 0 8 43 8 55 8 56 8P0e7d6827941b040e 0 2 0 1 1 1P0ea096b3ec1d3bee 0 4 0 8 43 8 55 8 56 8P0ea8a6965c8c0c4e 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P0eb3572acb39d1d9 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0ebd22dc1f326681 0 2 0 1 2 1P0f9ccc71376e56f8 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0fa37f11303025c3 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P0fad4eb7abc64fc0 0 4 0 8 42 8 56 8 57 8P0ff3324611185ae2 0 2 0 1 1 1P1017aee5e9de6b2b 0 4 0 8 40 8 52 8 53 8P106ef45efe30f632 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P10a70f29e395ceff 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P10c57d7f457c5dbb 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P10cb3caf3a417005 0 2 0 1 1 1P10ddda713207d504 0 4 0 8 43 8 55 8 56 8P10eb543817c7c3b0 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P11351bd61a15bc91 0 2 0 1 2 1P115a409ea51b8775 0 2 0 1 2 1P1198afbe34693558 0 2 0 1 2 1P11d2c001f4f5ffa0 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P11ef8bf3e562ebe8 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P12023885d8413efb 0 4 0 8 42 8 56 8 57 8P120c5ad6500ee9b0 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P1223e489848b11e3 0 4 0 8 43 8 55 8 56 8P122bb8d7a6796c80 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P12443db726a2e2e1 0 2 0 1 1 1P1257a5fe15df4ea9 0 4 0 8 43 8 55 8 56 8P125bd36e1355dc2c 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P12df92102d239ccc 2 52 1 1 8 3 2 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 1 1 57 1 60 1 4 0 2 58 2 59 2 61 16P13c90364291824fa 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P141ba639a9222b0f 0 4 0 1 49 1 55 1 56 1P144b190fd23e99a2 0 2 0 1 1 1P14f72b5c7f575a7c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P15204c4982c60efd 0 4 0 8 42 8 56 8 57 8P15661586dcc4c7ad 0 4 0 8 42 8 56 8 57 8P1587759e279ba164 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P15e9c9d156275e37 0 4 0 8 43 8 55 8 56 8P1645b5781eb06f57 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P164b24a71af09f6b 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1682d9655d4cf1b0 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P1729ff5f695aa29f 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P1736b9c202d51b43 0 2 0 1 1 1P17453e60662b2782 0 2 0 1 1 1P1765283a4dd5b1cc 0 2 0 1 2 1P17b5484c850bee57 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P17fd0b08f2a62ead 0 2 0 1 2 1P180d3104ac0e90f1 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P18106f39784f22b5 0 4 0 8 44 8 58 8 59 8P18a2dc7ffc1ad6bc 0 4 0 8 43 8 55 8 56 8P18a6adbb8010c5e1 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P18cace87a0386baa 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P18dd29dc0f1359fb 2 48 1 1 8 3 1 1 55 1 56 1 5 0 1 49 1 54 1 57 1 58 8 1 1 8 3 2 1 54 1 57 1 4 0 2 55 2 56 2 58 16P196d536284a6eb58 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1990bb368a490504 0 4 0 8 42 8 56 8 57 8P19a053475b0ecee3 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P19e860652f8638bc 0 2 0 1 1 1P1a11ab73dcc0c1fd 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1a1e566d16f42fa5 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P1a4e24bee915742e 0 2 0 1 2 1P1a5848d2ce1b5b87 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1aa7d31c8a81668c 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P1af25d6cf3829ac6 0 4 0 8 42 8 56 8 57 8P1b18ae78d0a2a29f 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1b3ee2de453488eb 0 4 0 1 53 1 58 1 59 1P1b46479b409d9f2c 0 2 0 1 1 1P1b4f6a6f30f5a78a 0 4 0 8 42 8 56 8 57 8P1b5b8e9685c9b777 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P1b9236aff068c4b1 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1bca3b6a3fbfcea3 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1be4c6413f0aa74d 0 4 0 8 43 8 55 8 56 8P1c2bb2bc076c2a16 0 2 0 1 1 1P1c62e6feb91c37a3 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1d8720aa5735d480 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1db2a27174f8771e 0 2 0 1 2 1P1df11186d81f159f 0 2 0 1 1 1P1e20743a542de6dc 0 4 0 1 50 1 55 1 56 1P1e39681b73e41735 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1e53f267efd4725d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P1e57ad5dda5421fa 0 4 0 8 43 8 55 8 56 8P1e64a2d9988effdc 0 4 0 8 43 8 55 8 56 8P1ea2550b798211ef 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P1ed78904bd572bf9 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P1edfa4dcbf67d9d0 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P1efb95667b60ce7a 0 4 0 8 42 8 56 8 57 8P1f17a01d2a0578a2 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P1f19659df1103cab 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P20123166c00276de 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P202a074d5a2ad691 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P20a712bc9a49548c 0 2 0 1 2 1P21054d225bd0efde 0 2 0 1 2 1P2156ad31e4a8a4cf 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P215c2bb84e81e04d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P215db95a818ba59e 0 2 0 1 1 1P21aa238b3b3e8ac8 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P21f37f11f47b307e 0 2 0 1 2 1P222112a20e4a6e3a 0 4 0 8 43 8 55 8 56 8P2248f3b62789a6d6 0 4 0 8 44 8 58 8 59 8P22de13c379872f7d 0 4 0 1 50 1 55 1 56 1P22deb23e475a6dea 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P2374f910d3c7a9f8 0 2 0 1 1 1P238fd69f1b5e8f1e 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P23c1cd9997bbfb80 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P23f3cd98c2af400b 0 4 0 8 43 8 55 8 56 8P24738ecd0b2b7335 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P247d54ee1042dc0c 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P248cb08f42ff89d5 0 2 0 1 1 1P24a652bcba7a46aa 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P254b3c10e699b90f 0 4 0 8 43 8 55 8 56 8P254fd5516e780759 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P258057695933c65c 0 4 0 8 44 8 58 8 59 8P258907d056bcad4b 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P25971f3bb59a1f87 0 4 0 8 43 8 55 8 56 8P25d898891f5fbabf 0 2 0 1 2 1P25de86f5ef320f98 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P25df5fe9b293f993 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P2792a30baea96079 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P280237197372902d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P282f79e1f8d31974 0 4 0 8 42 8 56 8 57 8P2872756dcc0aa35d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P289a5a43cb98fc77 0 4 0 8 42 8 56 8 57 8P28c62a9e0317544d 0 5 0 1 50 1 51 1 55 1 56 1P28d35dd0c390221f 1 1 8 2 0 1 58 1 3 2 1 59 1 60 8P291c410659c1f24f 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P2996fbc211de94bb 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P29ad6ee54bf0cd36 1 1 8 2 0 1 52 1 3 2 1 53 1 54 8P29c9454465899dde 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P2a00dbc185444d72 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P2a680426b95b556c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P2a989930b9183167 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P2b3d110940b2f9db 0 5 0 1 50 1 51 1 55 1 56 1P2baf1ba7a022f82b 0 2 0 1 1 1P2bd989872c81fbde 0 2 0 1 1 1P2bfb9c7e6abc08d4 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P2c22ab87def4a4d3 0 2 0 1 2 1P2c22cc01851fde06 0 2 0 1 2 1P2c5b8214e6ddfb9b 0 2 0 1 1 1P2c6e3acb0c8dc518 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P2cc4e5d636cba551 0 4 0 8 42 8 56 8 57 8P2d06baf29d60a871 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P2d2d128add81dd4a 0 2 0 1 2 1P2d63c1afc5e0b49a 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P2de60cbb4ac4f7cd 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2e223c1e0b25e5bf 2 52 1 1 8 3 1 1 60 1 61 1 5 0 1 52 1 59 1 62 1 63 8 1 1 8 3 2 1 59 1 62 1 4 0 2 60 2 61 2 63 16P2ec2cecad54e04d7 0 4 0 8 43 8 55 8 56 8P2ef2709eaebd36e6 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P2f9e55c8fc7f6deb 0 2 0 1 1 1P2fa2c386f78b997c 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P2fb5508a9c7f9cfb 0 4 0 1 53 1 58 1 59 1P2fba9d1dfa815f85 1 1 8 2 0 1 57 1 3 42 1 56 1 58 8P2ff4e676d261d375 0 2 0 1 1 1P2fff4276bfb230e9 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P304ae94dadc43e77 0 2 0 1 2 1P305f91ce1ea2bc06 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P30b200ff006520b6 0 2 0 1 1 1P30e9edd0e98e316e 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P31956961f34a040c 0 4 0 8 43 8 57 8 58 8P31bf86dd25ba8b5d 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P32081da8982e0c7f 0 4 0 1 50 1 55 1 56 1P3237e234a84227a9 0 2 0 1 2 1P324b24aa8d0fcaaf 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P325573ac971800b9 0 4 0 8 42 8 56 8 57 8P32b205f0d5727d40 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P32e60c4ef409def8 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P32f14ad207db209c 0 2 0 1 1 1P332b8e864b36198c 0 2 0 1 2 1P332e96d9295d720d 0 4 0 8 43 8 55 8 56 8P33efa64091bf8b3d 0 2 0 1 1 1P3487341c33e55ff3 0 2 0 1 2 1P34999498ff6e1045 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P350fc69a240a7b46 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P3538e9dcd8efa9a1 0 2 0 1 1 1P3554c8b97ba732a6 0 2 0 1 1 1P3594a39c5cfbadc7 0 4 0 8 43 8 57 8 58 8P35ad1e97f8fdb26b 1 1 8 2 0 1 58 1 3 18 1 59 1 60 8P35f985a71b09d1b7 2 54 1 1 8 3 1 1 61 1 62 1 5 0 1 55 1 60 1 63 1 64 8 1 1 8 3 2 1 60 1 63 1 4 0 2 61 2 62 2 64 16P360409f158a9f0ca 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P361eaff91c6c69ce 0 2 0 1 2 1P366e3bccc7f0f8f0 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P36a65265d7c6956d 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P36fbcd3553d6046c 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P375bc7744f7c6c83 0 2 0 1 2 1P37ceb342207a1919 0 4 0 8 43 8 57 8 58 8P38bd3d4cac8a7869 0 2 0 1 2 1P38d7cc60b96711f4 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P38e7fba05cfdaf82 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P38f94595431055c6 0 2 0 1 1 1P390e6740951161a1 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P390f1e9ad6607dd0 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P394e6a416b705b08 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P39a16561eb9fa82a 0 4 0 8 40 8 52 8 53 8P3a1821678834e58d 0 4 0 8 42 8 56 8 57 8P3a5a1ded14d14584 0 4 0 8 44 8 58 8 59 8P3a5dfead04d2f504 0 4 0 8 42 8 56 8 57 8P3a94aded77606a48 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3ab7cb3ef6b842c2 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3abb176c9cbfc1ec 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3b0e7d1a72d99413 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P3b229df87eee6f81 1 1 8 2 0 1 57 1 3 5 1 58 1 59 8P3b2a4a6d8c53e3d9 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P3b6c723114f88393 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P3b76904d7d1e2f37 0 4 0 8 43 8 55 8 56 8P3ba870a9b9465560 0 2 0 1 2 1P3c00802c6f0d1951 0 2 0 1 2 1P3c35ca8506a5a606 0 2 0 1 1 1P3c4b5181ee20499c 0 4 0 8 43 8 55 8 56 8P3c927fd92996b8b0 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3cc306dab2b0d693 0 2 0 1 1 1P3dad385b7f531e3e 1 1 8 2 0 1 53 1 3 40 1 52 1 54 8P3dc50902bae49d06 2 52 1 1 8 3 1 1 58 1 59 1 5 0 1 52 1 57 1 60 1 61 8 1 1 8 3 2 1 57 1 60 1 4 0 2 58 2 59 2 61 16P3dd61b163465fac7 2 51 1 1 8 3 1 1 59 1 60 1 5 0 1 51 1 58 1 61 1 62 8 1 1 8 3 2 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3df149daed9b1367 0 4 0 8 42 8 56 8 57 8P3e0d3b6a2b22c660 0 4 0 8 42 8 56 8 57 8P3e5afeca2543a072 0 4 0 8 43 8 55 8 56 8P3ea64f357ee3c348 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8P3efa6a5607a3f013 0 4 0 8 42 8 56 8 57 8P3f02389b4c93d16d 0 4 0 8 43 8 57 8 58 8P3f786ee70a093982 1 1 8 2 0 1 56 1 3 4 1 57 1 58 8P3f8c978a4e4cc1a6 1 1 8 2 0 1 55 1 3 5 1 56 1 57 8N0099dc23b0bad0c0N00dfd9de6405ff97N012fe4beb848b35eN01483f81191c1552N01860d788a3f9fb5N02b57d6e77ee8c39N030b3e501bdbb1bdN03ca87b0227e1efcN0490ddcdbc03edf7N0493ac0fae77cdf5N091f5813c56922c0N0a3b35a876fd7143N0a6e5a6c28c9a50bN0a734ec20310b6f3N0b32951e2089f450N0c75efd971cdff68N0c87aee437d20f54N0d71aa72bf28c89bN0f218863c36bd8cfN0fd0e1e6a8170871N1027512673cfe26dN11f1e452a9165420N11fa68fb9dd695a8N1231c8d4851fd785N12512db52564f391N12aa6fed5aa79389N12df446d8b7988d6N135e843f4003e86aN1361d50aeaf52dcfN1414469ac6f8dac5N148f30e44ad5be5fN1496a0918a84c478N14a13d2c53b5b272N151e597a0760349cN15a95e21c749c261N16721c9122365018N187e1a25bae253d3N193ef663d9044e98N1b52c9e0de92d9a2N1b79b14125eb759eN1be20fbd5d8b6851N1c088ca82ccb89caN1c3eeae10fe343deN1c96d5be87df830bN1d541f5e6f9bd671N1db92681907a55f1N1df6947b9e006762N1f657362fac487b2N1fe74cf3ef244bfeN2086d97590c9ed59N20b1763768143f9dN213c790a531930c5N214d63cf2cb01984N2186cc487b6177efN21a72d2470d0fe72N21a7a2ae475f97ecN23713b0ffc927987N25312d37595f0b3eN253b082ac206cbefN26073d7aee038b8fN26218c7cbf3f9751N2829992bb35837a5N286e723c650f7866N28791dcc0c692e4dN2b2e4fefd3a44c7eN2b8580a85bdc1046N2bb94c279b4da11aN2c2cdce4892c55f6N2c4d7d2f7a1e1804N2e27b82e5792ffa5N2e63a0cbaa901f02N2eecaa769a6ed037N2f8a73f359ffd732N2fbda01adeae262fN301dc0828a050aebN304ac5fcbb6b997bN30a517378bc08b8aN30ce3d4cb174f4ceN319de3f3d80498d7N31b09a65058d58bbN31cfbc07b987f91fN322872d6dfd9ca7cN32fa708771dedd75N330c370a39091f49N33710681561154d3N34393f1d07a4d801N34ae9cca6c567486N352c28f466ca269fN35356afc54851456N35aebe9136e1dcbeN35ca9e1833637696N36898aa8bee242baN370c9b2e726b1275N37315b6e954e1a87N37375e88d579a2c6N378d582dc68be725N388a688e88bde2b2N3ab43d39a5813bf0N3bb7b19db8fad1a6N3c35061f4a2b8a5aN3c372dfc8d465750N3c38c6388970b13aN3d6209da3950b2e5N3da5373c508a5182N3db62636b1cb0073N3e22efecb61647f5N3e3b79e6cda54c5fN3e80633d53e88f61N3f3bdb883745382d"%lxh.
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
Ltac2 gd_tbl_A_ecp_group_load_c1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_init_cells"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load.gl_sw_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section GLC.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Notation gl_sw_post := (gl_sw_post R HIA).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L13839416533.14 L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L30029615597.6  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40280805793.0  L40340425745.3  L42036188562.0  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46883672865.0  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    L9674490349.6   N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05Y05`05a05d05g05h05i06506606=06H06K06N06Q06c06d07407507807P07S07T07X07[07\07]07^07a07h07i07j07k07l07m07n07o08008<08=08>08?08@08A08D08G08Q08R08U08X08[09;09>09?09R09U09V09Y09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFFS1A3POSFS1AS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFS1R2lo3LOS3ALO1HFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1ASFSS1AS2sp2loFFFFFFSFS2sp1A2lo2DSFFFFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS1R2lo3LOS3ALO1HS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case1 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+1.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+1.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+1.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=0:14.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 1 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd0a24, DJoin); (0xd0a48, DJoin); (0xd0a68, DJoin); (0xd0a88, DJoin); (0xd0aac, DJoin); (0xd0acc, DJoin); (0xd0aec, DJoin); (0xd0b10, DJoin); (0xd0b30, DJoin); (0xd0b50, DJoin); (0xd0b74, DJoin); (0xd0b94, DJoin); (0xd0bb4, DJoin); (0xd0bd8, DJoin); (0xd0bf8, DJoin); (0xd0c18, DJoin); (0xd0c3c, DJoin); (0xd0c5c, DJoin); (0xd0c78, DJoin); (0xd0ca0, DJoin); (0xd0cc4, DJoin); (0xd0ce0, DJoin); (0xd0d00, DJoin); (0xd0d24, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 1)) (cP 1) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 1)) (4 * Z.of_nat (length (cP 1))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 1)) (cP 1) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 1)); vm_compute (Z.of_nat (length (cP 1))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd0a24, DJoin); (0xd0a48, DJoin); (0xd0a68, DJoin); (0xd0a88, DJoin); (0xd0aac, DJoin); (0xd0acc, DJoin); (0xd0aec, DJoin); (0xd0b10, DJoin); (0xd0b30, DJoin); (0xd0b50, DJoin); (0xd0b74, DJoin); (0xd0b94, DJoin); (0xd0bb4, DJoin); (0xd0bd8, DJoin); (0xd0bf8, DJoin); (0xd0c18, DJoin); (0xd0c3c, DJoin); (0xd0c5c, DJoin); (0xd0c78, DJoin); (0xd0ca0, DJoin); (0xd0cc4, DJoin); (0xd0ce0, DJoin); (0xd0d00, DJoin); (0xd0d24, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 1)) (cN 1) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 1)) (4 * Z.of_nat (length (cN 1))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 1)) (cN 1) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 1)); vm_compute (Z.of_nat (length (cN 1))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd0a24, DJoin); (0xd0a48, DJoin); (0xd0a68, DJoin); (0xd0a88, DJoin); (0xd0aac, DJoin); (0xd0acc, DJoin); (0xd0aec, DJoin); (0xd0b10, DJoin); (0xd0b30, DJoin); (0xd0b50, DJoin); (0xd0b74, DJoin); (0xd0b94, DJoin); (0xd0bb4, DJoin); (0xd0bd8, DJoin); (0xd0bf8, DJoin); (0xd0c18, DJoin); (0xd0c3c, DJoin); (0xd0c5c, DJoin); (0xd0c78, DJoin); (0xd0ca0, DJoin); (0xd0cc4, DJoin); (0xd0ce0, DJoin); (0xd0d00, DJoin); (0xd0d24, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE1-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L22441126887.1  L22724575928.1  L23201827973.14 L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35357999949.6  L35653441506.7  L36216445415.1  L36783814929.3  L37973898685.6  L38235734261.1  L39576650800.1  L40011557266.0  L40340425745.3  L40870879649.0  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    L9798245153.0   N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05c05f05g05h05i06506606=06H06K06N06Q06c06d06e06h07807P07S07T07d07h07k07l07m07n08108808908:08;08<08=08>08?08K08L08M08N08O08P08S08V08`08a08d08g08j09J09M09N09a09d09e09h09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFS1AS1AFFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R2lo3LOS3ALO1HS1R3HIA1h2sp2lo3TOP4HTOPS1AFS1R2lo3LOS3ALO1HS2loS1ASFSS1AS2sp2loFFFFFFFS2sp1A2lo2DSFFFFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1ASS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case2 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+2.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+2.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+2.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=2268.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 2 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd225c, DJoin); (0xd2278, DJoin); (0xd229c, DJoin); (0xd22bc, DJoin); (0xd22dc, DJoin); (0xd2300, DJoin); (0xd2320, DJoin); (0xd2340, DJoin); (0xd2364, DJoin); (0xd2384, DJoin); (0xd23a4, DJoin); (0xd23c8, DJoin); (0xd23e8, DJoin); (0xd2408, DJoin); (0xd242c, DJoin); (0xd244c, DJoin); (0xd246c, DJoin); (0xd2490, DJoin); (0xd24b0, DJoin); (0xd24cc, DJoin); (0xd24f4, DJoin); (0xd2518, DJoin); (0xd2534, DJoin); (0xd2554, DJoin); (0xd2578, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 2)) (cP 2) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 2)) (4 * Z.of_nat (length (cP 2))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 2)) (cP 2) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 2)); vm_compute (Z.of_nat (length (cP 2))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd225c, DJoin); (0xd2278, DJoin); (0xd229c, DJoin); (0xd22bc, DJoin); (0xd22dc, DJoin); (0xd2300, DJoin); (0xd2320, DJoin); (0xd2340, DJoin); (0xd2364, DJoin); (0xd2384, DJoin); (0xd23a4, DJoin); (0xd23c8, DJoin); (0xd23e8, DJoin); (0xd2408, DJoin); (0xd242c, DJoin); (0xd244c, DJoin); (0xd246c, DJoin); (0xd2490, DJoin); (0xd24b0, DJoin); (0xd24cc, DJoin); (0xd24f4, DJoin); (0xd2518, DJoin); (0xd2534, DJoin); (0xd2554, DJoin); (0xd2578, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 2)) (cN 2) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 2)) (4 * Z.of_nat (length (cN 2))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 2)) (cN 2) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 2)); vm_compute (Z.of_nat (length (cN 2))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd225c, DJoin); (0xd2278, DJoin); (0xd229c, DJoin); (0xd22bc, DJoin); (0xd22dc, DJoin); (0xd2300, DJoin); (0xd2320, DJoin); (0xd2340, DJoin); (0xd2364, DJoin); (0xd2384, DJoin); (0xd23a4, DJoin); (0xd23c8, DJoin); (0xd23e8, DJoin); (0xd2408, DJoin); (0xd242c, DJoin); (0xd244c, DJoin); (0xd246c, DJoin); (0xd2490, DJoin); (0xd24b0, DJoin); (0xd24cc, DJoin); (0xd24f4, DJoin); (0xd2518, DJoin); (0xd2534, DJoin); (0xd2554, DJoin); (0xd2578, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE2-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L17071587445.14 L22441126887.1  L22724575928.1  L22734331725.6  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L26661471905.0  L27014673383.1  L27677179367.1  L28572447521.0  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L46262226765.6  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L54937175313.3  L56511072978.0  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05a05d05g06706806906E06F06M06X06Y06\06_06`06c07507607707:07R07U07V07Z07]07^07a07h07i07j07k07l07m07n08>08?08K08L08M08N08O08P08Q08T08W08a08b08e08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFFS1AS1AS1R2lo3LOS3ALO1HFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOSS1AS1ASS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1AFS1AS2sp2loFFFFFFS1R2lo3LOS3ALO1HFS2sp1A2lo2DSFFFFSFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case3 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+3.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+3.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+3.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=18<<.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 3 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd18bc, DJoin); (0xd18dc, DJoin); (0xd1900, DJoin); (0xd1920, DJoin); (0xd1940, DJoin); (0xd1964, DJoin); (0xd1984, DJoin); (0xd19a4, DJoin); (0xd19c8, DJoin); (0xd19e8, DJoin); (0xd1a08, DJoin); (0xd1a2c, DJoin); (0xd1a4c, DJoin); (0xd1a6c, DJoin); (0xd1a90, DJoin); (0xd1ab0, DJoin); (0xd1ad0, DJoin); (0xd1af4, DJoin); (0xd1b14, DJoin); (0xd1b30, DJoin); (0xd1b58, DJoin); (0xd1b7c, DJoin); (0xd1b98, DJoin); (0xd1bb8, DJoin); (0xd1bdc, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 3)) (cP 3) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 3)) (4 * Z.of_nat (length (cP 3))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 3)) (cP 3) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 3)); vm_compute (Z.of_nat (length (cP 3))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd18bc, DJoin); (0xd18dc, DJoin); (0xd1900, DJoin); (0xd1920, DJoin); (0xd1940, DJoin); (0xd1964, DJoin); (0xd1984, DJoin); (0xd19a4, DJoin); (0xd19c8, DJoin); (0xd19e8, DJoin); (0xd1a08, DJoin); (0xd1a2c, DJoin); (0xd1a4c, DJoin); (0xd1a6c, DJoin); (0xd1a90, DJoin); (0xd1ab0, DJoin); (0xd1ad0, DJoin); (0xd1af4, DJoin); (0xd1b14, DJoin); (0xd1b30, DJoin); (0xd1b58, DJoin); (0xd1b7c, DJoin); (0xd1b98, DJoin); (0xd1bb8, DJoin); (0xd1bdc, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 3)) (cN 3) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 3)) (4 * Z.of_nat (length (cN 3))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 3)) (cN 3) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 3)); vm_compute (Z.of_nat (length (cN 3))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd18bc, DJoin); (0xd18dc, DJoin); (0xd1900, DJoin); (0xd1920, DJoin); (0xd1940, DJoin); (0xd1964, DJoin); (0xd1984, DJoin); (0xd19a4, DJoin); (0xd19c8, DJoin); (0xd19e8, DJoin); (0xd1a08, DJoin); (0xd1a2c, DJoin); (0xd1a4c, DJoin); (0xd1a6c, DJoin); (0xd1a90, DJoin); (0xd1ab0, DJoin); (0xd1ad0, DJoin); (0xd1af4, DJoin); (0xd1b14, DJoin); (0xd1b30, DJoin); (0xd1b58, DJoin); (0xd1b7c, DJoin); (0xd1b98, DJoin); (0xd1bb8, DJoin); (0xd1bdc, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE3-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L14601520535.2  L15051368977.3  L20343950113.0  L21916970893.6  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L24915495845.14 L25964569660.3  L26466616993.0  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39020528466.0  L39576650800.1  L40340425745.3  L42560833421.6  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05_05`05a06106406706806906E06F06M06N06Y06Z06]06`06c07507607707:07R07U07V07Z07[07^07_07o08208908:08;08<08=08>08?08@08L08M08N08O08P08Q08T08W08a08b08e08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFS1A3POSFSS1R2lo3LOS3ALO1HS1AS1AFFS2sp1A2lo2DSFS2sp2loFS2sp2lo3SLOSS1AS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loSS1AFS1R2lo3LOS3ALO1HS1AS2sp2loFFFFFFFS2sp1A2lo2DSFFFFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case4 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+4.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+4.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+4.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=1;><.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 4 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1bdc, DJoin); (0xd1bfc, DJoin); (0xd1c20, DJoin); (0xd1c40, DJoin); (0xd1c60, DJoin); (0xd1c84, DJoin); (0xd1ca4, DJoin); (0xd1cc4, DJoin); (0xd1ce8, DJoin); (0xd1d08, DJoin); (0xd1d28, DJoin); (0xd1d4c, DJoin); (0xd1d6c, DJoin); (0xd1d8c, DJoin); (0xd1db0, DJoin); (0xd1dd0, DJoin); (0xd1df0, DJoin); (0xd1e14, DJoin); (0xd1e34, DJoin); (0xd1e50, DJoin); (0xd1e78, DJoin); (0xd1e9c, DJoin); (0xd1eb8, DJoin); (0xd1ed8, DJoin); (0xd1efc, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 4)) (cP 4) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 4)) (4 * Z.of_nat (length (cP 4))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 4)) (cP 4) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 4)); vm_compute (Z.of_nat (length (cP 4))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd1bdc, DJoin); (0xd1bfc, DJoin); (0xd1c20, DJoin); (0xd1c40, DJoin); (0xd1c60, DJoin); (0xd1c84, DJoin); (0xd1ca4, DJoin); (0xd1cc4, DJoin); (0xd1ce8, DJoin); (0xd1d08, DJoin); (0xd1d28, DJoin); (0xd1d4c, DJoin); (0xd1d6c, DJoin); (0xd1d8c, DJoin); (0xd1db0, DJoin); (0xd1dd0, DJoin); (0xd1df0, DJoin); (0xd1e14, DJoin); (0xd1e34, DJoin); (0xd1e50, DJoin); (0xd1e78, DJoin); (0xd1e9c, DJoin); (0xd1eb8, DJoin); (0xd1ed8, DJoin); (0xd1efc, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 4)) (cN 4) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 4)) (4 * Z.of_nat (length (cN 4))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 4)) (cN 4) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 4)); vm_compute (Z.of_nat (length (cN 4))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd1bdc, DJoin); (0xd1bfc, DJoin); (0xd1c20, DJoin); (0xd1c40, DJoin); (0xd1c60, DJoin); (0xd1c84, DJoin); (0xd1ca4, DJoin); (0xd1cc4, DJoin); (0xd1ce8, DJoin); (0xd1d08, DJoin); (0xd1d28, DJoin); (0xd1d4c, DJoin); (0xd1d6c, DJoin); (0xd1d8c, DJoin); (0xd1db0, DJoin); (0xd1dd0, DJoin); (0xd1df0, DJoin); (0xd1e14, DJoin); (0xd1e34, DJoin); (0xd1e50, DJoin); (0xd1e78, DJoin); (0xd1e9c, DJoin); (0xd1eb8, DJoin); (0xd1ed8, DJoin); (0xd1efc, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE4-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L13917980321.0  L14052942365.6  L14601520535.2  L15051368977.3  L21181284893.6  L22441126887.1  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43417168277.14 L43884818473.2  L45194705697.0  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50597913045.3  L52037157650.0  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L60098763854.3  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05Y05i06006106A06D06G06H06I06U06V06]06h06k06n07107C07D07E07H07`07c07d07h07k07l07o08008708808908:08;08<08=08>08?08K08L08M08N08O08P08Q08T08W08a08b08e08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFSS1R2lo3LOS3ALO1HS1A3POSFS1R2lo3LOS3ALO1HS1AS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1AFS1AFS2sp2loSFFFFFFFS2sp1A2lo2DSFFFSFFS1AS1AS1R2lo3LOSFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case5 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+5.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+5.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+5.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=10;0.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 5 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd10a0, DJoin); (0xd10c0, DJoin); (0xd10e4, DJoin); (0xd1104, DJoin); (0xd1124, DJoin); (0xd1148, DJoin); (0xd1168, DJoin); (0xd1188, DJoin); (0xd11ac, DJoin); (0xd11cc, DJoin); (0xd11ec, DJoin); (0xd1210, DJoin); (0xd1230, DJoin); (0xd1250, DJoin); (0xd1274, DJoin); (0xd1294, DJoin); (0xd12b4, DJoin); (0xd12d8, DJoin); (0xd12f8, DJoin); (0xd1314, DJoin); (0xd133c, DJoin); (0xd1360, DJoin); (0xd137c, DJoin); (0xd139c, DJoin); (0xd13c0, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 5)) (cP 5) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 5)) (4 * Z.of_nat (length (cP 5))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 5)) (cP 5) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 5)); vm_compute (Z.of_nat (length (cP 5))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd10a0, DJoin); (0xd10c0, DJoin); (0xd10e4, DJoin); (0xd1104, DJoin); (0xd1124, DJoin); (0xd1148, DJoin); (0xd1168, DJoin); (0xd1188, DJoin); (0xd11ac, DJoin); (0xd11cc, DJoin); (0xd11ec, DJoin); (0xd1210, DJoin); (0xd1230, DJoin); (0xd1250, DJoin); (0xd1274, DJoin); (0xd1294, DJoin); (0xd12b4, DJoin); (0xd12d8, DJoin); (0xd12f8, DJoin); (0xd1314, DJoin); (0xd133c, DJoin); (0xd1360, DJoin); (0xd137c, DJoin); (0xd139c, DJoin); (0xd13c0, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 5)) (cN 5) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 5)) (4 * Z.of_nat (length (cN 5))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 5)) (cN 5) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 5)); vm_compute (Z.of_nat (length (cN 5))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd10a0, DJoin); (0xd10c0, DJoin); (0xd10e4, DJoin); (0xd1104, DJoin); (0xd1124, DJoin); (0xd1148, DJoin); (0xd1168, DJoin); (0xd1188, DJoin); (0xd11ac, DJoin); (0xd11cc, DJoin); (0xd11ec, DJoin); (0xd1210, DJoin); (0xd1230, DJoin); (0xd1250, DJoin); (0xd1274, DJoin); (0xd1294, DJoin); (0xd12b4, DJoin); (0xd12d8, DJoin); (0xd12f8, DJoin); (0xd1314, DJoin); (0xd133c, DJoin); (0xd1360, DJoin); (0xd137c, DJoin); (0xd139c, DJoin); (0xd13c0, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE5-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0200@C17025492443.130C17025492443.147D37708108083.97 D4412853009.97  D563007111.98   D60109446735.130D60109446735.147D62022258533.98 D64311484648.130D64311484648.147K11493750132.130K11493750132.147K15064807540.130K15064807540.147K33231037556.130K33231037556.147K36787415924.130K36787415924.147K40344297076.130K40344297076.147K50584482736.130K50584482736.147K54933706612.130K54933706612.147K58490083956.130K58490083956.147K62048029044.130K62048029044.147L11014368388.13 L11016396417.6  L11016802336.6  L11084276631.2  L11506788113.3  L12696972339.2  L13705671073.0  L14601520535.2  L15051368977.3  L22441126887.1  L22658091809.0  L22724575928.1  L23983263738.4  L23983309147.4  L23985229279.4  L23985307135.11 L24617487510.2  L25964569660.3  L27014673383.1  L27677179367.1  L2920766268.1   L29428324939.5  L29790966853.2  L33226651153.3  L33565347303.1  L35323480397.6  L35653441506.7  L36216445415.1  L36783814929.3  L38235734261.1  L39576650800.1  L40340425745.3  L43227412528.1  L43884818473.2  L45290832372.3  L45290917717.3  L45328191184.4  L45328269040.10 L45329973844.3  L45330418933.3  L49270838271.11 L49270907871.4  L49272827739.4  L49272873466.4  L50012526354.0  L50597913045.3  L54937175313.3  L58494339089.3  L59094008880.1  L59242620976.1  L59292919877.14 L60098763854.3  L61158657357.6  L62052031249.3  L62132976688.1  L62255369191.1  L63372510183.1  L66151427842.16 L67360804024.1  L67405403709.2  L7193111478.5   L8428417511.1   L8956124477.2   L914432316.1    N21806751459.131N37104593031.131N45607708002.148N6394274292.148 O17025492443.130O17025492443.147O21061669077.130O21061669077.147O21610544085.130O21610544085.147O26328763605.130O26328763605.147O28312938197.130O28312938197.147O30724803029.130O30724803029.147O31711449813.130O31711449813.147O34798215125.130O34798215125.147O37051008023.130O37051008023.147O40145708501.130O40145708501.147O4492316913.147 O48978854641.147P67400615000.147P8944127832.147 Q38248387216.130Q38248387216.147Q39935065476.130Q39935065476.147Q43879899724.130Q43879899724.147Q7192832789.110 Q7192832789.127 00000100200;00D00U00g01901D01\02402@02L02X02d03003<03H03T03`03l04804D04P04\04h05405@05L05M05N05O05V05W05X05Y05`05a05d05e05h05i05j06606706>06I06L06O06R06d06e06f06i07907Q07T07U07Y07\07]07`07g07h07i07j07k07l07m07n08:08;08<08=08>08?08@08C08F08G08Q08a08b08e08h08k09K09N09O09b09e09f09i0:60:C0:P0:]0:h0;30;40;50;60;70;80;90;:0;;0;<0;=0;>0;?0;@0;A0;B0;C0;D0;E0;F0;G0;Z0;m0<10<50<@0<K0<R0<Y0=40=OFFS2ra2sp1AS2ra2sp1AS1R3HIA1h2ra2sp1AS1R2ra2sp1A2lo3LOSS1R2ra2sp1A2lo3LOSS1R2ra2sp1AS1R3HIA1h2ra2sp1A2lo3TOPS1R3HIA1h2ra2sp1A2lo3TOPS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSS2sp1A2lo2DSFFFS1A3POSFFSS1A3POSFS1ASS1AFFS2sp1A2lo2DSFS2sp2loS2sp2lo3SLOS1AS1AS1AS1R2lo3LOS3ALO3ACPFFS1AS1R2lo3LOS3ALO1HS1R3HIA1h2sp2lo3TOP4HTOPS1AFS2loS1AFS1AS2sp2loFFFFFFFS2sp1A2lo2DSFFSFFFS1AS1AFS1R2lo3LOSS1R2lo3LOS3ALO1HFS1AS1AS1AS1A2r03AL81q1r1H2H02q02H42sp3SPAS1AFS2sp2lo3SLO3SPR3LO0S1AFS1AS2sp2lo3x151CS2sp2lo3x151CS2sp2lo3x301CS2sp2lo3x301CS2sp2lo3SLOS2sp2lo3SLOFFFFFFFFFFFFFFFFFFFFS1R2sp2lo3LOS3ALO1HS1R2sp2lo3LOS3ALO1HS2loS2loS2sp2lo3SLOS2sp2lo3SLOS2sp2loS2sp2loS1R2sp2lo3LOS3SLO3ALO3SPR1HS1R2sp2lo3LOS3SLO3ALO3SPR1H". (* [comment removed for export] *)
  Lemma case6 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_group_load_c1 ()) "Ph,(0.$1.VR,VHIA,)PLB,(2.$3.)PLF,(2.$3.)Pra,(4.&40.)Psp,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pxa0,(4.&40.)Pxa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pxra,(4.&40.)PF,(5.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(6.(4.&8.))PA,$7.Plo,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)P,(8.$1.VR,VHIA,R31.R30.R2?.R<.)P,(9.R=.R<.+6.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(:.$7.(;.R=.+8.)=)P,(<.=R>.)P,(=.$1.R10.(>.(?.&40.R31.)-20.)(10.$11.(12.R21.)(10.$11.(12.R2:.)(10.$11.(12.R2;.)(10.$11.(12.R32.)(13.$11.))))))P,(14.$1.R11.R?.(>.(?.&40.R32.)-20.))P,(15.(16.VR,)R10.)P,(15.R11.(17.(17.(?.&40.R34.)+20.)+40.))P,(15.(?.&40.R35.)(18.$1.VR,VHIA,R39.))P,(:.$7.(;.(?.&40.R36.)+10.)=)P,(19.(15.(>.R15.+<0.)R14.)(15.(?.&40.R37.)R15.))P,(1:.$1.R17.)P,(1;.$1.(1<.VR,)(1=.$1.VR,VHIA,R3=.)R18.R17.+<0.)P,(1>.(1?.VR,)(20.$3.R3=.(21.R3<.))(16.VR,)(18.$1.VR,VHIA,R3>.)R18.+<0.)P,(:.$7.(;.(?.&40.R3<.)+2.)=)(22.$1.(1<.VR,)(1=.$1.VR,VHIA,R40.)(23.VR,VHIA,R40.R3?.R3>.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1=.R1<.R1:.+6.R18.R17.R16.R15.R14.R13.R12.R11.R10.R19.R1;.)(24.(25.R1>.(26.&40.(>.(?.&40.R3<.)-20.))R3;.R3:.R39.R38.R37.(26.&40.R1:.)(26.&40.+6.)R34.R33.R32.R31.R30.R2?.R2>.R2=.(26.&40.(27.(1<.VR,)))R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1=.(26.&40.+=2584.)R1<.(28.(4.&40.))R1;.(29.$1.)))")
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
    pose proof (A_curve_statics m 6 MI ltac:(clear; lia)) as CS. pose proof CS as (STP & _ & _ & STN & _).
    unfold mpi_cells in HP, HA, HB, HX, HY, HZ, HN.
    pose (lxi := lxA_img (arl_AL R) IMG).
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd2578, DJoin); (0xd2594, DJoin); (0xd25b4, DJoin); (0xd25d4, DJoin); (0xd25f8, DJoin); (0xd2618, DJoin); (0xd2638, DJoin); (0xd265c, DJoin); (0xd267c, DJoin); (0xd269c, DJoin); (0xd26c0, DJoin); (0xd26e0, DJoin); (0xd2700, DJoin); (0xd2724, DJoin); (0xd2744, DJoin); (0xd2764, DJoin); (0xd2788, DJoin); (0xd27a8, DJoin); (0xd27c8, DJoin); (0xd27ec, DJoin); (0xd280c, DJoin); (0xd2828, DJoin); (0xd2850, DJoin); (0xd2874, DJoin); (0xd2890, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_P LB (smpd (A + 8) (ca_P (A_CA 6)) (cP 6) pP))
        by (eapply smpd_mpd_at; [exact HP| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_P HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_P (ca_P (A_CA 6)) (4 * Z.of_nat (length (cP 6))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 8) (ca_P (A_CA 6)) (cP 6) pP) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_P (A_CA 6)); vm_compute (Z.of_nat (length (cP 6))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9c8a8] [(0xd2578, DJoin); (0xd2594, DJoin); (0xd25b4, DJoin); (0xd25d4, DJoin); (0xd25f8, DJoin); (0xd2618, DJoin); (0xd2638, DJoin); (0xd265c, DJoin); (0xd267c, DJoin); (0xd269c, DJoin); (0xd26c0, DJoin); (0xd26e0, DJoin); (0xd2700, DJoin); (0xd2724, DJoin); (0xd2744, DJoin); (0xd2764, DJoin); (0xd2788, DJoin); (0xd27a8, DJoin); (0xd27c8, DJoin); (0xd27ec, DJoin); (0xd280c, DJoin); (0xd2828, DJoin); (0xd2850, DJoin); (0xd2874, DJoin); (0xd2890, DJoin)] 260%N). lx_tree.
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
      assert (MPq : mpd_at asegs mq_N LB (smpd (A + 104) (ca_N (A_CA 6)) (cN 6) pN))
        by (eapply smpd_mpd_at; [exact HN| clear - AL8; Z.div_mod_to_equations; lia| clear - POS; lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| exact MIc]]);
      pose proof (hm_abase asegs R HIA h _ _ mq_N HHc) as ABq;
      assert (OLq : aobj asegs AL (hcs asegs R HIA h) mq_N (ca_N (A_CA 6)) (4 * Z.of_nat (length (cN 6))))
        by (eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHc| vm_compute; reflexivity])
    end.
    pose proof (A_mpi_bitlen_spec AL IMG) as SPQ. unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q in SPQ.
    callxA_sp (bv_unsigned sp + -32)
      (eapply SPQ with (CS := hcs asegs R HIA h) (LB := LB) (dX := smpd (A + 104) (ca_N (A_CA 6)) (cN 6) pN) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear - SPR LO0 SLO; lia); cbn [md_addr md_own md_n md_p smpd];
       first [ exact MPq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (intros C; discriminate C)
             | (intros _; exact OLq)
             | (match goal with OAc : aobj _ _ _ _ A 192 |- _ => eapply aobj_sub; [exact OAc| clear; lia| clear; lia] end)
             | (clear - SLO; lia) | (clear - LO0; lia)
             | (clear - SPA; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear; lia])
             | (clear - DS; lia)
             | (intros _; left; vm_compute (ca_N (A_CA 6)); vm_compute (Z.of_nat (length (cN 6))); clear - ALO LOS ACP; pose proof (alloc_ceiling_lo (L := arl_L R)); lia)
             | match goal with |- ?g => idtac "BITLEN-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-BITLEN-SIDE:" g end.
    clear MPq ABq OLq.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [(0xd2578, DJoin); (0xd2594, DJoin); (0xd25b4, DJoin); (0xd25d4, DJoin); (0xd25f8, DJoin); (0xd2618, DJoin); (0xd2638, DJoin); (0xd265c, DJoin); (0xd267c, DJoin); (0xd269c, DJoin); (0xd26c0, DJoin); (0xd26e0, DJoin); (0xd2700, DJoin); (0xd2724, DJoin); (0xd2744, DJoin); (0xd2764, DJoin); (0xd2788, DJoin); (0xd27a8, DJoin); (0xd27c8, DJoin); (0xd27ec, DJoin); (0xd280c, DJoin); (0xd2828, DJoin); (0xd2850, DJoin); (0xd2874, DJoin); (0xd2890, DJoin)] 260%N). lx_tree.
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
    all: match goal with |- ?g => idtac "CASE6-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End GLC.
