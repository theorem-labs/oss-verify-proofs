(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_copy P_mpi_shrink.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_copy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
(* [comment removed for export] *)
#[local] Ltac lx_wdecl_note ::= idtac.
(* [comment removed for export] *)
#[local] Ltac lxr_pose ::= lazymatch goal with |- evtA _ _ _ _ _ => lxr_abs_lists; try lxr_pose_HM; try lxr_pose_presW; try lxr_pose_sshad | |- _ => idtac end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0009f3287db26f14 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0087813068ce83f2 1 1 8 2 0 1 72 1 3 1 1 73 1 74 8P00a49a57555dae4a 0 2 0 1 35 1P00c77b33cf9c2468 2 64 0 4 0 1 2 1 75 1 76 1 0 5 0 1 3 1 45 4 75 1 76 1P00c8fce6e96ab63a 0 5 0 1 43 1 45 1 56 1 57 1P0120255165f10a7b 0 5 0 1 37 1 40 1 49 1 50 1P015620997534d7bf 1 1 8 2 0 1 93 1 3 5 1 94 1 95 8P0163b52db7351fb8 0 2 0 1 1 1P018f4cc76cb7d7b6 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P01a48e69cb972e31 2 70 0 4 0 1 2 1 106 1 107 1 0 5 0 4 3 4 70 16 106 4 107 4P01c81e66c60ddedd 0 2 0 1 41 1P01d6c71b1c60eb98 1 1 8 2 0 1 73 1 3 42 1 72 1 74 8P01dc8da71412e695 0 5 0 1 43 1 45 1 56 1 57 1P024f9541a0f0d5f4 0 4 0 8 39 8 76 8 77 8P0290040df19a3821 0 5 0 1 43 1 45 1 56 1 57 1P02a5294c2408e4bf 0 2 0 1 27 1P02c92a4f5dbd4850 0 2 0 1 36 1P02ddc32916948d7b 1 1 8 2 0 1 72 1 3 2 1 73 1 74 8P032b36959e98d368 0 2 0 1 37 1P03576ec2d448bf95 0 2 0 1 30 1P03e01ccdbb8d850b 0 5 0 1 43 1 45 1 56 1 57 1P0461cf6c4cf556d1 1 1 8 2 0 1 89 1 3 55 1 88 1 90 8P04f70427fd647138 0 2 0 1 66 1P053957551136045e 0 2 0 1 2 1P05411a82717c7aed 0 2 0 1 2 1P0566670a8ab46269 0 5 0 1 62 1 65 1 78 1 79 1P05a1973584bf2f56 0 5 0 1 63 1 66 1 85 1 86 1P061ab89267f117a9 0 2 0 1 38 1P065ab3e843865518 2 69 0 4 0 1 2 1 106 1 107 1 0 5 0 1 3 1 55 4 106 1 107 1P0686036bdca0b82d 1 1 8 2 0 1 71 1 3 2 1 72 1 73 8P06c97e5559a4a2d0 1 1 8 2 0 1 78 1 3 45 1 77 1 79 8P07b0a73ea3a05abd 0 5 0 1 58 1 61 1 70 1 71 1P07c5dad313ff0ae0 0 5 0 1 37 1 40 1 49 1 50 1P084fdfd1d411494f 0 2 0 1 39 1P08632b918025c2ca 0 3 0 1 24 1 33 1P08ceef3f23f02cca 0 2 0 1 34 1P091c0d050c8c1f02 0 5 0 1 58 1 61 1 70 1 71 1P091e2d6c0d2d0900 0 2 0 1 2 1P092034618e799eb2 1 1 8 2 0 1 72 1 3 8 1 73 1 74 8P092f7e85c9fefccd 0 4 0 8 55 8 88 8 89 8P0a2bd7bb87d6be9a 0 2 0 1 39 1P0b00319048a96874 0 5 0 1 43 1 45 1 56 1 57 1P0b2715e37b7b477e 0 4 0 8 40 8 72 8 73 8P0b3a76be815b3313 0 4 0 8 41 8 72 8 73 8P0b4593f74d5e927f 1 1 4 1 0 1 2 22 1 65 1P0b6d215a840040e1 0 5 0 1 43 1 45 1 56 1 57 1P0b8d1d6a7a3bbdf5 0 2 0 1 38 1P0bb2380ee91fb8aa 0 2 0 1 1 1P0bcf9868fbeed146 0 5 0 1 58 1 61 1 70 1 71 1P0c18246c015b9431 1 1 8 2 45 1 73 1 3 0 1 72 1 74 8P0c2bb07752fdd84f 0 5 0 1 58 1 61 1 70 1 71 1P0c593724187be017 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0cbbb0242dc555f9 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P0ce49a356270a436 0 3 0 16 28 1 78 1P0d0475ca6f52f575 0 2 0 1 1 1P0d282f7e06b2cca0 0 2 0 1 2 1P0d6ccf55213798cf 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P0d7b1ccad2de982a 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P0d891bb78dd2f451 0 5 0 1 43 1 45 1 56 1 57 1P0d8b05111cb7ae2b 0 5 0 1 58 1 61 1 70 1 71 1P0ddb665b1dd84ad8 0 2 0 1 1 1P0de88171b4e12055 0 5 0 1 37 1 40 1 49 1 50 1P0dfb7f18f8330dc3 0 5 0 1 58 1 61 1 70 1 71 1P0e226c1fe9053a78 0 5 0 1 37 1 40 1 49 1 50 1P0e342121c472ecb4 0 5 0 1 43 1 45 1 56 1 57 1P0e9d608a6dea870a 1 1 8 2 0 1 73 1 3 41 1 72 1 74 8P0ea8a167800cf0cf 0 2 0 1 65 1P0f2273dfd15a5253 0 2 0 1 1 1P0f2ba4f3d6b8dc7d 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P0fbda088fb3f172f 0 2 0 1 38 1P100ddfa6ea5709b5 0 4 0 16 27 1 40 1 77 1P102c5286881a3db8 0 2 0 1 65 1P105038a0d7cbe83d 1 1 8 2 0 1 75 1 3 11 1 76 1 77 8P105dbdf0ffee9c19 0 2 0 1 2 1P1063727e52d3255a 1 1 4 1 0 1 2 23 1 65 1P10d37ac665f0ad0f 0 2 0 1 1 1P10f21b7818cbce5d 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1127293622523941 0 2 0 1 39 4294967296P119db33be2f95933 0 2 0 1 1 1P11c55c35f758015c 0 2 0 1 2 1P11d0a5d714f2d34f 1 1 4294967296 1 0 1 2 1 1 77 1P11ddb1cbc5402519 0 5 0 1 43 1 45 1 56 1 57 1P1247804d060295cd 0 4 0 8 42 8 72 8 73 8P127bd25dd6ecbcd5 0 2 0 1 35 1P12805c4dd20dc321 0 5 0 1 37 1 40 1 49 1 50 1P12b8869c9a38c4e1 1 1 8 2 0 1 72 1 3 9 1 73 1 74 8P13a91e02cb1e89b4 0 2 0 1 1 1P1403df7494efcf60 0 2 0 1 39 1P140c53772e587866 0 2 0 1 36 1P143c1c89ba2b8f67 0 2 0 1 2 1P145c99a9e24cc542 0 3 0 1 27 1 40 1P14be64a4289736c4 0 2 0 1 2 1P14c717593483d299 0 2 0 1 25 1P14d686b2c61b1e2a 0 2 0 1 2 1P14fcd581c8872071 1 2 8 2 0 1 76 1 8 2 45 1 77 1 2 78 1 79 1P159317cfaaa49880 0 5 0 1 62 1 65 1 78 1 79 1P15f52dee50f19155 0 5 0 1 43 1 45 1 56 1 57 1P16248b0d64aeb099 0 5 0 1 43 1 45 1 56 1 57 1P1640f0a5a8a909d1 1 1 4 1 0 1 2 21 1 61 1P165567e4f42bacb8 0 5 0 1 58 1 61 1 70 1 71 1P165a13405616b637 0 2 0 1 65 1P167a1c0c645ea336 1 1 8 2 0 1 77 1 3 11 1 78 1 79 8P16b2dba5936cf460 0 2 0 1 2 1P16f59bdef3f56d3d 1 1 8 2 0 1 71 1 3 1 1 72 1 73 8P17932ddcb85f993f 0 2 0 1 1 1P17bf0aa82fed8759 0 4 0 8 41 8 72 8 73 8P17f939911410be2f 0 2 0 1 2 1P183f5df8f1dcf76e 0 2 0 1 1 1P185a76ccbdaa666b 1 1 16 2 37 1 89 1 3 0 1 88 1 90 16P188625f344c4f2fe 0 5 0 1 62 1 65 1 78 1 79 1P18a4885c9ef214a5 0 5 0 1 37 1 40 1 49 1 50 1P1903a2464401ddeb 0 5 0 1 43 1 45 1 56 1 57 1P1911310347014471 0 5 0 1 63 1 66 1 85 1 86 1P1954589ff26c48a4 0 5 0 1 62 1 65 1 78 1 79 1P1962fb1a44899124 0 5 0 1 63 1 66 1 85 1 86 1P1a6c99c023800c71 0 5 0 1 63 1 66 1 85 1 86 1P1b2fd84531298259 2 60 1 1 8 3 1 1 75 1 76 1 6 0 1 62 1 65 1 74 1 77 1 78 8 1 1 8 3 2 1 74 1 77 1 4 0 2 75 2 76 2 78 16P1b4624ca473999f6 2 57 1 1 8 3 1 1 79 1 80 1 6 0 1 60 1 63 1 78 1 81 1 82 8 1 1 8 3 2 1 78 1 81 1 4 0 2 79 2 80 2 82 16P1b6df06951bcfedb 0 5 0 1 43 1 45 1 56 1 57 1P1bad51454e164590 1 1 8 2 0 1 73 1 3 41 1 72 1 74 8P1bc697093772fc2c 2 69 0 4 0 1 2 1 106 1 107 1 0 5 0 1 3 1 55 4 106 1 107 1P1bcd13c0c444eb3d 0 5 0 1 37 1 40 1 49 1 50 1P1bf259009b3edda9 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1c12251cbc37c513 0 2 0 1 2 1P1c50a0bcee8b5e23 0 5 0 1 58 1 61 1 70 1 71 1P1cb4bd3ebd49d63d 0 3 0 1 24 1 33 1P1cd1b5a024beb49a 0 5 0 1 58 1 61 1 70 1 71 1P1cd76fa5dad3ea53 0 5 0 1 62 1 65 1 78 1 79 1P1cf723eb9be8d45e 0 2 0 1 2 1P1d2b4deb2353a727 0 5 0 1 58 1 61 1 70 1 71 1P1dcdbf3f306d4173 0 2 0 1 35 1P1dfdce8b1ead0ec0 0 5 0 1 43 1 45 1 56 1 57 1P1dff66a5779f8e63 0 2 0 1 51 1P1e0622e13c2594d5 0 5 0 1 62 1 65 1 78 1 79 1P1e1c7256a0013aa3 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1e7137331fbd5613 0 5 0 1 43 1 45 1 56 1 57 1P1e7976d6b65a2128 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1ea158e8358d24b4 1 1 8 2 0 1 80 1 3 15 1 81 1 82 8P1ead2d918d5fbd6b 0 5 0 1 63 1 66 1 85 1 86 1P1ec0465471c77250 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1ecdfcf98b3082e7 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1ed7b1d4e413e530 1 1 8 2 0 1 72 1 3 9 1 73 1 74 8P1eef8c21c3126081 0 2 0 1 2 1P1efc418ba3d7fa80 1 1 8 2 0 1 88 1 3 1 1 89 1 90 8P1efda9b7b52f5e93 0 5 0 1 58 1 61 1 70 1 71 1P1f16aa177d021ea3 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1f177f3fac65b14a 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P1f39775fcce6fd0e 0 2 0 1 2 1P1f3cabf507e0b3ee 0 4 0 8 47 8 89 8 90 8P1f46f9853591f566 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1f7d52c17539e09f 0 8 0 1 19 4 21 1 22 1 37 1 69 1 89 1 90 1P1fbe30a99e6bc374 0 2 0 1 2 1P1ff22294387c0552 0 2 0 1 1 1P20494900b7243210 0 5 0 1 62 1 65 1 78 1 79 1P20766f4a93968dcd 1 2 8 2 0 1 76 1 8 2 45 1 77 1 2 78 1 79 1P207a01a7ad68f3ae 0 5 0 1 43 1 45 1 56 1 57 1P207b61eafe53684a 0 5 0 1 63 1 66 1 85 1 86 1P20cfede689b02dd4 1 1 8 2 0 1 74 1 3 4 1 75 1 76 8P20d6958a1be92089 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P21271115a1c944c9 0 2 0 1 1 1P21605993741a4298 0 2 0 1 27 1P2193c997404cabec 0 5 0 1 58 1 61 1 70 1 71 1P219900689d07e48a 2 72 1 1 8 3 1 1 106 1 107 1 6 0 2 77 2 80 2 105 2 108 2 109 16 1 1 8 3 2 1 105 1 108 1 4 0 2 106 2 107 2 109 16P21d05e224c0cd0f9 0 4 0 8 38 8 71 8 72 8P2249ecae1564b01c 0 5 0 1 58 1 61 1 70 1 71 1P2333fbcdd2d774e8 0 2 0 1 38 1P23412d48c38ca859 0 2 0 1 37 1P2352feef50c879e8 1 1 8 2 0 1 73 1 3 41 1 72 1 74 8P2354c2485571b61a 0 5 0 1 58 1 61 1 70 1 71 1P239a2cec736140a4 1 1 8 2 0 1 86 1 3 1 1 87 1 88 8P23bd2cad14a3d345 1 1 8 2 48 1 73 1 3 0 1 72 1 74 8P23e120ac1d08b8e7 1 1 16 2 32 1 88 1 3 0 1 89 1 90 16P23f7fff3baa70815 0 4 0 8 48 8 86 8 87 8P24a1a348b015a8fe 0 2 0 1 2 1P255beed3559133f8 0 2 0 1 37 1P25802041407e3704 0 5 0 1 58 1 61 1 70 1 71 1P25af2597621df9ca 0 5 0 1 63 1 66 1 85 1 86 1P25f82e6895ba4a7f 0 5 0 1 58 1 61 1 70 1 71 1P2674baf472410c4d 2 58 1 1 8 3 2 1 80 1 81 1 4 0 2 79 2 82 2 83 16 1 1 4 4 3 1 46 4 79 1 82 1 4 0 1 80 1 81 1 83 4P2714f75de2f4a79b 0 2 0 1 37 1P272e10a6f87faea7 0 4 0 8 44 8 77 8 78 8P273bf3cf4a01be7f 0 5 0 1 63 1 66 1 85 1 86 1P274f96e0407277b2 0 2 0 1 1 1P27509367122be998 0 2 0 1 2 1P2785fc90398d1d16 1 1 8 2 0 1 72 1 3 8 1 73 1 74 8P279fd2d02f8d47a4 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P27b68b0891ba3318 1 1 8 2 0 1 88 1 3 1 1 89 1 90 8P27c60ee3289322f3 0 2 0 1 51 1P2840b9fe51a41933 1 1 8 2 0 1 71 1 3 1 1 72 1 73 8P28539b2324b8dd30 1 1 8 2 0 1 89 1 3 1 1 90 1 91 8P288a6a1b8ae31228 0 2 0 1 25 1P28c5b3d870034d1b 0 2 0 4 7 4P29b091ce6c59881d 0 2 0 1 2 1P29f00c44490470d2 0 5 0 1 37 1 40 1 49 1 50 1P2a56a569f28a9e5f 1 1 16 2 0 1 88 1 3 33 1 89 1 90 16P2a81067e2d360eb2 0 2 0 1 38 1P2ab1520df617b656 0 5 0 1 62 1 65 1 78 1 79 1P2b2420675c7c16b5 1 1 4 1 0 1 2 23 1 64 1P2b672e42aa884430 0 2 0 1 38 1P2b86a196cc50c1b6 2 59 1 1 8 3 1 1 74 1 75 1 6 0 1 61 1 64 1 73 1 76 1 77 8 1 1 8 3 2 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2b9b28fcdf6b09d9 2 70 0 4 0 1 2 1 106 1 107 1 0 5 0 4 3 4 70 16 106 4 107 4P2ba0b018a57bdb06 0 2 0 1 28 1P2bacf00c2ddd347e 0 5 0 1 58 1 61 1 70 1 71 1P2bc8d863daf8e8d7 1 1 8 2 0 1 102 1 3 4 1 103 1 104 8P2c6b8770c2db4a7c 0 4 0 4 1 4 20 16 39 16P2ccc6fd07cea545a 1 1 4 1 0 1 2 21 1 61 1P2d49176c5300294c 0 2 0 1 1 1P2db3906ad6bf86f4 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P2e81b3a4a324b48d 1 1 8 2 0 1 72 1 3 1 1 73 1 74 8P2ea90337adf86b1f 0 5 0 1 43 1 45 1 56 1 57 1P2ebb0d44707c7b12 0 2 0 1 1 1P2ee1d4c616e3a010 0 5 0 1 63 1 66 1 85 1 86 1P2f148d49d847e866 0 5 0 1 62 1 65 1 78 1 79 1P2f165828ee6c3042 0 5 0 1 62 1 65 1 78 1 79 1P2f5dc19126e7fc6a 0 5 0 1 58 1 61 1 70 1 71 1P2fd384954a97e558 0 2 0 1 1 1P302a6e0eb3eeac8d 0 2 0 1 28 1P320fd16899380445 0 2 0 1 36 1P321838d535c0c3fd 0 5 0 1 37 1 40 1 49 1 50 1P323bd34ea71b1f0b 0 2 0 1 39 1P324be368474377d5 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3318194748e2f073 0 2 0 1 2 1P335a334e02a1a76b 1 1 4 1 0 1 2 24 1 64 1P33b5bf61a9cc6514 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P33db3b49c52dee0f 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P33ed794c3324a3cb 0 5 0 1 63 1 66 1 85 1 86 1P341a20571061d1e0 0 2 0 1 20 4P342128fa81c23b80 2 72 1 1 8 3 1 1 106 1 107 1 6 0 2 77 2 80 2 105 2 108 2 109 16 1 1 8 3 2 1 105 1 108 1 4 0 2 106 2 107 2 109 16P34b3a1709fd0b402 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P34c3d5b408ba514e 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P35137cc31f9ad054 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P35381b42a0465443 0 5 0 1 43 1 45 1 56 1 57 1P3639f98f0fc6f619 0 4 0 8 39 8 71 8 72 8P363d459324b0c146 0 2 0 1 20 4P365e3adceb07c49a 0 4 0 8 39 8 76 8 77 8P3677b2c0dedd21c1 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P3695d4ae1e88d934 0 2 0 1 1 1P375c614de053476d 1 1 8 2 0 1 72 1 3 39 1 71 1 73 8P376981c26c5d1178 0 3 0 1 26 1 39 1P37792c76b900e847 0 2 0 1 2 1P3786cb0bd2c9e079 0 4 0 16 27 1 40 1 77 1P37afe05d235e9068 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P388ad6d7a9f2196c 0 2 0 1 39 1P38c1c0046ab4d48c 0 5 0 1 43 1 45 1 56 1 57 1P391c975a12f0ee63 0 5 0 1 43 1 45 1 56 1 57 1P3969063c05cdf336 0 5 0 1 58 1 61 1 70 1 71 1P39876556635e685a 0 8 0 1 18 4 20 1 21 1 36 1 68 1 88 1 89 1P3a06b9971cb0bbf3 0 2 0 1 1 1P3a648ae1329c5307 0 2 0 1 1 1P3a661b94544658c5 0 5 0 1 63 1 66 1 85 1 86 1P3a67a9d534b7d234 0 2 0 1 2 1P3a78df45dbbf7da4 0 2 0 1 51 1P3a8657ccc5e7183f 0 2 0 1 1 1P3a9de9501964c316 0 5 0 1 62 1 65 1 78 1 79 1P3b0ea757f44b0ee1 0 2 0 1 25 1P3b19d0e1548a9578 2 38 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P3b442873cf289acb 0 2 0 1 1 1P3b4f079301ff3d14 0 2 0 1 1 1P3b5a8a063d538abd 0 5 0 1 43 1 45 1 56 1 57 1P3b71e665aaeaa8f4 2 32 1 1 8 3 2 1 59 1 60 1 6 0 1 45 1 47 1 58 1 61 1 62 8 1 1 8 3 1 1 58 1 61 1 4 0 2 59 2 60 2 62 16P3bd524702c7b87d3 1 1 8 2 0 1 75 1 3 4 1 76 1 77 8P3be29c8015cd9b44 0 2 0 4 4 4P3bfffa67aa26beaf 0 2 0 1 1 1P3cedb398bf59c2fe 0 2 0 1 38 1P3d00784dd7f71318 0 2 0 1 37 1P3d143038eed6c788 2 41 1 1 8 3 2 1 73 1 74 1 6 0 1 60 1 63 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P3db4b6bd7386d12c 0 5 0 1 37 1 40 1 49 1 50 1P3dc1469a17b391f7 0 5 0 1 37 1 40 1 49 1 50 1P3dd6f9bba6f5acc4 1 1 8 2 0 1 77 1 3 12 1 78 1 79 8P3e655f4d2ee1b020 0 5 0 1 58 1 61 1 70 1 71 1P3e8582e82dbeddbe 2 63 0 4 0 1 2 1 74 1 75 1 0 5 0 1 3 1 43 4 74 1 75 1P3ef09aff24a20e65 0 2 0 1 1 1N000c8d8ecd34029dN003363f26888e835N00d6b5797467fab0N0110189179b2e0dcN011e204e68547f5cN0124d0aa64121197N01b960433f716c2aN01c39d804acc2d4bN01d6c64d2f67f3f2N021a8529d10ade52N02247ebca1359f93N02294219a793db75N02971404f71c06d0N02a0b0f94f67474eN02c5334310028db4N02e2d280c0cb197bN02e975760f1d1b8eN032333a321c77e91N036d731e57124427N03cd05509d623c69N040ad38fa692a403N041367451f053031N04145d692537507dN0418ed62a77c9328N044dce6a22c0cf89N0487dc7fae687145N04a60bf8e4cfc1a2N04aa9f4683d31316N04ba9540d3ec867aN05497ec14d42e9ffN05c1748fa9ef49e9N05ed8e0989a68fdcN05f05d39c9752cb2N05ff5001e4efe667N062e2d5e8d9cf89bN0632c56af841945bN06524102f8460370N066bf18da0ab23d7N06a0c47e920d9ab1N06e9d2bfa913bd2cN073bcf216bbbef64N074ab252e5cf1db2N074f377e61a538fcN0798778262289a51N07d53218922dd5b4N08148cfc4d2cc02eN085bc8f61fc93a30N08cd1fc9c290924bN0936408db9a72186N095eadc107c0d812N097499b4c3fb4843N097b784b9b64e490N09b3807cced79922N09b7d3d27ad7bf2cN09db02dacbe55a0bN0a47ed450ffaa486N0a87c412dc248b9bN0b0c22ba24756423N0b2485b72af45e03N0b42186f4390bc20N0b7d11addc394b14N0b9cdf7821ac2ca8N0ba7656431dcc8ceN0c3441254b9ab168N0c95b24db7152e41N0cce0cff896d3688N0cd4b53cd53f19e5N0d00bbefc77b4fd2N0d1ca7700011f7aaN0d3df3d33e835156N0d54add6cc6733f4N0d5902d979aae499N0d626afefbe587f3N0dbf91f46cf1f200N0dfe38aa80725774N0e1bed1736a9cbe9N0e50d7fc0fb7fcb0N0e57e26eec1d6304N0eb7ea006c71e3a0N0ecc0aeeda49b59cN0f5c82abae82ec6fN0f7fa873f39a931fN0ff48eceb84e681aN1001ceae728719dcN1001f1f47763091fN100d711a0b7fe748N103658e223ebbb17N10eed4a76b154dedN1122cc21e6d54767N11232554c65ed862N115a5f5e456b2161N1191d4cf6b3f5cddN11bca084dd56d25aN1216da924b58b7abN123177125eaaf0dbN12458ec6d1c6ae34N125c7358d3c1c769N12acea5b2532b22bN12b7504617c33f35N1335d7672d05f01bN13397a8c843576d0N137e68914e4979b1N13ceb24ef60bd264N13d5b91680b67ceeN13ea0ddca8b5563cN14080401ecbed15aN14264c06f0e7c2fcN144fe1b3ef87265fN145122ddb2cf84ebN149494f0494bc19fN14ad5806e339cc85N14b61db949756c5aN14d75891c5c28441N152ee40db41f35f1N155ef10be49c5f0bN158cd35b92843a92N15959e5896bd1ceeN159f6b960243b253N15e369b5778b561dN15fe41ea43dffae7N1622a54644979a87N1664be9c221b64c6N166f658ce55b761bN16d4cb7854dbc09dN16dab63a773f8594N16eae8d9d4f9d1d4N1727014d4cb1f123N17592ab8f3ca80a4N17bec6f2f50a6194N17c23c8ff95df1b6N17fbfb8ca9b6c0eeN18089d2c65f032a3N18210863625c0e5eN1824db581d6963ddN182b7c99341a5d7fN1837f027fa7298eeN18481cb97a6e2908N1859b04d76e78827N1873166bd660d205N189303f1fdfe0335N18bdde1e2fe48ef1N190c50150267f070N190ea70372318dffN19105659bf579098N1924d39e7b258a6eN19496e403115a25cN1969aabea9e3d391N1a2182125d62bf53N1a5c53b4c937513cN1a82f40dfe834f01N1ab05e90416ca5aaN1b7ef86e06e133efN1ba45007833db5faN1bcc2f15c65d083dN1be725203aaa2046N1beaf6cc33f0b5abN1c0fb595825d5d7eN1c159d333fe9907fN1c271676191f5279N1c5862192e5ccec1N1c809c679afb5c3eN1c88181fbc8a5a04N1c98f57babe20bbcN1cb86f71b0a54f9fN1d4322b61a769e2bN1d79143904093652N1d95acd7303f05d7N1d9991e085ff652eN1df51f8335f87980N1e190726b1ea570dN1e593526ad5ab348N1e85fb5b323eeb93N1ea3524bb85a60caN1ebb0cfe20be614bN1f009f4aa8ac7890N1f11472e085ba0cdN1f1d3f7e85fd57c1N1f5ed6ee90381d2fN1f8f4cfd8c02403aN1fa7298110701441N1fc9d712831f6ceeN1ff253db9606e44eN200b98c47bd99e45N202c3e4ad24d0542N20875dcdb2e4d100N20a722b214e26d9eN20cb64d01a988e42N21121a785060c788N21400c8f9885a692N21b5ed84a1a478cdN21c761d8b75e9c8fN22052ffd1656e2e4N2225cc12023e38e6N2229d3cac49959f7N2257dcf08c13f7ccN226f8a065e1bc5c7N2288b63e2afd4273N22b559c6fd7a925cN22c0cb46fb075a72N23067db13329d788N235991a6a1bcd885N236f10b3a4c1844cN23af6f957f6dea6dN23c7644a7a988f98N23d14fc5385ff38bN23d15f965b7954ccN23d743fd3045b6baN2403e8292365d185N242fd035f0eaa5b9N2455c6a138d4eda4N24562dbcd0bf0230N2465733fde78e178N24cb9391adce2d4cN24cc735a8828d817N24dc56af550dba14N25465b5ff0ecc63dN254cd28efbcd2152N255fff644bd8b6b8N256a6382b51a1011N25a83dc5d2bf4885N25b18a62dd0a8b44N25f9e84e15819b51N26026b7678cadfb6N26079a38b3a57cc7N2637fde525010bc8N263ce3a0c09d0829N2652ae3695050fb9N267530050711d5a9N26cacba7a9983d51N270d2145e243493aN272974f113422fecN276777be9cd250e9N2791fa896e8069a3N27a3a45d829e9e78N27bc3badc971a8e2N27d408f7875e0e7dN281227e626d4206dN283bfffd4d930149N283d9edb6e05c1caN2888bd2cda31be7fN288b8903e950bc60N289d84da73b5bfcdN28b907e7559ea9f2N28dcbcc2750bf79dN28e0b1b6bc84d2b2N29277dc27b599b0dN2942967d2c0e0f6eN29651a508b63ae7cN2974ea33fae5f410N298dc6e85e47c5ecN29af1253b73e19ecN29cb7c56cc3e173cN29da985e57e009e0N2a08984b46997be9N2a0aa287102268ddN2a235352724cfde9N2a35fde862f7faccN2a49c06ed0a57328N2a50ffd79fdd3618N2a6152c460311732N2af662ff3ad1e258N2b33f257033feb6bN2b5cb882256a1cb6N2b96261f07d329cdN2ba8ea05620af95bN2c2fef5dcf89b2b8N2c4c204ebb692efbN2c6cf7246ef0545dN2c8b223a5ddb5aecN2cf42ff85eb32b66N2cf46bd95808865cN2d15c040e746394bN2d2a21c7962659faN2d37702216f1f2cfN2d60a442812140c1N2d6c5b9c36ad0605N2d91b8ee51bc40fbN2dc71f5c9c396238N2dd37b727d79c4f1N2e26d30adf8076b9N2e4486ec137a5785N2e6c4c560f093371N2e6e8c8a16c9d8ceN2ec9d01681c82d26N2ed3dd03dcccbf36N2f25a8ec8c6f9f19N2f4e5f3896a3ba44N2f90d668af421179N2fa20d19c39c8b10N2fae7175f9766280N2fafcddbc7a97fdcN2fc9d8c8bfd9269bN2fdf1812f6fa3fb3N2fe7afcf20aa1fd6N2fe9b56ad93bba40N2ffd234a2442a16bN301bff631966788bN3057a65f4620bdbaN3062a7f1b4cac8c9N30720c8aa04cfd95N3082e3571233c573N30885aa9ebc6ed02N30a002fdf1d505f8N30dba54a4a351e60N30dfb19e945994feN30e287fbd549b5ccN3115d20a8c1156c6N31381b7e77cad830N31789561d383661cN31b71248a9ff1b03N31d02d2610de5afeN31e3a85538141d9fN31e6875af04251bfN31fddf0bee0a9a5cN3208dc5bc534c279N321762d231e3ed9fN321e97c27a617ec8N32227211e763831cN3255f912779067e6N325ddf1eafd30761N327333ab8a96897bN328620166fdb0564N32c4105cef672166N32da8d5e5cc2343bN33812049a7e3cff4N33e4255c72fdfbe8N33e63115fae2a40bN3419439eefc344e7N342c0a75e74e562eN3440759dc4670b5dN344d60a26d534841N346875a26fad8bb2N349abec3ec60b8dcN34dff898cc70c8beN352235e26566f738N353a4f25574fe537N353ffbb8f4605d6dN3562956e6aa050daN35674902f852a5eeN356be91beebe098dN35c0b6190e90c0ddN35f497781e96af51N361deda0aaeaab55N3655cca7234c448fN36856dde69abc74cN369a3074ba00815cN36aa9a2ff4559ce0N36c39721d4bfb242N36fd4ca7e5acbd45N37659261a7437614N37917663824f9806N37a4a1d05a0c5481N37c4809fa0913f29N37d201df1268648bN37f45e6d398314dbN38934967ef691f02N38a112312008e63eN38c8a7020cc6755fN39280448cd3f7a8aN3952a3df5bf00b2dN39576bd548b8b0a1N395adf7bd06e0d01N399050a8a31d9d64N3991997d54840803N39956637a9cbf3ddN39e9678c7fb2fa49N39eed0e88c974001N39fd68f5b37ece58N3a2768ba1f1ebeb3N3a6b89e0f4e30afaN3a7d24b76e9e4162N3a891a60817b44e6N3abb3229c0f5dbedN3ae9e41f74e7b1e6N3b000260c98d9febN3b0b6a187eaa4f89N3b155840ae5192d3N3b2047b30dee3708N3b41f479dc634737N3b5e8f86eebf7130N3b750ed2a2494d34N3bacb77eb8c94484N3bb0528f987553a8N3bc3c5454c2f3ff2N3bfa8853c57029dcN3c0932977c3ea5a7N3c4cec8182c94b34N3c79d752d7475572N3c82076b9c0367a9N3cacb907ac6ce671N3cd6c08076792977N3cd85f8b84ee7327N3d5380ec653ff6b0N3d68cdb81fca5befN3d6f634eb93388a3N3d728fbc141dd183N3d7b4b939507f584N3d859a209ee5a07dN3dc6a3568f1d81f5N3dc81ac97dadf277N3dd9d0115972c508N3e649ab294407367N3e6d79d7c0821c5dN3eb1c6c824c9ac37N3eb394056ddc48deN3ed6f1fcb8fc64c6N3eeba5bfdd08a0bbN3f32ffd3949d0299N3fb4b681e9ddf2d3"%lxh.
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
Ltac2 gd_tbl_A_mpi_copy_c24 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "C24_COPY_c"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.trim_i"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.zeros_above"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_Rx"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Nat.mul"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_COPY"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.A_WRAP_CALLOC_CP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.A_ASAN_MEMCPY_CP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.A_ASAN_MEMSET_CP"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "mpi_copy_stmtA_x_c"; "mpi_copy_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_MEMSET_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_WRAP_FREE_ZF"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_free"].



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition C24_COPY_c : Z := 1.
Definition mpi_copy_stmtA_gen_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z)
    (Rr : mpd -> mpd -> list blk -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Ph,(0.O5.O4.O3.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdY,$7.Plo,$8.Pd,$8.P,(9.O5.O4.O3.R2:.R29.R28.R6.)P,(:.O5.O4.O3.R2;.R6.)P,(;.O5.R8.R2;.R6.)P,(<.(=.$>.(?.R7.)$10.))P,(;.O5.R:.R2=.R7.)P,(11.R9.R8.)P,(12.R:.R9.R8.(13.&40.R2<.))P,(14.(15.O4.)(16.$2.R30.(17.R2?.))R9.(18.R:.)+10.)P,P,(=.$>.(?.R;.)$19.)(14.(15.O4.)(16.$2.R32.(17.R31.))R;.(1:.R<.)(1;.+4.(1<.R<.)))P,(1=.O4.R32.R31.(13.&40.R2?.)(1>.O5.O4.O3.R33.)R=.)P,(1?.O5.R10.R<.(13.&40.R30.))P,(20.(21.O4.)R=.)P,(20.R>.(22.(22.(13.&40.R32.)+70.)(23.O4.)))P,(20.(13.&40.R33.)(1>.O5.O4.O3.R37.))P,(=.$8.(24.(13.&40.R34.)+10.)=)P,(=.(3.&40.)R33.(25.&40.(26.O4.)))P,(27.O5.R16.)P,(=.$8.(24.(13.&40.R38.)+2.)=)P,(28.O5.(29.O4.)(2:.O5.O4.O3.R3<.)R18.(18.R16.)+10.)P,(28.O5.(29.O4.)(2:.O5.O4.O3.R3=.)R19.(18.R16.)+10.)P,P,(=.$>.(?.R17.)$10.)(=.$2;.(2<.(1:.R18.)(1;.+4.(1<.R18.)))$2=.)P,(20.(2>.(2?.O5.O4.O3.R3?.)(30.R18.))$31.)P,(32.O4.(18.R1:.)+10.R17.)P,(20.(2>.(33.O5.O4.O3.R41.)(34.R18.))$35.)P,(20.(2>.(36.R41.)$37.)$38.)P,(=.(3.&40.)R37.(25.&40.(18.R1=.)))P,(=.(3.&40.)R37.(25.&40.(18.R1=.)))(39.O5.(3:.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R45.R44.R43.R1?.A3.O1.R1>.R1?.R44.(30.R1>.)(34.R1<.)R1=.R21.R20.)(3;.(3<.(3=.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(25.&40.O2.)R22.(3>.(3.&40.))R21.(3?.O5.))R20.))")
(* [comment removed for export] *).

Definition mpi_copy_stmtA_x_c segs R HIA ENTRY := mpi_copy_stmtA_gen_c segs R HIA ENTRY copy_Rx.
Definition mpi_copy_stmtA_c segs R HIA ENTRY := mpi_copy_stmtA_gen_c segs R HIA ENTRY copy_R.

Lemma mpi_copy_stmtA_of_x : forall segs R HIA ENTRY, mpi_copy_stmtA_x_c segs R HIA ENTRY -> mpi_copy_stmtA_c segs R HIA ENTRY.
Proof.
  intros segs R HIA ENTRY HX. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_x_c, mpi_copy_stmtA_gen_c in *.
  intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo dX dY lo d.
  intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27.
  eapply aevtS_mono.
  { exact (HX h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo dX dY lo d
             A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27). }
  cbv beta. intros c PO. unfold mpi_binop_postA in *.
  flat constr:(PO) 21%nat. flclear PO. intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 m' mo' h' LB' dX' r PO.
  repeat match type of PO with _ /\ _ => destruct PO as [?H PO] end.
  do 20 eexists. repeat (split; [eassumption|]). exact (proj1 PO).
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_CP.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_CP.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis RIMG : hl_img_lo L <= 0x10000 /\ 0x0f1000 <= hl_img_hi L.   (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Hypothesis C24H : cnt24 LB + C24_COPY_c <= C24MAX.     (* [comment removed for export] *)
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sgX nX pX : Z) (xs : list word) (padX : word) (ownX : limb_own)
            (Y sgY nY pY : Z) (ys : list word) (padY : word) (ownY : limb_own)
            (lo d : Z).
  Local Notation dX := (mkMPD X sgX nX pX xs padX ownX).
  Local Notation dY := (mkMPD Y sgY nY pY ys padY ownY).
  Hypothesis MAX : mpd_at asegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis MAY : mpd_at asegs m LB dY.
  Hypothesis NEQ : X <> Y.
  Hypothesis SEP : mpd_sep dX dY.
  Hypothesis CSEP : copy_sep dX dY lo (bv_unsigned sp).
  Hypothesis YCR : client_range L (LB ++ fdata LF) lo Y 16.
  Hypothesis YLCR : ownY = LHeap -> client_range L (LB ++ fdata LF) lo pY (4 * nY).
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 112 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis YNZ : ownY = LStatic -> img_norz pY (4 * nY) = true.
  Hypothesis XUW : uw_obj R X 16 d.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3)).
  (* [comment removed for export] *)
  Notation FRAME jk := ([CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).
  Notation POST mo := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                         (copy_Rx dY dX LB) (copy_PHI dY) (copy_FR d) lo m mo).

  Ltac basic_facts hc LBc mm HH TOPc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0; pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L30309475896.9L45370438041.9L60453088131.9L63312638695.9L819727256.9  L9364571742.9 00000B00M00_01101<01NS1X1Y2nY3NRY2XB2YBS1X1Y2XB2YBS1X2nX1Y3NRX2XB2YBS1X2nX1Y3NRX2XB2YBS1X1Y2XB2YBS1X1Y2nY3NRY2XB2YB". (* [comment removed for export] *)
  Lemma facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "(40.(=.$8.(24.VX,+8.)=)(40.(41.=VX,)(40.(=.$8.(42.(43.(3.&40.)Vxs,))VnX,)(40.(40.(20.=VnX,)(20.VnX,+2710.))(40.(44.(=.$8.VsgX,+1.)(=.$8.VsgX,-1.))(40.(=.$8.(24.VY,+8.)=)(40.(41.=VY,)(40.(=.$8.(42.(43.(3.&40.)Vys,))VnY,)(40.(40.(20.=VnY,)(20.VnY,+2710.))(40.(44.(=.$8.VsgY,+1.)(=.$8.VsgY,-1.))(40.(20.(2>.VX,+10.)(45.+2.+40.))(40.(20.(2>.VY,+10.)(45.+2.+40.))(44.(20.(2>.VX,+10.)VY,)(20.(2>.VY,+10.)VX,))))))))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(MAX) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 2%nat. flclear FLt1. intros CHX FLt2. flat constr:(FLt2) 5%nat. flclear FLt2. intros XAL X0 LENX NRX _. flat constr:(MAY) 2%nat. intros FLt3 SGY. flat constr:(FLt3) 2%nat. flclear FLt3. intros CHY FLt4. flat constr:(FLt4) 5%nat. flclear FLt4. intros YAL Y0 LENY NRY _.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold MPI_MAX_LIMBS in NRX, NRY.
    pose proof (rw_cells_bound _ _ _ _ CHX) as XB. pose proof (rw_cells_bound _ _ _ _ CHY) as YB.
    unfold mpi_cells in XB, YB. cbn [cells_size csize Nat.add] in XB, YB.
    destruct SEP as [E|SEP']; [exfalso; apply NEQ; injection E; auto|]. cbn [md_addr] in SEP'.
    repeat split; try assumption; clear - XB YB SEP' NRX NRY; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma hcs_img_cs_cp : forall hc, img_cs (hcs asegs R HIA hc).
  Proof.
    intros hc. flat constr:(IMG) 4%nat. intros G LO HI GSB. eapply img_cs_of; [exact LO | exact HI | exact G | exact GSB |].
    intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA hc); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma opy_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Phc,(0.$46.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))P,(9.$46.VR,VHIA,R3.R2.VLF,R1.)P,P,(=.$>.VownY,$19.)(47.(48.$8.$8.)(49.$8.$8.VpY,(1;.+4.VnY,))R4.)P,(<.(=.$>.VownY,$4:.))(28.$46.(29.VR,)(2:.$46.VR,VHIA,R6.)R4.VpY,(1;.+4.VnY,))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc HH HIN ON. destruct ownY; [exfalso; exact (ON eq_refl)| |].
    - eapply hm_aobj_block; [exact HH| exact (HIN eq_refl)].
    - eapply (aobj_img asegs AL); [apply hcs_img_cs_cp| eapply (hm_img_shadow asegs R HIA); exact HH| exact (YNZ eq_refl)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L1461017411.3 L15175825515.1L17030833117.4L63904838234.500000:00>00K00ZS2nY2ys2LYS2pYS2nY2pY2ys2LYS2nY2ys2LY1i2Hi". (* [comment removed for export] *)
  Lemma pby_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PLB0,(1.$2.)PLF0,(1.$2.)PSPx,$8.PTOPx,$8.PW,(1.$4;.)PmA,P,(3.&40.)(5.(3.&8.))PmB,P,(3.&40.)(5.(3.&8.))P,(4<.$46.VR,R7.R6.R5.(21.VR,)R4.R3.R2.R1.)P,(4=.$46.R3.VpY,(4>.Vys,))P,(27.$46.R4.)P,(27.$46.R4.)P,P,(=.$>.VownY,$19.)(47.(48.$8.$8.)(49.$8.$8.VpY,(1;.+4.VnY,))R<.)P,(<.(=.$>.VownY,$4:.))P,(4?.R9.VpY,(1;.+4.VnY,))(4=.$46.R8.VpY,(4>.Vys,))")
(* [comment removed for export] *).
  Proof.
    intros LB0 LF0 SPx TOPx W mA mB HP HB MIA MIB HIN ON HD.
    flat constr:(MAY) 2%nat. intros FLt5 _. flat constr:(FLt5) 2%nat. flclear FLt5. intros _ FLt6. flat constr:(FLt6) 5%nat. flclear FLt6. intros _ _ LY _ OY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LY, OY.
    destruct ownY; [exfalso; exact (ON eq_refl)| |].
    - eapply (presA_bytes_at asegs R); [exact HP| exact HB| |]; rewrite u32s_length.
      + eapply client_range_block; [apply in_app_iff; left; exact (HIN eq_refl)| clear; lia| clear - LY; lia].
      + replace (Z.of_nat (4 * length ys)) with (4 * nY) by (clear - LY; lia). exact HD.
    - flat constr:(OY) 5%nat. flclear OY. intros _ _ _ _ RO. eapply static_limbs_any_mem; [exact MIA| exact MIB| exact HB|].
      rewrite u32s_length. intros i Hi. apply RO. clear - Hi LY. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L29428324939.5L35653441506.7L60098763854.300000B00\00fS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS1R2lo3LOS". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Phc,(0.$46.VR,VHIA,)PLBc,(1.$2.)Pmm,P,(3.&40.)(5.(3.&8.))Pr,$8.Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,R1>.R1=.VLF,R1<.)P,(20.(13.&40.Vsp,)(1>.$46.VR,VHIA,R1?.))P,(50.$46.R1>.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R1<.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R1?.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R20.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,R23.)Lms',$56.(57.(3.&40.)Lx5,(3.&40.)(57.(3.&40.)Lx6,(3.&40.)(57.(3.&40.)Lx7,(3.&40.)(57.(3.&40.)La1',(3.&40.)(57.(3.&40.)La2',(3.&40.)(57.(3.&40.)La3',(3.&40.)(57.(3.&40.)La4',(3.&40.)(57.(3.&40.)La5',(3.&40.)(57.(3.&40.)La6',(3.&40.)(57.(3.&40.)La7',(3.&40.)(57.(3.&40.)Lx28,(3.&40.)(57.(3.&40.)Lx29,(3.&40.)(57.(3.&40.)Lx30,(3.&40.)(57.(3.&40.)Lx31,(3.&40.)(40.(=.$56.R?.(3<.(3=.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(25.&40.R2?.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R30.(3?.$46.)))(1?.$46.R30.Vlo,(13.&40.Vsp,)))))))))))))))))(3<.(3=.R1>.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R13.R12.R11.R1=.R1<.(25.&40.R20.)R10.R?.R>.R=.R<.R;.R:.R1;.R1:.R19.R18.R17.R16.R15.R14.Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+9<100.)Vfc,(3>.(3.&40.))R21.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    lx_pre. lx_run_tac (PLAN [] [] 30%N). lx_tree.
    all: lx_same_mem; lx_gc.
    lx_post.
    all: first [exact C24H | match goal with |- ?g => idtac "EPI-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.68L59308579027.7000000900ES2sp1a2HaS2sp1a2Ha2H0". (* [comment removed for export] *)
  Lemma ro_addr_ge_cp : forall a : Z, 0x0f1000 <= a < 2^64 -> ro_addr asegs (wa a) = false.
  Proof.
    intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
    unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
    repeat match goal with
    | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
    | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
    | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
    end.
    repeat match goal with |- context [if ?c then _ else _] =>
      let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
    reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.68L59308579027.7000000900DS2sp1a2HaS2sp1a2Ha1H". (* [comment removed for export] *)
  Lemma ro_addr_low_cp : forall a : Z, 0 <= a < 0x10000 -> ro_addr asegs (wa a) = false.
  Proof.
    intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
    unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
    repeat match goal with
    | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
    | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
    | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
    end.
    repeat match goal with |- context [if ?c then _ else _] =>
      let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
    reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L10829342886.2L11611731062.2L36836628079.3L37477245982.3L54691089461.2L62509910829.800000600<00F00O00V00hS1n2HnS1n2HnS1P2P03HltS1P1n3HltS1P3HgeS1P1n2ws2HL2PB3Hge". (* [comment removed for export] *)
  Lemma static_limbs_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmm,P,(3.&40.)(5.(3.&8.))PP,$8.Pn,$8.Pws,(1.(3.&40.))P,(4=.$46.R4.R3.(4>.R1.))P,(=.$8.(42.(43.(3.&40.)R2.))R3.)P,(20.+1.R4.)P,Pi,$8.P,(40.(20.=R1.)(41.R1.(1;.+4.R6.)))(=.$2;.(59.$46.(5:.(2>.R8.R2.)))$2=.)(40.(20.+10000.R7.)(20.(2>.R7.(1;.+4.R6.))+?1000.))")
(* [comment removed for export] *).
  Proof.
    intros mm P n ws HB HL Hn RO. flat constr:(HB) 3%nat. intros P0 PB _. rewrite u32s_length in PB. split.
    - destruct (Z_lt_ge_dec P 0x10000) as [Hlt|Hge]; [| clear - Hge; lia].
      exfalso. pose proof (RO 0 ltac:(clear - Hn; lia)) as R1. rewrite Z.add_0_r in R1.
      rewrite (ro_addr_low_cp P) in R1; [discriminate R1|]. clear - Hlt P0. lia.
    - destruct (Z_lt_ge_dec (P + 4 * n - 1) 0x0f1000) as [Hlt|Hge]; [clear - Hlt; lia|].
      exfalso. pose proof (RO (4 * n - 1) ltac:(clear - Hn; lia)) as R1.
      rewrite (ro_addr_ge_cp (P + (4 * n - 1))) in R1; [discriminate R1|]. clear - Hge PB HL Hn P0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01H0@C17025492443.173C25179474043.174C25179474043.175D13186458071.178D24994714674.152D62024748659.152K40494987808.177K61251806371.177K6288013615.174 K6288013615.175 K6379668000.173 L10514433047.3  L10718992232.12 L1222472026.7   L1222472026.8   L12880976633.3  L1335938295.2   L15175825515.1  L16960695120.9  L21845917364.16 L21847519070.3  L21847952408.8  L22683776779.11 L23144025037.4  L27040582980.7  L27842804030.3  L2802024539.16  L2803954423.10  L2804554661.4   L29428324939.5  L29443285534.3  L32332382178.8  L3253508485.5   L34263059663.14 L35653441506.7  L3641572268.13  L37035366229.2  L39172636981.0  L40485397855.5  L40491059971.7  L40491771973.4  L41084420269.1  L41523417557.7  L41993492402.4  L42252534531.154L42252534548.69 L44169409993.12 L44169409993.9  L48288935062.2  L48487841484.1  L48491422268.16 L48493695120.7  L58059560066.11 L60098763854.3  L6097558802.9   L61237649950.4  L61646496682.6  L62228589345.0  L6276868363.3   L63614613648.8  L63614701339.5  L6384586821.2   L64957412299.2  L66151427842.16 L68268214829.8  N21806751459.174N37104593031.174O17025492443.173O25179474043.174O25179474043.175O26567557383.177O28520546523.173O32791873655.177O40272236209.176O41811637710.177O48965075207.177P10508665514.177P27840184195.176P29429130403.177P42008695055.173P6288013615.174 P6288013615.175 P6379668000.173 Q30877736124.178Q38248387216.178Q41074460176.178Q42252534531.158Q43879899724.17800000100200300400^01A02002e02f02g02h02i02j02k02l03503603:03;03P03Q03R03S03_03`03a04304404504G04H04I04Z04[05505605705805905N05O05T05l05m07D07E07F07G07N07O07c07d08B08L08M08N08\08]08^08_08o09009109K09f0:M0;40;50;60;70;80;90;:0;;0;<0;=0<F0<G0<H0=G0=H0=I0=J0>60>T0?30@50@VFFFFS1R3HIA2sp1X2xs1Y2pY2ys2hc3pX'3xs03PY03PYBS1R2sp1X2xs1Y2pY2ys3pX'3xs03PY03PYBS2sp2xs2nY2pY2ys2lo1i3xs02Hi2C53PYB2LI3LIy4LENYS2xs2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3SY23PYB2LI3LIy4LENYFFFFFFFS2nY1i2HiFS2pYFS1R2sp2lo3SLO3NRA3SPRFFFS2nY2pY1i2HiFFS1R3HIA2sp2hc4TOPcFFS1R2lo3LOS3ALO3ACPFFS2nY2ys1i2Hi4LENYFS1R3HIA2sp2lo2hc4TOPc4HTOPFFSFS2sp2nY2pY2lo1i2Hi2C5FS3pX'S2nY1i2n'3xs02Hi3Hin3LL0FS1R5NEEDR2sp1X2xs1Y2nY2pY2ys2lo3LOS3SLO1i3pX'3xs02Hi3ALO3SPR2X02Y02B03PY03PYB2H02LI3LIyFFFS2sp2loFS2sp2nY1i2Hi3SPR3NRYFS1R2lo3LOS1i2n'3pX'3Hin3ALO2BCS1R2lo3LOSFFS1i2n'3pX'3HinSFFS2nY2pY1i2Hi3Y47FFS2pY2r03P161q1r1H2H02q02H4S2nY2pY1i2n'3pX'2Hi3Hin3SY2S2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIy3x151CS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIy3x151CFFFFFFFFFS1R5NEEDR2sp2xs2nY2pY2ys2lo3LOS3SLO1i2n'3pX'3xs02Hi3Hin3ALO2BC3PYB2LI3LIyFFS1R2sp2xs2nY2pY2ys2lo3LOS1i2n'3pX'3xs02Hi3Hin3ALO2BC3PYB2LI3LIyFFFS2xs2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3PYB2LI3LIyS2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2xs2pY2ys1i3pX'3xs03PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3LOS3SLO1i3xs02Hi3ALO3SPR3PYB2H02LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIy". (* [comment removed for export] *)
  Lemma final_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Phc,(0.$46.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pn',$8.PpX',$8.Pxs0,(1.(3.&40.))Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,R1=.R1<.VLF,R1;.)P,(20.(13.&40.Vsp,)(1>.$46.VR,VHIA,R1>.))P,(40.(20.+1.R1<.)(20.R1<.VnY,))P,(20.R1=.R1<.)P,(20.R1=.+2710.)P,(50.$46.R20.VX,(5;.R1=.(25.&40.VsgY,)R1>.VpadX,))P,(47.(48.$8.$8.)(49.$8.$8.R1>.(1;.+4.R1?.))R22.)P,(=.$8.(24.R1?.+4.)=)P,(5<.$46.R23.R20.R1?.)P,(=.$8.(42.(43.(3.&40.)R20.))R22.)P,(50.$46.R25.VY,(5;.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4=.$46.R26.VpY,(4>.Vys,))P,(<.(=.$>.VownY,$4:.))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R2:.)R28.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R2;.)R29.VY,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R2<.)R2:.VpY,(1;.+4.VnY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))R28.)(20.(2>.R28.(1;.+4.R29.))VpY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(45.+2.+2?.))P,(50.$46.R2>.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R29.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R2?.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R30.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,R33.)Lms',$56.(57.(3.&40.)Lx5,(3.&40.)(57.(3.&40.)Lx6,(3.&40.)(57.(3.&40.)Lx7,(3.&40.)(57.(3.&40.)La1',(3.&40.)(57.(3.&40.)La2',(3.&40.)(57.(3.&40.)La3',(3.&40.)(57.(3.&40.)La4',(3.&40.)(57.(3.&40.)La5',(3.&40.)(57.(3.&40.)La6',(3.&40.)(57.(3.&40.)La7',(3.&40.)(57.(3.&40.)Lx28,(3.&40.)(57.(3.&40.)Lx29,(3.&40.)(57.(3.&40.)Lx30,(3.&40.)(57.(3.&40.)Lx31,(3.&40.)(57.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(40.(=.$56.R10.(3<.(3=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1.(3?.$46.)))(40.(5=.(51.(48.$8.$8.)(49.$8.$8.R3>.(2>.R3>.(1;.+4.R40.)))(51.(48.$8.$8.)(49.$8.$8.Vlo,(13.&40.Vsp,))(54.(48.$8.$8.))))R41.R1.)(40.(5>.$46.R41.R1.)(40.(27.$46.R1.)(40.(5?.$46.R1.R3>.(4>.(60.(3.&40.)(61.R40.)Vys,)))(40.(1?.$46.R1.Vlo,(13.&40.Vsp,))(9.$46.VR,VHIA,R43.R42.VLF,R1.))))))))))))))))))))))(3<.(3=.R2;.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R2:.R29.R28.(25.&40.(1;.+4.R30.))R27.(25.&40.VX,)R26.(25.&40.VY,)R25.R24.R23.R22.R21.R20.R1?.R1>.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R1=.R1<.R1;.Vs10,Vs11,R1:.R19.R18.R17.)VF,(25.&40.+9<0<4.)Vfc,(3>.(3.&40.))R31.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc Hi Hin N10 HXS HIN XPA HXL LL0 HYS PBY OYN OX OY OPY SY2 C5 Y47 FR ST MI. basic_facts hc LBc mc HH TOPc.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    flat constr:((hm_apart asegs R HIA hc LBc LF mc HH)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    unfold mpi_cells in HXS, HYS.
    assert (PYA : pY mod 4 = 0).
    { flat constr:(MAY) 2%nat. intros FLa _. flat constr:(FLa) 2%nat. flclear FLa. intros _ FLb. flat constr:(FLb) 5%nat. flclear FLb. intros _ _ _ _ OYa. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OYa.
      destruct ownY; [exfalso; exact (OYN eq_refl)| |]; [flat constr:(OYa) 4%nat; intros _ _ P16 _; clear - P16; Z.div_mod_to_equations; lia| flat constr:(OYa) 5%nat; intros _ P4 _ _ _; exact P4]. }
    assert (LQ : Z.land (Z.lor pX' pY) 3 = 0).
    { rewrite Z.land_lor_distr_l. change 3 with (Z.ones 2). rewrite !Z.land_ones by (clear; lia). change (2 ^ 2) with 4. rewrite XPA, PYA. reflexivity. }
    pose proof (munch_refl [(pX', pX' + 4 * i); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x067dbc] [] 40%N). lx_tree.
    all: try (match goal with LXKT : (if zlow 64 (Z.land (Z.lor _ _) 3) =? _ then false else true) = true |- False => rewrite LQ in LXKT; rewrite Z.eqb_refl in LXKT; discriminate LXKT end).
    all: lx_same_mem; lx_gc; try clear OQH.
    (* [comment removed for export] *)
    pose proof HXL as PU. rewrite <- (firstn_skipn (Z.to_nat i) xs0) in PU. apply u32arr_app in PU. flat constr:(PU) 2%nat. flclear PU. intros PUi _.
    assert (LI : length (firstn (Z.to_nat i) xs0) = Z.to_nat i) by (apply firstn_length_le; clear - Hi Hin LL0; lia).
    assert (LIy : length (firstn (Z.to_nat i) ys) = Z.to_nat i) by (apply firstn_length_le; clear - Hi LENY; lia).
    pose proof PBY as PBY'. rewrite <- (firstn_skipn (Z.to_nat i) ys) in PBY'. rewrite u32s_app in PBY'. apply bytes_at_app in PBY'. flat constr:(PBY') 2%nat. flclear PBY'. intros PBA _.
    pose proof (hm_aobj_block asegs R HIA hc LBc LF mc pX' (4 * n') HH HIN) as OPX.
    pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CP) as SPC. unfold A_ASAN_MEMCPY_CP in SPC.
    callxA_sp (bv_unsigned sp + -96)
      (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (DST := pX') (SRC := pY) (n := 4 * i) (lo := lo)
                        (ds := u32s (firstn (Z.to_nat i) xs0)) (ss := u32s (firstn (Z.to_nat i) ys));
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by klia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMC; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact PUi
             | rewrite u32s_length, LI; clear - Hi; lia
             | rewrite u32s_length, LIy; clear - Hi; lia
             | eapply aobj_sub; [exact OPX| clear; lia| clear - Hi Hin; lia]
             | eapply aobj_sub; [exact OPY| clear; lia| clear - Hi; lia]
             | right; clear - SY2 Hi Hin; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]
             | left; clear - BC ALO LOS Hi Hin; lia
             | clear - C5 Hi; lia
             | eapply (blk_top47_sub asegs R HIA hc LBc LF mc); [exact HH| exact HIN| clear - Hi Hin; lia]
             | right; clear - Y47 Hi; lia
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear; lia| clear - Hi Hin; lia]
             | f_equal; clear; lia
             | clear - Hi NRY LOS SLO NEEDR NRA TOPc SPA SPR; lia
             | first [exact C24H | match goal with |- ?g => idtac "MEMCPYF-PRE-LEFT:" g end] ]).
    clear SPC.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPYF-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 pX' _ |- _ => rename H into HPA end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ hc LBc LF m5 |- _ => rename H into HH5 end.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    lx_post.
    all: first [exact C24H | match goal with |- ?g => idtac "LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L10351595562.3L41250020593.3L982998592.4  00000900B00MS2nY1i2HiS2nY1i2HiS1i2n'1E2I1". (* [comment removed for export] *)
  Lemma post_ok : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmo,$6.Pmo',$6.Ph',(0.$46.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))PLB',(1.$2.)Pi,$8.Pn',$8.PpX',$8.Pzs,(1.(3.&40.))Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(40.(20.+1.R12.)(20.R12.VnY,))P,(20.R13.R12.)P,(40.(20.VnX,R13.)(20.R13.(64.VnX,VnY,)))P,(44.(=.$8.R14.VnX,)(40.(=.$8.R14.R15.)(65.Vys,R15.)))P,(66.Vys,R16.)P,Pk,$67.Pw,(3.&40.)P,(=.(5.(3.&40.))(68.(3.&40.)R16.R2.)(69.(3.&40.)R1.))(=.$8.(24.(13.&40.R2.)(45.+2.+20.))=)P,(27.$46.R1:.)P,(1?.$46.R1;.Vlo,(13.&40.Vsp,))P,(6:.R1?.R1>.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R1=.)P,(=.$8.(1>.$46.VR,VHIA,R1?.)(1>.$46.VR,VHIA,Vh,))P,(=.$8.(6=.$46.VR,VHIA,R20.)(6=.$46.VR,VHIA,Vh,))P,(=.$8.(6>.$46.VR,VHIA,R21.)(6>.$46.VR,VHIA,Vh,))P,(:.$46.VR,VHIA,R22.R23.)P,Px,$8.P,(2:.$46.VR,VHIA,Vh,R1.)(2:.$46.VR,VHIA,R25.R2.)P,(20.(2?.$46.VR,VHIA,R24.)(2>.(2?.$46.VR,VHIA,Vh,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$46.VR,VHIA,R25.)(2>.(33.$46.VR,VHIA,Vh,)(34.Vd,)))P,(9.$46.VR,VHIA,R26.R24.VLF,R25.)P,(;.$46.R26.R25.(6<.VX,VsgY,R23.R22.(16.(3.&40.)(60.(3.&40.)(61.R24.)Vys,)R21.)VpadX,$19.))P,(6?.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)R26.(6<.VX,VsgY,R24.R23.(16.(3.&40.)(60.(3.&40.)(61.R25.)Vys,)R22.)VpadX,$19.))P,(44.(47.(48.$8.$8.)(49.$8.$8.R24.(1;.+4.R25.))(70.(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(71.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,R24.(1;.+4.R25.)))P,(44.(47.(48.$8.$8.)(49.$8.$8.R25.(1;.+4.R26.))(70.(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(<.(47.(48.$8.$8.)(49.$8.$8.R25.(1;.+4.R26.))VLB,)))(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R2=.(3;.(3<.(3=.Vra,Vsp,Vgp,Vtp,R24.R23.R22.Vs0,Vs1,(25.&40.=)R21.R20.R1?.R1>.R1=.R1<.R1;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1:.R19.R18.R17.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R2:.(3?.$46.))R2<.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros Hi Hin NB TR ZY ZS MI ST MF HP HT HS HFL HK HCS HV HFR HH MA MO FRA FRB.
    unfold mpi_binop_postA. do 14 eexists. exists m', mo', h', LB', (mkMPD X sgY n' pX' (firstn (Z.to_nat i) ys ++ zs) padX LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|]. split; [exact MO|].
    split; [cbn [mpd_blk md_own md_p md_n]; intros b [<-|[]]; exact FRA|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split.
    { split.
      { left. split; [reflexivity|]. split; [| exact NB]. unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_app.
        rewrite (limbs_val_zeros zs ZS). rewrite limbs_val_firstn; [rewrite Z.mul_0_r, Z.add_0_r; reflexivity| clear - Hi; lia| exact ZY]. }
      split; [reflexivity|]. split; [reflexivity|]. intros b [<-|[]]. exact FRB. }
    intros _. unfold copy_trim, mpd_abs. cbn [md_n md_limbs].
    destruct TR as [E|[E TI]]; [left; exact E|]. right. destruct TI as [I1|(w & Hw & NZ)]; [left; clear - E I1; lia| right].
    pose proof (limbs_val_nth_lower ys (Z.to_nat (i - 1)) w Hw NZ) as LOW. rewrite Z2Nat.id in LOW by (clear - Hi; lia). rewrite E. exact LOW.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L39789476001.111L59321100280.4  L59321100283.4  L8273516665.0   00000@00N00\00]S2sp1X1Y3sgY3sg'S2nY1l2EY4LENYS2nX1l2EX4LENXS". (* [comment removed for export] *)
  Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmo,$6.Pmo',$6.Ph',(0.$46.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))Pr,$8.Psg',$8.Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(27.$46.R11.)P,(1?.$46.R12.Vlo,(13.&40.Vsp,))P,(6:.R16.R15.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R14.)P,(=.$8.(1>.$46.VR,VHIA,R16.)(1>.$46.VR,VHIA,Vh,))P,(=.$8.(6=.$46.VR,VHIA,R17.)(6=.$46.VR,VHIA,Vh,))P,(=.$8.(6>.$46.VR,VHIA,R18.)(6>.$46.VR,VHIA,Vh,))P,(:.$46.VR,VHIA,R19.R1:.)P,Px,$8.P,(2:.$46.VR,VHIA,Vh,R1.)(2:.$46.VR,VHIA,R1<.R2.)P,(20.(2?.$46.VR,VHIA,R1;.)(2>.(2?.$46.VR,VHIA,Vh,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$46.VR,VHIA,R1<.)(2>.(33.$46.VR,VHIA,Vh,)(34.Vd,)))P,(9.$46.VR,VHIA,R1=.VLB,VLF,R1<.)P,(;.$46.R1=.VLB,(6<.VX,R1;.VnX,VpX,Vxs,VpadX,VownX,))P,(44.(=.$8.R1=.$73.)(40.(=.$8.R1=.=)(40.(=.$8.VnX,=)(=.$8.VnY,=))))(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R22.(3;.(3<.(3=.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(25.&40.R1>.)R19.R18.R17.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1?.(3?.$46.))R21.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA Hr.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    unfold mpi_binop_postA. do 14 eexists. exists m', mo', h', LB, (mkMPD X sg' nX pX xs padX ownX), r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [eapply mpd_out_ext; [apply mpd_out_refl; cbn [md_own]; exact NST| reflexivity| cbn [md_own]; exact NST| reflexivity]|].
    split; [cbn [mpd_blk md_own md_p md_n]; intros b Hb; left; exact Hb|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split; [| intros E; unfold copy_trim; cbn [md_n]; left; reflexivity].
    split; [| split; [reflexivity| split; [reflexivity| intros b Hb; left; exact Hb]]].
    destruct Hr as [->|(-> & EX & EY)]; [right; repeat split; reflexivity| left].
    split; [reflexivity|]. split; [| rewrite EX, EY; clear; lia].
    unfold mpd_val. cbn [md_sg md_limbs].
    assert (xs = []) as -> by (destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX EX; lia]).
    assert (ys = []) as -> by (destruct ys; [reflexivity| exfalso; cbn in LENY; clear - LENY EY; lia]).
    cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0@C17025492443.167C24172564923.170C57547066598.168C57547066598.169D26117128935.171D563003398.148  D62022255076.148K11451933403.170K14278493136.170K22605501532.168K22605501532.169K40494987808.170K6379668000.167 L11302909470.18 L11307674349.2  L11445796260.4  L14289919151.5  L14527203937.2  L17786296710.7  L18480872817.6  L2098519654.2   L21044925120.5  L21516681952.3  L21845917367.18 L21847519070.3  L21870408481.0  L22257015276.4  L22612200227.4  L2340205082.14  L24391971372.5  L27213746399.18 L27216806327.4  L29428324939.5  L3253508485.5   L35339770834.11 L35653441506.7  L35691325410.12 L38130778761.3  L40491771973.4  L41843607083.7  L42252534537.145L42252534548.60 L43031326719.11 L47907397394.12 L48288935062.2  L49659320776.5  L5175984652.2   L5376454999.5   L55196948550.11 L57628700040.10 L5917264152.4   L60098763854.3  L60124437587.5  L60262272144.5  L60459821746.2  L6384586821.2   L65284824489.11 L66151427842.16 L67032356243.8  L67676074422.2  L7832156787.7   L8265267294.0   N10156624428.168N13003184628.168N21806751459.168N37104593031.168N4592533095.168 O11652562492.170O17025492443.167O24172564923.170O32791873655.170O41046580696.167O57547066598.168O57547066598.169O61114386491.170P11451933403.170P22605501532.168P22605501532.169P5382893096.167 P5907420775.170 P6379668000.167 Q18771245053.171Q22252422803.171Q38248387216.171Q42252534537.151Q43879899724.17100000100200300400500U00o01001Z01[01\02C02D02[02\02]02^02d03<03E03F03G03P03e03f03g04304404504604F04G04Y04j05G05_06E06F06G06Z07a07b08@08`08g08m09309409509M09N09X09b09c09k09l0:E0:_0:`0:a0;50;60;U0<=0<_0=A0=`0=a0=b0=c0=d0=e0=f0=g0=h0=i0=j0=k0>W0?M0?N0?g0@F0@_0AV0B2FFFFFS1R3HIA1h2sp1X2pX2xs1Y2pY2ys3PYBS1R2sp1X2pX2xs1Y2pY2ys3PYBFS2nX2pX2xs2nY2pY2ys1i2Hi2Q34LENY2N13PYB2LRFFS2sp2nX2xs2nY2pY2ys2lo1i2Q54LENY3PYB2LRFS2sp2nX2nY1i2Hi3SPR3NRXFFFS2pX1iS2nX2xs2nY1i2Hi3Hin4LENXS2nX2pX1iFFS2nY1i2HiS1R2sp2lo3SLO3NRA3SPRFSS2pX2nY1i2HiFFFS1R3HIA1h2sp3TOPFS1R2lo3LOS3ALO3ACPS2nY2ys1i2Hi4LENYS2sp2nX2pX1Y2nY2lo1i2Hi2Q12Q4S1R3HIA1h2sp2lo3TOP4HTOPS1R2sp2nX2pX2nY2lo3LOS1i2Hi3Hin3ALO2BCFFS2nX2xs2nY1i2Hi3HinS1R5NEEDR2sp1X2nX2pX2xs1Y2pY2ys2lo3LOS3SLO1i3ALO3SPR2X02Y02B03PYB2H02LRFS2sp1X2nX2pX2nY2lo1i2Hi2Q23DSXS1R2sp2nX2pX2lo3LOS1i3Hin3ALO2BCS2sp2loS2nX1iS2nX1iFFS2sp2nX2pX2lo1i3Hin1x2HxFS1R2lo3LOSS2nX1i3HinFS2nX3NRXFS1R2nX2pX2lo3LOS1i3ALO2BCS2pX2r03P161q1r1H2H02q02H4FFS2nX2xs2nY1i2Hi4LENXSS2nX2pX2xs2pY2ys1i3PYB2LR3x151CS2nX2pX2xs2nY2pY2ys1i2Hi2N13PYB2LR3x151CS2sp2nX2xs2pY2ys2lo1i3PYB2LR3x151CS2sp2nX2xs2pY2ys2lo1i3PYB2LR3x151CS2nX2pX2xs2pY2ys1i3PYB2LR3x151CFFFFFFFFFFFS1R2sp2nX2pX2xs2pY2ys2lo3LOS1i3ALO2BC3PYB2LRS1R5NEEDR2sp2nX2pX2xs2pY2ys2lo3LOS3SLO1i3ALO2BC3PYB2LRFS2nX2pX2xs2pY2ys1i3PYB2LRS2nX2pX2xs2nY2pY2ys1i2Hi3PYB2LRS2nX2xs2pY2ys2lo1i3PYB2LRS1R5NEEDR2sp2nX2xs2pY2ys2lo3LOS3SLO1i3ALO3SPR3PYB2H02LRS2sp2nX2xs2pY2ys2lo1i3PYB2LR". (* [comment removed for export] *)
  Lemma memset_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,R16.)P,(40.(20.+1.R16.)(20.R16.VnY,))P,(20.R17.VnX,)P,(=.$>.VownX,$19.)P,(50.$46.R1:.VX,(5;.VpX,(25.&40.VsgY,)VnX,VpadX,))P,(5<.$46.R1;.VpX,Vxs,)P,(50.$46.R1<.VY,(5;.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4=.$46.R1=.VpY,(4>.Vys,))P,(<.(=.$>.VownY,$4:.))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1?.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R20.VY,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R21.VpY,(1;.+4.VnY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))VpX,)(20.(2>.VpX,(1;.+4.VnX,))VpY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(45.+2.+2?.))P,(44.(20.(2>.VY,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VY,))P,(44.(20.(2>.VX,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VX,))P,(44.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(44.(20.(2>.VY,+10.)Vlo,)(20.(13.&40.Vsp,)VY,))P,(50.$46.R29.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R27.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R2:.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R2;.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)Lms',$56.(57.(3.&40.)Lx5,(3.&40.)(57.(3.&40.)Lx6,(3.&40.)(57.(3.&40.)Lx7,(3.&40.)(57.(3.&40.)La1',(3.&40.)(57.(3.&40.)La2',(3.&40.)(57.(3.&40.)La3',(3.&40.)(57.(3.&40.)La4',(3.&40.)(57.(3.&40.)La5',(3.&40.)(57.(3.&40.)La6',(3.&40.)(57.(3.&40.)La7',(3.&40.)(57.(3.&40.)Lx28,(3.&40.)(57.(3.&40.)Lx29,(3.&40.)(57.(3.&40.)Lx30,(3.&40.)(57.(3.&40.)Lx31,(3.&40.)(57.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(40.(=.$56.R10.(3<.(3=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1.(3?.$46.)))(40.(5=.(51.(48.$8.$8.)(49.$8.$8.VpX,(2>.VpX,(1;.+4.VnX,)))(51.(48.$8.$8.)(49.$8.$8.Vlo,(13.&40.Vsp,))(54.(48.$8.$8.))))R3<.R1.)(40.(5>.$46.R3<.R1.)(40.(27.$46.R1.)(40.(5<.$46.R1.VpX,(16.(3.&40.)(60.(3.&40.)(61.R3;.)Vys,)(74.(3.&40.)(25.&40.=)(61.(22.VnX,R3;.)))))(40.(1?.$46.R1.Vlo,(13.&40.Vsp,))(9.$46.VR,VHIA,Vh,VLB,VLF,R1.))))))))))))))))))))))(3<.(3=.R29.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R28.R27.R26.(25.&40.(1;.+4.R2;.))R25.(25.&40.VX,)(25.&40.VY,)(25.&40.VnX,)R24.R23.R22.R21.R20.(25.&40.R2;.)R1?.R1>.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R1=.R1<.R1;.Vs10,Vs11,R1:.R19.R18.R17.)VF,(25.&40.+9;>><.)Vfc,(3>.(3.&40.))R2<.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH Hi Hin EO HXS HXL HYS PBY OYN OX OY OPY Q3 Q5 Y47 Q1 Q2 DSX Q4 FR ST MI. basic_facts h LB mc HH TOP.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    flat constr:(MAX) 2%nat. intros FLt7 _. flat constr:(FLt7) 2%nat. flclear FLt7. intros _ FLt8. flat constr:(FLt8) 5%nat. flclear FLt8. intros _ _ _ _ HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
    flat constr:(HOWN) 4%nat. flclear HOWN. intros N1 HIN P16 _.
    flat constr:((hm_apart asegs R HIA h LB LF mc HH)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    unfold mpi_cells in HXS, HYS.
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (munch_refl [(pX + 4 * i, pX + 4 * nX); (lo, bv_unsigned sp)] mc) as MU'.
    pose proof (hm_aobj_block asegs R HIA h LB LF mc pX (4 * nX) HH HIN) as OPX.
    (* [comment removed for export] *)
    lx_hide MU'.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x068258] [] 40%N). lx_tree.
    all: lx_unhide; lx_same_mem; lx_gc; try clear OQH.
    (* [comment removed for export] *)
    pose proof HXL as PU. rewrite <- (firstn_skipn (Z.to_nat i) xs) in PU. apply u32arr_app in PU. flat constr:(PU) 2%nat. flclear PU. intros PUi PUr.
    rewrite firstn_length_le in PUr by (clear - Hi Hin LENX; lia). replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) in PUr by (clear - Hi; lia).
    assert (LR : length (skipn (Z.to_nat i) xs) = Z.to_nat (nX - i)) by (rewrite length_skipn; clear - Hi Hin LENX; lia).
    pose proof (conj HXS I) as HXS0. pose proof (conj HYS I) as HYS0. pose proof (conj HXL I) as HXL0. clear HXS HYS.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_CP) as SPM. unfold A_ASAN_MEMSET_CP in SPM.
    callxA_sp (bv_unsigned sp + -96)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := pX + 4 * i) (v := 0) (n := 4 * (nX - i)) (lo := lo)
                        (ds := u32s (skipn (Z.to_nat i) xs));
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by klia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact PUr
             | rewrite u32s_length, LR; clear - Hi Hin; lia
             | eapply aobj_sub; [exact OPX| clear - Hi; lia| clear - Hi Hin; lia]
             | clear; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
             | left; clear - BC ALO LOS Hi Hin; lia
             | eapply (blk_top47_sub asegs R HIA h LB LF mc); [exact HH| exact HIN| clear - Hi Hin; lia]
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear - Hi; lia| clear - Hi Hin; lia]
             | f_equal; clear; lia
             | clear - Hi Hin NRX LOS SLO NEEDR NRA TOP SPA SPR; lia
             | first [exact C24H | match goal with |- ?g => idtac "MEMSETP-PRE-LEFT:" g end] ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSETP-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 (pX + 4 * i) _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : HM asegs R HIA h LB LF m5 |- _ => rename H into HH5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    (* [comment removed for export] *)
    try clear PUi. flat constr:(HXS0) 2%nat. flclear HXS0. intros HXS _. flat constr:(HYS0) 2%nat. flclear HYS0. intros HYS _. flat constr:(HXL0) 2%nat. flclear HXL0. intros HXL _.
    pose proof (rw_cells_transport asegs _ mc m5 _ _ HXS MU' WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Q2 DSX Hi Hin; lia)) as HXS5.
    pose proof (rw_cells_transport asegs _ mc m5 _ _ HYS MU' WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Q1 Q4 Hi Hin; lia)) as HYS5.
    clear HXS HYS.
    rewrite <- (firstn_skipn (Z.to_nat i) xs) in HXL. apply u32arr_app in HXL. flat constr:(HXL) 2%nat. flclear HXL. intros HXL _.
    pose proof (u32arr_transport asegs _ mc m5 _ _ HXL MU' WM) as PUi.
    rewrite firstn_length_le in PUi by (clear - Hi Hin LENX; lia).
    specialize (PUi ltac:(cbn [disjoint_from]; clear - BC ALO LOS Hi Hin; lia)). clear HXL MU'.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x9c0c4] [] 20%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    eapply evtA_mono.
    { eapply (final_walk h LB m5 i nX pX (firstn (Z.to_nat i) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nX - i))));
        try eassumption.
      1: clear - NRX; lia.
      1: clear - P16; Z.div_mod_to_equations; lia.
      1: { apply u32arr_app. split; [exact PUi|]. rewrite firstn_length_le by (clear - Hi Hin LENX; lia).
           replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) by (clear - Hi; lia).
           replace (Z.to_nat (4 * (nX - i))) with (4 * Z.to_nat (nX - i))%nat in HPZ by (clear - Hi Hin; lia).
           apply (rw_cells_of_u8arr asegs) in HPZ.
           eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
      rewrite length_app, firstn_length_le, repeat_length by (clear - Hi Hin LENX; lia); clear - Hi Hin LENX; lia. }
    cbv beta. intros ms' PO. flat constr:(PO) 22%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 ST9 HH9.
    do 15 eexists. split; [exact E9|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU9]; clear - Hi Hin; intros x Hx; cbn [outside] in *; lia]|].
    split; [eapply wmono_trans; [exact WM| exact WM9]|].
    split; [exact MI9|].
    split; [| split; [exact ST9| exact HH9]].
    apply u32arr_app. split.
    - eapply (u32arr_of_cells asegs); [| reflexivity]. apply (rw_cells_of_u8arr asegs) in HA9. rewrite u32s_length, firstn_length_le in HA9 by (clear - Hi LENY; lia).
      exact HA9.
    - rewrite firstn_length_le by (clear - Hi LENY; lia). replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) by (clear - Hi; lia).
      replace (Z.to_nat (4 * (nX - i))) with (4 * Z.to_nat (nX - i))%nat in HPZ by (clear - Hi Hin; lia).
      apply (rw_cells_of_u8arr asegs) in HPZ.
      eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
      eapply (rw_cells_transport asegs _ m5 m9); [exact HPZ| exact MU9| exact WM9|].
      rewrite repeat_length. cbn [disjoint_from cells_size csize Nat.add]. clear - Hi Hin BC ALO LOS; lia.
    all: match goal with |- ?g => idtac "MP-LEFT2:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D24996680996.151D51169044392.150D5485126037.150 D62022258533.151L18160155068.4  L29428324939.5  L35653441506.7  L39953140637.9  L40254489227.4  L50790580594.6  L57628700040.7  L60098763854.3  00000M00a01501K01X01j02D02X02[03203D03NS1R3HIA2sp1X2xs1Y2ys2hc1A3xs0S2sp1X2xs1Y2ys1A3xs0S2sp1X2xs1Y2ys1A3xs0S1R2sp1X2xs1Y2ys1A3xs0S2nY1i2Hi3NRYS1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPS2sp1X2lo1i1A3DSX2XAS1iS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2lo1i1A1x2HxS1R2lo3LOS". (* [comment removed for export] *)
  Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Phc,(0.$46.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.PA,$8.Ppold,$8.Pxs0,(1.(3.&40.))Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs4,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,R18.R17.VLF,R16.)P,(=.$8.(1>.$46.VR,VHIA,R19.)(1>.$46.VR,VHIA,Vh,))P,(20.(13.&40.Vsp,)(1>.$46.VR,VHIA,R1:.))P,(40.(20.+1.R18.)(20.R18.VnY,))P,(40.(20.=R18.)(41.R18.(45.+2.+40.)))P,(40.(20.=R18.)(41.R18.(45.+2.+40.)))P,(50.$46.R1<.VX,(51.$52.(53.(25.&40.R19.))(51.$52.(75.(25.&40.VsgY,))(51.$52.(75.(25.&40.VnX,))(51.$52.(76.VpadX,)(54.$52.))))))P,(77.(15.VR,)(16.$2.R1>.(17.VLF,))(13.&40.Vsp,)(1>.$46.VR,VHIA,Vh,)VX,+10.)P,(47.(48.$8.$8.)(49.$8.$8.R1<.(1;.+4.R1=.))R1?.)P,(=.$8.(24.R1=.+4.)=)P,(5<.$46.R20.R1>.R1<.)P,(=.$8.(42.(43.(3.&40.)R1=.))R20.)P,(50.$46.R22.VY,(5;.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4=.$46.R23.VpY,(4>.Vys,))P,(<.(=.$>.VownY,$4:.))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R27.)R25.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R28.)R26.VY,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R29.)R27.VpY,(1;.+4.VnY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))R26.)(20.(2>.R26.(1;.+4.R27.))VpY,))P,(44.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(45.+2.+2?.))P,(44.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(44.(20.(2>.VY,+10.)R2:.)(20.(2>.R2:.(1;.+4.R2;.))VY,))P,(44.(20.(2>.VX,+10.)R2;.)(20.(2>.R2;.(1;.+4.R2<.))VX,))P,(44.(20.(2>.VX,+10.)VpY,)(20.(2>.VpY,(1;.+4.VnY,))VX,))P,(50.$46.R2?.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R2:.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R30.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R31.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,R34.)Lms',$56.(57.(3.&40.)Lx5,(3.&40.)(57.(3.&40.)Lx6,(3.&40.)(57.(3.&40.)Lx7,(3.&40.)(57.(3.&40.)La1',(3.&40.)(57.(3.&40.)La2',(3.&40.)(57.(3.&40.)La3',(3.&40.)(57.(3.&40.)La4',(3.&40.)(57.(3.&40.)La5',(3.&40.)(57.(3.&40.)La6',(3.&40.)(57.(3.&40.)La7',(3.&40.)(57.(3.&40.)Lx28,(3.&40.)(57.(3.&40.)Lx29,(3.&40.)(57.(3.&40.)Lx30,(3.&40.)(57.(3.&40.)Lx31,(3.&40.)(57.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(40.(=.$56.R10.(3<.(3=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1.(3?.$46.)))(40.(5=.(51.(48.$8.$8.)(49.$8.$8.R40.(2>.R40.(1;.+4.R41.)))(51.(48.$8.$8.)(49.$8.$8.Vlo,(13.&40.Vsp,))(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))))R42.R1.)(40.(5>.$46.R42.R1.)(40.(27.$46.R1.)(40.(5?.$46.R1.R40.(4>.(60.(3.&40.)(61.R41.)Vys,)))(40.(50.$46.R1.VX,(5;.R40.(25.&40.VsgY,)R41.VpadX,))(40.(1?.$46.R1.Vlo,(13.&40.Vsp,))(9.$46.VR,VHIA,R44.R43.VLF,R1.)))))))))))))))))))))))(3<.(3=.R2<.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R2;.R2:.R29.(25.&40.(1;.+4.R31.))(25.&40.(2>.VX,+:.))(25.&40.VX,)R28.(25.&40.VY,)R27.R26.R25.R24.R23.(25.&40.R31.)(25.&40.R30.)R22.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))(25.&40.(2>.(62.(29.VR,))(63.(2>.VX,+:.)+3.)))R21.(25.&40.(2>.(62.(29.VR,))(63.VX,+3.)))Vs10,Vs11,R20.R1?.R1>.R1=.)VF,(25.&40.+9<0:<.)Vfc,(3>.(3.&40.))R32.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc Hi AB PB HXS CW HIN A4 HAL LL0 HYS PBY OYN OX OY OPY SY2 Q5 Y47 DSX Q1 XA XPY FR ST MI. basic_facts hc LBc mc HH TOPc.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    flat constr:((hm_apart asegs R HIA hc LBc LF mc HH)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CW]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HYS.
    pose proof (munch_refl [(A, A + 4 * i); (lo, bv_unsigned sp); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x9c0c4] [(0x9c0b0, DJoin)] 40%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc; lx_rn_munch MU; lx_rn_wmono WM.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    eapply evtA_mono.
    { eapply (final_walk hc LBc m4 i i A xs0); try eassumption.
      all: clear - Hi NRY; lia. }
    cbv beta. intros ms' PO. flat constr:(PO) 22%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 ST9 HH9.
    do 15 eexists. split; [exact E9|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU9]; clear; intros x Hx; cbn [outside] in *; lia]|].
    split; [eapply wmono_trans; [exact WM| exact WM9]|].
    split; [exact MI9|]. split; [exact HA9|].
    split; [| split; [exact ST9| exact HH9]].
    unfold mpi_cells. eapply (rw_cells_transport asegs _ m4 m9); [exact HXS| exact MU9| exact WM9|].
    cbn [disjoint_from cells_size csize Nat.add]. clear - XA DSX Hi; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L1164172544.1 L26892418956.1L35666020638.8L37714553091.1L41751294858.3L50790809970.7L57124062131.2L59308588187.5L60280819195.4L62018535662.1L64900791963.400000300700R00U00_01601;01J01W01Z01fS1XS2spS1R3HIA2sp2lo2hh4TOPh5HTOPhS1AS1R3HIA2hhS1R5NEEDR2sp2lo3LOS3SLOS1A1kS2sp2lo2Hl1x2HxS1k2kb2Hk3HkbS1RS1A1k2kb3Hkb". (* [comment removed for export] *)
  Lemma presA_tail3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Phh,(0.$46.VR,VHIA,)PLBh,(1.$2.)PA,$8.Pk,$8.Pkb,$8.Pmm,P,(3.&40.)(5.(3.&8.))PmX,P,(3.&40.)(5.(3.&8.))Pm1,P,(3.&40.)(5.(3.&8.))Pm2,P,(3.&40.)(5.(3.&8.))P,(9.$46.VR,VHIA,R9.R8.VLF,R4.)P,Pb,$2.P,(47.$2.R1.(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(47.$2.R2.R;.)P,(47.(48.$8.$8.)(49.$8.$8.R9.R7.)R:.)P,(71.VR,VLB,VLF,R:.R8.)P,(41.=R:.)P,(20.R;.R:.)P,(20.(13.&40.Vsp,)(1>.$46.VR,VHIA,R?.))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,R10.)R:.VX,+10.)P,(5=.(51.(48.$8.$8.)(49.$8.$8.R?.(2>.R?.R>.))(51.(48.$8.$8.)(49.$8.$8.Vlo,(13.&40.Vsp,))(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))))R:.R9.)P,(5>.$46.R;.R:.)(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,R13.)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))R<.R;.)")
(* [comment removed for export] *).
  Proof.
    intros hh LBh A k kb mm mX m1 m2 HH HI HIN HFRA Hk Hkb TOPh OX MU WM.
    pose proof (hcs_ok asegs R HIA hh) as CSOK. pose proof (hm_top asegs R HIA hh LBh LF mm HH) as HTOPh. pose proof (hcs_stack asegs R HIA hh) as SCS0.
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hm_aobj_block asegs R HIA hh LBh LF mm A kb HH HIN) as OA.
    apply (munch_weaken _ [(lo, bv_unsigned sp); (A, A + k); (X, X + 16)]) in MU; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
    eapply (presA_drop_fresh asegs R HIA hh (mpd_keep LB dX) LF [(X, X + 16)] A k m1 m2 (bv_unsigned sp));
      [| apply fresh_apart_keep; eapply fresh_apart_sub; [exact HFRA| clear - Hk Hkb; lia]| clear - ALO LOS SLO NEEDR; lia].
    eapply (presA_weaken asegs R LBh (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
              (hstkhi asegs R HIA hh) (hstkhi asegs R HIA hh) [(A, A + k); (X, X + 16)]);
      [| exact HI| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
    eapply (presA_drop_below asegs R HIA hh LBh LF _ lo (bv_unsigned sp) mm m1 m2); [exact HH| | clear; lia| exact LOS].
    eapply (presA_of_munch asegs R LBh LF _ _ _ _ m1 m2 (hcs asegs R HIA hh) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
    unfold w_client. apply Forall_cons; [cbn [fst snd]|].
    { destruct (Z_lt_le_dec lo (bv_unsigned sp)) as [Hl|Hl].
      - eapply crange_sub; [exact SCS0| exact LOS| clear - TOPh HTOPh Hl; lia].
      - intros x Hx. exfalso. clear - Hx Hl. lia. }
    apply Forall_cons; [cbn [fst snd]; replace (A + k - A) with k by (clear; lia); eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - Hkb; lia]|].
    apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Grow.
    Variables (mo : Model) (m1 : mem) (i : Z) (jk : list (bv 8)).
    Hypothesis HH1 : HM asegs R HIA h LB LF m1.
    Hypothesis Hi : 1 <= i <= nY.
    Hypothesis Hin : nX < i.
    Hypothesis ZY : zeros_above ys i.
    Hypothesis TI : trim_i ys i.
    Hypothesis HXS1 : rw_cells asegs m1 X [C8 (Z_to_bv 64 pX); C2 (Z_to_bv 64 sgY); C2 (Z_to_bv 64 nX); C4 padX].
    Hypothesis PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)].
    Hypothesis HYS1 : rw_cells asegs m1 Y [C8 (Z_to_bv 64 pY); C2 (Z_to_bv 64 sgY); C2 (Z_to_bv 64 nY); C4 padY].
    Hypothesis PBY1 : bytes_at asegs m1 pY (u32s ys).
    Hypothesis OYN : ownY <> LNull.
    Hypothesis OX1 : aobj asegs AL CS m1 X 16.
    Hypothesis OY1 : aobj asegs AL CS m1 Y 16.
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -96) (FRAME jk).
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -96).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis HP1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,Vm1,)")
(* [comment removed for export] *).
    Hypothesis BUD : havol asegs R HIA h + copy_PHI dY <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + copy_FR d <= FR_MAX.
    (* [comment removed for export] *)
    Hypothesis Q1 : X + 16 <= pY \/ pY + 4 * nY <= X.
    Hypothesis Q2 : ownX = LHeap -> Y + 16 <= pX \/ pX + 4 * nX <= Y.
    Hypothesis Q3 : ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX.
    Hypothesis Q4 : Y + 16 <= lo \/ bv_unsigned sp <= Y.
    Hypothesis Q5 : pY + 4 * nY <= lo \/ bv_unsigned sp <= pY.
    Hypothesis Y47 : pY + 4 * nY + 8 <= 2^47.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis DXP : ownX = LHeap -> X + 16 <= pX \/ pX + 4 * nX <= X.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis PYfresh : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PA,$8.Pk,$8.P,(71.VR,VLB,VLF,R2.R1.)P,(44.(20.(2>.R3.R2.)(78.(15.VR,)))(20.(79.(15.VR,))R3.))P,(41.=R3.)(44.(20.(2>.VpY,(1;.+4.VnY,))R5.)(20.(2>.R5.R4.)VpY,))")
(* [comment removed for export] *).
    Hypothesis Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y.

    (* [comment removed for export] *)
    Ltac calloc_call cntv :=
      replace (Z_to_bv 64 431236) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity);
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := cntv) (sz := 4) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ eapply uw_obj_uwc; [exact XUW | clear; lia]
              | (apply uwc_data; [exact (uw_obj_nonneg _ _ _ _ XUW)| pose proof (alloc_ceiling_val R) as ACVu; pose proof (art_lo asegs R HIA) as ALOu; lazymatch goal with NRq : 0 <= nY <= _ |- _ => rewrite unsigned_lit by (clear - Hi NRq; lia); clear - Hi NRq ALOu ACVu; lia end])
              | clear - SPA; lia
              | unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; cbn [md_n] in *; qlia
              | (intros _; first [ clear - C24H; unfold C24_COPY_c in C24H; lia | match goal with HS : forall b, In b ?L -> In b LB, HHr : HM _ _ _ _ ?L _ _ |- _ => let NDq := fresh "NDq" in let CI := fresh "CI" in pose proof (HND _ _ _ _ HHr) as NDq; apply NoDup_map_inv in NDq; pose proof (cnt24_incl _ _ NDq HS) as CI; clear - CI C24H; unfold C24_COPY_c in C24H; lia end ])   (* [comment removed for export] *)
              | first [exact C24H | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end] ]
      | ].

    (* [comment removed for export] *)
    Ltac free_limbs_call hh LBx HIN PCHx :=
      let SPZ := fresh "SPZ" in
      pose proof ZF as SPZ; unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ;
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply SPZ with (h := hh) (LB := LBx) (LF := LF) (buf := pX) (len := nX * 4) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ right; split; [right; replace (nX * 4) with (4 * nX) by (clear; lia); exact HIN | exact PCHx]
              | eapply uw_obj_uwc; [exact XUW | clear; lia]
              | (apply uwc_data; [exact (uw_obj_nonneg _ _ _ _ XUW)| pose proof (alloc_ceiling_val R) as ACVu; pose proof (art_lo asegs R HIA) as ALOu; lazymatch goal with NRq : 0 <= nY <= _ |- _ => rewrite unsigned_lit by (clear - Hi NRq; lia); clear - Hi NRq ALOu ACVu; lia end])
              | clear - SPA; lia
              | unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; cbn [md_n] in *; qlia
              | first [exact C24H | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end] ]
      | clear SPZ ].

    Local Ltac2 Set LiaOrc.tbl := fun () => "03n0@C17025492443.238C31740276271.239D16049893661.240D16945601739.254D16945998672.187D16958154085.188D16958154085.255D16958154085.256D16960236374.255D21363900101.255D21364017502.187D28291287678.253D28291287678.255D28291287678.256D28291287678.257D28291287678.258D29803878622.254D29805965123.251D29805965123.253D32954576255.253D32965073634.254D37703914153.251D37703914153.253D37710325044.254D37730786031.251D38983586459.255D39230898703.255D39230898703.256D39233014844.255D39235206049.254D43864128417.251D43864128417.255D48001522891.251D48001522891.255D49468338534.187D49468338534.189D49468338534.190D50796826103.240D61560670416.255D63595235433.240D64336185449.240D8543679517.255 K1227220751.239 K22413380088.239K23294715799.239K24664242720.239K25897202343.239K40494987808.239K5848377239.239 K61205767951.239K6379668000.238 L10358394922.3  L11404239431.12 L1233234968.4   L12694533441.2  L12750819336.13 L12755534717.11 L14350476896.7  L15682647203.7  L16256253080.7  L1649577667.2   L1675511041.5   L17585880332.15 L17852819865.6  L18568380981.2  L19061415402.1  L20813968635.12 L21563705165.3  L21845606316.4  L21860237213.19 L22401653661.3  L2295337761.0   L23301287040.3  L23926814669.1  L24391384886.2  L24432892232.7  L24676493381.3  L2486882617.4   L25033921014.12 L25436154562.19 L25890634160.3  L2649968878.8   L27214188996.5  L27711224602.12 L2851373008.7   L28553555646.2  L28655862141.5  L28813938827.14 L29428324939.5  L29801895145.8  L30990067275.3  L31465033794.6  L31532528036.5  L31532528036.7  L31968595033.5  L32250862063.4  L3253508485.5   L32960714453.7  L3309110695.3   L33799276397.1  L33816268745.3  L34171955900.9  L34209806743.184L34423643938.4  L35653441506.7  L35655538624.7  L35788255425.4  L36440793763.3  L36457694076.4  L37591067891.5  L37714553091.1  L37762309942.260L38948636245.0  L39172636981.0  L39280637297.0  L40249794171.1  L40281191306.3  L40491771973.4  L40823592413.2  L41114660167.2  L41841290036.4  L41858767142.4  L42592489632.2  L42865824567.3  L43646462316.7  L44697879740.4  L45026238780.2  L46380960401.6  L47107138245.3  L47858894730.7  L47860712607.10 L48132467214.7  L48288935062.2  L49659320776.5  L50440626417.3  L50677039807.13 L50677039807.14 L50680843071.5  L50682938047.4  L50683331001.14 L51622416288.9  L52476506375.13 L52957736619.3  L53018262813.17 L53018625706.18 L54232820919.18 L54271395752.2  L5479049730.1   L56121906081.7  L57737878429.4  L58307024458.1  L5841841280.4   L59308587409.7  L59308587542.6  L59308661072.10 L59308668813.4  L59308742867.3  L59310648656.8  L59310679242.5  L59310758218.10 L59335885566.2  L60098763854.3  L60549562490.3  L60684097692.2  L60858800200.1  L61211782168.3  L62018535662.1  L62622656665.46 L62624471726.46 L62624471726.53 L62624751897.46 L62624995887.53 L62625145375.53 L62627242265.44 L62627242265.52 L63070224179.5  L63074471475.19 L63799194974.10 L6384586821.2   L64194470200.2  L64372451842.1  L64626866417.15 L64633158647.15 L64834004734.3  L64893239004.7  L64966926188.10 L64968776825.7  L656136024.1    L66151427842.16 L66151427842.17 L66256213271.3  L66610753222.8  L68469196698.2  L9223833819.5   L9596616833.4   N34515723252.239N4182430466.239 N64719295348.239N8534856257.239 N8783436488.239 O10066905207.239O10068491663.239O17025492443.238O24356205430.239O26871806789.239O31740276271.239O32791873655.239O39322336069.239O48499521681.239O49587672251.238O53059091855.239O57399310481.239O65674534437.239P24664243462.187P25897202343.239P37585053668.239P40019312322.255P44704452523.238P50446642150.239P50688965474.253P51151736818.250P51151736818.255P51152140393.185P51152140393.187P53225320550.185P57742789112.239P6379668000.238 Q10353739506.153Q17377103875.153Q21563673726.231Q21845963932.153Q24433119981.253Q24439301488.250Q24439301488.251Q24439427819.185Q27213699828.153Q34423215121.231Q34555067928.240Q34841007899.153Q37703787028.240Q38248387216.240Q41836510700.153Q42250421143.171Q42250421143.249Q42252534531.220Q42252699701.153Q42252699702.231Q43879899724.240Q46954851733.231Q49589754978.231Q54967815506.153Q63072781617.231Q68332217306.186Q68332344385.25200000100200300400500600700800900V00k01O02302402X02Y02Z02[02\02]02^03;03X04504T05D05E05F05G05H05I05J05K05L05h06D06E07B08:08;08<08=08g09A09h0:A0:B0:a0;O0<60<70<80<J0<K0<L0<M0<N0<`0=90=O0=W0=i0=j0=k0=l0>00>K0>L0>M0>b0>c0>d0>e0>h0>i0?@0?A0?N0?e0@@0@A0@B0@C0@D0@Y0@`0@a0AP0Ab0Ac0Am0An0B:0BI0BV0Be0C60CJ0CK0CN0CW0D20DG0DH0D`0E;0EH0ET0Ea0Eb0Ee0FB0FC0FD0FE0FH0FQ0FR0FV0F^0F_0Fm0G50G>0GP0GQ0GZ0G[0Gg0Gh0H80HS0HZ0Hd0He0Hf0Hg0Hh0Hi0Hj0I?0In0J80J90J:0J;0JB0JE0J^0J_0Jc0Jd0K90KI0Ka0Ko0L90LS0Lb0M;0MB0ML0MT0MU0MY0MZ0M]0M^0M_0M`0Ma0Mb0Mc0Md0Me0Mf0N80NW0NX0N_0Nc0Nd0Ne0Nn0OI0O^0O_0Ob0PB0PC0PL0Pd0Pk0Q;0QI0Qc0R=0Ro0S00S10S20S30S40S50S60S70S80S90S:0S;0S<0S=0S>0SW0SX0TA0U00UR0VH0W70WJ0W]0X00XC0X\0YH0YI0Y_0ZA0Ze0[C0[g0\K0\o0]S0^00^J0^c0_C0_S0_d0_e0`S0aA0ao0b]0cK0c_0dH0dm0eG0ef0eg0ehFFFFFFFFFS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2xs1Y2pY2ys3PYBS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x282HxS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x282HxFS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x282HxFFFFFFS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys1i3PYB2P01AS2sp1X2nX2pX2xs1Y2pY2ys3SPR2X02Y03PYB2P01A2A02N1FFFFFFFFS2sp1X2xs1Y2pY2ys3PYB3x142HxS2sp1X2xs1Y2pY2ys3PYB3x142HxFS1R5NEEDR2sp1X2pX2xs1Y2pY2ys2lo3LOS3SLO3SPR2X02Y03PYB2P01A2A0S2sp1X2nX2pX2xs1Y2pY2ys1i3Hin3SPR2X04LENX2Y03PYB2P01A2A0FFFS2nX2pX2xs2pY2ys1i3Hin4LENX3PYB2P01A2KP2PAS2sp1X2xs2pY2ys2lo3DSX3PYBS2nX2pX2xs1Y2pY2ys1i3Hin3PYB2P01A2YA2KPS2sp2xs1Y2pY2ys2lo2Q43PYBFS2sp2xs2nY2pY2ys2lo2Q54LENY3PYBS2nX2pX2xs2nY2pY2ys1i3Hin4LENY3PYB2P01A3YPA2KPS1X2nX2pX2xs2pY2ys1i3Hin3PYB2P01A2XA2KPFFS2nX2lo1i3Hin1A2ASFFFFS2nX2pX1i3Hin1A2PAS1R2nY1i2Hi3NRY4ACVu4ALOuS1R3HIA1h1d2D02h24HFR2S2nX3NRXS2nX2xs1i3Hin4LENXFFFS2nXS2sp1X2nX2lo1i3Hin3DSX1A2XAFFS1R2sp2lo3SLO3NRA3SPRFSFS1iFS1R5NEEDR2sp2lo3LOS3SLOFS2nY1i2Hi3NRYS1R2nX2pX2lo3LOS3ALO2PCS2sp2nX2nY1i2Hi3Hin3SPR3NRYFFFFS1R2lo3LOS1i3ALO1A2ACS2nX2pXFS1R5NEEDR2sp2nY2lo3LOS3SLO1i2Hi3ALO3SPR1A2A02ACS1R2lo3LOS3ALO3ACPFS2nX1i3HinFS2nX1i3Hin1AS2nX2xs1i3Hin1AS2sp1Y1a2Ha1QS2nX2pX2xs4LENXS2nY2ys1i2Hi4LENYS2nX2xs1i3Hin4LENX1AFS1iS2nY1i2HiS1R3HIA1h1d2h24HFR22h44HFR4S2sp1X2xs1Y2pY2ys3PYBFS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA2sp2lo2h24TOP25HTOP2S2nY1i2Hi3NRYS2nX2xs4LENXS2nY1i2Hi3NRYFS1AS2sp1X2pX2xs1Y2pY2ys3PYB2P01ASSSS1iS1R3HIA1hFS2spS2sp3SPAFS2nX2xs4LENX1AS2pX3H14S2nY1i2HiS2nX2xs1i3Hin4LENXFS2LB4C24HFS2nX2xs4LENXFS1R2nX2pX2PC3ACVS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp2loS2nX1i3HinFFFFFFS2nX2pX1i3Hin1A2N12PAS1R5NEEDR2sp2nX2pX2lo3LOS3SLO3ALO3SPR3NRX2P02PCS2pX2P02H9FFFS2nX2pXS1XS1R2nY1i2Hi3NRY4ACVu4ALOuFS2nXFS2nX2pX1Y3Q2'1a2Ha2HrS1Y2lo1a2Ha1Q2HsS2nX2pX1i3Hin1A2N12PA2E1S2nX1l4LENX2EnS2pX2KP2B0S2nX2pX2nY2pY2N13Q3'1E3NY1S2nY1i2Hi1A3HH'S2nX2pX1i3Hin1A2N12PA3E1'S2pX2B0S1R2lo3LOSS2nX1i1AFS2spFS1RFFFFFFFFFS1R3HIA2sp2h24TOP2S1R3HIA1h2nY1i2Hi2h23HV22h43HV4FS1R3ACPS2pXFFS2nY1i2HiS1R5NEEDR2sp2lo3LOS3SLO3ALOS1R2nX1i3Hin1A2AC3ACVFS1XS2pX2r03P161q1r1H2H02q02H41A3A16FS2nY1i2HiS1R3HIA1h2nY1i2Hi2h23HV2S2nX2N1S2nX2nY1i2Hi3HinS2nX2xs4LENX1AS2sp2xs2pY2ys2lo3PYB3x261CS2sp2xs2pY2ys2lo3PYB3x261CS1R2sp2nX2xs2pY2ys2lo3LOS1i3Hin3PYB1A3H152N13x261CFFFFFFFFFFFFFFFS2sp2xs1Y2pY2ys2lo2Q43PYBFS1R2sp2nX2xs2pY2ys2lo3LOS1i3Hin3PYB1A3H15S1R5NEEDR2sp1X2xs1Y2pY2ys2lo3NEQ3SLO2Q43DSX3PYBS2sp2nX2xs2pY2ys2lo1i3Hin3PYB1A2ASS1R5NEEDR2sp2nX2xs2pY2ys2lo3LOS3SLO1i3Hin3ALO3PYB1A2ACS1R5NEEDR2sp1X2xs1Y2pY2ys2lo3NEQ3SLO2Q43DSX3PYBS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp2xs1Y2pY2ys2lo2Q43PYBS1R2sp2nX2pX2xs2pY2ys2lo3LOS3ALO4LENX3PYB2PCFS2xs2nY2pY2ys1i2Hi3PYBS1R3HIA1h2xs2nY2pY2ys1i2Hi3BUD3PYBS2nX2xs2nY2pY2ys1i2Hi3Hin3NRY3PYB2N1S1R2sp2xs2pY2ys2lo3SLO3NRM3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R3HIA1h2sp2xs2pY2ys3TOP3PYBS1R2sp2xs2pY2ys2lo3SLO3PYBS2nX2xs2pY2ys1i3Hin3PYB1AS1R3HIA1h2xs2pY2ys1d4BUDF2D03PYBS2xs2pY2ys3PYB1AS2xs2pY2ys2lo3PYBFS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3SPR3PYB1HS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3SPR3PYB1HS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3SPR3PYB1HS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3SPR3PYB1HS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3SPR3PYB1HS2sp2xs2pY2ys2lo3PYBS1R3HIA1h2xs2nY2pY2ys1i2Hi3BUD3PYB2h23HV2S1R3HIA1h2xs2pY2ys1d4BUDF3PYB2h24HFR2S2xs2nY2pY2ys1i2Hi3NRY3PYBS1R3HIA2sp2xs2pY2ys3PYB2h24TOP2FF". (* [comment removed for export] *)
    Lemma grow_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)(7:.$46.(7;.$46.VR,VHIA,Vh,Vmo,)(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(3<.(3=.R11.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R10.R?.R>.(25.&40.(1;.+4.Vi,))(25.&40.(2>.VX,+:.))(25.&40.VX,)(25.&40.VY,)R=.R<.(25.&40.(22.Vi,+1.))R;.R:.R9.(25.&40.Vi,)R8.R7.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))(25.&40.(2>.(62.(29.VR,))(63.(2>.VX,+:.)+3.)))R6.R5.Vs10,Vs11,R4.R3.R2.R1.)VF,(25.&40.+9<014.)Vfc,(3>.(3.&40.))Vm1,(3?.$46.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. basic_facts h LB m1 HH1 TOP. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
      flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
      pose proof (HND _ _ _ _ HH1) as ND.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      flat constr:(PBY1) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
      (* [comment removed for export] *)
      assert (PB : 0 <= pX /\ pX + 4 * nX <= alloc_ceiling
                   /\ (ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ 1 <= nX)
                   /\ (ownX = LNull -> pX = 0 /\ nX = 0)).
      { flat constr:(MAX) 2%nat. intros FLt9 _. flat constr:(FLt9) 2%nat. flclear FLt9. intros _ FLt10. flat constr:(FLt10) 5%nat. flclear FLt10. intros _ _ _ _ HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN.
        flat constr:((hm_apart asegs R HIA h LB LF m1 HH1)) 2%nat. intros HF _. rewrite Forall_forall in HF.
        destruct ownX; [| | exfalso; exact (NST eq_refl)].
        - flat constr:(HOWN) 2%nat. flclear HOWN. intros E0 En. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
          split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
        - flat constr:(HOWN) 4%nat. flclear HOWN. intros N1 HIN HP16 HXL. destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
          split; [clear - B0; lia|]. split; [exact BC|].
          split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| exact N1]]]| intros E; discriminate E]. }
      flat constr:(PB) 4%nat. flclear PB. intros P0 PC PHEAP PNULL.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      lx_pre. lx_run_tac (PLAN [0x069484] [] 20%N). lx_tree.
      all: lx_same_mem; lx_gc; try clear MU WM.
      calloc_call i.
      all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "CALLOC1-LEFT:" g end.
      intros ms' mo' (mo1' & [HK1 MF1] & PO).
      flat constr:(PO) 4%nat. flclear PO. intros ms2 mo2 E PO. injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
      flat constr:(PO) 14%nat. flclear PO. intros MI2 ST2 MF2 WM2 HP2 h2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 CASES.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      (* [comment removed for export] *)
      assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
      { intros E0. flat constr:((PHEAP E0)) 3%nat. intros B0' HIN' _.
        eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 E0)| | cbn; clear; tauto].
        simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN'| clear; lia| clear - LENX; lia]. }
      assert (YBLK : ownY = LHeap -> In (pY, 4 * nY) LB).
      { intros E0. flat constr:(MAY) 2%nat. intros FLt11 _. flat constr:(FLt11) 2%nat. flclear FLt11. intros _ FLt12. flat constr:(FLt12) 5%nat. flclear FLt12. intros _ _ _ _ OY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY. rewrite E0 in OY.
        exact (proj1 (proj2 OY)). }
      pose proof (pby_keep _ _ _ _ _ _ _ HP2 PBY1 MI1 MI2 YBLK OYN ltac:(cbn; exact I)) as PBY2.
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX1) as OX2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OY1) as OY2.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      pose proof (hcs_ok asegs R HIA h2) as CSOK2. pose proof (cs_ok_sb _ _ CSOK2) as SB64'. pose proof (hcs_stack asegs R HIA h2) as SCS2.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      - (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP2.
        assert (SCS2' : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
        assert (MA2 : mpd_at asegs m2 LB (mkMPD X sgY nX pX xs padX ownX)).
        { eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS1| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGY| exact PNULL|].
          intros E. flat constr:((PHEAP E)) 4%nat. intros B0 HIN HP16 N1. split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
        (* [comment removed for export] *)
        clear SCS SCS0. lx_pre. lx_run_tac (PLAN [0x9c100] [] 20%N). lx_tree.
        all: lx_same_mem; lx_gc; try clear MU WM.
        eapply (aevtA_cut_evtA asegs AL _ LAWS2 _ _ _ _ _ _ KINV2);
          [ eapply epi_walk with (hc := h2) (LBc := LB) (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); try eassumption
          | intros y Hy; exact Hy | ].
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFAIL-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E ST9. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply post_keep; try eassumption.
        all: first [exact C24H | match goal with |- ?g => idtac "GFAIL-LEFT:" g end].
        { unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 Hi. lia. }
        { unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 D0. lia. }
        { left; reflexivity. }
      - (* [comment removed for export] *)
        replace (i * 4) with (4 * i) in HFRA, HAS, HH2, HNEW by (clear; lia).
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP2.
        assert (SCS2' : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
        flat constr:(HFRA) 4%nat. intros A0 AC AD HAP.
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 A (4 * i) HH2 (or_introl eq_refl)) as OA.
        assert (HINA : In (A, 4 * i) (((A, 4 * i) :: LB) ++ fdata LF)) by (left; reflexivity).
        assert (XA : X + 16 <= A \/ A + 4 * i <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * i) HFRA); [| clear; lia| clear - Hi; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (AS : A + 4 * i <= lo) by (clear - AC ALO LOS; lia).
        assert (AIMG : A + 4 * i <= hl_img_lo L \/ hl_img_hi L <= A).
        { flat constr:((hm_apart asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 HH2)) 2%nat. intros HFa _. rewrite Forall_forall in HFa.
          destruct (HFa (A, 4 * i) ltac:(apply in_app_iff; left; left; reflexivity)) as (_ & _ & _ & AI). exact AI. }
        pose proof (PYfresh A (4 * i) HFRA AIMG ltac:(clear - Hi; lia)) as YPA.
        pose proof (Yfresh A (4 * i) HFRA ltac:(clear - Hi; lia)) as YA.
        assert (AB : 0 <= A < 2^64) by (clear - A0 AC ALO LOS SLO SPR NEEDR Hi; lia).
        assert (PB : 0 <= pX < 2^64) by (clear - P0 PC NRX ALO LOS SLO SPR NEEDR; lia).
        (* [comment removed for export] *)
        clear SCS SCS0. lx_pre. lx_run_tac (PLAN [0x9c0ac; 0x067dbc] [(0x9c078, DJoin)] 40%N). lx_tree.
        all: try (match goal with LXKT : (if zlow 64 (Z.land (Z.lor ?a ?b) 3) =? _ then false else true) = true |- False => let KP := fresh "KP" in let EO := fresh "EO" in let P16 := fresh "P16" in let Ma := fresh "Ma" in let Mb := fresh "Mb" in assert (KP : pX <> 0) by (first [match goal with Hz : 0 <= pX + -1 |- _ => clear - Hz; lia end| match goal with Hk : (zlow 64 pX =? zlow 64 0) = false |- _ => intros Ez; rewrite Ez in Hk; rewrite Z.eqb_refl in Hk; discriminate Hk end]); assert (EO : ownX = LHeap) by (destruct ownX; [| reflexivity| exfalso; exact (NST eq_refl)]; exfalso; exact (KP (proj1 (PNULL eq_refl)))); flat constr:((PHEAP EO)) 4%nat; intros _ _ P16 _; assert (Ma : a mod 4 = 0) by (first [clear - P16; Z.div_mod_to_equations; lia| clear - A16; Z.div_mod_to_equations; lia]); assert (Mb : b mod 4 = 0) by (first [clear - P16; Z.div_mod_to_equations; lia| clear - A16; Z.div_mod_to_equations; lia]); rewrite Z.land_lor_distr_l in LXKT; change 3 with (Z.ones 2) in LXKT; rewrite !Z.land_ones in LXKT by (clear; lia); change (2 ^ 2) with 4 in LXKT; rewrite Ma, Mb in LXKT; cbv in LXKT; discriminate LXKT end).
        all: lx_same_mem; lx_gc; try clear MU WM.
        + (* [comment removed for export] *)
          assert (KP : pX = 0) by (match goal with Hz : 0 <= - pX |- _ => clear - Hz P0; lia end).
          assert (EO : ownX = LNull) by (destruct ownX; [reflexivity| exfalso; (flat constr:((PHEAP eq_refl)) 2%nat; intros B0 _); clear - B0 KP; lia| exfalso; exact (NST eq_refl)]).
          flat constr:((PNULL EO)) 2%nat. intros EP En.
          assert (CW3 : client_wrange L (((A, 4 * i) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
          assert (xs = []) as EL by (destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX En; lia]).
          assert (HA2 : u32arr asegs m2 A (repeat (Z_to_bv 64 0) (Z.to_nat i))).
          { replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat in HNEW by (clear - Hi; lia).
            eapply (u32arr_of_cells asegs); [exact HNEW| symmetry; apply u32s_repeat0]. }
          try replace (Z_to_bv 64 (i * 4)) with (Z_to_bv 64 (4 * i)) by (f_equal; clear; lia).
          eapply (aevtA_cut_evtA asegs AL _ LAWS2 _ _ _ _ _ _ KINV2);
            [ eapply (fin_walk h2 ((A, 4 * i) :: LB) m2 i A pX (repeat (Z_to_bv 64 0) (Z.to_nat i))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite repeat_length; clear - Hi; lia).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR Hi; lia).
          all: try (clear - P0 PC ALO LOS SLO SPR NEEDR; lia).
          all: try (left; reflexivity).
          all: try (eapply opy_at; [exact HH2| intros E0; right; exact (YBLK E0)| exact OYN]).
          all: try (clear - YPA; lia).
          all: try (clear - YA; lia).
          all: try (rewrite EP; clear; lia).
          all: try (clear - A16; Z.div_mod_to_equations; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN0-PRE-LEFT:" g end.
          intros ms' PO. flat constr:(PO) 23%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 HX9 ST9 HH9. subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. rewrite <- HS2.
            eapply (presA_tail3 h2 ((A, 4 * i) :: LB) A (4 * i) (4 * i) m2 m2 m2 m9);
              [exact HH2| intros b Hb; right; eapply In_mpd_keep; exact Hb| left; reflexivity| exact HFRA| clear - Hi; lia| clear; lia| exact TOP2| exact OX2| exact MU9| exact WM9]. }
          eapply (post_ok mo mo9 h2 m9 ((A, 4 * i) :: LB) i i A []); try eassumption.
          * clear; lia.
          * clear - Hi Hin; lia.
          * right. split; [reflexivity| exact TI].
          * intros k w Hk. destruct k; discriminate Hk.
          * unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 Hi. lia.
          * unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 D0. lia.
          * rewrite app_nil_r. eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - Hi NRY; lia| exact SGY| intros E; discriminate E|].
            { rewrite firstn_length_le by (clear - Hi LENY; lia). clear - Hi; lia. }
            intros _. split; [clear - Hi; lia|]. split; [left; reflexivity|]. split; [exact A16|].
            apply (rw_cells_of_u8arr asegs) in HA9. eapply (u32arr_of_cells asegs); [exact HA9| reflexivity].
          * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
            split; [reflexivity|]. split; [discriminate|].
            split; [intros b [Hb|Hb]; [right; left; exact Hb| left; exact Hb]|].
            split; [intros b Hb _; right; exact Hb|]. intros b [].
          * right. apply fresh_apart_keep. exact HFRA.
          * right. intros Hin'. destruct (HAP A (4 * i) ltac:(apply in_app_iff; left; exact Hin')) as [HH'|HH']; clear - HH' Hi; lia.
        + (* [comment removed for export] *)
          assert (KP : pX <> 0) by (first [match goal with Hz : 0 <= pX + -1 |- _ => clear - Hz; lia end| match goal with Hk : (zlow 64 pX =? zlow 64 0) = false |- _ => intros Ez; rewrite Ez in Hk; rewrite Z.eqb_refl in Hk; discriminate Hk end]).
          assert (EO : ownX = LHeap).
          { destruct ownX; [| reflexivity| exfalso; exact (NST eq_refl)]. exfalso. exact (KP (proj1 (PNULL eq_refl))). }
          flat constr:((PHEAP EO)) 4%nat. intros B0 HIN HP16 N1. pose proof (PCH2 EO) as PCH. clear PCH2.
          pose proof (DXP EO) as DXP'. pose proof (Q2 EO) as Q2'.
          assert (Q3' : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX) by (destruct Q3 as [Q|Q]; [exfalso; exact (Q EO)| exact Q]).
          pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 pX (4 * nX) HH2 (or_intror HIN)) as OP.
          assert (PA : A + 4 * i <= pX \/ pX + 4 * nX <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
          assert (HINP : In (pX, 4 * nX) (((A, 4 * i) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
          replace (Z_to_bv 64 (4 * nX)) with (Z_to_bv 64 (nX * 4)) by (clear; f_equal; lia).
          (* [comment removed for export] *)
          assert (HN2 : rw_cells asegs m2 A ([CB (4 * length xs)%nat (repeat (Z_to_bv 8 0) (4 * length xs))]
                                              ++ [CB (Z.to_nat (4 * (i - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (i - nX))))])).
          { eapply rw_cells_reshape; [exact HNEW| |].
            - cbn. rewrite !repeat_length; repeat split; reflexivity.
            - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LENX Hin; lia. }
          apply rw_cells_app in HN2. flat constr:(HN2) 2%nat. flclear HN2. intros HNA HNB. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
          replace (A + Z.of_nat (4 * length xs + 0)) with (A + nX * 4) in HNB by (clear - LENX; lia).
          apply (u8arr_of_rw_cells asegs) in HNA.
          pose proof (proj1 (u32arr_of_cells asegs m2 pX _ _ xs PCH eq_refl)) as PBA.
          pose proof (munch_refl [(A, A + nX * 4); (lo, bv_unsigned sp); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
          pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + nX * 4)] m2) as MUX.
          pose proof (conj HXS1 I) as HXS0. pose proof (conj HYS1 I) as HYS0. pose proof (conj PBY2 I) as PBY0.
          pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CP) as SPC. unfold A_ASAN_MEMCPY_CP in SPC.
          acallxA_sp (bv_unsigned sp + -96)
            (eapply SPC with (h := h2) (LB := (A, 4 * i) :: LB) (LF := LF) (DST := A) (SRC := pX) (n := nX * 4) (lo := lo)
                              (ds := repeat (Z_to_bv 8 0) (4 * length xs)) (ss := u32s xs);
             rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
             try eassumption; try reflexivity;
             first [ left; rewrite AMC; reflexivity
                   | rewrite repeat_length; clear - LENX; lia
                   | rewrite u32s_length; clear - LENX; lia
                   | eapply aobj_sub; [exact OA| clear; lia| clear - Hin LENX NRX; lia]
                   | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
                   | right; clear - PA Hin N1; lia
                   | left; clear - AS PC ALO LOS Hin N1; lia
                   | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC Hin N1 ACV; lia
                   | eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]
                   | eapply client_wrange_block; [exact HINA| clear; lia| clear - Hin NRX; lia]
                   | clear - NRX NRY Hi Hin LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                   | first [exact C24H | match goal with |- ?g => idtac "MEMCPY1-PRE-LEFT:" g end] ]).
          clear SPC.
          all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY1-SIDE:" g end.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          match goal with H : u8arr asegs m3 A (u32s xs) |- _ => rename H into HPA end.
          match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
          match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
          match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
          try clear HXS1. flat constr:(HXS0) 2%nat. flclear HXS0. intros HXS1 _.
          apply (rw_cells_transport asegs _ m2 m3 _ _ HXS1 MUX) in WM2' as HXS3; [| cbn [disjoint_from cells_size csize Nat.add]; clear - XA DSX Hin Hi NRX; lia].
          (* [comment removed for export] *)
          clear HYS0 PBY0 MUX. lx_hide PCH.   (* [comment removed for export] *)
          lx_hide MU2. lx_hide WM2'.            (* [comment removed for export] *)
          lx_pre. lx_run_tac (PLAN [0x0a7f14] [] 20%N). lx_tree.
          all: lx_same_mem; lx_gc; try clear MU WM. lx_unhide.
          replace (Z_to_bv 64 (4 * nX)) with (Z_to_bv 64 (nX * 4)) by (clear; f_equal; lia).
          replace (4 * length xs)%nat with (Z.to_nat (nX * 4)) in PCH by (clear - LENX; lia).
          assert (CW4 : client_wrange L (((A, 4 * i) :: lb_remove pX LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
            destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
          pose proof (conj HXS3 I) as HXS0'. pose proof (conj HPA I) as HPA0.
          match goal with H : rw_cells asegs m3 Y _ |- _ => pose proof (conj H I) as HYS0 end.
          match goal with H : bytes_at asegs m3 pY (u32s ys) |- _ => pose proof (conj H I) as PBY0 end. pose proof (conj MI3 I) as MI30.
          match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 Y 16 |- _ => pose proof (conj H I) as OY20 end.
          free_limbs_call h2 ((A, 4 * i) :: LB) HIN PCH.
          all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "ZF1-LEFT:" g end.
          intros ms' mo4' (mo3 & [HK3 MF3] & PO).
          destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo4'.
          rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in PO by qlia.
          flat constr:(PO) 12%nat. flclear PO. intros MI4 ST4 MF4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HH4.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
            replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
          match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
          rewrite (lb_remove_cons_other A (4 * i) pX LB) in HP4, HH4 by (clear - PA Hin N1 Hi; lia).
          assert (HP4' : presA asegs R ((A, 4 * i) :: lb_remove pX LB) LF (bv_unsigned sp + -96) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
          { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * i) :: LB) LF _ [] pX (4 * nX) m3 m3 m4);
              [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
              | replace (pX + 4 * nX) with (pX + nX * 4) by (clear; lia); exact HP4].
            intros b xb [Hb|Hb] Hr.
            - subst b. split; [left; reflexivity|]. intros E. injection E as E1' E2'. clear - E1' PA Hin N1 Hi. lia.
            - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB pX (4 * nX) ND Hb). }
          clear HP4 PCH PBA OP HINP HINA.
          presA_transport HP4'.
          (* [comment removed for export] *)
          assert (YCR4 : client_range L (((A, 4 * i) :: lb_remove pX LB) ++ fdata LF) (bv_unsigned sp + -96) Y 16).
          { intros a Ha. destruct Q4 as [Q|Q]; [| left; clear - Q Ha; lia].
            destruct (YCR a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [exfalso; clear - Hs Q Ha; lia| right; left; exact Hd| right; right].
            apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exists b; split; [apply in_app_iff; right; exact Hb| exact Hr]].
            destruct b as [B k]. exists (B, k). split; [| exact Hr]. apply in_app_iff. left. right. apply In_lb_remove_keep; [exact Hb|].
            intros ->. cbn in Hr. pose proof (nodup_fst_neq LB pX (4 * nX) pX k ND HIN Hb) as NE.
            destruct (Z.eq_dec k (4 * nX)) as [->|NK]; [clear - Hr Ha Q2'; lia|]. apply NE; [| reflexivity]. intros E. injection E as E'. exact (NK E'). }
          assert (YBLK4 : ownY = LHeap -> In (pY, 4 * nY) ((A, 4 * i) :: lb_remove pX LB)).
          { intros E0. right. apply In_lb_remove_keep; [exact (YBLK E0)|]. intros E. flat constr:(MAY) 2%nat. intros FLt13 _. flat constr:(FLt13) 2%nat. flclear FLt13. intros _ FLt14. flat constr:(FLt14) 5%nat. flclear FLt14. intros _ _ LY _ OY.
            cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LY, OY. rewrite E0 in OY. flat constr:(OY) 2%nat. flclear OY. intros NY1 _. clear - E Q3' NY1 N1. lia. }
          flat constr:(HYS0) 2%nat. flclear HYS0. intros HYS3 _. flat constr:(HPA0) 2%nat. flclear HPA0. intros HPA3 _. flat constr:(PBY0) 2%nat. flclear PBY0. intros PBY3 _. try clear MI3. flat constr:(MI30) 2%nat. flclear MI30. intros MI3 _. try clear OY2. flat constr:(OY20) 2%nat. flclear OY20. intros OY2 _.
          pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 Y _ HP4' HYS3 YCR4 ltac:(cbn; exact I)) as HYS4.
          pose proof (pby_keep _ _ _ _ _ _ _ HP4' PBY3 MI3 MI4 YBLK4 OYN ltac:(cbn; exact I)) as PBY4.
          assert (HPA4 : u8arr asegs m4 A (u32s xs)).
          { apply (rw_cells_of_u8arr asegs) in HPA3. apply (u8arr_of_rw_cells asegs) with (n := length (u32s xs)).
            eapply (presA_rw_cells asegs R); [exact HP4'| exact HPA3| | cbn; exact I].
            cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, u32s_length.
            eapply client_range_block; [apply in_app_iff; left; left; reflexivity| clear; lia| clear - LENX Hin NRX; lia]. }
          pose proof (presA_aobj0 asegs R (hcs asegs R HIA h2) _ _ _ _ _ _ m3 m4 Y 16 CSOK2 HP4' OY2 (hcs_below_top asegs R HIA h2) ltac:(right; split; [exact YCR4| clear - ALO LOS SLO NEEDR; lia])) as OY4.
          presA_transport HP4'.
          apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
          pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4.
          pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX2) as OX4. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OY4) as OY4'.
          assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
          assert (HINA4 : In (A, 4 * i) ((A, 4 * i) :: lb_remove pX LB)) by (left; reflexivity).
          apply (rw_cells_of_u8arr asegs) in HPA4. rewrite u32s_length in HPA4.
          assert (HA4 : u32arr asegs m4 A (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - nX)))).
          { apply u32arr_app. split; [eapply (u32arr_of_cells asegs); [exact HPA4| reflexivity]|].
            replace (A + 4 * Z.of_nat (length xs)) with (A + nX * 4) by (clear - LENX; lia).
            replace (Z.to_nat (4 * (i - nX))) with (4 * Z.to_nat (i - nX))%nat in HNB by (clear - Hin Hi; lia).
            eapply (u32arr_of_cells asegs); [exact HNB| symmetry; apply u32s_repeat0]. }
          (* [comment removed for export] *)
          zstep. zstep.
          try replace (Z_to_bv 64 (i * 4)) with (Z_to_bv 64 (4 * i)) by (f_equal; clear; lia).
          eapply (aevtA_cut_evtA asegs AL _ LAWS4 _ _ _ _ _ _ KINV4);
            [ eapply (fin_walk h4 ((A, 4 * i) :: lb_remove pX LB) m4 i A pX (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - nX)))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite HT4; exact HT2).
          all: try (rewrite length_app, repeat_length; clear - Hi Hin LENX; lia).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR Hi; lia).
          all: try (clear - P0 PC ALO LOS SLO SPR NEEDR NRX; lia).
          all: try (eapply opy_at; [exact HH4| exact YBLK4| exact OYN]).
          all: try (clear - YPA; lia).
          all: try (clear - YA; lia).
          all: try (clear - A16; Z.div_mod_to_equations; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN1-PRE-LEFT:" g end.
          intros ms' PO. flat constr:(PO) 23%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 HX9 ST9 HH9. subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          (* [comment removed for export] *)
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. eapply presA_trans; [| eapply presA_trans].
            - (* [comment removed for export] *)
              rewrite <- HS2. eapply (presA_tail3 h2 ((A, 4 * i) :: LB) A (nX * 4) (4 * i) m3 m4 m2 m3);
                [exact HH3| intros b Hb; right; eapply In_mpd_keep; exact Hb| left; reflexivity| exact HFRA| clear - N1; lia| clear - Hin; lia| exact TOP2| exact OX2| exact MU2| exact WM2'].
              all: first [exact C24H | match goal with |- ?g => idtac "M23-LEFT:" g end].
            - (* [comment removed for export] *)
              eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb].
            - (* [comment removed for export] *)
              rewrite <- HS2, <- HS4.
              eapply (presA_tail3 h4 ((A, 4 * i) :: lb_remove pX LB) A (4 * i) (4 * i) m4 m4 m4 m9);
                [exact HH4| | left; reflexivity| exact HFRA| clear - Hi; lia| clear; lia| exact TOP4| exact OX4| exact MU9| exact WM9].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
          eapply (post_ok mo mo9 h4 m9 ((A, 4 * i) :: lb_remove pX LB) i i A []); try eassumption.
          * clear; lia.
          * clear - Hi Hin; lia.
          * right. split; [reflexivity| exact TI].
          * intros k w Hk. destruct k; discriminate Hk.
          * rewrite HT4; exact HT2.
          * rewrite HS4; exact HS2.
          * rewrite HF4; exact HF2.
          * intros y Hy. apply HCS4, HCS2, Hy.
          * unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 HV4 Hi. lia.
          * unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 HFR4 D0. lia.
          * rewrite app_nil_r. eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - Hi NRY; lia| exact SGY| intros E; discriminate E|].
            { rewrite firstn_length_le by (clear - Hi LENY; lia). clear - Hi; lia. }
            intros _. split; [clear - Hi; lia|]. split; [left; reflexivity|]. split; [exact A16|].
            apply (rw_cells_of_u8arr asegs) in HA9. eapply (u32arr_of_cells asegs); [exact HA9| reflexivity].
          * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
            split; [reflexivity|]. split; [discriminate|].
            split; [intros b [Hb|Hb]; [right; left; exact Hb| left; eapply In_lb_remove; exact Hb]|].
            split.
            { intros [Bb kb] Hb Hn. right. apply In_lb_remove_keep; [exact Hb|].
              apply (nodup_fst_neq LB pX (4 * nX) Bb kb ND HIN Hb). intros E. apply Hn. left. symmetry. exact E. }
            intros b [<-|[]] [E|Hb']; [exfalso; injection E as E1 E2; clear - E1 PA Hi Hin N1; lia| exfalso; exact (lb_remove_notin LB pX (4 * nX) ND Hb')].
          * right. apply fresh_apart_keep. exact HFRA.
          * right. intros Hin'. destruct (HAP A (4 * i) ltac:(apply in_app_iff; left; exact Hin')) as [HH'|HH']; clear - HH' Hi; lia.
      all: first [exact C24H | match goal with |- ?g => idtac "GROW-LEFT:" g end].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Grow.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L16046136858.70L38717875063.70L42465045280.67L46223366314.70L62544261284.7000000=00E00I00V00cS2sp1w1u2Rw1HS2sp1w1uS2spS2sp1w1u2Rw1HS2sp1w1u2Rw1H". (* [comment removed for export] *)
  Lemma lx_sw32_zero_iff : forall w : word, zswrap 32 (zlow 32 (bv_unsigned w)) = 0 <-> bv_unsigned w mod 2 ^ 32 = 0.
  Proof.
    intros w. unfold zswrap, zlow. change (2 ^ (32 - 1)) with (2 ^ 31).
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)) as Rw.
    set (u := bv_unsigned w mod 2 ^ 32) in *.
    destruct (Z.lt_ge_cases u (2 ^ 31)).
    - rewrite (Z.mod_small (u + 2 ^ 31)) by lia. lia.
    - rewrite <- (Z.mod_add (u + 2 ^ 31) (-1)) by lia. rewrite (Z.mod_small (_ + _ * _)) by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0>L10569489964.3L13015518834.1L27255558078.3L30259373055.6L33113984576.2L33115562649.3L36571201320.0L372338538.4  L43442324747.4L45270656294.3L48044449366.3L51497033277.2L53722319862.1L59308551419.6L59308961273.3L59310683537.4L68633794283.300000800;00E00M00S00\00]00j01701A01J01P01S01h02102>02HS1k1j2HjS1jS2nY1j3HjrS1j1i2HiS2pY1jS2pY1j2J1SS2nY1j3Hjr2H4S2nY1j3Hjr2H4S2nY1j3HjrS1w2H52H6S1j2J1S1jS2nY2ys1j3Hjr4LENY2NXS1w2H42WZS2nY1j2Hj3HjrS2nY1j3Hjr". (* [comment removed for export] *)
  Lemma scan_loop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pk,$67.Pj,$8.Pmm,P,(3.&40.)(5.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(=.$8.R12.(42.R13.))P,(40.(20.+1.R13.)(20.R13.(22.VnY,+1.)))P,(66.Vys,(2>.R14.+1.))P,(4=.$46.R14.VpY,(4>.Vys,))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R15.VpY,(1;.+4.VnY,))P,(27.$46.R16.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)Lms',$56.(57.$8.Li,$8.(57.(3.&40.)Lxt0',(3.&40.)(57.(3.&40.)Lxt1',(3.&40.)(44.(40.(=.$56.R4.(3<.(3=.R1:.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R2.R1.R17.R16.R15.(25.&40.VX,)(25.&40.VY,)(25.&40.(2>.VpY,(1;.+4.(22.R3.+1.))))(25.&40.VpY,)(25.&40.(22.R3.+1.))(25.&40.=)(25.&40.(2>.VpY,(1;.+4.(22.R3.+1.))))(25.&40.+1.)R14.R13.R12.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R11.R10.R?.Vs10,Vs11,R>.R=.R<.R;.)VF,(25.&40.+9;>8<.)Vfc,(3>.(3.&40.))R1;.(3?.$46.)))(40.(40.(20.+2.R3.)(20.R3.(2>.R1<.+1.)))(40.(66.Vys,R3.)(65.Vys,R3.))))(40.(=.$56.R4.(3<.(3=.R1:.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R2.R1.R17.R16.R15.(25.&40.VX,)(25.&40.VY,)(25.&40.(2>.VpY,(1;.+4.(22.R3.+1.))))(25.&40.VpY,)(25.&40.(22.R3.+1.))(25.&40.=)(25.&40.(2>.VpY,(1;.+4.(22.R3.+1.))))(25.&40.+1.)R14.R13.R12.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R11.R10.R?.Vs10,Vs11,R>.R=.R<.R;.)VF,(25.&40.+9;>8<.)Vfc,(3>.(3.&40.))R1;.(3?.$46.)))(40.(=.$8.R3.+1.)(66.Vys,+1.)))))))(3<.(3=.R16.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.R12.R11.(25.&40.VX,)(25.&40.VY,)(25.&40.(2>.VpY,(1;.+4.R18.)))(25.&40.VpY,)(25.&40.R18.)(25.&40.=)(25.&40.(2>.VpY,(1;.+4.R18.)))(25.&40.+1.)R10.R?.R>.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R=.R<.R;.Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+9;?<0.)Vfc,(3>.(3.&40.))R17.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hj Hjr ZY PBY OPY MI; [exfalso; clear - Hj Hjr; lia|].
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    flat constr:(PBY) 3%nat. intros PY0 PYB _. rewrite u32s_length in PYB.
    destruct (nth_error ys (Z.to_nat j)) as [w|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hjr LENY; lia].
    pose proof (u32ro_cell_at mm pY ys j (pY + 4 * j) w PBY NX ltac:(clear - Hjr; lia) eq_refl) as LCw.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as Bw.
    (* [comment removed for export] *)
    lx_pre. lx_run_tac (PLAN [0x9bfc0; 0x9be8c] [(0x9bfe0, DJoin)] 30%N). lx_tree.
    all: lx_same_mem; lx_gc.
    - (* [comment removed for export] *)
      apply evtA_done. exists (j + 1). do 2 eexists. left.
      split; [replace (j + 1 - 1) with j by (clear; lia); reflexivity|].
      split; [clear - Hjr; lia|]. split; [exact ZY|].
      right. exists w. split; [replace (Z.to_nat (j + 1 - 1)) with (Z.to_nat j) by (clear - Hjr; lia); exact NX|].
      match goal with Hn : _ + 1 <= 0 \/ 0 + 1 <= _ |- _ => intros WZ; apply (proj2 (lx_sw32_zero_iff w)) in WZ; clear - Hn WZ; lia end.
    - (* [comment removed for export] *)
      assert (K2 : bv_unsigned w mod 2 ^ 32 = 0) by (match goal with Hp : 0 <= - zswrap 32 _, Hq : 0 <= zswrap 32 _ |- _ => apply (proj1 (lx_sw32_zero_iff w)); clear - Hp Hq; lia end).
      pose proof (zeros_above_down' ys j w ltac:(clear - Hjr; lia) ZY NX K2) as ZY'.
      replace (pY + (4 * j + -4)) with (pY + 4 * (j - 1)) by (clear; lia).
      replace (j + -1) with (j - 1) by (clear; lia).
      eapply evtA_mono; [eapply (IH (j - 1)); try eassumption; [clear - Hj; lia| match goal with Hp : 0 <= j + -2 |- _ => clear - Hjr Hp; lia end| replace (j - 1 + 1) with j by (clear; lia); exact ZY'] |].
      cbv beta. intros ms' PO. destruct PO as (i & xt0' & xt1' & [(E & Hi & Zi & Ti)|(E & Hi & Zi)]).
      * exists i. do 2 eexists. left. split; [exact E|]. split; [match goal with Hp : 0 <= j + -2 |- _ => clear - Hi Hp Hjr; lia end|]. split; [exact Zi| exact Ti].
      * exists i. do 2 eexists. right. split; [exact E|]. split; [exact Hi| exact Zi].
    - (* [comment removed for export] *)
      assert (K2 : bv_unsigned w mod 2 ^ 32 = 0) by (match goal with Hp : 0 <= - zswrap 32 _, Hq : 0 <= zswrap 32 _ |- _ => apply (proj1 (lx_sw32_zero_iff w)); clear - Hp Hq; lia end).
      pose proof (zeros_above_down' ys j w ltac:(clear - Hjr; lia) ZY NX K2) as ZY'.
      apply evtA_done. exists 1. do 2 eexists. right.
      match goal with Hp : 0 <= - j + 1 |- _ => assert (J1 : j = 1) by (clear - Hp Hjr; lia) end.
      split; [replace (pY + (4 * j + -4)) with (pY + 4 * (1 - 1)) by (clear - J1; lia); replace (j + -1) with (1 - 1) by (clear - J1; lia); reflexivity|]. split; [reflexivity| rewrite J1 in ZY'; exact ZY'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma sign_mod16 : forall s, s = 1 \/ s = -1 -> (bv_unsigned (Z_to_bv 64 s) mod 2 ^ 16) mod 2 ^ 16 = s mod 2 ^ 16.
  Proof. intros s [-> | ->]; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Tail.
    Variable mo : Model.
    Hypothesis OYN : ownY <> LNull.
    Hypothesis BUD : havol asegs R HIA h + copy_PHI dY <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + copy_FR d <= FR_MAX.
    Hypothesis Q1 : X + 16 <= pY \/ pY + 4 * nY <= X.
    Hypothesis Q2 : ownX = LHeap -> Y + 16 <= pX \/ pX + 4 * nX <= Y.
    Hypothesis Q3 : ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX.
    Hypothesis Q4 : Y + 16 <= lo \/ bv_unsigned sp <= Y.
    Hypothesis Q5 : pY + 4 * nY <= lo \/ bv_unsigned sp <= pY.
    Hypothesis Y47 : pY + 4 * nY + 8 <= 2^47.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis DXP : ownX = LHeap -> X + 16 <= pX \/ pX + 4 * nX <= X.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis PYfresh : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PA,$8.Pk,$8.P,(71.VR,VLB,VLF,R2.R1.)P,(44.(20.(2>.R3.R2.)(78.(15.VR,)))(20.(79.(15.VR,))R3.))P,(41.=R3.)(44.(20.(2>.VpY,(1;.+4.VnY,))R5.)(20.(2>.R5.R4.)VpY,))")
(* [comment removed for export] *).
    Hypothesis Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y.
    Hypothesis YBLK : ownY = LHeap -> In (pY, 4 * nY) LB.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L1164172544.1  L14579576775.14L1649577667.2  L19945316590.2 L2547996026.5  L26892418956.1 L29428324939.5 L32027975233.0 L3253508485.5  L35653441506.7 L38723301197.5 L40281191306.3 L41858356445.5 L4235704437.5  L48132467214.7 L59308668813.6 L60098763854.3 L62018535662.1 L62622784051.44L68294535841.2 L7007305626.5  00000300H00P00W00^00b01401501F01^01m02602F02V03103D03N03Q03R03Y03jS1XS2sp1X2nX2pX2lo3DSX1HS2nX3NRXS2sp2loS2nX2nYS2spS1R2lo3LOS3ALO3ACPSS2nY2ys1i2Hi4LENYS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h1d3D0'S1R3HIA1hS2nX2nY1i2Hi3HinS1R3HIA1h2nY3NRYS1R5NEEDR2sp2lo3LOS3SLO3ALOS2nX2nY1i2Hi3Hin2EnS1R2lo3LOSS1RFS2nX2pXS2nX2pX2nY2pY3Q3'". (* [comment removed for export] *)
    Lemma memset_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,R16.)P,(40.(20.+1.R16.)(20.R16.VnY,))P,(20.R17.VnX,)P,(66.Vys,R18.)P,(44.(=.$8.VnX,VnX,)(40.(=.$8.VnX,R19.)(65.Vys,R19.)))P,(50.$46.R1;.VX,(51.$52.(53.(25.&40.VpX,))(51.$52.(75.(25.&40.VsgY,))(51.$52.(75.(25.&40.VnX,))(51.$52.(76.VpadX,)(54.$52.))))))P,P,(=.$>.VownX,$19.)(50.$46.R1=.VpX,(51.$52.(7<.(7=.#4.(43.(3.&40.)Vxs,))(4>.Vxs,))(54.$52.)))P,(50.$46.R1=.VY,(51.$52.(53.(25.&40.VpY,))(51.$52.(75.(25.&40.VsgY,))(51.$52.(75.(25.&40.VnY,))(51.$52.(76.VpadY,)(54.$52.))))))P,(4=.$46.R1>.VpY,(4>.Vys,))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1?.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R20.VY,+10.)P,(50.$46.R21.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R1?.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R22.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R23.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R24.)(7:.$46.(7;.$46.VR,VHIA,Vh,Vmo,)(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(3<.(3=.R22.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R21.R20.R1?.(25.&40.(1;.+4.R24.))R1>.(25.&40.VX,)(25.&40.VY,)(25.&40.VnX,)R1=.R1<.R1;.R1:.R19.(25.&40.R24.)R18.R17.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R16.R15.R14.Vs10,Vs11,R13.R12.R11.R10.)VF,(25.&40.+9;>><.)Vfc,(3>.(3.&40.))R25.(3?.$46.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HHc Hi Hin ZY _ HXS PCH HYS PBY OX OY FR ST MI HP. basic_facts h LB mc HHc TOP.
      flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      assert (EO : ownX = LHeap).
      { flat constr:(MAX) 2%nat. intros FLt15 _. flat constr:(FLt15) 2%nat. flclear FLt15. intros _ FLt16. flat constr:(FLt16) 5%nat. flclear FLt16. intros _ _ _ _ HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN.
        destruct ownX; [(flat constr:(HOWN) 2%nat; flclear HOWN; intros _ En); exfalso; clear - En Hi Hin; lia| reflexivity| exfalso; exact (NST eq_refl)]. }
      flat constr:(MAX) 2%nat. intros FLt17 _. flat constr:(FLt17) 2%nat. flclear FLt17. intros _ FLt18. flat constr:(FLt18) 5%nat. flclear FLt18. intros _ _ _ _ HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
      flat constr:(HOWN) 4%nat. flclear HOWN. intros N1 HIN P16 _.
      assert (Q3' : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX) by (destruct Q3 as [Q|Q]; [exfalso; exact (Q EO)| exact Q]).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply (memset_path mc i); try eassumption; try exact EO
        | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS).
      all: try (eapply (u32arr_of_cells asegs); [exact (PCH EO)| reflexivity]).
      all: try (eapply opy_at; [exact HHc| exact YBLK| exact OYN]).
      all: try exact (Q2 EO). all: try exact (DXP EO). all: try (clear - Q3'; lia).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "MSF-PRE-LEFT:" g end.
      intros ms' PO. flat constr:(PO) 22%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 ST9 HH9. subst ms'.
      apply aevtA_done. intros mo9 [HK9 MF9].
      assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
      { eapply presA_trans; [exact HP|].
        apply (munch_weaken _ [(lo, bv_unsigned sp); (pX, pX + 4 * nX); (X, X + 16)]) in MU9; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
        eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] pX (4 * nX) mc mc m9);
          [exact HHc| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
        { intros b xb Hb Hr. split; [eapply In_mpd_keep; exact Hb|]. intros E. subst b.
          exact (lb_remove_notin LB pX (4 * nX) (HND _ _ _ _ HHc) (in_keep_remove LB dX _ (HND _ _ _ _ HHc) EO HIN Hb)). }
        eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                  (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (X, X + 16)]);
          [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) mc mc m9); [exact HHc| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ mc m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HHc| | exact Hc]; clear; lia | exact MU9 | exact WM9].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (pX + 4 * nX - pX) with (4 * nX) by (clear; lia); eapply aobj_crange; eapply hm_aobj_block; [exact HHc| exact HIN]|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil. }
      eapply (post_ok mo mo9 h m9 LB i nX pX (repeat (Z_to_bv 64 0) (Z.to_nat (nX - i)))); try eassumption; try reflexivity.
      * clear - Hin NRY; lia.
      * left; reflexivity.
      * intros k w Hk. apply nth_error_In, repeat_spec in Hk. subst w. rewrite unsigned_lit by (clear; lia). reflexivity.
      * intros y Hy; exact Hy.
      * unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
      * unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
      * eapply mpd_at_rebuild; [discriminate| unfold mpi_cells| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGY| intros E; discriminate E|].
        { eapply (rw_cells_transport asegs _ mc m9); [exact HXS| exact MU9| exact WM9| cbn [disjoint_from cells_size csize Nat.add]; clear - DSX DXP EO Hi Hin; pose proof (DXP EO); lia]. }
        { rewrite length_app, firstn_length_le, repeat_length by (clear - Hi LENY; lia). clear - Hi Hin; lia. }
        intros _. split; [exact N1|]. split; [exact HIN|]. split; [exact P16| exact HA9].
      * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
        split; [reflexivity|]. split; [discriminate|].
        split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b _ _; reflexivity.
      * left. cbn [mpd_blk md_own md_p md_n]. rewrite EO. left. reflexivity.
      * left. cbn [mpd_blk md_own md_p md_n]. rewrite EO. left. reflexivity.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25163584650.83000004S2sp". (* [comment removed for export] *)
    Lemma lx_zlow16_mod16 : forall s, zlow 16 s mod 2 ^ 16 = s mod 2 ^ 16.
    Proof. intros s. unfold zlow. apply Z.mod_mod. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@D50796823377.160D51156378645.160D5472625192.160 D60109443305.160D64311488078.160L10320323253.6  L11913635791.5  L29428324939.5  L35653441506.7  L41850029165.5  L60098763854.3  L68470634364.14 00000[00i01701N01k02402=02O02g03003:03`S1R5NEEDR2sp1X2xs1Y2ys2lo3LOS3SLO3SPR2X02Y0S2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS1R2sp1X2xs1Y2ys2lo3LOSS1R3HIA1h2sp1X2xs1Y2ys2lo3TOPS2nX2ys1iS2nX1i2H8S1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2nX1i2H8S1R2lo3LOSS1R2sp1X2nX2pX2xs2lo3LOS3ALO4LENX2BC1D". (* [comment removed for export] *)
    Lemma tail_i : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pm1,P,(3.&40.)(5.(3.&8.))Pi,$8.Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,R18.)P,(50.$46.R19.VX,(51.$52.(53.(25.&40.VpX,))(51.$52.(75.(25.&40.VsgX,))(51.$52.(75.(25.&40.VnX,))(51.$52.(76.VpadX,)(54.$52.))))))P,P,(=.$>.VownX,$19.)(50.$46.R1;.VpX,(51.$52.(7<.(7=.#4.(43.(3.&40.)Vxs,))(4>.Vxs,))(54.$52.)))P,(50.$46.R1;.VY,(51.$52.(53.(25.&40.VpY,))(51.$52.(75.(25.&40.VsgY,))(51.$52.(75.(25.&40.VnY,))(51.$52.(76.VpadY,)(54.$52.))))))P,(4=.$46.R1<.VpY,(4>.Vys,))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1=.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1>.VY,+10.)P,(50.$46.R1?.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R1=.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R20.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R21.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R22.)P,(40.(20.+1.R22.)(20.R22.VnY,))P,(66.Vys,R23.)P,(65.Vys,R24.)(7:.$46.(7;.$46.VR,VHIA,Vh,Vmo,)(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(3<.(3=.R23.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R22.R21.R20.R1?.R1>.(25.&40.VX,)(25.&40.VY,)R1=.R1<.(25.&40.(22.R25.+1.))R1;.R1:.R19.R18.R17.R16.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R15.R14.R13.Vs10,Vs11,R12.R11.R10.R?.)VF,(25.&40.+9;>8<.)Vfc,(3>.(3.&40.))R26.(3?.$46.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH1 HXS1 PCH1 HYS1 PBY1 OX1 OY1 FR1 ST1 MI1 HP1 Hi ZY TI. basic_facts h LB m1 HH1 TOP.
      flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      (* [comment removed for export] *)
      lx_pre. lx_run_tac (PLAN [0x9beec; 0x9c014] [(0x9bea8, DJoin); (0x9bec0, DJoin); (0x9bed8, DJoin)] 40%N). lx_tree.
      all: lxr_leaf; lx_carry; lx_gc; lx_rn_munch MU; lx_rn_wmono WM.
      all: rename lxm into m2.
      all: apply (rw_cells_C2_congr asegs m2 X [C8 (Z_to_bv 64 pX)] _ sgY) in HXS1; [| apply lx_zlow16_mod16]; cbn [app] in HXS1.
      all: assert (HP2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2)
        by (eapply presA_trans; [exact HP1|]; eapply (presA_tail asegs R HIA h LB); [exact HH1| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact OX1| exact MU| exact WM]).
      all: assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]) by
       (intros E0; pose proof MAX as [[_ (_ & _ & _ & _ & HOWN)] _]; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN; rewrite E0 in HOWN;
        (flat constr:(HOWN) 3%nat; flclear HOWN; intros N1 HIN _); (flat constr:((hm_apart asegs R HIA h LB LF m1 HH1)) 2%nat; intros HF _); rewrite Forall_forall in HF;
        destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _); cbn in B0, BC;
        eapply (rw_cells_transport asegs _ m1 m2); [exact (PCH1 E0)| exact MU| exact WM|];
        cbn [disjoint_from cells_size csize Nat.add]; pose proof (DXP E0) as D; clear - D BC ALO LOS SLO NEEDR LENX; lia).
      all: first [ apply (hm_munch asegs R HIA h LB LF [(lo, bv_unsigned sp); (X, X + 16)] m1 m2) in HH1; [| exact MU| exact WM| solve_w_writable]
          | let mx := lx_cur_mem in lazymatch type of HH1 with HM _ _ _ _ _ _ ?my => constr_eq my mx end
          | let mx := lx_cur_mem in match goal with H : HM _ _ _ _ _ _ ?my |- _ => constr_eq my mx; clear HH1; rename H into HH1 end ].   (* [comment removed for export] *)
      all: clear MU WM HP1 PCH1.
      - (* [comment removed for export] *)
        rewrite (Z.add_comm (Z.shiftr (X + 10) 3) (al_sb AL)).
        eapply (grow_path mo m2 i); try eassumption. all: try (match goal with K : 0 <= _ |- _ => clear - K Hi; lia end).   (* [comment removed for export] *)
        all: first [exact C24H | match goal with |- ?g => idtac "TI-GP-LEFT:" g end].
      - (* [comment removed for export] *)
        eapply (memset_finish m2 i); try eassumption. all: try (match goal with K : 0 <= _ |- _ => clear - K Hi; lia end).   (* [comment removed for export] *)
        all: first [exact C24H | match goal with |- ?g => idtac "TI-MS-LEFT:" g end].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11662292589.2000008S2nY3HnY". (* [comment removed for export] *)
    Lemma tail_1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pm1,P,(3.&40.)(5.(3.&8.))Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,R17.)P,(50.$46.R18.VX,(51.$52.(53.(25.&40.VpX,))(51.$52.(75.(25.&40.VsgX,))(51.$52.(75.(25.&40.VnX,))(51.$52.(76.VpadX,)(54.$52.))))))P,P,(=.$>.VownX,$19.)(50.$46.R1:.VpX,(51.$52.(7<.(7=.#4.(43.(3.&40.)Vxs,))(4>.Vxs,))(54.$52.)))P,(50.$46.R1:.VY,(51.$52.(53.(25.&40.VpY,))(51.$52.(75.(25.&40.VsgY,))(51.$52.(75.(25.&40.VnY,))(51.$52.(76.VpadY,)(54.$52.))))))P,(4=.$46.R1;.VpY,(4>.Vys,))P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1<.VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1=.VY,+10.)P,(50.$46.R1>.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R1=.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R1?.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R20.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R21.)P,(20.+1.VnY,)P,(66.Vys,+1.)(7:.$46.(7;.$46.VR,VHIA,Vh,Vmo,)(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(3<.(3=.R22.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R21.R20.R1?.R1>.R1=.(25.&40.VX,)(25.&40.VY,)R1<.R1;.(25.&40.(22.+1.+1.))R1:.R19.R18.R17.R16.R15.(25.&40.(62.(29.VR,)))(25.&40.(63.VY,+3.))R14.R13.R12.Vs10,Vs11,R11.R10.R?.R>.)VF,(25.&40.+9;>8<.)Vfc,(3>.(3.&40.))R24.(3?.$46.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH1 HXS1 PCH1 HYS1 PBY1 OX1 OY1 FR1 ST1 MI1 HP1 HnY ZY. assert (TI : trim_i ys 1) by (left; reflexivity).
      (* [comment removed for export] *)
      eapply (tail_i m1 1); try eassumption.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      all: clear - HnY; lia.   (* [comment removed for export] *) (* [comment removed for export] *)
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Tail.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00n0@C17025492443.169C62520918539.170D15994190938.171D16043977870.171D50796826103.171D51167340607.139D5483425282.139 D563007111.140  D62012212072.171D62022258533.140K22413380088.170K3634076879.170 K6379668000.169 L14583701847.8  L18779735146.3  L20666177036.7  L21044925120.5  L21845917367.14 L21847519070.3  L22401653661.3  L2340205082.10  L24579960702.2  L27213746399.14 L27216806327.4  L29428324939.5  L34145086486.4  L35511548052.2  L35653441506.7  L3629223086.3   L39376392229.2  L40280805793.0  L4296725181.7   L47542916419.3  L48288935062.2  L50790580594.6  L55802464936.14 L55805087656.1  L57737878429.4  L60098763854.3  L6384586821.2   L64372451842.1  L8265267294.0   L919506048.7    N21806751459.170N22834764276.170N37104593031.170O17025492443.169O5739683649.169 O57399310481.170O62520918539.170O7131117660.170 P18783404774.170P34158132851.169P3634076879.170 P6379668000.169 Q22155430506.171Q32737234924.171Q38248387216.171Q42252534537.151Q43879899724.171Q60498968964.171Q64360393870.17100000100200300400e01601G01`02302F02Y02Z02[03203303403503J03K03L03M03T03d03e04704804904Q04R04Y04Z04[04g04n05E05T05U05V05`05a05e05f06=06P06Q06d06e06f06g06h06i07S08308408508B08R08\09D09Q09j0:4FFFFS1R5NEEDR2sp1X2pX2xs1Y2ys2lo3LOS3SLO3SPR2X02Y02B0S2sp1X2pX2xs1Y2ysS2sp1X2pX2xs1Y2ysS1R3HIA1h2sp1X2pX2xs1Y2ysS1R2sp1X2pX2xs1Y2ysS1R2sp1X2pX2xs1Y2ysS2sp1X2xs2ys2lo3DSXFFS2sp1X2nX2pX2lo3DXP3DSXFFFS1R2sp2lo3SLO3NRA3SPRFFFS2nX2pXS1R3HIA1h2sp3TOPFS1R2lo3LOS3ALO3ACPFFS1R3HIA1h2sp2lo3TOP4HTOPFS2nX2N1SFS2nX2xs4LENXS2sp2loS1R5NEEDR2sp2lo3LOS3SLOS2sp2nX3SPR3NRXFFS1R2lo3LOSFS2pXSS1R2nX2pX2lo3LOS3ALO2BCS2sp2xs2ys2lo3x151CFS2sp2xs2ys2lo3x151CFFFFFS1R5NEEDR2sp2nX2pX2xs2ys2lo3LOS3SLO3ALO2BCS1R2sp2nX2pX2xs2ys2lo3LOS3ALO2BCFFS2nX2pX2xs2ysS2nX2pX2xs2ys2N1S2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3LOS3SLO3ALO3SPR2H0S2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS2pX2xs2ys". (* [comment removed for export] *)
  Lemma zero_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pjk,(1.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxs9,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,R19.)P,(=.$8.VnY,=)P,(20.+1.VnX,)P,(=.$>.VownX,$19.)P,(50.$46.R1=.VX,(51.$52.(53.(25.&40.VpX,))(51.$52.(75.(25.&40.VsgX,))(51.$52.(75.(25.&40.VnX,))(51.$52.(76.VpadX,)(54.$52.))))))P,(5<.$46.R1>.VpX,Vxs,)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)R1?.VX,+10.)P,(77.(15.VR,)(16.$2.VLB,(17.VLF,))(13.&40.Vsp,)(1>.$46.VR,VHIA,Vh,)VX,+10.)P,(44.(20.(2>.VX,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VX,))P,(44.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(50.$46.R23.(2>.(13.&40.Vsp,)-60.)(51.$52.(7<.#8.R22.)(51.$52.(53.Vs9,)(51.$52.(53.Vs8,)(51.$52.(53.Vs7,)(51.$52.(53.Vs6,)(51.$52.(53.Vs5,)(51.$52.(53.Vs4,)(51.$52.(53.Vs3,)(51.$52.(53.Vs2,)(51.$52.(53.Vs1,)(51.$52.(53.Vs0,)(51.$52.(53.Vra,)(54.$52.))))))))))))))P,(1?.$46.R24.Vlo,(2>.(13.&40.Vsp,)-60.))P,(27.$46.R25.)(55.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)Lms',$56.(57.(3.&40.)Lx5,(3.&40.)(57.(3.&40.)Lx6,(3.&40.)(57.(3.&40.)Lx7,(3.&40.)(57.(3.&40.)La1',(3.&40.)(57.(3.&40.)La2',(3.&40.)(57.(3.&40.)La3',(3.&40.)(57.(3.&40.)La4',(3.&40.)(57.(3.&40.)La5',(3.&40.)(57.(3.&40.)La6',(3.&40.)(57.(3.&40.)La7',(3.&40.)(57.(3.&40.)Lx28,(3.&40.)(57.(3.&40.)Lx29,(3.&40.)(57.(3.&40.)Lx30,(3.&40.)(57.(3.&40.)Lx31,(3.&40.)(57.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(40.(=.$56.R10.(3<.(3=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1.(3?.$46.)))(40.(5=.(51.(48.$8.$8.)(49.$8.$8.VpX,(2>.VpX,(1;.+4.VnX,)))(51.(48.$8.$8.)(49.$8.$8.Vlo,(13.&40.Vsp,))(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))))R36.R1.)(40.(5>.$46.R36.R1.)(40.(27.$46.R1.)(40.(5<.$46.R1.VpX,(74.(3.&40.)(25.&40.=)(61.VnX,)))(40.(50.$46.R1.VX,(5;.VpX,(25.&40.+1.)VnX,VpadX,))(40.(1?.$46.R1.Vlo,(13.&40.Vsp,))(9.$46.VR,VHIA,Vh,VLB,VLF,R1.)))))))))))))))))))))))(3<.(3=.R24.(25.&40.(2>.(13.&40.Vsp,)-60.))Vgp,Vtp,R23.R22.R21.R20.R1?.(25.&40.VX,)R1>.(25.&40.VnX,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(25.&40.(62.(29.VR,)))R15.R14.R13.R12.Vs10,Vs11,R11.R10.R?.R>.)VF,(25.&40.+9;?60.)Vfc,(3>.(3.&40.))R26.(3?.$46.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH EY N1 EO HXS HXL OX CW DXP DSX FR ST MI. basic_facts h LB mc HH TOP.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    flat constr:(MAX) 2%nat. intros FLt19 _. flat constr:(FLt19) 2%nat. flclear FLt19. intros _ FLt20. flat constr:(FLt20) 5%nat. flclear FLt20. intros _ _ _ _ HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
    flat constr:(HOWN) 4%nat. flclear HOWN. intros _ HIN P16 _.
    flat constr:((hm_apart asegs R HIA h LB LF mc HH)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    assert (CWs : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X 16) by (eapply client_wrange_sp_mono; [| exact CW]; clear - LOS SLO NEEDR; lia).
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (hm_aobj_block asegs R HIA h LB LF mc pX (4 * nX) HH HIN) as OPX.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [A_ASAN_MEMSET_CP] [(0x9bf70, DJoin)] 40%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc; lx_rn_munch MU; lx_rn_wmono WM.
    rename lxm into m2.
    match goal with H : rw_cells asegs m2 X _ |- _ => pose proof (conj H I) as HXS0 end.
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp)] m2) as MUX. pose proof (wmono_refl asegs m2) as WMX.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_CP) as SPM. unfold A_ASAN_MEMSET_CP in SPM.
    callxA_sp (bv_unsigned sp + -96)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := pX) (v := 0) (n := 4 * nX) (lo := lo) (ds := u32s xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; eassumption
             | rewrite u32s_length; clear - LENX; lia
             | clear; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
             | left; clear - BC ALO LOS; lia
             | eapply (blk_top47_sub asegs R HIA h LB LF _); [exact HH| exact HIN| clear; lia]
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear; lia| clear; lia]
             | f_equal; clear; lia
             | clear - NRX LOS SLO NEEDR NRA TOP SPA SPR; lia
             | first [exact C24H | match goal with |- ?g => idtac "ZMEMSET-PRE-LEFT:" g end] ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-ZMEMSET-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 pX _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    flat constr:(HXS0) 2%nat. flclear HXS0. intros HXS2 _.
    pose proof (rw_cells_transport asegs _ m2 m5 _ _ HXS2 MUX WMX ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - DXP DSX N1; lia)) as HXS5.
    replace (Z.to_nat (4 * nX)) with (4 * Z.to_nat nX)%nat in HPZ by (clear - N1; lia).
    apply (rw_cells_of_u8arr asegs) in HPZ. pose proof (u32arr_of_cells asegs m5 pX _ _ (repeat (Z_to_bv 64 0) (Z.to_nat nX)) HPZ ltac:(symmetry; apply u32s_repeat0)) as HZ5.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [] [] 30%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    lx_post.
    all: try (unfold mpi_cells; exact HXS5).
    all: first [exact C24H | match goal with |- ?g => idtac "ZW-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L33992082665.2L59321100280.4L6998223978.1 00000700E00JS2nX2N1S2nY1l2EY4LENYS3sgY". (* [comment removed for export] *)
  Lemma post_zero : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmo,$6.Pmo',$6.Ph',(0.$46.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(=.$8.VnY,=)P,(20.+1.VnX,)P,(=.$>.VownX,$19.)P,(27.$46.R12.)P,(1?.$46.R13.Vlo,(13.&40.Vsp,))P,(6:.R17.R16.)P,(4<.$46.VR,(6;.VLB,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6=.$46.VR,VHIA,Vh,)(51.(48.$8.$8.)(49.$8.$8.VX,(2>.VX,+10.))(54.(48.$8.$8.)))Vm,R15.)P,(=.$8.(1>.$46.VR,VHIA,R17.)(1>.$46.VR,VHIA,Vh,))P,(=.$8.(6=.$46.VR,VHIA,R18.)(6=.$46.VR,VHIA,Vh,))P,(=.$8.(6>.$46.VR,VHIA,R19.)(6>.$46.VR,VHIA,Vh,))P,(:.$46.VR,VHIA,R1:.R1;.)P,Px,$8.P,(2:.$46.VR,VHIA,Vh,R1.)(2:.$46.VR,VHIA,R1=.R2.)P,(20.(2?.$46.VR,VHIA,R1<.)(2>.(2?.$46.VR,VHIA,Vh,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$46.VR,VHIA,R1=.)(2>.(33.$46.VR,VHIA,Vh,)(34.Vd,)))P,(9.$46.VR,VHIA,R1>.VLB,VLF,R1=.)P,(;.$46.R1>.VLB,(6<.VX,+1.VnX,VpX,(74.(3.&40.)(25.&40.=)(61.VnX,))VpadX,$19.))(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R22.(3;.(3<.(3=.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(25.&40.=)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(58.Vra,)Vfc,(3>.(3.&40.))R1?.(3?.$46.))R21.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros EY N1 EO MI ST MF HP HT HS HFL HK HCS HV HFR HH MA.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    unfold mpi_binop_postA. do 14 eexists. exists m', mo', h', LB, (mkMPD X 1 nX pX (repeat (Z_to_bv 64 0) (Z.to_nat nX)) padX LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [eapply mpd_out_ext; [apply mpd_out_refl; cbn [md_own]; exact NST| reflexivity| cbn [md_own]; discriminate| cbn [mpd_blk md_own md_p md_n]; rewrite EO; reflexivity]|].
    split; [cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb; left; exact Hb|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split; [| intros _; unfold copy_trim; cbn [md_n]; left; reflexivity].
    split; [| split; [reflexivity| split; [reflexivity| rewrite EO; intros b Hb; left; exact Hb]]].
    left. split; [reflexivity|]. split; [| rewrite EY; clear - N1; lia].
    unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_repeat0.
    assert (ys = []) as -> by (destruct ys; [reflexivity| exfalso; cbn in LENY; clear - LENY EY; lia]). cbn. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00k0@D60109445480.156D64311486415.156L1158059155.153 L1164172544.1   L12092711958.3  L12457983458.9  L12681606856.54 L14983166754.2  L15756354262.4  L1649577667.2   L19945316590.2  L19945831828.153L20880416051.5  L22471004326.57 L22686136688.55 L22698354369.3  L26892418956.1  L28587818745.4  L29428324939.5  L30964849631.57 L35653441506.7  L36180999398.147L38692635477.0  L38723301197.5  L38948636245.0  L38983344078.7  L39172636981.0  L39280637297.0  L40281191306.3  L4235704437.5   L43061363337.145L44435606829.1  L44829210496.3  L48132467214.7  L49982885495.66 L50493221538.57 L50664059503.12 L51326438992.3  L52825213806.4  L55532094391.10 L57256936953.5  L59308668813.3  L59310648603.3  L59335885566.2  L60098763854.3  L61282314347.4  L62018535662.1  L62155016064.3  L62624979503.50 L63612514602.3  L63619150122.3  L64056784486.2  L64194470200.2  L66343863638.5  L67080771090.2  L67082884370.53 L68294535841.2  L7424514157.9   L774765788.5    00000G00d01201501@01[01c01l02:02B02I02Z02[02c02o03803<03C03U03a04904G04H04W04X04Y04Z04[04d05405[05_05j06E06V06b07E07M07[08408508?08J08Q08[08i08l09009109;09D09L09S09g09n0:60:=0:>0:QS1R2sp1X2xs1Y2ys2lo3LOSS1R3HIA1h2sp1X2xs1Y2ys2lo3TOPS2sp1X2xs1Y2ysS1XS2nY3NRY2K1S1R4RIMG2nY2pY1A1k2AI2SL2SHS2nY3H12S2pY4HP16S1R2lo3LOS3ALOS2nX3NRXS2sp2loS2sp1X2xs1Y2ys2loFS2nX3H12S2nY3H123H13S2nY1i2HiS2spS2nY2K3S1R2lo3LOS3ALO3ACPS2nY3NRY3H16S1R3HIA1h2sp2lo3TOP4HTOPS2sp1X2xs1Y2ysSS1R3HIA1h1d3D0'SFSSS1R3HIA1hS1R3HIA1h2nY3NRYS1R5NEEDR2sp1X2xs1Y2ys2lo3SLO3SPR2X02Y0S2nYS2pY3PYp2LTS1R5NEEDR2sp2lo3LOS3SLO3ALOS1X1Y3NEQ3H123H13S2nX3NRX3H12S1R2sp2nX2pX2xs2lo3LOS3ALO4LENX3PXCS1A1k2A0S2nY3NRY2K12K3S2sp2nY2pY2ys2lo4LENY3Q5xFS2nX2K22EnS2nY2K13NYxS2pX2B0S1R2lo3LOSS2nY3NRY2K12K3S1RS2nYFS2nY2pY2SHS2nY2pY1HS2nX3NRXS1R3ACPS2nY2pY3NRY3PYp4Y47xS2nY2K3S2nY3H12S2nX2pXFS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "Pmo,$6.Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(9.$46.VR,VHIA,Vh,VLB,VLF,Vm,)P,(:.$46.VR,VHIA,Vh,R?.)P,(1?.$46.Vm,Vlo,(13.&40.Vsp,))P,(27.$46.Vm,)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)Vm,VX,+10.)P,(28.$46.(29.VR,)(2:.$46.VR,VHIA,Vh,)Vm,VY,+10.)P,(20.(2>.(2?.$46.VR,VHIA,Vh,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)))$31.)P,(20.(2>.(33.$46.VR,VHIA,Vh,)(34.Vd,))$35.)(39.$46.(3:.$46.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(72.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(6<.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(6<.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R16.)(3;.(3<.(3=.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(25.&40.VX,)(25.&40.VY,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.$7>.)Vfc,(3>.(3.&40.))Vm,(3?.$46.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo ST MI OX OY BUD BUDF. unfold A_MPI_COPY. basic_facts h LB m HH TOP.
    flat constr:(facts) 13%nat. intros XAL X0 LENX NRX SGX YAL Y0 LENY NRY SGY XB YB SXY.
    pose proof (HND _ _ _ _ HH) as ND.
    flat constr:(MAX) 2%nat. intros FLt21 _. flat constr:(FLt21) 2%nat. flclear FLt21. intros HXS FLt22. flat constr:(FLt22) 5%nat. flclear FLt22. intros _ _ _ _ HOWNX. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, HOWNX.
    flat constr:(MAY) 2%nat. intros FLt23 _. flat constr:(FLt23) 2%nat. flclear FLt23. intros HYS FLt24. flat constr:(FLt24) 5%nat. flclear FLt24. intros _ _ _ _ HOWNY. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HYS, HOWNY.
    flat constr:(XW) 2%nat. intros CW DXP0. cbn [md_addr md_own md_p md_n] in CW, DXP0.
    flat constr:(CSEP) 6%nat. intros Q1' Q2' Q3' Q4 Q5' _. cbn [md_addr md_own md_p md_n] in Q1', Q2', Q3', Q4, Q5'.
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in *.
    (* [comment removed for export] *)
    assert (PBX : 0 <= pX /\ pX + 4 * nX <= alloc_ceiling
                 /\ (ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ u32arr asegs m pX xs /\ 1 <= nX)
                 /\ (ownX = LNull -> pX = 0 /\ nX = 0)).
    { destruct ownX; [| | exfalso; exact (NST eq_refl)].
      - flat constr:(HOWNX) 2%nat. flclear HOWNX. intros E0 En. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - flat constr:(HOWNX) 4%nat. flclear HOWNX. intros N1 HIN HP16 HXL. destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    flat constr:(PBX) 4%nat. flclear PBX. intros PX0 PXC PHEAP PNULL. clear HOWNX.
    assert (YBLK : ownY = LHeap -> In (pY, 4 * nY) LB) by (intros E0; rewrite E0 in HOWNY; exact (proj1 (proj2 HOWNY))).
    assert (PBY : ownY <> LNull -> bytes_at asegs m pY (u32s ys)).
    { intros ON. destruct ownY; [exfalso; exact (ON eq_refl)| (flat constr:(HOWNY) 4%nat; flclear HOWNY; intros _ _ _ (PB & _)); exact PB| (flat constr:(HOWNY) 5%nat; flclear HOWNY; intros _ _ _ PB _); exact PB]. }
    assert (NY0 : ownY = LNull -> nY = 0) by (intros E0; rewrite E0 in HOWNY; exact (proj2 HOWNY)).
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    (* [comment removed for export] *)
    assert (Y47 : ownY <> LNull -> pY + 4 * nY + 8 <= 2^47).
    { intros ON. destruct ownY; [exfalso; exact (ON eq_refl)| |].
      - pose proof (blk_top47 asegs R HIA h LB LF m pY (4 * nY) HH (YBLK eq_refl)). clear - H. lia.
      - flat constr:(HOWNY) 5%nat. flclear HOWNY. intros N1 _ _ PB RO. flat constr:((static_limbs_low m pY nY ys PB LENY N1 RO)) 2%nat. intros _ SH. clear - SH. lia. }
    (* [comment removed for export] *)
    assert (Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y).
    { intros A k HFRA Hk. destruct (fresh_apart_client R LB LF lo Y 16 A k HFRA); [exact YCR| clear; lia| exact Hk| clear - ALO LOS; lia| right; assumption| left; assumption]. }
    assert (PYfresh : forall A k, fresh_apart R LB LF A k -> (A + k <= hl_img_lo L \/ hl_img_hi L <= A) -> 0 < k -> pY + 4 * nY <= A \/ A + k <= pY).
    { intros A k HFRA AI Hk. flat constr:(HFRA) 4%nat. intros A0 AC AD HAP. destruct ownY.
      - rewrite (proj1 HOWNY), (proj2 HOWNY). clear - A0. lia.
      - destruct (HAP pY (4 * nY) ltac:(apply in_app_iff; left; exact (YBLK eq_refl))); [right| left]; assumption.
      - flat constr:(HOWNY) 5%nat. flclear HOWNY. intros N1 _ _ PB RO. flat constr:((static_limbs_low m pY nY ys PB LENY N1 RO)) 2%nat. intros SL SH.
        clear - SL SH AI RIMG. lia. }
    assert (PYA : ownY <> LNull -> Z.land pY 3 = 0 /\ 0 < pY).
    { intros ON. change 3 with (Z.ones 2). rewrite Z.land_ones by (clear; lia). destruct ownY; [exfalso; exact (ON eq_refl)| |].
      - flat constr:(HOWNY) 4%nat. flclear HOWNY. intros _ _ HP16 _. destruct (HF _ ltac:(apply in_app_iff; left; exact (YBLK eq_refl))) as (B0 & _). cbn in B0.
        split; [replace (2 ^ 2) with 4 by reflexivity; clear - HP16; lia| exact B0].
      - flat constr:(HOWNY) 5%nat. flclear HOWNY. intros _ P4 P0 _ _. split; [exact P4| exact P0]. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS, HYS.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x9be3c] [] 30%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc; lx_rn_munch MU0; lx_rn_wmono WM0.
    rename lxm into m1.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
        [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
      eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16)] lo (bv_unsigned sp) _ m m1); [exact HH| | clear; lia| exact LOS].
      eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM0].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
      - eapply munch_weaken; [| exact MU0]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
    assert (PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)]).
    { intros E. flat constr:((PHEAP E)) 5%nat. intros B0 _ _ HXL _. apply u32arr_cells.
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PXC ALO LOS SLO NEEDR LENX; lia]. }
    assert (PBY1 : ownY <> LNull -> bytes_at asegs m1 pY (u32s ys)).
    { intros ON. eapply (bytes_at_transport asegs _ m m1); [exact (PBY ON)| exact MU0|]. rewrite u32s_length. cbn [disjoint_from].
      pose proof (Q5' ON) as Q5x. clear - Q5x LENY LO0 SLO; lia. }
    first [ apply (hm_munch asegs R HIA h LB LF [(lo, bv_unsigned sp)] m m1) in HH as HH1; [| exact MU0| exact WM0| solve_w_writable]
          | let mx := lx_cur_mem in match goal with H : HM _ _ _ _ _ _ ?my |- _ => constr_eq my mx; pose proof H as HH1 end ].   (* [comment removed for export] *)
    clear MU0 WM0.
    assert (Q3x : ownY <> LNull -> ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX).
    { intros OYN. destruct Q3' as [E|[Q|[Q|Q]]]; [exfalso; injection E; intros; exact (NEQ ltac:(assumption))| left; exact Q| exfalso; exact (OYN Q)| right; exact Q]. }
    (* [comment removed for export] *)
    lx_pre. lx_run_tac (PLAN [0x9c100; 0x9bf60; 0x9bfc0; 0x9be8c] [(0x9be68, DJoin); (0x9bf54, DJoin)] 50%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear MU WM.
    - (* [comment removed for export] *)
      exfalso. apply NEQ. klia.
    - (* [comment removed for export] *)
      assert (K1 : nY = 0) by klia. assert (K2 : nX = 0) by klia.
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply epi_walk with (hc := h) (LBc := LB) (r := 0); try eassumption
          | intros y Hy; exact Hy | ].
        intros ms' PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E ST9. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_keep mo mo9 h m1 0 sgX); try eassumption; try reflexivity.
        + intros y Hy; exact Hy.
        + unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
        + unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
        + eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| exact PNULL|].
          intros E. flat constr:((PHEAP E)) 5%nat. intros B0 HIN HP16 _ N1. split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH1 E)| reflexivity].
        + right. split; [reflexivity|]. split; [exact K2| exact K1].
    - (* [comment removed for export] *)
      assert (K1 : nY = 0) by klia. assert (K2 : nX <> 0) by klia.
        assert (EO : ownX = LHeap) by (destruct ownX; [exfalso; (flat constr:((PNULL eq_refl)) 2%nat; intros _ En); clear - En K2; lia| reflexivity| exfalso; exact (NST eq_refl)]).
        flat constr:((PHEAP EO)) 5%nat. intros B0 HIN HP16 _ N1.
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply (zero_walk m1); try eassumption; try exact EO
          | intros y Hy; exact Hy | ].
        all: try (eapply (u32arr_of_cells asegs); [exact (PCH1 EO)| reflexivity]).
        all: try exact (DXP0 EO).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "ZW-PRE-LEFT:" g end.
        intros ms' PO. flat constr:(PO) 23%nat. flclear PO. intros y5 y6 y7 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 m9 E9 MU9 WM9 MI9 HA9 HX9 ST9 HH9. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_zero mo mo9 h m9); try eassumption; try reflexivity.
        + eapply presA_trans; [exact HP1|].
          apply (munch_weaken _ [(lo, bv_unsigned sp); (pX, pX + 4 * nX); (X, X + 16)]) in MU9; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
          eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] pX (4 * nX) m1 m1 m9);
            [exact HH1| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
          { intros b xb Hb Hr. split; [eapply In_mpd_keep; exact Hb|]. intros E. subst b.
            exact (lb_remove_notin LB pX (4 * nX) ND (in_keep_remove LB dX _ ND EO HIN Hb)). }
          eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (X, X + 16)]);
            [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
          eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m1 m1 m9); [exact HH1| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH1| | exact Hc]; clear; lia | exact MU9 | exact WM9].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (pX + 4 * nX - pX) with (4 * nX) by (clear; lia); eapply aobj_crange; eapply hm_aobj_block; [exact HH1| exact HIN]|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil.
        + intros y Hy; exact Hy.
        + unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
        + unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
        + eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| rewrite repeat_length; clear - NRX; lia| unfold MPI_MAX_LIMBS; clear - NRX; lia| left; reflexivity| intros E; discriminate E|].
          intros _. split; [exact N1|]. split; [exact HIN|]. split; [exact HP16| exact HA9].
    - (* [comment removed for export] *)
      assert (K1 : nY <> 0) by klia. assert (K3 : nY <> 1) by klia.
      assert (OYN : ownY <> LNull) by (intros E0; pose proof (NY0 E0) as NYx; clear - NYx K1; lia). specialize (Q3x OYN).
      (* [comment removed for export] *)
      replace (Z.shiftr (4294967296 * nY + -4294967296) 32) with (nY - 1) by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - K1 NRY; lia).
      destruct (PYA OYN) as [PYl PYp]. rewrite PYl.
      replace (Z.b2z (0 <? zlow 64 pY)) with 1 by (unfold zlow; pose proof (Y47 OYN) as Y47x; rewrite Z.mod_small by (clear - PYp Y47x NRY; lia); destruct (Z.ltb_spec 0 pY) as [LT|LT]; [reflexivity| clear - PYp LT; lia]).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply (scan_loop (Z.to_nat (nY - 1)) (nY - 1) m1); try eassumption
        | intros y Hy; exact Hy | ].
      all: try (clear - K1 K3 NRY; lia).
      all: try (replace (nY - 1 + 1) with nY by (clear; lia); apply zeros_above_all; exact LENY).
      all: try (exact (PBY1 OYN)).
      all: try (eapply opy_at; [exact HH1| exact YBLK| exact OYN]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "SC-PRE-LEFT:" g end.
      intros ms' PO. destruct PO as (i & xt0' & xt1' & [(E & Hi & Zi & Ti)|(E & Hi & Zi)]); subst ms'.
      + eapply tail_i with (mo := mo) (m1 := m1) (i := i); try eassumption.
        all: try exact (Q1' OYN). all: try exact (Q5' OYN). all: try exact (Y47 OYN).
        all: try exact (PBY1 OYN). all: try (clear - Hi; lia).
        all: first [exact C24H | match goal with |- ?g => idtac "TIA-LEFT:" g end].
      + subst i. eapply tail_1 with (mo := mo) (m1 := m1); try eassumption.
        all: try exact (Q1' OYN). all: try exact (Q5' OYN). all: try exact (Y47 OYN).
        all: try exact (PBY1 OYN). all: try (clear - K1 NRY; lia).
        all: first [exact C24H | match goal with |- ?g => idtac "T1A-LEFT:" g end].
    - (* [comment removed for export] *)
      assert (K3 : nY = 1) by klia. assert (K1 : nY <> 0) by (clear - K3; lia).
      assert (OYN : ownY <> LNull) by (intros E0; pose proof (NY0 E0) as NYx; clear - NYx K1; lia). specialize (Q3x OYN).
      replace (Z.shiftr (4294967296 * nY + -4294967296) 32) with (nY - 1) by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - K1 NRY; lia).
      eapply tail_i with (mo := mo) (m1 := m1) (i := nY); try eassumption.
      all: try exact (Q1' OYN). all: try exact (Q5' OYN). all: try exact (Y47 OYN).
      all: try exact (PBY1 OYN). all: try (clear - K1 K3 NRY; lia).
      all: try (apply zeros_above_all; exact LENY).
      all: try (left; exact K3).
      all: first [exact C24H | match goal with |- ?g => idtac "TIB-LEFT:" g end].
    all: first [exact C24H | match goal with |- ?g => idtac "MAIN-LEFT:" g end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@D50792841960.116D51169404332.116D5485552529.116 D60096647504.116D64315731959.116L14069479286.2  L1649577667.2   L29428324939.5  L35653441506.7  L36180999398.113L38723301197.5  L38948636245.0  L4235704438.5   L43061363337.111L59310763256.4  L60098763854.3  L68472728715.14 L774765788.5    00000Y00h01701O01m02102902K02c03503D03E03U04=04K04U05<05OS1R5NEEDR2ra2sp1X2pX2xs2lo3LOS3SLO3SPR2X0S2ra2sp1X2pX2xsS2ra2sp1X2pX2xsS1R2ra2sp1X2pX2xs2lo3LOSS1R3HIA1h2ra2sp1X2pX2xs2lo3TOPS2nXS2nX3NRXS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X2pX2xs2XBS1R3HIA1h1d3D0'SS1R3HIA1h2nX3NRXS1R5NEEDR2ra2sp1X2pX2xs2lo3SLO3SPR2X02XBS1X1Y4SEP'3EXYS1R2lo3LOSS1R2sp1X2nX2pX2xs2lo3LOS3ALO4LENX2BC2DqS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
Lemma A_mpi_copy_spec_x_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PR,$7?.PHIA,(80.$46.R1.)P,(81.(29.R2.))P,(82.$46.R3.R2.$83.)P,(=.$8.(84.R4.)$85.)P,(=.$8.(86.R5.)$87.)P,(=.$8.(88.R6.)$89.)P,(20.=(23.R7.))P,Ph,(0.$46.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$46.R<.R;.R4.R3.R2.R1.)(8:.$8.(8;.(48.$8.$8.)$8.(8<.$8.$8.)R4.))P,(40.(20.(78.(15.R9.))(8=.(15.R9.)))(20.(8>.(15.R9.))(79.(15.R9.))))P,(40.(20.(78.(15.R:.))+10000.)(20.+?1000.(79.(15.R:.))))(8?.$46.R;.R:.$7>.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG ZF CAL AMC AMS NEEDR HND DIMG RIMG. unfold mpi_copy_stmtA_x_c, mpi_copy_stmtA_gen_c.
  intros until d. intros HH HK MX NST MY SEP CSEP YCR YLCR XW ST LOS SLO TOP SPA TPV MI RA2 OX OY YNZ BUD XUW BUDF C24H -> ->.
  destruct dX as [X sgX nX pX xs padX ownX]. destruct dY as [Y sgY nY pY ys padY ownY].
  unfold A_MPI_COPY. pose (lxi := lxA_img (arl_AL R) IMG).
  cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
  destruct (Z.eq_dec X Y) as [EXY|NEQ].
  - (* [comment removed for export] *)
    assert (E : mkMPD X sgX nX pX xs padX ownX = mkMPD Y sgY nY pY ys padY ownY).
    { destruct SEP as [E|SEP']; [exact E|]. exfalso. cbn [md_addr] in SEP'. clear - SEP' EXY. lia. }
    rewrite <- E. rewrite <- EXY in OY |- *. clear E EXY MY YCR YLCR YNZ CSEP SEP.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (art_lo asegs R HIA) as ALO. pose proof (@alloc_ceiling_pos (arl_L R)) as ACP.
    pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    flat constr:(MX) 2%nat. intros FLt25 SGX. flat constr:(FLt25) 2%nat. flclear FLt25. intros HXS FLt26. flat constr:(FLt26) 5%nat. flclear FLt26. intros XAL X0 LENX NRX HOWN. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, XAL, X0, LENX, NRX, HOWN, SGX.
    unfold MPI_MAX_LIMBS in NRX. unfold mpi_cells in HXS.
    pose proof (rw_cells_bound _ _ _ _ HXS) as XB. cbn [cells_size csize Nat.add] in XB.
    flat constr:(XW) 2%nat. intros CW DXP0. cbn [md_addr md_own md_p md_n] in CW, DXP0.
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HF _. rewrite Forall_forall in HF.
    assert (PXC : ownX = LHeap -> pX + 4 * nX <= @alloc_ceiling (arl_L R)).
    { intros E0. rewrite E0 in HOWN. flat constr:(HOWN) 3%nat. flclear HOWN. intros _ HIN _. destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (_ & _ & BC & _). exact BC. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc; lx_rn_munch MU0; lx_rn_wmono WM0.
    rename lxm into m1. try clear ST. match goal with STq : stk _ m1 lo _ |- _ => rename STq into ST end.
    first [ apply (hm_munch asegs R HIA h LB LF [(lo, bv_unsigned sp); (X, X + 16)] m m1) in HH; [| exact MU0| exact WM0| solve_w_writable]
          | let mx := lx_cur_mem in lazymatch type of HH with HM _ _ _ _ _ _ ?my => constr_eq my mx end
          | let mx := lx_cur_mem in match goal with H : HM _ _ _ _ _ _ ?my |- _ => constr_eq my mx; clear HH; rename H into HH end ].   (* [comment removed for export] *)
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA. do 14 eexists. exists m1, mo9, h, LB, (mkMPD X sgX nX pX xs padX ownX), 0.
    split; [reflexivity|]. split; [assumption|]. split; [exact ST|]. split; [exact MF9|].
    split; [eapply (presA_tail asegs R HIA h LB); [exact HH| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact OX| exact MU0| exact WM0]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [intros y Hy; exact Hy|].
    split; [unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]; clear - NRX; lia|].
    split; [unfold copy_FR, calls_FR, fr_charge; pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'; clear - D0'; lia|].
    split; [assumption|].
    split.
    { eapply mpd_at_rebuild; [exact NST| | exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| |].
      - unfold mpi_cells. first [exact HXS | eapply (rw_cells_transport asegs _ m m1); [exact HXS| exact MU0| exact WM0| cbn [disjoint_from cells_size csize Nat.add]; clear - DSX XB; lia]].
      - intros E0. rewrite E0 in HOWN. exact HOWN.
      - intros E0. pose proof (PXC E0) as BC. rewrite E0 in HOWN. flat constr:(HOWN) 4%nat. flclear HOWN. intros N1 HIN HP16 HXL.
        split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
        eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0|]. cbn [disjoint_from]. pose proof (DXP0 E0) as Dq. clear - Dq BC ALO LOS SLO NEEDR LENX; lia. }
    split; [apply mpd_out_refl; cbn [md_own]; exact NST|].
    split; [intros b Hb; left; exact Hb|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split; [| intros _; unfold copy_trim; cbn [md_n]; left; reflexivity].
    split; [left; split; [reflexivity| split; [reflexivity| clear - NRX; lia]]|].
    split; [reflexivity|]. split; [reflexivity|]. intros b Hb; left; exact Hb.
  - eapply main_walk; try eassumption.
    all: first [exact C24H | match goal with |- ?g => idtac "SPECX-LEFT:" g end].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma A_mpi_copy_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PR,$7?.PHIA,(80.$46.R1.)P,(81.(29.R2.))P,(82.$46.R3.R2.$83.)P,(=.$8.(84.R4.)$85.)P,(=.$8.(86.R5.)$87.)P,(=.$8.(88.R6.)$89.)P,(20.=(23.R7.))P,Ph,(0.$46.R8.R7.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$46.R<.R;.R4.R3.R2.R1.)(8:.$8.(8;.(48.$8.$8.)$8.(8<.$8.$8.)R4.))P,(40.(20.(78.(15.R9.))(8=.(15.R9.)))(20.(8>.(15.R9.))(79.(15.R9.))))P,(40.(20.(78.(15.R:.))+10000.)(20.+?1000.(79.(15.R:.))))(90.$46.R;.R:.$7>.)")
(* [comment removed for export] *).
Proof. intros. apply mpi_copy_stmtA_of_x. eapply A_mpi_copy_spec_x_c; eassumption. Qed.

(* [comment removed for export] *)
Lemma A_mpi_copy_spec_closed_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy_c24 ()) "PR,$7?.PHIA,(80.$46.R1.)P,(81.(29.R2.))P,(=.$8.(91.R3.)$92.)P,(=.$8.(93.R4.)$94.)P,(=.$8.(84.R5.)$85.)P,(=.$8.(86.R6.)$87.)P,(=.$8.(88.R7.)$89.)P,Pm,P,(3.&40.)(5.(3.&8.))P,(95.R9.R1.)(96.R2.)P,(20.=(97.R9.))P,(20.=(98.R:.))P,(20.=(23.R;.))P,Ph,(0.$46.R<.R;.)PLB,(1.$2.)PLF,(1.$2.)Pm,P,(3.&40.)(5.(3.&8.))P,(9.$46.R10.R?.R4.R3.R2.R1.)(8:.$8.(8;.(48.$8.$8.)$8.(8<.$8.$8.)R4.))P,(40.(20.(78.(15.R=.))(8=.(15.R=.)))(20.(8>.(15.R=.))(79.(15.R=.))))P,(40.(20.(78.(15.R>.))+10000.)(20.+?1000.(79.(15.R>.))))(90.$46.R?.R>.$7>.)")
(* [comment removed for export] *).
Proof.
  intros. eapply A_mpi_copy_spec_c; eauto. eapply A_zeroize_and_free_spec; eauto.
Qed.

