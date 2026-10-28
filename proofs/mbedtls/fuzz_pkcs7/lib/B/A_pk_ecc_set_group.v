(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_mul_mod P_ecp_check_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_oid A_pk_defs A_pk_type.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0026359038e0036f 0 7 0 1 44 1 70 1 81 1 83 1 87 1 88 1P0037ce4b3551b543 0 7 0 1 44 1 70 1 81 1 83 1 87 1 88 1P008c2e6cc2d13683 0 4 0 1 49 1 60 1 61 1P0091f977eab7aad2 0 5 0 1 66 1 75 1 76 1 77 1P01a0f8fcf37504aa 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P01c2996d97e6ab1a 1 1 64 2 9 1 88 1 3 0 1 89 1 90 64P01c57ebe457da068 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P01def8edad5c117d 1 2 32 3 0 1 88 1 91 1 32 3 1 1 89 1 90 1 2 92 2 93 2P022495bbee31fdaf 0 3 0 1 41 1 74 1P02428a989eb87c53 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P03d9225817589414 0 6 0 1 45 1 50 1 52 1 60 1 61 1P04a920b593255812 0 7 0 1 44 1 67 1 78 1 80 1 84 1 85 1P04d5f75acbf58097 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P04e4b1f259064b62 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P04f06727c9d9e941 2 82 2 81 1 1 8 3 3 1 87 1 90 1 8 0 1 47 1 70 1 81 1 83 1 88 1 89 1 91 8 1 1 8 3 2 1 88 1 89 1 5 0 1 46 1 87 1 90 1 91 8 1 1 8 3 2 1 86 1 89 1 11 0 1 46 1 66 1 69 1 71 1 80 1 81 1 82 1 87 1 88 1 90 8P0511183e62a09e66 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P054b7a3456333f0c 0 3 0 1 41 1 74 1P056b5a8a33ae68eb 0 5 0 1 66 1 75 1 76 1 77 1P058934199589dee9 0 4 0 1 29 1 81 1 82 1P058f575bce69a195 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P05956fd797ad5bed 1 2 32 3 0 1 89 1 92 1 32 3 1 1 90 1 91 1 2 93 2 94 2P060107e3a4516b44 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P0661953051f13f4e 0 8 0 1 44 1 67 1 78 1 79 1 80 1 84 1 85 1P069c311f954e65c0 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P06f5f74e9ed0decb 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P072512a175865140 0 3 0 1 41 1 74 1P072acd0fd8ba2316 0 3 0 1 41 1 62 1P07a5e6888df44d61 1 2 32 3 0 1 84 1 87 1 32 9 44 1 64 1 67 1 69 1 78 1 79 1 80 1 85 1 86 1 2 88 1 89 1P07d2510d37de7787 0 6 0 1 45 1 50 1 52 1 60 1 61 1P07db3405ad5f7133 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P07e958bd93b7546f 0 7 0 1 45 1 73 1 78 1 80 1 88 1 89 1P07eb3fc8a51574c0 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P081c90bd774cc955 1 2 32 3 0 1 84 1 87 1 32 9 44 1 64 1 67 1 69 1 78 1 79 1 80 1 85 1 86 1 2 88 1 89 1P083fc0361eab5c2b 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P08e273e8e41a5431 0 5 0 1 66 1 75 1 76 1 77 1P091c3b7574b55c47 0 9 0 1 65 1 68 1 70 1 79 1 80 1 81 1 85 1 86 1P0927e8ef78abeee8 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P09530641443dd75c 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P09b87477e68059e2 0 3 0 1 41 1 74 1P09c92f2ddf393986 1 2 32 3 0 1 89 1 92 1 32 3 1 1 90 1 91 1 2 93 2 94 2P09fa2b5e30605c93 0 6 0 1 45 1 50 1 52 1 60 1 61 1P0a4ad055a524b664 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P0a511a942d048dbd 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P0ad69dc3ae547397 0 6 0 1 45 1 50 1 52 1 60 1 61 1P0b16c04efcdd94d8 0 4 0 1 49 1 60 1 61 1P0b712d39f6c1ac57 0 4 0 1 43 1 87 1 88 1P0b9f597604e4b63e 1 1 16 3 0 1 89 1 90 1 9 50 1 73 1 75 1 78 1 79 1 80 1 88 1 91 1 92 16P0bd31cf20f243c10 0 7 0 1 44 1 67 1 78 1 80 1 84 1 85 1P0bfb408a42fb89aa 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P0c2d1732fd4cee42 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P0c54c594e1606701 0 4 0 1 49 1 60 1 61 1P0c6d9f1723cac964 0 6 0 1 43 1 75 1 77 1 84 1 85 1P0cdc1b05827b7c30 0 4 0 16 3 16 60 16 61 16P0d0a210a339122cc 0 2 0 1 62 1P0d9a1c07da3f5a0a 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P0dc04fbe00d0d1e7 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P0dc3d5e91e69a8de 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P0f24f9f868c289bc 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P0f45dbc6dff97d74 0 4 0 1 49 1 60 1 61 1P0f492c05375a341f 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P1017957f5707b013 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P10d898ffc7cb7758 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P10ef0fcfd50f0252 0 5 0 1 66 1 75 1 76 1 77 1P10f20bc340ec7f88 0 4 0 1 49 1 60 1 61 1P1187fc16b239f7f3 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P11f64331c89f8609 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P122c5295c120a7f7 1 1 16 2 0 1 60 1 3 4 1 61 1 62 16P123472c3e6a42bc4 0 4 0 1 43 1 87 1 88 1P1293c1f11a511621 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P12e2e3f8277a91a7 0 4 0 1 49 1 60 1 61 1P12e8a3b1e971e7c7 0 4 0 1 29 1 81 1 82 1P130074d942dd8e85 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P131bc612ae73474b 0 7 0 1 30 1 66 1 75 1 77 1 81 1 82 1P13320a4565c9e781 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P13f89f74e3069629 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P14e1242bcfe30946 0 4 0 1 44 1 85 1 86 1P150273cc9c2322a4 0 6 0 1 45 1 50 1 52 1 60 1 61 1P1527eef6aa4e5310 0 4 0 1 49 1 60 1 61 1P1529301f06b4703c 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P1533d3ba4650b80b 1 2 32 3 0 1 88 1 91 1 32 3 1 1 89 1 90 1 2 92 2 93 2P1553800c52810c7b 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P15705fe28705959f 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P1613d1b9935decba 0 2 0 1 61 1P16ad0a5d845e5898 0 3 0 1 38 1 40 1P16db4f832e56e54a 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P17361b96d93b6194 0 5 0 1 66 1 75 1 76 1 77 1P1743f768d78ef6f2 0 4 0 1 29 1 81 1 82 1P17a15639191c5d31 0 3 0 1 41 1 74 1P17a3c04dc969cbb4 1 2 32 3 0 1 87 1 90 1 32 9 44 1 67 1 70 1 72 1 81 1 82 1 83 1 88 1 89 1 2 91 1 92 1P17ed65eadd7c3809 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P183fa667af9e228f 0 6 0 1 45 1 50 1 52 1 60 1 61 1P184b386576ac85ae 0 4 0 1 43 1 89 1 90 1P18800e37291d0122 0 6 0 1 45 1 50 1 52 1 60 1 61 1P1883d64cf8b67b06 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P18ad9da95dc79d4c 0 7 0 1 44 1 72 1 83 1 85 1 89 1 90 1P18fc61c0da8cd1b4 0 3 0 1 41 1 74 1P18fda3b310edb2fa 1 1 64 2 1 1 69 1 3 0 1 70 1 71 64P1972bf0c689f5123 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P199a0dafaa25c40c 1 2 32 3 1 1 85 1 88 1 32 9 45 1 65 1 68 1 70 1 79 1 80 1 81 1 86 1 87 1 2 89 1 90 1P19b7b3f34fb9aa4c 0 6 0 1 45 1 50 1 52 1 60 1 61 1P1a9cbfab894a92a8 0 4 0 1 49 1 60 1 61 1P1abed0583504aa27 0 9 0 1 64 1 67 1 69 1 78 1 79 1 80 1 84 1 85 1P1b14604b83199c41 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P1b19cf3e0fc843e8 0 9 0 1 65 1 68 1 70 1 79 1 80 1 81 1 85 1 86 1P1b5f179cd40a66cd 0 2 0 1 61 1P1b651806c55bfe4e 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P1b96ea394400ae32 0 6 0 1 29 1 41 1 62 1 69 1 70 1P1bf61257e04f72e3 0 9 0 1 51 1 55 1 57 1 64 1 65 1 66 1 70 1 71 1P1c74814fdf71cd9d 1 2 32 3 0 1 84 1 87 1 32 9 44 1 64 1 67 1 69 1 78 1 79 1 80 1 85 1 86 1 2 88 1 89 1P1c775c660af67e9b 0 4 0 1 44 1 85 1 86 1P1c7fdb9a51a82e58 0 3 0 1 41 1 74 1P1c8a9c58b2e25d61 0 4 0 1 72 1 83 1 85 1P1c92e8e1cad6d95f 1 1 16 3 0 1 90 1 91 1 9 51 1 74 1 76 1 79 1 80 1 81 1 89 1 92 1 93 16P1dafb0e8f479f59b 1 1 8 3 1 1 85 1 88 1 10 45 4 68 4 70 4 71 4 79 4 80 4 81 4 86 4 87 4 89 32P1e513d8dbb2034e6 1 1 8 3 1 1 85 1 88 1 10 45 4 68 4 70 4 71 4 79 4 80 4 81 4 86 4 87 4 89 32P1e8874fe1fc877b7 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P1ebe22f6a44d6f8c 0 6 0 1 45 1 50 1 52 1 60 1 61 1P1ede543b0361c692 0 4 0 1 49 1 60 1 61 1P1f11dab57f43d066 1 1 16 3 0 1 90 1 91 1 9 51 1 74 1 76 1 79 1 80 1 81 1 89 1 92 1 93 16P1f22dad798c3bf94 1 2 32 3 0 1 88 1 91 1 32 9 45 1 50 1 73 1 75 1 78 1 79 1 80 1 89 1 90 1 2 92 2 93 2P1fa306c2081a0ea5 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P1fc954e8a964a2ec 0 3 0 1 41 1 74 1P2021f701cd4030a4 0 9 0 1 69 1 72 1 74 1 83 1 84 1 85 1 89 1 90 1P20774374fede7b6a 0 5 0 1 66 1 75 1 76 1 77 1P20b2656833dc6c2a 1 1 8 2 0 1 84 1 3 42 1 85 1 86 8P20b44822abea44a0 0 3 0 1 41 1 74 1P210e8ba41682163a 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P2155565708ff3abc 0 4 0 1 43 1 89 1 90 1P215dcc79bed06c1c 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P228ba1ff05fae7f8 0 3 0 1 41 1 45 1P22b5a7bb7d714625 1 1 16 3 0 1 89 1 90 1 4 64 2 88 2 91 2 92 32P22c6dd1130270aaf 0 4 0 1 49 1 60 1 61 1P22e2c5bbea25e6dc 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P22f82ea41c352595 0 6 0 1 29 1 41 1 62 1 69 1 70 1P2418ab29b3a27b1e 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P2474ef7c033caf0b 0 9 0 1 68 1 71 1 73 1 82 1 83 1 84 1 88 1 89 1P24aa384d498ad51f 1 2 32 3 0 1 70 1 73 1 32 3 1 1 71 1 72 1 2 74 2 75 2P24e521276dc8c8a4 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P24e6845f9c0f6348 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P25209deafd1fd872 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P259c24283c345e34 0 5 0 1 66 1 75 1 76 1 77 1P25c57fc56e8f4690 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P25ebf170d4fb3231 1 2 32 3 0 1 84 1 87 1 32 9 44 1 64 1 67 1 69 1 78 1 79 1 80 1 85 1 86 1 2 88 1 89 1P261db41d8f0d9e03 0 4 0 1 43 1 84 1 85 1P2642308654451647 0 4 0 1 49 1 60 1 61 1P26965314bb12c78f 1 1 16 3 0 1 89 1 90 1 4 64 2 88 2 91 2 92 32P276b3b1112955a83 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P288c67c60a936a10 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P28b534c490bf53a5 0 4 0 1 70 1 81 1 83 1P28e8a3d4dc2865b4 0 5 0 1 66 1 75 1 76 1 77 1P29279875199e06fd 1 2 32 3 0 1 88 1 91 1 32 3 1 1 89 1 90 1 2 92 2 93 2P292fb8743100f745 0 4 0 1 43 1 84 1 85 1P29668e777a558697 0 6 0 1 45 1 50 1 52 1 60 1 61 1P299cc7e1df0da902 0 3 0 1 41 1 74 1P29b3b132a8ae5ecb 0 5 0 1 66 1 75 1 76 1 77 1P2a4d590424a444e7 0 5 0 1 66 1 75 1 76 1 77 1P2a79a6784f8bbcf1 1 2 32 3 0 1 70 1 73 1 32 3 1 1 71 1 72 1 2 74 2 75 2P2ad55d9ce8405236 0 4 0 1 29 1 81 1 82 1P2ae37d9802e96a64 1 1 64 2 51 1 70 1 3 0 1 69 1 71 64P2aed1849468d54ac 0 3 0 1 41 1 74 1P2b2cfc0bb8937564 0 5 0 1 66 1 75 1 76 1 77 1P2b631492a05aac1c 1 2 32 3 0 1 89 1 92 1 32 3 1 1 90 1 91 1 2 93 2 94 2P2c26bca3f6d9d79a 0 4 0 8 16 8 89 8 90 8P2c4549ebde31b707 0 5 0 1 54 1 63 1 64 1 65 1P2cb175487fd7ebc4 0 6 0 1 43 1 75 1 77 1 84 1 85 1P2d4d1b5b9a69724e 1 2 32 3 0 1 89 1 92 1 32 9 44 1 69 1 72 1 74 1 83 1 84 1 85 1 90 1 91 1 2 93 1 94 1P2d73fcacd6ca8583 1 1 16 2 1 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P2d9b76d9208271ce 0 4 0 1 49 1 60 1 61 1P2da353496617474b 0 9 0 1 67 1 70 1 72 1 81 1 82 1 83 1 87 1 88 1P2e415ac747fa975a 0 4 0 1 29 1 81 1 82 1P2e6bc5daa9824e82 0 4 0 1 49 1 60 1 61 1P2e84b41c9ffe47a8 0 6 0 1 73 1 78 1 80 1 88 1 89 1P2ed45d1fd5608b5c 1 2 32 3 0 1 89 1 92 1 32 3 1 1 90 1 91 1 2 93 2 94 2P2fad159fd9536dbe 0 9 0 1 68 1 71 1 73 1 82 1 83 1 84 1 88 1 89 1P2fbdeb65f198dff4 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P300ee3b942db4e7a 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P30323aab7d246846 0 4 0 1 67 1 78 1 80 1P30753836fc46d4bc 1 2 32 3 0 1 89 1 92 1 32 3 1 1 90 1 91 1 2 93 2 94 2P308081f190c97d0e 1 2 32 3 0 1 89 1 92 1 32 9 46 1 51 1 74 1 76 1 79 1 80 1 81 1 90 1 91 1 2 93 2 94 2P30905e7e0310cddc 0 2 0 1 29 1P3122f3f234097427 2 82 2 81 1 1 8 3 3 1 87 1 90 1 8 0 1 47 1 70 1 81 1 83 1 88 1 89 1 91 8 1 1 8 3 2 1 88 1 89 1 5 0 1 46 1 87 1 90 1 91 8 1 1 8 3 2 1 86 1 89 1 11 0 1 46 1 66 1 69 1 71 1 80 1 81 1 82 1 87 1 88 1 90 8P313ee6e18e69331e 0 5 0 1 66 1 75 1 76 1 77 1P319adacf2d0f2522 0 5 0 1 66 1 75 1 76 1 77 1P325bc595db9a37ad 1 1 16 3 0 1 90 1 91 1 9 51 1 74 1 76 1 79 1 80 1 81 1 89 1 92 1 93 16P328349fafc3dd8c1 0 8 0 1 44 1 67 1 78 1 79 1 80 1 84 1 85 1P32d63148e576859f 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P3381748ab3c0642c 1 2 8 2 0 1 89 1 8 2 76 1 90 1 2 91 1 92 1P339706319d4aa9f6 0 6 0 1 45 1 50 1 52 1 60 1 61 1P33cf1956e56e15bf 0 4 0 1 29 1 81 1 82 1P34f0a2c84b9c755b 0 4 0 8 41 8 84 8 85 8P35225faedf672a5d 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P3627468263a7d4d6 1 1 16 4 1 1 35 1 37 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P36662e1ebff795f3 1 2 32 3 0 1 87 1 90 1 32 9 44 1 67 1 70 1 72 1 81 1 82 1 83 1 88 1 89 1 2 91 1 92 1P366cda0150f3e53f 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2P36da90a0f7cec145 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P37e383fbb21f7c3d 1 2 16 3 1 1 33 1 61 1 16 3 0 1 34 1 62 1 2 63 1 64 1P38af3ed671bc07d0 1 2 32 3 0 1 88 1 91 1 32 3 1 1 89 1 90 1 2 92 2 93 2P38e2868b2b0d9367 0 8 0 1 30 1 54 1 63 1 64 1 65 1 69 1 70 1P3915676c855d89e7 1 1 64 2 0 1 69 1 3 2 1 70 1 71 64P39256fc9528708de 0 6 0 1 45 1 50 1 52 1 60 1 61 1P393d1aa66ac58182 0 4 0 1 49 1 60 1 61 1P39880b0b71146301 1 2 32 3 0 1 89 1 92 1 32 9 44 1 69 1 72 1 74 1 83 1 84 1 85 1 90 1 91 1 2 93 1 94 1P3a83b7b5c4cff223 1 2 32 3 0 1 85 1 88 1 32 3 1 1 86 1 87 1 2 89 2 90 2P3ab1662214b04e0a 0 2 0 1 62 1P3ad44fe9680f2a3c 0 6 0 1 45 1 50 1 52 1 60 1 61 1P3af1c13e5d5a1c0c 0 7 0 1 45 1 73 1 78 1 80 1 88 1 89 1P3af6e08649cd80dd 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P3b04f6cfc48d1be0 0 3 0 1 41 1 74 1P3b37ad9ea8c0caa1 0 8 0 1 30 1 54 1 63 1 64 1 65 1 69 1 70 1P3bdf38808978dafd 1 1 16 3 1 1 33 1 61 1 8 40 1 46 1 48 1 51 1 52 1 53 1 62 1 63 16P3c2cda2f8e123bb0 0 2 0 1 76 1P3c4729dc359e5f3c 1 2 32 3 0 1 88 1 91 1 32 9 45 1 50 1 73 1 75 1 78 1 79 1 80 1 89 1 90 1 2 92 2 93 2P3c4d784bac1853f7 1 1 64 2 0 1 88 1 3 6 1 89 1 90 64P3ca47d996c5e7c52 0 7 0 1 45 1 50 1 51 1 52 1 60 1 61 1P3dc2d2396c0e3c28 0 2 0 1 62 1P3e2e1f354e9713da 0 6 0 1 45 1 50 1 52 1 60 1 61 1P3e73bb46359d88eb 0 7 0 1 44 1 72 1 83 1 85 1 89 1 90 1P3ed651d8b74613e1 0 3 0 1 41 1 74 1P3fc510c9d6b9b139 1 2 32 3 0 1 86 1 87 1 32 3 1 1 85 1 88 1 2 89 2 90 2N018f155bc5b4e726N044a3b045c8ab24fN0567eb77f8afa256N0598671a513fdb3dN068081514f1858c9N0698027aeee339a4N07b76d032151b901N07bac040d9628f89N0851cd115e0acb97N088867b049618b14N08a7374ab465861aN08ca6afbd9c182abN094a2e70b8094446N09ce5cfd5910a129N09e92aa65f1a2d5eN09fef2526847f1cdN0a30e8142729545cN0a52419363d6a8d1N0b380a4106537861N0cd00472914f8e1aN0d5603318fbaab98N0df5d762675ef4b0N0e607a113f0c07cbN0f51bea5069206eaN0fb34d5a38847015N10820da2112cb2c4N108a448366534d8aN10cd459c2af4ca6cN133980c5cf4099b9N142d596830c98410N14857c90447a9e9cN1564a2b9beaa8f23N15d29c32d77bc7d0N15dc89cefb0e4d01N15f9804f4310885bN15fec878d1598b12N16b1bfbe29e59858N16c61b55bedd83f4N1789f7a37a976f55N18640757c7d6ceb9N192ccb93530c3210N19329ae3dffe2d6eN1a8a1393cff8def4N1b000476a488dac8N1b426246041d8e5aN1c7201b7fd4499b9N1d0dcd30982689b7N1d8bd9b6d546925fN1e0c84c81e62c417N1e8c01ce5b202542N1e8c875cc6816c48N1f2378b333180843N1f5540b70339122cN1fe9ce473a17bf84N21a8c61883c2aad1N2393e06fc7414f8dN23dfe97558338223N26183899c2bae922N26bf9ff1731c31a2N26c66d69300eaf28N26db54c88d932663N271ae4cca363de14N28c576198916c8acN28e4e0c9dfe31c15N294671d9a6d9202dN294caf8a3855e29eN29ca79e2be334192N2a430062c20f479cN2bdb328a59731650N2cbfe038f0b2d1f9N2cc373b4c0ab7abfN2d2d364993ddc6b0N2d6305a8c7ce5048N2ef8a2bd60c6d582N2f17a921ddc8cb67N2f378938c37f0a49N2f719730302e312aN306964f4851f1526N30ebbff7906e9de1N3120304b587e3a68N31b68c88412fb55eN31ffd8dd9b47f3edN324651384a1ac489N32b53545d04e14fcN331e2c862dcade9aN333f7039e3f2fe15N33988f55120b7f99N351be1568e43f749N353288e509e81244N366b66506dc7322eN37451daab60228bcN376c58072e27f4d7N378a9edfa878bebeN379a25bdd99ec1ddN38a43d62115b3119N3941ec47619bdf38N394a9c162b8fd593N3a6ce6c9c9c59c63N3e94ec5a32e61777N3f8747990c4c9cd5"%lxh.
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
Ltac2 gd_tbl_A_pk_ecc_set_group () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "pk_set_group_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "pk_set_group_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_d"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_Q"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_keypair_init.kp_init"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.C24_ECP_GROUP_LOAD"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "pk_ecc_set_group_postA"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkSG.Call.S1P"; "A_PK_ECC_SET_GROUP"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "WalkSG.Call.EPOST"; "A_ECP_GROUP_LOAD_SG"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "WalkSG.Call.CALLQ"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_group_load_stmtA"; "pk_ecc_set_group_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_pk_defs.A_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.curve_addrs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "A_UAR_GOT_SG"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "A_SMALLOC_1_SG"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"].


Definition A_PK_ECC_SET_GROUP : Z := 0x0da16c.      (* [comment removed for export] *)
Definition A_SMALLOC_1_SG : Z := 0x5306c.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_SG : Z := 0x0f5ea8.             (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ECP_GROUP_LOAD_SG : Z := 0x0d0988.      (* [comment removed for export] *)

(* [comment removed for export] *)
Notation PK_ECC_SET_GROUP_STACK_A := (176 + ECP_GROUP_LOAD_STACK_A) (only parsing).
(* [comment removed for export] *)
Definition pk_set_group_PHI : Z := group_load_PHI.
Definition pk_set_group_FR : Z := group_load_FRn 0.

Definition pk_ecc_set_group_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs R HIA) (LB LF : list blk) (PKA info C : Z) (k : ecp_kp) (id lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O23.O22.O21.)Lh',(5.O23.O22.O21.)(1.$6.Lr,$6.(1.$7.Lg',$7.(1.(8.$9.)LNB,(8.$9.)(1.(8.$9.)LLB',(8.$9.)(:.(;.$0.R16.(<.(=.(>.O1=.O1<.O1;.O1:.R15.R14.R13.O19.O18.(?.&40.R4.)R12.R11.R10.R?.R>.R=.R<.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R;.R:.R9.R8.)O=.(10.O1=.)O<.(11.(2.&40.))R7.(12.O23.))R6.))(:.(13.O23.R7.)(:.(14.O23.R7.O3.(15.&40.O1<.))(:.(16.O1.R6.)(:.(17.O23.O22.O:.O9.(15.&40.O1<.)(18.O22.)(19.O23.O22.O21.O;.)(1:.(1;.$6.$6.)(1<.$6.$6.O6.(1=.O6.$1>.))(1?.(1;.$6.$6.)))O2.R7.)(:.(;.$6.(20.O23.O22.O21.R5.)(20.O23.O22.O21.O;.))(:.(;.$6.(19.O23.O22.O21.R5.)(19.O23.O22.O21.O;.))(:.(;.$6.(21.O23.O22.O21.R5.)(21.O23.O22.O21.O;.))(:.(22.O23.O22.O21.R5.R6.)(:.Px,$6.P,(23.O23.O22.O21.O;.R1.)(23.O23.O22.O21.R7.R2.)(:.(24.(25.O23.O22.O21.R5.)(1=.(25.O23.O22.O21.O;.)$26.))(:.(24.(27.O23.O22.O21.R5.)(1=.(27.O23.O22.O21.O;.)$28.))(:.(29.O23.O22.O21.R5.R1.O9.R7.)(:.Pb,$9.(2:.(2;.$9.R1.R2.)(2<.(2;.$9.R1.R3.)(2;.$9.R1.O:.)))(:.Pb,$9.P,(2;.$9.R1.R3.)(:.(2=.(2;.$9.R2.O:.))(2>.O22.O:.O9.(2?.$6.$6.R2.)(30.$6.$6.R2.)))(:.(31.O23.O20.R7.R1.O6.(32.R3.(33.O5.)(34.O5.)))(:.(35.(36.R3.))(:.(;.(8.$9.)(37.R3.)R2.)(:.(38.O1?.O1>.O4.O6.R4.R3.R2.)(39.O23.R7.O8.(1:.$3:.(3;.(?.&40.O7.))(1:.$3:.(3;.(?.&40.O6.))(1?.$3:.))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_ecc_set_group_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z) (ECIS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Ph,(5.O8.O7.O6.)PLB,(8.$9.)PLF,(8.$9.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(3<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PPKA,$6.Pinfo,$6.PC,$6.Pid,$6.Plo,$6.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)Ppd,(2.&40.)PqX,(2.&40.)PqY,(2.&40.)PqZ,(2.&40.)Zk,$3=.(3>.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(29.O8.O7.O6.R39.R38.R37.R15.)P,(22.O8.O7.O6.R3:.R15.)P,(3?.(40.$9.R39.)#200.)P,(39.O8.R18.R16.(1:.$3:.(3;.(?.&40.R15.))(1:.$3:.(3;.(?.&40.R14.))(1?.$3:.))))P,(;.$6.(41.R17.+8.)=)P,(42.=R18.)P,(2;.$6.R18.O2.)P,(43.O8.(44.O7.)(23.O8.O7.O6.R40.)R1<.R1:.+10.)P,(45.(46.O7.)(47.$9.R40.(48.R3?.))R17.R1;.+10.)P,(2<.(24.(1=.R1<.+10.)R18.)(24.(15.&40.R3>.)R1<.))P,(2<.(24.(1=.R1=.+10.)R1;.)(24.(1=.R1;.$49.)R1=.))P,(31.O8.O5.R20.R43.R1<.R<.)P,(2;.(1;.$6.$6.)(1<.$6.$6.R1=.$49.)R44.)P,(:.(24.=R1=.)(42.R1=.(4:.+2.+1?.)))P,(14.O8.R23.R1=.(15.&40.R43.))P,(24.(18.O7.)R1>.)P,(24.R1?.(4;.(4;.(15.&40.R45.)(1=.+;0.+<0.))(4<.O7.)))P,(24.(15.&40.R46.)(20.O8.O7.O6.R4:.))P,(;.$6.(41.(15.&40.R47.)+10.)=)P,(;.(2.&40.)R46.(?.&40.(4=.O7.)))P,(13.O8.R29.)P,(;.$6.(41.(15.&40.R4;.)+2.)=)P,(24.(1=.(25.O8.O7.O6.R4?.)$26.)$4>.)P,(24.(1=.(27.O8.O7.O6.R50.)$28.)$4?.)P,(24.(1=.(50.R50.)$51.)$52.)P,(;.(2.&40.)R46.(?.&40.R2<.))P,(;.(2.&40.)R46.(?.&40.R2:.))(53.O8.(54.O8.O7.O6.O5.O4.O3.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R54.R53.R52.R2>.R2=.R2<.R1<.R2;.R2:.R30.R2?.)(<.(=.(>.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(?.&40.O1.)R31.(11.(2.&40.))R30.(12.O8.))R2?.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma grp_free_LB_initA : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PC,$6.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PLB,(8.$9.)(;.(8.$9.)(55.(56.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)R1.)R1.)")
(* [comment removed for export] *).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ecp_group_at_LB_noheap : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Psegs,(8.$57.)PMT,(8.$58.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(8.$9.)PLB',(8.$9.)PG,$6.Pg,$7.P,(59.R7.R6.R5.R4.R2.R1.)P,Pe,$5:.P,(2;.$5:.R1.(36.R3.))(2=.(;.$5;.(5<.R2.)$5=.))(59.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB LB' G g HG NH.
  flat constr:(HG) 13%nat. flclear HG. intros HD AL POS EP EA EB EN MP MA MB FLt1 MN REST. flat constr:(FLt1) 6%nat. flclear FLt1. intros EX EY EZ MX MY MZ.
  pose proof (fun e He Hm => mpdr_at_LB_any segs m LB LB' e Hm (NH e He)) as RB.
  unfold grp_mpds, pt_mpds in RB. cbn [app In] in RB.
  refine (conj HD (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _))))))).
  split; [apply RB; [tauto| exact MP]|]. split; [apply RB; [tauto| exact MA]|]. split; [apply RB; [tauto| exact MB]|].
  split; [refine (conj EX (conj EY (conj EZ _))); split; [apply RB; [tauto| exact MX]| split; [apply RB; [tauto| exact MY]| apply RB; [tauto| exact MZ]]]|].
  split; [apply RB; [tauto| exact MN]| exact REST].
Qed.

Lemma grp_init_noheap : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PC,$6.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)Pe,$5:.P,(2;.$5:.R1.(36.(56.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)))(;.$5;.(5<.R2.)$5>.)")
(* [comment removed for export] *).
Proof.
  intros until e. unfold grp_mpds, grp_init. cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
  intros H; decompose [or] H; subst; try reflexivity; contradiction.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56669685265.1900000<S2FB1n1B1j1X". (* [comment removed for export] *)
Lemma fresh_apart_relist_sg : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PR,$5?.PHIA,(60.$61.R1.)Ph3,(5.$61.R2.R1.)PLB,(8.$9.)PLB',(8.$9.)PLF,(8.$9.)Pm3,P,(2.&40.)(3.(2.&8.))PFB,$6.Pn,$6.P,(2>.R9.R6.R4.R2.R1.)P,(29.$61.R:.R9.R8.R6.(1:.(1;.$6.$6.)(1<.$6.$6.R3.R2.)R5.)R4.)(2>.R;.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R HIA h3 LB LB' LF m3 FB n (F0 & F1 & F2 & F3) HH. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
  flat constr:((hm_apart asegs R HIA h3 _ _ _ HH)) 2%nat. intros _ BA.
  pose proof (blocks_apart_app2 LB' ((FB, n) :: LF) (B, j) (FB, n) BA Hb ltac:(left; reflexivity)) as X. cbn [fst snd] in X. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma fresh_apart_frames_mono_sg : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PR,$5?.PLB,(8.$9.)PLF,(8.$9.)PLF',(8.$9.)PN,$6.Pk,$6.P,(2>.R6.R5.R3.R2.R1.)P,Pb,$9.P,(2;.$9.R1.(48.R6.))(2;.$9.R2.(48.R6.))(2>.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R LB LF LF' N k (F0 & F1 & F2 & F3) HI. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros B j Hb. apply F3. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply HI, Hb].
Qed.

(* [comment removed for export] *)
Lemma ecp_group_at_LB_mono : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Psegs,(8.$57.)PMT,(8.$58.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(8.$9.)PLB',(8.$9.)PG,$6.Pg,$7.P,(59.R7.R6.R5.R4.R2.R1.)P,Pb,$9.P,(2;.$9.R1.R6.)(2;.$9.R2.R6.)(59.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB LB' G g HG SUB.
  flat constr:(HG) 13%nat. flclear HG. intros HD AL POS EP EA EB EN MP MA MB FLt2 MN REST. flat constr:(FLt2) 6%nat. flclear FLt2. intros EX EY EZ MX MY MZ.
  pose proof (fun e Hm => mpdr_at_LB_mono segs m LB LB' e Hm SUB) as RB.
  refine (conj HD (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _))))))).
  split; [apply RB; exact MP|]. split; [apply RB; exact MA|]. split; [apply RB; exact MB|].
  split; [refine (conj EX (conj EY (conj EZ _))); split; [apply RB; exact MX| split; [apply RB; exact MY| apply RB; exact MZ]]|].
  split; [apply RB; exact MN| exact REST].
Qed.

(* [comment removed for export] *)
Lemma ecp_group_at_heap_in : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Psegs,(8.$57.)PMT,(8.$58.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(8.$9.)PG,$6.Pg,$7.Pe,$5:.P,(59.R7.R6.R5.R4.R3.R2.)P,(2;.$5:.R2.(36.R3.))P,(;.$5;.(5<.R3.)$5=.)(2;.(1;.$6.$6.)(1<.$6.$6.(62.R4.)(63.+4.(64.R4.)))R7.)")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB G g e HG He O.
  flat constr:(HG) 13%nat. flclear HG. intros _ _ _ _ _ _ _ MP MA MB FLt3 MN _. flat constr:(FLt3) 6%nat. flclear FLt3. intros _ _ _ MX MY MZ.
  assert (MDe : mpdr_at segs m LB e) by (unfold grp_mpds, pt_mpds in He; cbn in He; destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
  flat constr:(MDe) 6%nat. flclear MDe. intros _ _ _ _ _ OW. rewrite O in OW. flat constr:(OW) 3%nat. flclear OW. intros _ EIN _. exact EIN.
Qed.

(* [comment removed for export] *)
Lemma mpdr_init_presA : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PR,$5?.PLBp,(8.$9.)PLF,(8.$9.)PSP,$6.PSSP,$6.PTOP,$6.PW,(8.$65.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(8.$9.)PLB',(8.$9.)PA,$6.Ppad,(2.&40.)P,(66.$61.R6.R4.(67.R2.R1.))P,(17.$61.R>.R=.R<.R;.R:.R9.R8.R7.R6.)P,(45.(46.R?.)(47.$9.R>.(48.R=.))R<.R4.+10.)P,(68.R:.R5.+10.)(66.$61.R9.R7.(67.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros R LBp LF SP SSP TOP W m m' LB LB' A pad (Hc & Hal & Hpos & _) HP CR DJ.
  apply mpdr_at_init; [| exact Hal| exact Hpos].
  exact (presA_rw_cells asegs R _ _ _ _ _ _ m m' _ _ HP Hc CR DJ).
Qed.

Section WalkSG.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_SG.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_SG.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis RTCL : forall m, arl_rtc R m -> asan_rtc m.
  Variable MT : list modp_ent.
  Variable ca : Z -> curve_addrs.
  Variable ONE : Z.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PKA info C id lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 368 - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis IDB : 0 <= id < 2^31.
  Hypothesis NZP : 0 < PKA.
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis PKB : 0 <= PKA /\ PKA + 16 <= 2^64.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_SG in UARG; unfold A_SMALLOC_1_SG in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Lms,$69.(1.$6.LFB,$6.(1.$6.Lsp1,$6.(1.(5.$61.VR,VHIA,)Lh1,(5.$61.VR,VHIA,)(1.P,(2.&40.)(3.(2.&8.))Lm1,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(1.(2.&40.)Ll32a,(2.&40.)(1.(2.&40.)Ll32b,(2.&40.)(1.(2.&40.)Ll64a,(2.&40.)(1.(2.&40.)Ll64b,(2.&40.)(1.(2.&40.)Ll96a,(2.&40.)(1.(2.&40.)Ll96b,(2.&40.)(1.(2.&40.)Lw24,(2.&40.)(1.(2.&40.)Lw48,(2.&40.)(:.(;.$69.R1>.(=.(>.(?.&40.+=:1>0.)(?.&40.R1<.)Vgp,Vtp,R19.R18.R17.Vsp,(?.&40.R1<.)(?.&40.R1=.)R16.R15.R14.R13.R12.R11.R10.(?.&40.Vid,)(?.&40.(6:.(44.VR,)))(?.&40.VPKA,)Vs5,Vs6,Vs7,(?.&40.(1=.(6;.R1=.+3.)(6:.(44.VR,))))(?.&40.R1=.)Vs10,(?.&40.(1=.(6;.VPKA,+3.)(6:.(44.VR,))))R?.R>.R=.R<.)VF,(?.&40.+=:298.)Vfc,(11.(2.&40.))R1:.(12.$61.)))(:.(:.(24.(4;.(15.&40.Vsp,)+;0.)R1<.)(24.R1<.(4;.(15.&40.Vsp,)+:0.)))(:.(;.$6.(41.R1<.+20.)=)(:.(29.$61.VR,VHIA,R1;.VLB,(1:.(1;.$6.$6.)(1<.$6.$6.R1=.+80.)VLF,)R1:.)(:.(;.P,$6.Sp(23.$61.VR,VHIA,R1;.)(23.$61.VR,VHIA,Vh,))(:.(;.$6.(20.$61.VR,VHIA,R1;.)(20.$61.VR,VHIA,Vh,))(:.(;.$6.(19.$61.VR,VHIA,R1;.)(19.$61.VR,VHIA,Vh,))(:.(;.$6.(21.$61.VR,VHIA,R1;.)(21.$61.VR,VHIA,Vh,))(:.(;.$6.(25.$61.VR,VHIA,R1;.)(25.$61.VR,VHIA,Vh,))(:.(;.$6.(27.$61.VR,VHIA,R1;.)(27.$61.VR,VHIA,Vh,))(:.Pmo,$4.(2:.(22.$61.VR,VHIA,R1<.R1.)(22.$61.VR,VHIA,Vh,R1.))(:.(;.$6.(41.R1=.+40.)=)(:.(2>.VR,VLB,VLF,R1=.+80.)(:.(39.$61.R1:.R1=.(1:.$3:.(3;.R;.)(1:.$3:.(3;.R:.)(1:.$3:.(3;.R9.)(1?.$3:.)))))(:.(39.$61.R1:.(1=.R1=.+20.)(1:.$3:.(3;.R8.)(1:.$3:.(3;.R7.)(1?.$3:.))))(:.(39.$61.R1:.(1=.R1=.+40.)(1:.$3:.(3;.R6.)(1:.$3:.(3;.R5.)(1?.$3:.))))(:.(39.$61.R1:.(1=.R1=.+60.)(1:.$3:.(3;.R4.)(1:.$3:.(3;.R3.)(1?.$3:.))))(:.(39.$61.R1:.(1=.(6;.R1=.+3.)(6:.(44.VR,)))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?3.))(1:.$3:.(6<.(?.&8.+?3.))(1?.$3:.))))))))))))))))))(:.(39.$61.R1:.(1=.(15.&40.Vsp,)-68.)(1:.$3:.(3;.Vs11,)(1:.$3:.(3;.Vs10,)(1:.$3:.(3;.Vs9,)(1:.$3:.(3;.Vs8,)(1:.$3:.(3;.Vs7,)(1:.$3:.(3;.Vs6,)(1:.$3:.(3;.Vs5,)(1:.$3:.(3;.Vs4,)(1:.$3:.(3;.Vs3,)(1:.$3:.(3;.Vs2,)(1:.$3:.(3;.Vs1,)(1:.$3:.(3;.Vs0,)(1:.$3:.(3;.Vra,)(1?.$3:.)))))))))))))))(:.(39.$61.R1:.(1=.R1<.+18.)(1:.$3:.(3;.R2.)(1?.$3:.)))(:.(39.$61.R1:.(1=.R1<.+30.)(1:.$3:.(3;.R1.)(1?.$3:.)))(:.(14.$61.R1:.R1<.(1=.R1<.+18.))(:.(14.$61.R1:.(1=.R1<.+20.)(1=.R1<.+30.))(:.(14.$61.R1:.(1=.R1<.+38.)(1=.(15.&40.Vsp,)-68.))(:.(14.$61.R1:.Vlo,R1<.)(:.(13.$61.R1:.)(6=.$61.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(18.VR,)(1?.$65.)Vm,R1:.))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 ALP; try lx_pin1 IDB; try lx_pin1 C; try lx_pin1 info; try lx_pin1 mo0; try lx_pin1 ONE; try lx_pin1 ca; try lx_pin1 MT; try lx_pin1 RTCL.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@D18607476203.112D2457697676.146 D29569067328.146D32458983511.146D32604263317.147D3379604520.145 D45712672153.145D50254960491.113D51038213418.113D558665111.82   D62009822325.82 D62011770190.147D68402935403.145D6907585646.145 L11453604505.11 L13424450160.128L15629616632.11 L19546883925.128L19980016842.11 L21980071943.1  L2275137097.0   L24131365019.123L24511873114.81 L25187853190.12 L25188864540.1  L25194140199.83 L27188209011.150L27729706458.136L27843863047.1  L29738741675.1  L40226756952.1  L43061657906.83 L43495095303.1  L46938848127.1  L47230721790.123L48117620902.124L48117620911.72 L51038230838.137L53537894342.3  L54437681876.8  L55351494680.11 L57355539152.123L58150969761.0  L58790154276.11 L58970213517.1  L59308677456.12 L59351324120.1  L62018535662.1  L63405906047.1  L6912107244.123 L7040749983.82  L7715476710.85  L9356559645.12  Q10533598597.84 Q10592386206.151Q1530342990.113 Q23937998252.84 Q24131365019.152Q24137657765.150Q30223088059.151Q32440833928.150Q35653441506.78 Q40271359350.113Q47241206720.84 Q48117620904.151Q48132302231.150Q56531220660.151Q59310664043.150Q59310664043.84 Q59321150548.151Q60109315147.78 Q6192914196.111 Q62012212072.113Q62022254708.84 Q6897428434.150 Q6912107244.152 Q9356560156.94  00000100200H00^01=01>01T01U01l02?02L02d02e03;03<03\03]04=04U04Y04Z04e05L05M05N05O05j06@06D06H06M07507907>07L08208X09209>09[09k09l09m0:F0:K0:U0:Z0:]0:b0:m0;H0;W0<F0<S0<^0=10=M0=X0=c0=n0=o0>N0>^0>l0?R0@80@90@:0@;0@<0@M0@Y0@c0@m0A80AC0AWFFS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBS1R3HIA2LF2sp3LFB3sp13H152h12FBFS2LF2sp3LFB3sp13H152FBFS2LF2sp3LFB3sp13H133H15S1R3HIA1h2LF2sp3LFBS1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H152FBFS2LF2sp3LFB3sp13H152FBSS2LF2sp3LFB3SPR3sp13H152FB2F02F8SS2LF2sp3LFB3SPR3sp13H152FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1S2spSS2LF3LFB2FBS2LF2sp3SPA3LFB3SPR3sp13H113H123H133H15FFFS2LF2sp3LFB3sp13H152FB1c2HcS2LF2sp3LFB3sp13H152FBS2FBS2FBS3sp1S1R3NS12LF2sp3PKA2lo3SLO3LFB3NZP3NES3SPRS2FBS3sp1S1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS2LF2sp3LFB3sp13H133H152FBS2sp3sp13SP1S1R3NS12sp2lo3SLO3NES3sp13SP1S1R3ACV2FB2F02F1FSS1R2sp2lo3SLO3NES3sp13SP1S3sp1S2FB2Kb2F0S3sp1S1RS3sp1S2LF3LFB2FBS2LF2sp3LFB3SPR3sp13H113H15S2LF2sp3PKA3LFBS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp13H13S1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERFFFFS1R2LF2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp13H143H15". (* [comment removed for export] *)
  #[using="PKB NZP LFB TPV SPA TOP SLO LOS NEEDR NS1 SM1 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(29.$61.VR,VHIA,Vh,VLB,VLF,Vm,)P,(14.$61.Vm,Vlo,(15.&40.Vsp,))P,(13.$61.Vm,)(6>.$61.(44.VR,)(23.$61.VR,VHIA,Vh,)$6?.(=.(>.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(?.&40.VPKA,)(?.&40.Vid,)R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(?.&40.$70.)Vfc,(11.(2.&40.))Vm,(12.$61.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI.
  unfold A_PK_ECC_SET_GROUP.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
  carve_frame 160%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 250%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1' end.
      destruct (stk_split asegs m1' lo sp1 (bv_unsigned sp + -160) ST ltac:(first [ clear - SP1 SLO NS1 NES; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340076) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1' |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 128); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP NS1 NES; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1' ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. flat constr:(FRSH) 3%nat. flclear FRSH. intros F0 F1 _.
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 56) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STa SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 56) 8 STa ltac:(clear; lia)) as [STa' [jslot48 SLOT48]].
      replace (sp1 + 56 - Z.of_nat 8) with (sp1 + 48) in STa', SLOT48 by (clear; lia). clear STa.
      destruct (stk_split asegs m3 sp1 (sp1 + 32) (sp1 + 48) STa' ltac:(clear; lia)) as [STb STmid]. clear STa'.
      destruct (stk_carve asegs m3 sp1 (sp1 + 32) 8 STb ltac:(clear; lia)) as [STlo [jslot24 SLOT24]].
      replace (sp1 + 32 - Z.of_nat 8) with (sp1 + 24) in STlo, SLOT24 by (clear; lia). clear STb.
      cb8_to_c8 SLOT24 (@nil cell). cb8_to_c8 SLOT48 (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 8; 16; 8; 8; 16; 8; 8; 8; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 2%nat L32 FRM3. chunk_split FRM3 1%nat G1 FRM4.
      chunk_split FRM4 2%nat L64 FRM5. chunk_split FRM5 1%nat G2 FRM6. chunk_split FRM6 2%nat L96 FREST.
      lazymatch type of L32 with rw_cells _ _ ?a _ => replace a with (FB + 32) in L32 by (clear; lia) end.
      lazymatch type of L64 with rw_cells _ _ ?a _ => replace a with (FB + 64) in L64 by (clear; lia) end.
      lazymatch type of L96 with rw_cells _ _ ?a _ => replace a with (FB + 96) in L96 by (clear; lia) end.
      clear FLNK FREST G1 G2.
      cb8_to_c8 FHD (@nil cell).
      cb8_to_c8 L32 (@nil cell). lazymatch type of L32 with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 L32 [c1] end.
      cb8_to_c8 L64 (@nil cell). lazymatch type of L64 with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 L64 [c1] end.
      cb8_to_c8 L96 (@nil cell). lazymatch type of L96 with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 L96 [c1] end.
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xda298] [] 250%N). lx_tree.
  lxr_leaf. lx_carry.
  match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 14 eexists. do 3 eexists. do 8 eexists.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact L32|]. split; [exact L64|]. split; [exact L96|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT24|]. split; [exact SLOT48|]. split; [exact STlo|]. split; [exact STmid|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (a0v : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Lms,$69.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(5.$61.VR,VHIA,)Lh4,(5.$61.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(:.(;.$69.R11.(=.(>.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,O1.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(10.Vra,)Vfc,(11.(2.&40.))R10.(12.$61.)))(:.(13.$61.R10.)(:.(14.$61.R10.Vlo,(15.&40.Vsp,))(:.(6=.$61.VR,VHIA,O8.O7.VLF,(15.&40.Vsp,)(18.VR,)O3.O5.R10.)(:.(6=.$61.VR,VHIA,O8.O6.VLF,(15.&40.Vsp,)(18.VR,)O2.O4.R10.)(:.(;.P,$6.Sp(23.$61.VR,VHIA,R?.)(23.$61.VR,VHIA,O8.))(:.(;.$6.(20.$61.VR,VHIA,R?.)(20.$61.VR,VHIA,O8.))(:.(;.$6.(19.$61.VR,VHIA,R?.)(19.$61.VR,VHIA,O8.))(:.(;.$6.(21.$61.VR,VHIA,R?.)(21.$61.VR,VHIA,O8.))(:.(;.$6.(25.$61.VR,VHIA,R?.)(25.$61.VR,VHIA,O8.))(:.(;.$6.(27.$61.VR,VHIA,R?.)(27.$61.VR,VHIA,O8.))(:.Pmo,$4.(2:.(22.$61.VR,VHIA,R10.R1.)(22.$61.VR,VHIA,O8.R1.))(29.$61.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 PKB; try lx_pin1 ALP; try lx_pin1 IDB; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 id; try lx_pin1 C; try lx_pin1 info; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 ONE; try lx_pin1 ca; try lx_pin1 MT; try lx_pin1 RTCL; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01A0@D10777814275.127D2459793318.127 D32452690557.127D3385958441.126 D43016287773.128D45702252952.126D62011770188.128D68409162346.126D6897035375.126 L10048050688.9  L12019524068.162L1230675542.167 L13312155929.156L13424450162.109L13424450175.113L19546883927.109L19546883930.113L2275137097.0   L24131365012.110L24131365017.106L27188209011.131L29789883990.165L30443638347.7  L35655538631.10 L38077847203.1  L39332637397.0  L39540652971.1  L39844638933.0  L42411609006.0  L47230721777.110L47230721788.106L48117620903.111L48117620904.107L50790761713.7  L5162232212.2   L54924291876.164L5692162643.166 L60098763854.3  L60703428480.9  L61954813922.163L62018535662.1  L62408677348.160L63104439427.168L6912107235.110 L6912107246.106 L9356559676.12  P5152549648.162 Q10592386204.132Q10592386207.136Q21721340005.133Q21721340008.137Q22358563588.135Q24131365012.137Q24131365017.133Q24137657765.131Q24137657789.135Q30147450662.133Q30223088057.132Q30223088058.136Q30871588746.160Q31314676345.131Q34796740410.136Q4125667684.159 Q4279611329.161 Q48117620905.136Q48117620906.132Q48132302223.135Q48132302231.131Q52741535643.160Q5935758158.161 Q59668625896.137Q60382659730.137Q60382659743.133Q64133651577.160Q67397950268.132Q6897428426.135 Q6897428434.131 Q6912107235.137 Q6912107246.133 Q7917062807.137 Q7917062810.133 00000?00@00O00P00h01701H01I01X02;02J03903M03g04A04V04k04l05705B05V06E06`07907=07>07B07C07D07R07`08F08l09G09H0:70:f0;00;S0<@0<C0<R0=?0=J0=U0>D0>E0>P0>[0>\0>]0>^0>i0?40??0?J0?K0?V0?a0@10@20@30@@0@M0A30AY0B?0Be0C50CB0CC0CD0CE0CR0CS0C^0Ci0D40D?0DS0DgS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1FS1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13NERS2LF3LFB2FB3sp1S1R3NS12LF2sp2lo3SLO3LFB2FB3sp13SP13NES4SP1R2F0S2LF3LFB2FB3sp11p2PBS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0SS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB3sp11c2HcS1R3NS12LF2sp2lo3SLO3LFB2FB3sp13SP13NES4SP1R2F0S1R5NEEDR2sp2lo3LOS3SLO3NERS1R3HIA1h2sp2lo3TOP5HTOP3S2spSS2FBSSS1R2LF3LFB3ALOS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2sp2lo3LOS3SLO3NERFS1R3NS12LF2sp2lo3SLO3LFB2FB3sp13SP13NES4SP1R2F0S1R3NS12LF2sp2lo3SLO3LFB2FB3sp13SP13NES4SP1R2F0S1R2lo3LOSS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13NERS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13NER4SP1R2F0S1RS2LF3LFB2FB3sp1S1R3NS12LF2sp2lo3SLO3LFB2FB3sp13SP13NES2F02H9S2LF3LFB2FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPRFS2LF3LFB2FBS2LF3LFB2FBFFFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB1p2PBFFS2LF3LFB1p2PBS2LF3LFB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS2LF3LFB2FB1p2PBS2LF3LFB1p2PBFFFS2LF3LFB1p2PBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="NZP LFB TOP SLO LOS PKA NEEDR NS1 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Ph3,(5.$61.VR,VHIA,)PLBa,(8.$9.)PLBb,(8.$9.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(8.$65.)PWB,(8.$65.)PFB,$6.Psp1,$6.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0v,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps2v,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps10v,(2.&40.)Ps11v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pw48,(2.&40.)P,(29.$61.VR,VHIA,R26.R24.(1:.(1;.$6.$6.)(1<.$6.$6.R1>.+80.)VLF,)R21.)P,Px,$6.P,(23.$61.VR,VHIA,Vh,R1.)(23.$61.VR,VHIA,R29.R2.)P,(;.$6.(20.$61.VR,VHIA,R28.)(20.$61.VR,VHIA,Vh,))P,(;.$6.(19.$61.VR,VHIA,R29.)(19.$61.VR,VHIA,Vh,))P,(:.(24.(4;.(15.&40.Vsp,)+;0.)R21.)(24.R21.(4;.(15.&40.Vsp,)+:0.)))P,(;.$6.(41.R22.+20.)=)P,(;.$6.(41.R24.+40.)=)P,(2>.VR,R2<.VLF,R25.+80.)P,(2>.VR,R2<.VLF,R26.+80.)P,(71.(23.$61.VR,VHIA,Vh,)R27.+80.)P,PB,$6.Pj,$6.P,(2;.(1;.$6.$6.)(1<.$6.$6.R2.R1.)VLF,)(2<.(24.(1=.R2;.+80.)R3.)(24.(1=.R3.R2.)R2;.))P,Pb',$9.P,(2;.$9.R1.R31.)(2;.$9.R2.R31.)P,(39.$61.R2=.R2:.(1:.$3:.(3;.R10.)(1:.$3:.(3;.R?.)(1:.$3:.(3;.R>.)(1?.$3:.)))))P,(39.$61.R2>.(1=.(6;.R2;.+3.)(6:.(44.VR,)))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?3.))(1:.$3:.(6<.(?.&8.+?3.))(1?.$3:.))))))))))))))))))P,(39.$61.R2?.(1=.(15.&40.Vsp,)-68.)(1:.$3:.(3;.Vs11,)(1:.$3:.(3;.Vs10,)(1:.$3:.(3;.Vs9,)(1:.$3:.(3;.Vs8,)(1:.$3:.(3;.Vs7,)(1:.$3:.(3;.Vs6,)(1:.$3:.(3;.Vs5,)(1:.$3:.(3;.Vs4,)(1:.$3:.(3;.Vs3,)(1:.$3:.(3;.Vs2,)(1:.$3:.(3;.Vs1,)(1:.$3:.(3;.Vs0,)(1:.$3:.(3;.Vra,)(1?.$3:.)))))))))))))))P,(39.$61.R30.(1=.R2<.+18.)(1:.$3:.(3;.(?.&40.R2=.))(1?.$3:.)))P,(39.$61.R31.(1=.R2=.+30.)(1:.$3:.(3;.R11.)(1?.$3:.)))P,(14.$61.R32.R2>.(1=.R2>.+18.))P,(14.$61.R33.(1=.R2?.+20.)(1=.R2?.+30.))P,(14.$61.R34.(1=.R30.+38.)(1=.(15.&40.Vsp,)-68.))P,(14.$61.R35.Vlo,R31.)P,(13.$61.R36.)P,(6=.$61.VR,VHIA,R3<.R3;.VLF,(15.&40.Vsp,)(18.VR,)R36.R39.R37.)P,(6=.$61.VR,VHIA,R3=.R3;.VLF,(15.&40.Vsp,)(18.VR,)R36.R39.R38.)(6>.$61.(44.VR,)(23.$61.VR,VHIA,R3>.)(72.R3>.R3=.R3<.R3;.R3:.R38.R37.R30.)(=.(>.R34.(?.&40.R35.)Vgp,Vtp,R33.R32.R31.Vsp,(?.&40.R35.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R24.R23.R22.R21.R20.R1?.(?.&40.(1=.(6;.R36.+3.)(6:.(44.VR,))))(?.&40.R36.)R1>.R1=.R28.R27.R26.R25.)VF,(?.&40.+=:400.)Vfc,(11.(2.&40.))R39.(12.$61.)))")
(* [comment removed for export] *).
  Proof.
  intros until w48.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT24 SLOT48 STlo STmid SThi STbelow MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR NER TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xda464] [] 250%N). lx_tree.
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NEEDR NER; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 24 + 8 <= p \/ p + 1 <= sp1 + 24).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR NER; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP7 : sp1 + 48 + 8 <= p \/ p + 1 <= sp1 + 48).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR NER; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NEEDR NER; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NEEDR NER; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 14 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  chunk_to_stk SLOT24.
  chunk_to_stk SLOT48.
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 24), STB : stk _ mf (sp1 + 32) (sp1 + 48), STC : stk _ mf (sp1 + 56) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOT24; stk_merge_into ST0 STB; stk_merge_into ST0 SLOT48; stk_merge_into ST0 STC; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end.
  }
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CALLQ (FB sp1 : Z) (h1 : HST asegs R HIA) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Lms,$69.(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)Ls5v,(2.&40.)(1.(2.&40.)Ls7v,(2.&40.)(1.(2.&40.)Ls10v,(2.&40.)(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(:.(;.$69.R15.(=.(>.(?.&40.+=:400.)(?.&40.O2.)Vgp,Vtp,R13.R12.R11.Vsp,(?.&40.O2.)(?.&40.VC,)(?.&40.Vid,)R10.R?.R>.R=.R<.R;.(?.&40.Vid,)(?.&40.(6:.(44.VR,)))(?.&40.VPKA,)(?.&40.VC,)R6.R5.(?.&40.(1=.(6;.O3.+3.)(6:.(44.VR,))))(?.&40.O3.)R4.(?.&40.(1=.(6;.VPKA,+3.)(6:.(44.VR,))))R:.R9.R8.R7.)VF,(?.&40.$73.)Vfc,(11.(2.&40.))R14.(12.$61.)))(:.(29.$61.VR,VHIA,O1.VLB,(1:.(1;.$6.$6.)(1<.$6.$6.O3.+80.)VLF,)R14.)(:.(39.$61.R14.O3.(1:.$3:.(3;.R3.)(1:.$3:.(3;.R2.)(1:.$3:.(3;.R1.)(1?.$3:.)))))(:.(39.$61.R14.(1=.(6;.O3.+3.)(6:.(44.VR,)))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?3.))(1:.$3:.(6<.(?.&8.+?3.))(1?.$3:.))))))))))))))))))(:.(39.$61.R14.(1=.(15.&40.Vsp,)-68.)(1:.$3:.(3;.Vs11,)(1:.$3:.(3;.Vs10,)(1:.$3:.(3;.Vs9,)(1:.$3:.(3;.Vs8,)(1:.$3:.(3;.Vs7,)(1:.$3:.(3;.Vs6,)(1:.$3:.(3;.Vs5,)(1:.$3:.(3;.Vs4,)(1:.$3:.(3;.Vs3,)(1:.$3:.(3;.Vs2,)(1:.$3:.(3;.Vs1,)(1:.$3:.(3;.Vs0,)(1:.$3:.(3;.Vra,)(1?.$3:.)))))))))))))))(:.(39.$61.R14.(1=.O2.+18.)(1:.$3:.(3;.(?.&40.O3.))(1?.$3:.)))(:.(39.$61.R14.(1=.O2.+30.)(1:.$3:.(3;.(?.&40.O3.))(1?.$3:.)))(:.(14.$61.R14.O2.(1=.O2.+18.))(:.(14.$61.R14.(1=.O2.+20.)(1=.O2.+30.))(:.(14.$61.R14.(1=.O2.+38.)(1=.(15.&40.Vsp,)-68.))(:.(14.$61.R14.Vlo,O2.)(:.(13.$61.R14.)(6=.$61.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(18.VR,)(1?.$65.)Vm,R14.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Hypothesis EI : In info A_EC_INFOS.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 IDB; try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 mo0; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 ONE; try lx_pin1 ca; try lx_pin1 MT; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@D10777814275.145D16069757090.180D16071854214.168D2459793318.145 D32452690557.145D32604263319.146D3388366767.144 D45704738334.144D62011770188.146D68221095944.168D68223193132.180D68411655660.144D6899603433.144 L11377594986.2  L13424450161.119L139395489.0    L15520003326.18 L15754270975.18 L17609328382.18 L19546883924.119L21646758165.156L21654730866.2  L2275137097.0   L24131365018.114L24206288344.1  L25632820001.0  L2621559066.1   L27188209011.149L27938633021.18 L31973969767.18 L32750658443.2  L33312312071.18 L33474028012.167L33474028012.169L33474029409.180L33474029409.182L3484572308.18  L35653441506.10 L37687006330.2  L37759748983.179L37759748983.181L38235734261.1  L47230721791.114L47593563639.179L47593563639.181L47870616696.2  L48117620905.115L48132302231.125L48132302231.135L49218659988.1  L50925318027.2  L54664923246.167L54664923246.169L54664924899.180L54664924899.182L56197924756.1  L56787311448.1  L57245280615.18 L58039649675.2  L59308586248.2  L60098763854.3  L66298372189.2  L66935663381.168L67653551064.2  L6912107245.114 L881835912.0    L9080220944.4   L9243720967.18  L9356559676.12  L9783143000.1   O10565637740.180O10567734856.168O14059567553.180O14061664741.168O17215019116.180O17217116232.168O30150276403.180O30152373527.168O32212734003.180O32214831127.168O38903829125.168O38905926305.180O44938202843.168O44940300031.180O55209884805.168O55211981985.180O64471909102.180O64474006218.168O65961212488.168O65963309676.180P11387568333.168P11389665513.180P21647862485.168P21649959665.180P32763785480.180P32765882668.168P37691770617.180P37693867741.168P47874275067.180P47876372191.168P49211896883.168P49213994007.180P50927926572.168P50930023688.180P56191128883.168P56193226007.180P58041177900.168P58043275016.180P66292560634.168P66294657758.180Q10523111609.151Q10592386204.150Q19551029871.156Q19551029871.168Q21765573510.180Q21767670690.168Q23927511184.151Q24131365018.152Q24137657765.149Q27942454161.168Q27944551349.180Q2803826605.168 Q2805923721.180 Q29775981542.168Q29778078658.180Q30223088057.150Q32440833928.149Q34664998821.168Q3477426724.168 Q3479523840.180 Q35344172262.168Q47230721788.151Q48117620906.150Q48132302231.149Q49736620774.156Q56531220662.150Q58740137381.156Q59310664043.149Q59321150550.150Q59321150551.151Q59321559671.168Q59323656787.180Q62011770184.151Q6897428434.149 Q6912107245.152 Q9356888220.172 Q9356888221.160 Q9640321936.156 Q9640321936.168 Q9644583048.168 Q9646680236.180 00000E01E02E02F02[03903:03O03f04f05f05g06<06=06d06e07^08O09H09c0:80:90::0:E0:J0:K0:P0:j0;[0<O0<P0<[0=70=S0=o0>K0?A0?Y0?Z0@60@R0@V0@d0A?0AZ0A[0BA0Bg0CM0CN0CO0Cj0DE0D`0E;0E<0EA0F50F60F<0FF0FG0F\0Fd0Fo0G00G?0GJ0H90H>0H?0H@0HA0HB0HC0HD0HE0HF0HG0HH0HI0HJ0HK0HL0HM0HN0HO0HP0HQ0HR0IF0J:0J;0J<0K00Kd0ME0NR0OF0P:0Pj0QZ0RN0SB0T20Tb0UV0VJ0V]0W00W=0WH0Wc0X>0Xj0YV0Z20Z=0ZH0Zl0[P0[\0[h0\;0\N0\Y0\Z0\e0]40]C0]N0]\0^B0^h0_30_40_?0_@0_A0_B0_C0_D0_N0_Y0_d0`50`F0`T0`b0a00a>S2LF3PKA1C3LFB2FB3sp1S1R3NS12LF2sp3PKA1C2lo3LOS3SLO3LFB3NZP2FB3sp13SP12C03NES4SP1R2F0S1R3NS12LF2sp3PKA1C2lo3LOS3SLO3LFB3NZP2FB3sp13SP12C03NES4SP1R2F0FS2LF3PKA1C3LFB2FB3sp1S1R3HIA2LF3PKA1C3LFB2FB3sp12h1FS2LF3PKA1C3LFB2FB3sp1S1R2LF3PKA1C3LFB2FB3sp1S1R3HIA1h2LF2sp3PKA1C3TOP3LFB3NZP2FB3sp12h13SP15Ehtop2C04SP1R2F0S1R3HIA1h2LF2sp3PKA1C3TOP3LFB3NZP2FB3sp12h13SP15Ehtop2C04SP1R2F0FS2LF3PKA1C3LFB2FB3sp1FS2LF3PKA1C3LFB3NZP2FB3sp12C04SP1R2F02F8SS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACV3NER2F02F8S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO3ACV3NER2F0S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACV3NER2F02F8S2LF3PKA1C3LFB2FB3sp12F02F8S2LF3PKA1C3LFB2FB3sp1FSS2LF3LFB2FBS3sp1SS3sp1S2LF3PKA1C3LFB2FB3sp11c2HcS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO3ACV3NER2F0S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO3ACV3NER2F02F1FS2FB3sp12F0S2LF3PKA1C3LFB2FB3sp12x13PC3S2LF3PKA1C3LFB2FB3sp12x13PC3S2LF3PKA1C3LFB2FB3sp12x13PC3S2LF3PKA1C3LFB2FB3sp12x13PC3S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACV3NER2F0S1R3HIA1h2sp2lo3TOP4HTOPFS2LF3PKA1C3LFB2FB3sp12x43PC6S2LF3PKA1C3LFB2FB3sp12x43PC6S2loS1R2LF3LFB3ALOS2LF3PKA1C3LFB2FB3sp12x42H3S2LF3PKA1C3LFB2FB3sp12x42H3FS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERFFS2LF3PKA1C3LFB2FB3sp12x12H3S2LF3PKA1C3LFB2FB3sp12x12H3S2LF3PKA1C3LFB2FB3sp12x12H8S2LF3PKA1C3LFB2FB3sp12x12H8FS3sp1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO3ACV3NER2F02F1FS1i2HiS1R2lo3LOSFS2LF3PKA1C3LFB2FB3sp1S2sp3sp1S2LF3LFB2FBSS2sp2lo3sp13SP1S2FB3sp12F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPRS3sp1FFFFFFFFFFFFFFFFFFFFS1R5NEEDR2LF2sp1C2lo3LOS3SLO3LFB3sp13SP13CAC3ALO3NERS1R5NEEDR2LF2sp1C2lo3LOS3SLO3LFB3sp13SP13CAC3ALO3NERFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R3NS15NEEDR2LF2sp3PKA4info1C2lo3LOS3SLO3LFB2FB3sp13SP13DSP3CAC3ALO3NER3NES2F02F12x13PC03PC13TYBS1R3NS15NEEDR2LF2sp3PKA1C2lo3LOS3SLO3LFB2FB3sp13SP13DSP3CAC3ALO3NER3NES2F02F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NER1HS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NER1HS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NER1HS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NER1HS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2FB3sp13SP13ALO3NER2F1S2LF2sp3LFB3sp13SP1S2LF2sp3LFB3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF3PKA1C3LFB2FB3sp12F02F8S2LF3PKA1C3LFB2FB3sp12F02F8S1R3NS12LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NESS1R3NS12LF2sp2lo3LOS3SLO3LFB3sp13SP13ALO3NESS1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBS1R3NS12LF2sp2lo3SLO3LFB3sp13SP13NESS1R3NS12LF2sp2lo3SLO3LFB3sp13SP13NESS2LF3LFB3sp1S2LF3LFB3sp1S2LF2sp3LFB3sp13SP1S2LF2sp3LFB3sp13SP1S2LF3LFB2FBFS2LF3LFB2FBS2LF2lo3LFB3sp1S2LF2lo3LFB3sp1S2LF3LFB2FBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NERS2LF3LFB2FBFS2LF3LFB2FBFFFFFS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp14SP1RS2LF3LFB3sp14SP1RS2LF3LFB2FB2F0S2LF3LFB2FB2F0S2LF3LFB2FB2F0S2LF3LFB2FB2F0". (* [comment removed for export] *)
  #[using="EI PKB ALP NZP LFB TOP SLO LOS RTCL NEEDR NS1 IMG"]
  Lemma seg_A : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PFB,$6.Psp1,$6.Ph1,(5.$61.VR,VHIA,)Pm1,P,(2.&40.)(3.(2.&8.))Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps10v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pl32a,(2.&40.)Pl32b,(2.&40.)Pl64a,(2.&40.)Pl64b,(2.&40.)Pl96a,(2.&40.)Pl96b,(2.&40.)Pw24,(2.&40.)Pw48,(2.&40.)Pidpad,(2.&40.)P,(:.(24.(4;.(15.&40.Vsp,)+;0.)R21.)(24.R21.(4;.(15.&40.Vsp,)+:0.)))P,(;.$6.(41.R22.+20.)=)P,(29.$61.VR,VHIA,R22.VLB,(1:.(1;.$6.$6.)(1<.$6.$6.R24.+80.)VLF,)R21.)P,(;.P,$6.Sp(23.$61.VR,VHIA,R23.)(23.$61.VR,VHIA,Vh,))P,(;.$6.(20.$61.VR,VHIA,R24.)(20.$61.VR,VHIA,Vh,))P,(;.$6.(19.$61.VR,VHIA,R25.)(19.$61.VR,VHIA,Vh,))P,(;.$6.(41.R28.+40.)=)P,(2>.VR,VLB,VLF,R29.+80.)P,(39.$61.R27.R2:.(1:.$3:.(3;.R14.)(1:.$3:.(3;.R13.)(1:.$3:.(3;.R12.)(1?.$3:.)))))P,(39.$61.R28.(1=.R2;.+20.)(1:.$3:.(3;.R12.)(1:.$3:.(3;.R11.)(1?.$3:.))))P,(39.$61.R29.(1=.R2<.+40.)(1:.$3:.(3;.R11.)(1:.$3:.(3;.R10.)(1?.$3:.))))P,(39.$61.R2:.(1=.R2=.+60.)(1:.$3:.(3;.R10.)(1:.$3:.(3;.R?.)(1?.$3:.))))P,(39.$61.R2;.(1=.(6;.R2>.+3.)(6:.(44.VR,)))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?1.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?2.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?8.))(1:.$3:.(6<.(?.&8.+?3.))(1:.$3:.(6<.(?.&8.+?3.))(1?.$3:.))))))))))))))))))P,(39.$61.R2<.(1=.(15.&40.Vsp,)-68.)(1:.$3:.(3;.Vs11,)(1:.$3:.(3;.Vs10,)(1:.$3:.(3;.Vs9,)(1:.$3:.(3;.Vs8,)(1:.$3:.(3;.Vs7,)(1:.$3:.(3;.Vs6,)(1:.$3:.(3;.Vs5,)(1:.$3:.(3;.Vs4,)(1:.$3:.(3;.Vs3,)(1:.$3:.(3;.Vs2,)(1:.$3:.(3;.Vs1,)(1:.$3:.(3;.Vs0,)(1:.$3:.(3;.Vra,)(1?.$3:.)))))))))))))))P,(39.$61.R2=.(1=.R2?.+18.)(1:.$3:.(3;.R11.)(1?.$3:.)))P,(39.$61.R2>.(1=.R30.+30.)(1:.$3:.(3;.R11.)(1?.$3:.)))P,(14.$61.R2?.R31.(1=.R31.+18.))P,(14.$61.R30.(1=.R32.+20.)(1=.R32.+30.))P,(14.$61.R31.(1=.R33.+38.)(1=.(15.&40.Vsp,)-68.))P,(14.$61.R32.Vlo,R34.)P,(13.$61.R33.)P,(6=.$61.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(18.VR,)(1?.$65.)Vm,R34.)P,(39.$61.R35.VPKA,(1:.$3:.(3;.(?.&40.Vinfo,))(1:.$3:.(3;.(?.&40.VC,))(1?.$3:.))))P,(43.$61.(44.VR,)(23.$61.VR,VHIA,Vh,)R36.VPKA,+10.)P,(39.$61.R37.VC,(1:.$3:.(74.(?.&40.=))(1:.$3:.(74.R19.)(1?.$3:.))))P,(43.$61.(44.VR,)(23.$61.VR,VHIA,Vh,)R38.VC,+8.)P,(2<.(24.(1=.R3<.+80.)VPKA,)(24.(1=.VPKA,+10.)R3<.))P,(2<.(24.(1=.VPKA,+10.)Vlo,)(24.(15.&40.Vsp,)VPKA,))P,(2<.(24.(1=.R3>.+80.)VC,)(24.(1=.VC,+8.)R3>.))P,(42.=VC,)P,(24.(1=.VC,+100.)(75.(46.VR,)))P,(;.$6.(41.VC,+8.)=)P,(2<.(24.(1=.VPKA,+10.)VC,)(24.(1=.VC,+100.)VPKA,))(6>.$61.(44.VR,)(23.$61.VR,VHIA,Vh,)(76.R43.R42.R41.)(=.(>.(?.&40.+=:1>0.)(?.&40.R42.)Vgp,Vtp,R3?.R3>.R3=.Vsp,(?.&40.R42.)(?.&40.R43.)R3<.R3;.R3:.R39.R38.R37.R36.(?.&40.Vid,)(?.&40.(6:.(44.VR,)))(?.&40.VPKA,)R31.R30.R2?.(?.&40.(1=.(6;.R43.+3.)(6:.(44.VR,))))(?.&40.R43.)R2>.(?.&40.(1=.(6;.VPKA,+3.)(6:.(44.VR,))))R35.R34.R33.R32.)VF,(?.&40.+=:298.)Vfc,(11.(2.&40.))R40.(12.$61.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until idpad.
  intros SP1 SP1M HH1 Ehcs Ehtop Estk F64 FRSH FHD L32 L64 L96 FSHX SAVE SLOT24 SLOT48 STlo STmid SThi STbelow MI1 PRES
    HPKA OPKA HGD OC APP DSP APC C0 CAC CAL DPC.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP.
  rewrite Ehtop, Estk in HTOP.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia | lx_side_lia ]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR NER TOP HTOP; lia | lx_side_lia ]]).
  assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]).
  destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
    as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
  
    assert (OINF : forall mx, HM asegs R HIA h1 LB ((FB, 128) :: LF) mx -> aobj asegs AL CS mx info 4).
    { intros mx HHx. pose proof (hm_img_shadow asegs R HIA h1 _ _ mx HHx) as ISH. pose proof (hcs_img_cs R HIA h1 IMG (proj2 (proj2 (proj2 IMG')))) as ICS. rewrite Ehcs in ICS. clear - EI ISH ICS. unfold A_EC_INFOS, A_ECKEY_INFO, A_ECKEYDH_INFO, A_ECDSA_INFO in EI. cbn [In] in EI. destruct EI as [<-|[<-|[<-|[]]]]; (eapply aobj_img; [exact ICS| exact ISH| vm_compute; reflexivity]). }
  pose proof (A_pk_get_type_spec AL IMG L) as GT'.
  unfold pk_get_type_stmtA, A_PK_GET_TYPE in GT'.
  lx_pre. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  lx_pre. lx_run_tac (PLAN [0x05306c; 0x0b195c; 0x0d0988; 0x0da400; 0x0da4f0; 0x0da4fc; 0x0da50c] [(0xda368, DJoin); (0xda3dc, DJoin)] 250%N).
  lx_tree. all: lxu_chk_leaves 0x0da4f0. all: lxu_chk_leaves 0x0da4fc. all: lxu_chk_leaves 0x0da50c.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda2e0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xb195c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH1 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH1 end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH1 (FB + 96) 2%nat as OL96 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB1; pose proof (RTCL mx (hm_rtc asegs R HIA h1 _ _ mx HHc)) as RT1; pose proof (OINF mx HHc) as OI1 end end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GT' with (CS := CS) (A := FB + 96) (info := info) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | (right; right; exact EI) | (intros _; exact OI1) | lazymatch goal with | |- _ => clear - SP1 SP1M SLO NEEDR NER F0 F1 F8 F64 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT1-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "GT1-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear OL96; try clear AB1; try clear RT1; try clear OI1| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : In info A_EC_INFOS -> 2 <= ?t <= 4 |- _ => pose proof (H EI) as TYB; clear H end| |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xd6fa4: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x05306c; 0x0b195c; 0x0d0988; 0x0da400; 0x0da4f0; 0x0da4fc; 0x0da50c] [(0xda368, DJoin); (0xda3dc, DJoin)] 250%N); lx_tree; lxu_chk_leaves 0x0da4f0; lxu_chk_leaves 0x0da4fc; lxu_chk_leaves 0x0da50c | |- _ => idtac end.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda334) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xb195c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH2 end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH2 (FB + 64) 2%nat as OL64 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2; pose proof (RTCL mx (hm_rtc asegs R HIA h1 _ _ mx HHc)) as RT2; pose proof (OINF mx HHc) as OI2 end end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GT' with (CS := CS) (A := FB + 64) (info := info) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | (right; right; exact EI) | (intros _; exact OI2) | lazymatch goal with | |- _ => clear - SP1 SP1M SLO NEEDR NER F0 F1 F8 F64 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT2-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "GT2-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear OL64; try clear AB2; try clear RT2; try clear OI2| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : In info A_EC_INFOS -> 2 <= ?t <= 4 |- _ => pose proof (H EI) as TYB2; clear H end| |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xd6ff8: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x05306c; 0x0b195c; 0x0d0988; 0x0da400; 0x0da4f0; 0x0da4fc; 0x0da50c] [(0xda368, DJoin); (0xda3dc, DJoin)] 250%N); lx_tree; lxu_chk_leaves 0x0da4f0; lxu_chk_leaves 0x0da4fc; lxu_chk_leaves 0x0da50c | |- _ => idtac end.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda334) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xb195c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename FSH2 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH2 end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => frame_aobj FSH2 (FB + 64) 2%nat as OL64 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2; pose proof (RTCL mx (hm_rtc asegs R HIA h1 _ _ mx HHc)) as RT2; pose proof (OINF mx HHc) as OI2 end end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callxA_sp sp1 (eapply GT' with (CS := CS) (A := FB + 64) (info := info) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity; try (exact (art_alwf asegs R HIA)); first [ solve_crange | (right; right; exact EI) | (intros _; exact OI2) | lazymatch goal with | |- _ => clear - SP1 SP1M SLO NEEDR NER F0 F1 F8 F64 ALO LOS ACP ACV; first [lia | Z.div_mod_to_equations; lia] end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "GT2-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "GT2-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear OL64; try clear AB2; try clear RT2; try clear OI2| |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m3 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => match goal with H : In info A_EC_INFOS -> 2 <= ?t <= 4 |- _ => pose proof (H EI) as TYB2; clear H end| |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0xd6ff8: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; lx_pre; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x05306c; 0x0b195c; 0x0d0988; 0x0da400; 0x0da4f0; 0x0da4fc; 0x0da50c] [(0xda368, DJoin); (0xda3dc, DJoin)] 250%N); lx_tree; lxu_chk_leaves 0x0da4f0; lxu_chk_leaves 0x0da4fc; lxu_chk_leaves 0x0da50c | |- _ => idtac end.
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda3a8) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xb195c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xd7054 (A_PK_GET_TYPE)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda400) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xd0988) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xd7088 (A_ECP_GROUP_LOAD_E)" ]; try clear LXM| |- _ => idtac end.
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0xda400) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0xd0988) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (lx_leaf) | idtac "lxw: no original call block for site 0xd7088 (A_ECP_GROUP_LOAD_E)" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xda400) _ _ _ (seg_rom _)] => lx_apply epi_walk | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  all: match goal with |- ?g => idtac "lxw seg_A: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HGL : ecp_group_load_stmtA asegs R HIA MT ca ONE A_ECP_GROUP_LOAD_SG.
  Variables (idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ : word).
  Local Notation KPI := (kp_init C idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ).
  Local Notation GI := (grp_init C idpad pP pA pB pX pY pZ pN hpad).
  Hypothesis HPKA0 : rw_cells asegs m PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis CRP : client_range L (LB ++ fdata LF) lo PKA 16.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis KP0 : ecp_keypair_at asegs MT m LB C KPI.
  Hypothesis INC : In (C, 256) LB.
  Hypothesis BUD : havol asegs R HIA h + pk_set_group_PHI <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + pk_set_group_FR <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_GROUP_LOAD <= C24MAX.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00l0?L11036440459.1 L13141509838.3 L15100951376.3 L1540877545.3  L18632861404.1 L19164520863.19L19965341046.19L21926499533.1 L2275137097.0  L2295337761.0  L23212527412.10L24128180555.1 L24502405210.1 L24711474703.1 L2549369822.10 L25985555144.1 L26892418956.1 L27188209011.3 L28390317327.1 L31995967304.1 L32550613799.5 L32586543723.0 L33238509327.1 L34014865929.19L3480690467.19 L35130921566.10L3532368918.3  L35653441506.10L37156630869.0 L38105656719.1 L38948636245.0 L39280637297.0 L40281191306.3 L40747269196.7 L44032381512.1 L45274923535.1 L46472593243.8 L49528903902.10L50059436232.1 L50790761713.7 L51240997340.1 L51460973114.1 L52045659405.3 L54262396250.1 L54526232525.1 L57463760624.3 L59314923118.1 L60098763854.3 L60408377438.10L62018535662.1 L6203936179.1  L63812927907.4 L63918187566.1 L6450286553.1  L64515521675.1 L6899380056.1  L7237223214.1  L9356559645.12 L957827166.0   L9631767084.2  00000300=00E00Q00T01E02:02=02>02?02e02i02l02o03U03Z03^03g03k04004=04>04A04l05\06B06M06e06f06i06j06k07407H07M07P07n08T08Y09409709:09F09I09L09V09Y09c0:I0:L0:Q0:[0:^0:a0:d0:h0:k0;Z0;[0;bS1CS1C2FB3APCS1C1A2HoS2sp3sp13SP1S1CS1R5NEEDR2sp1C2lo3LOS3SLO3ALO3ACV3NER3CAC3sp13SP1S1R3HIA5NEEDR1h2sp2lo3LOS3SLO3TOP3ALO3ACV3NER3sp13SP1S1CSSS1R5NEEDR2sp1C2lo3SLO3NER3sp13SP14STKCS2FBS1CS1CS1R5NEEDR2sp1C2lo3SLO3NER3sp13SP14STKCS3sp1S2spS2FB1c2HcS2FBS3sp1S1R1C3ALO3CACSS1CS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3sp13SP14SP1MS1R5NEEDR2sp1C2lo3SLO3NER3sp13SP14STKCS3PKA1C3DPCS1R3HIA1h2sp2lo3TOP4HTOPSS1CSSS1R3HIA1hS1R1C2lo3LOS3ALO3CACS3sp1S1CS1R5NEEDR2sp1C2lo3SLO3NER4STKCS1R5NEEDR2sp1C2lo3SLO3NER3sp13SP14STKCS3sp1S1R5NEEDR2sp2lo3LOS3SLO3NERS1CS1CS2sp3sp13SP1S1CS1CS1C2FB3APCS1KS1R2lo3LOSS1R5NEEDR2sp1C2lo3SLO3NER3sp13SP14STKCS1RS3sp1S1C1A1k2HAS1CS1CS1CS2FBS1CS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3SPR3sp13SP1SS2FB2F0". (* [comment removed for export] *)
  Lemma sg_main : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(29.$61.VR,VHIA,Vh,VLB,VLF,Vm,)P,(22.$61.VR,VHIA,Vh,Vmo0,)P,(14.$61.Vm,Vlo,(15.&40.Vsp,))P,(13.$61.Vm,)P,(43.$61.(44.VR,)(23.$61.VR,VHIA,Vh,)Vm,VPKA,+10.)(53.$61.(54.$61.VR,VHIA,VMT,Vca,VONE,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VPKA,Vinfo,VC,(3>.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vpd,VqX,VqY,VqZ,)Vid,Vlo,Vm,Vmo0,)(<.(=.(>.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(?.&40.VPKA,)(?.&40.Vid,)R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(?.&40.$70.)Vfc,(11.(2.&40.))Vm,(12.$61.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST MI OPKA0.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR NER TOP HTOP; lia]).
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HBR0 _. rewrite Forall_forall in HBR0.
    destruct (HBR0 _ ltac:(apply in_app_iff; left; exact INC)) as (C0 & _ & CAC & _). cbn [fst snd] in C0, CAC.
    flat constr:(KP0) 6%nat. intros HG0 ED0 MD0 FD0 HQ0 FQ0. cbn [kp_grp kp_d kp_Q kp_init] in HG0, ED0, MD0, FD0, HQ0, FQ0.
    flat constr:(HG0) 3%nat. intros HGD0 CAL _. cbn [grp_head_cells grp_init g_id g_idpad] in HGD0.
    assert (PHI0 : 0 <= pk_set_group_PHI) by (unfold pk_set_group_PHI, group_load_PHI, grow_PHI, AVOL_CALL; clear; lia).
    assert (FR0 : 0 <= pk_set_group_FR) by (unfold pk_set_group_FR, group_load_FRn, calls_FR, fr_charge; clear; lia).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & w0 & w1 & w2
                   & l32a & l32b & l64a & l64b & l96a & l96b & w24 & w48
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & L32 & L64 & L96 & FSHX
                   & SAVE & SLOT24 & SLOT48 & STlo & STmid & SThi & STbelow & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    (* [comment removed for export] *)
    assert (CRPs : client_range L (LB ++ fdata LF) (bv_unsigned sp) PKA 16).
    { eapply client_range_sep; [exact CRP| intros b Hb; exact Hb| exact DSP]. }
    assert (HPKA1 : rw_cells asegs m1 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]) by (eapply heap_presx_rw_cells; [exact HPX01| exact HPKA0| exact CRPs| cbn; exact I]).
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (OPKA1 : aobj asegs AL CS m1 PKA 16).
    { eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OPKA0| exact CRPs| clear - LOS SLO NEEDR NER; lia| exact TOPCS]. }
    assert (CRC : forall A n, C <= A -> A + n <= C + 256 -> client_range L (LB ++ fdata LF) (bv_unsigned sp) A n).
    { intros A n Ho Hn. eapply client_range_block; [apply in_app_iff; left; exact INC| exact Ho| exact Hn]. }
    assert (HGD1 : rw_cells asegs m1 C [C4 (Z_to_bv 64 0); C4 idpad]).
    { eapply heap_presx_rw_cells; [exact HPX01| exact HGD0| apply CRC; cbn; clear; lia| cbn; exact I]. }
    assert (OC1 : aobj asegs AL CS m1 C 8).
    { pose proof (hm_aobj_block asegs R HIA h1 LB _ m1 C 256 HH1 INC) as K. rewrite Ehcs in K. eapply aobj_sub; [exact K| clear; lia| clear; lia]. }
    assert (APP : FB + 128 <= PKA \/ PKA + 16 <= FB).
    { destruct (frame_apart_obj0 R HIA LB LF lo PKA 16 FB 128 FRSH CRP ltac:(clear; lia) ltac:(clear; lia) LOS) as [K|K]; [exfalso; clear - K; lia| exact K]. }
    assert (APC : FB + 128 <= C \/ C + 256 <= FB) by (apply F3; apply in_app_iff; left; exact INC).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply seg_A with (h1 := h1) (idpad := idpad); first [ eassumption | reflexivity | (clear - APC; lia) | match goal with |- ?g => idtac "SEGA-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 CQ.
    (* [comment removed for export] *)
    destruct CQ as (mc & c0 & c1 & c2 & ca2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & s5c & s7c & s10c & v0 & v1 & v2
                    & -> & HHc & FHDc & FSHXc & SAVEc & SLOT24c & SLOT48c & STloc & STmidc & SThic & STbelowc & MIc & PRESc).
    clear FHD L32 L64 L96 FSHX SAVE SLOT24 SLOT48 STlo STmid SThi STbelow HPKA1 OPKA1 HGD1 OC1 HH1 PRES0 HP01 HPX01.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m mc PRESc) as HP0c.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP0c) as HPX0c.
    pose proof (hm_aobj_block asegs R HIA h1 LB _ mc C 256 HHc INC) as OCc.
    assert (NHG : forall e, In e (grp_mpds GI) -> md_own e <> LHeap) by (intros e He; rewrite (grp_init_noheap _ _ _ _ _ _ _ _ _ _ e He); discriminate).
    assert (HGc : ecp_group_at asegs MT mc LB C GI).
    { pose proof (ecp_group_at_LB_noheap asegs MT m LB (LB ++ fdata LF) C GI HG0 NHG) as G0.
      eapply (ecp_group_at_presx asegs L MT m mc (LB ++ fdata LF) LB (bv_unsigned sp) [] C GI G0 HPX0c MI MIc);
        [apply CRC; clear; lia| cbn; exact I|].
      intros d Hd O. exfalso. exact (NHG d Hd O). }
    pose proof HGL as GL'. unfold ecp_group_load_stmtA, A_ECP_GROUP_LOAD_SG in GL'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GL' with (h := h1) (LB := LB) (LF := (FB, 128) :: LF) (A := C) (g := GI) (id := id) (lo := lo) (d := 0);
        rewrite ?grp_free_LB_initA; rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop, ?Evol, ?Efr;
        first [ exact HHc | exact HGc | exact IDB | exact STbelowc | exact LOS | exact MIc | exact TPV | exact C24H | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- mpds_apart _ => intros d1 d2 H1 H2 NE O1 O2; exfalso; exact (NHG d1 H1 O1)
                | |- client_wrange _ _ _ _ C _ => eapply client_wrange_block; [apply in_app_iff; left; exact INC| clear; lia| unfold ECP_GROUP_SIZE; clear; lia]
                | |- aobj _ _ _ _ C _ => eapply aobj_sub; [exact OCc| clear; lia| unfold ECP_GROUP_SIZE; clear; lia]
                | |- uw_obj _ _ _ _ => left; split; [unfold ECP_GROUP_SIZE; clear - CAC ACV ALO; lia| clear; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold pk_set_group_PHI in BUD; exact BUD
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold pk_set_group_FR in BUDF; exact BUDF
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ => unfold ECP_GROUP_SIZE; clear - SP1 SP1M SLO NEEDR NER TOP C0 CAC ACV ALO LOS SPR; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "GL-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    unfold ecp_group_load_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & r & g' & NB & LB2
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & LEQ & LNEW & HG2 & AP2 & GB2 & RES & OC2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xda400)) with (Z_to_bv 64 0xda400 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite grp_free_LB_initA in HP2, LEQ, LNEW.
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    rewrite Ehtop in HT2. rewrite Estk in HS2, HP2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2.
    unfold ECP_GROUP_SIZE in HP2.
    assert (HCSh2 : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; apply HCS2; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h2) as CSOK2.
    pose proof (fresh_apart_relist_sg R HIA h2 LB LB2 LF m2 FB 128 FRSH HH2) as FRSH2.
    assert (SUB2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply LEQ; right; exact Hb).
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(C, C + 192)] mc m2).
    { eapply presA_weaken; [exact HP2| intros b' Hb; exact Hb| intros b' Hb; right; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRESa2 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [(C, C + 192)] m m2).
    { flat constr:(PRESc) 4%nat. flclear PRESc. intros P0 C1 C2 C3. split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans.
      - eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I].
      - exact HP2'. }
    pose proof (presW_hmono R HIA h h2 LB LF _ _ _ m _ PRESa2 HCSh2 HS2) as PRESa2h.
    pose proof (presW_init_at R HIA h2 _ _ LB2 LF m2 (bv_unsigned sp) (arl_stklo R) [] h2 HH2
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 128 -> cshd R LBq ((FB, 128) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJX : forall A k, (A + k <= C \/ C + 256 <= A) -> disjoint_from [(C, C + 192)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    assert (STKC : C + 256 <= lo) by (clear - CAC ACV ALO LOS; lia).
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(C, C + 192)] mc m2 FB _ CSOK) in FSHXc;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 FB _ HP2) in FHDc;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | apply DJX; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SAVEc; [| apply client_range_stack; clear - SP1; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR NER; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SLOT24c; [| apply client_range_stack; clear; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR NER SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SLOT48c; [| apply client_range_stack; clear; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR NER SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in STloc; [| clear; lia| apply DJX; clear - STKC SLO NEEDR NER SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in STmidc; [| clear; lia| apply DJX; clear - STKC SLO NEEDR NER SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SThic; [| clear; lia| apply DJX; clear - STKC SLO NEEDR NER SP1; lia].
    (* [comment removed for export] *)
    assert (DJX' : forall A, C + 192 <= A -> disjoint_from [(C, C + 192)] A 16) by (intros A Ho; cbn [disjoint_from]; split; [clear - Ho; lia| exact I]).
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo0).
    { eapply epi_walk with (h3 := h2) (LBa := LB) (LBb := LB2) (m0 := m) (m2x := m2) (WA := [(C, C + 192)]) (WB := @nil ivl) (FB := FB) (sp1 := sp1);
        first [ exact HH2 | exact HCSh2 | exact HT2 | exact HS2 | exact PRESa2h | exact PRESb2 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact SUB2
              | exact SP1 | exact SP1M | exact F64 | exact FHDc | exact FSHXc | exact SAVEc | exact SLOT24c | exact SLOT48c | exact STloc | exact STmidc | exact SThic
              | exact ST2 | exact MI2 | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold pk_ecc_set_group_postA.
    do 14 eexists. exists m9, mo9, h4, r, g', NB, LB2.
    pose proof (presW_presA asegs R HIA h2 _ LF _ _ _ _ _ PRES9) as HPF. rewrite HS2 in HPF.
    pose proof (presW_presA asegs R HIA h2 _ LF _ _ _ _ _ PRES29) as HPF2.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [unfold ECP_GROUP_SIZE; exact HPF|].
    split; [rewrite E4top; exact HT2|]. split; [rewrite E4stk; exact HS2|]. split; [rewrite E4flag; exact HF2|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSh2 x Hx)|].
    split; [rewrite E4vol; unfold pk_set_group_PHI; exact HV2|]. split; [rewrite E4fr; unfold pk_set_group_FR; exact HFR2|].
    split; [exact HH4|].
    split; [exact LEQ|].
    split.
    { intros b Hb. flat constr:((LNEW b Hb)) 2%nat. intros N1 N2. split; [exact N1|].
      eapply fresh_apart_frames_mono_sg; [exact N2|]. intros b' Hb'. eapply fdata_incl; [| exact Hb']. intros fb Hfb. right. exact Hfb. }
    split.
    { (* [comment removed for export] *)
      cbn [kp_d kp_Q kp_init].
      split.
      { pose proof (ecp_group_at_LB_mono asegs MT m2 LB2 (LB2 ++ fdata LF) C g' HG2 ltac:(intros b Hb; apply in_app_iff; left; exact Hb)) as G2.
        eapply (ecp_group_at_presx asegs L MT m2 m9 (LB2 ++ fdata LF) LB2 (bv_unsigned sp) [] C g' G2 (presA_presx asegs R _ _ _ _ _ _ _ _ HPF2) MI2 MI9);
          [eapply client_range_block; [apply in_app_iff; left; apply SUB2; exact INC| clear; lia| clear; lia]| cbn; exact I|].
        intros d Hd O. split; [exact (ecp_group_at_heap_in asegs MT m2 LB2 C g' d HG2 Hd O)| cbn; exact I]. }
      cbn [kp_grp kp_d kp_Q].
      split; [exact ED0|]. split; [| split; [exact FD0| split; [| exact FQ0]]].
      - eapply (mpdr_init_presA R LB LF _ _ _ _ m m9 LB LB2); [exact MD0| exact HPF| apply CRC; clear; lia| apply DJX'; clear; lia].
      - flat constr:(HQ0) 6%nat. flclear HQ0. intros EX EY EZ MX MY MZ. cbn [pt_init pt_X pt_Y pt_Z] in *.
        split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
        split; [eapply (mpdr_init_presA R LB LF _ _ _ _ m m9 LB LB2); [exact MX| exact HPF| apply CRC; clear; lia| apply DJX'; clear; lia]|].
        split; [eapply (mpdr_init_presA R LB LF _ _ _ _ m m9 LB LB2); [exact MY| exact HPF| apply CRC; clear; lia| apply DJX'; clear; lia]
               | eapply (mpdr_init_presA R LB LF _ _ _ _ m m9 LB LB2); [exact MZ| exact HPF| apply CRC; clear; lia| apply DJX'; clear; lia]]. }
    split; [exact AP2|]. split; [exact GB2|]. split; [exact RES|].
    eapply (presA_rw_cells asegs R _ _ _ _ _ _ m m9 _ _ HPF); [exact HPKA0| exact CRPs| cbn; clear - DPC; lia].
    all: match goal with |- ?g => idtac "POST-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Theorem A_pk_ecc_set_group_spec_s : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "P,(77.$61.VR,VHIA,VMT,Vca,VONE,$73.)(78.$61.VR,VHIA,VMT,Vca,VONE,$79.$70.)")
(* [comment removed for export] *).
  Proof.
    intros HGL. unfold pk_ecc_set_group_stmtA. intros until qZ. cbv zeta.
    intros HH HK0 LFB HPKA ALP NZP EI OPKA CRP DSP DPC KP INC IDB ST LOS SLO TOP SPA TPV MI RA BUD BUDF C24H -> ->.
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    unfold ECP_KEYPAIR_SIZE in *.
    eapply sg_main with (lo := lo);
      first [ eassumption | reflexivity | (clear - SLO; lia) | (clear - PKB NZP; lia) | match goal with |- ?g => idtac "THM-LEFT:" g end ].
  Qed.
End WalkSG.

Theorem A_pk_ecc_set_group_spec : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecc_set_group ()) "PR,$5?.PHIA,(60.$61.R1.)PMT,(8.$58.)Pca,P,$6.$7:.PONE,$6.P,(7;.(44.R5.))P,(;.$6.(7<.R6.)$7=.)P,(;.$6.(7>.R7.+1.)$7?.)P,(24.=(80.R8.))P,(24.=(81.R9.))P,Pm,P,(2.&40.)(3.(2.&8.))P,(82.R;.R1.)(83.R2.)P,(77.$61.R;.R:.R9.R8.R7.$73.)(78.$61.R<.R;.R:.R9.R8.$79.$70.)")
(* [comment removed for export] *).
Proof. intros. eapply A_pk_ecc_set_group_spec_s; eassumption. Qed.
