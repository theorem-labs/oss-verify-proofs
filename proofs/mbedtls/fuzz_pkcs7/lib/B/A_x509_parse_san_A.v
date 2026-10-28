(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_crt_parse_stmts A_x509_get_name_stmt A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00424f207f104737 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P0091a2637c2f453f 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P00ff52d8bdd31c49 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P00ffe02645effb3a 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P0142f85bc7e6d5bd 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P0189c3c5c2203965 0 3 0 1 41 1 49 1P01a12a7ec179360c 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P0219c87c7b767fc9 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P036b0a0c33b0f517 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P03d77b624317a22c 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P0455009ecf2a0906 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P05237199c7daa161 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P0539a122b40a1587 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P0579c67a1080ac64 0 4 0 1 65 1 77 1 78 1P05d9a875678997bd 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P06a8ee366d0d6a48 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P06b39bb441a2a110 0 5 0 1 35 1 54 1 76 1 77 1P06c697b628a860a1 0 4 0 1 65 1 77 1 78 1P06e10a1c142adc8a 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P07c6fa3d7a7af38a 0 4 0 1 54 1 76 1 77 1P08521f113e7fb71f 0 5 0 1 35 1 54 1 76 1 77 1P08c6d11dcbd4fdee 0 4 0 1 65 1 77 1 78 1P08d825b80779af25 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P08ed92af6dce4b23 0 4 0 1 54 1 76 1 77 1P09719d3275ea88a7 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P09b70e9e236ff6a8 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P0a1f2bfbc6d7a8bd 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P0a312510189e3da7 0 4 0 1 54 1 76 1 77 1P0aa09fe3f155b920 0 5 0 1 35 1 54 1 76 1 77 1P0ac7bbc6ad67e74a 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P0acabee02c5ed9b1 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P0ae64eedde1cda58 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P0ae8491ff368cb17 0 4 0 1 65 1 77 1 78 1P0b157244b5f8c523 0 4 0 1 54 1 76 1 77 1P0c0c891bfeee3581 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P0ca90fe5adcb88cd 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P0d8edb6b90214b4d 0 4 0 1 54 1 76 1 77 1P0e9b5716956d8a4e 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P1023e4dac8f7dc7c 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P104f79f4e3224e06 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P108502de1d101f79 0 4 0 1 54 1 76 1 77 1P108d47d5da8f50b4 1 1 64 2 35 1 89 1 3 0 1 88 1 90 64P11ff55542dff57a2 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P121aac2e89d8f372 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P12ffbdb13929702c 0 5 0 1 35 1 54 1 76 1 77 1P13bd3073907a5298 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P147232ca21361db2 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P14776fca98d0fe48 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P147cc53e06161c0f 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P151d073f84876c5d 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P153258191136af2c 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P159a9bd441aa319a 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P160f09192c437883 0 4 0 1 54 1 76 1 77 1P162a8fc146de8dd2 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P162e2ada909b9803 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P16575db87fcfbfc7 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P16b713e86963cca7 0 4 0 1 65 1 77 1 78 1P16eda9c81c81e679 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P173a914dafe2e08a 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P17975d4f5d220d6f 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P17c9a81740aa1ed0 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P184c03cf5672450d 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P19503b7dd3ce69a4 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P197f67b40adf3751 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P1a0457b336913743 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P1a4a0213acaf9df5 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P1a546b4c409e3bfd 0 5 0 1 35 1 54 1 76 1 77 1P1af3a0561be8b6a0 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P1b308be766dfc317 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P1b7fd34205087c82 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P1b9ad288944c02b0 0 5 0 1 35 1 54 1 76 1 77 1P1bb74c56c0693cde 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P1bdfc4de20cf981d 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P1c16a48f4d5f3336 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P1d4a6f349ec89e05 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P1dbaee7883046212 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P1ddbe5bc5d120d7d 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P1de80c480b85dec7 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P1e38dd18ba2f93ef 0 4 0 1 65 1 77 1 78 1P1e3aca7bd82164f7 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P1e80fa055e097b99 0 5 0 1 35 1 54 1 76 1 77 1P1f30c6952e395805 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P1f5d0e47a39afb6a 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P1fb13a0340e4f034 0 5 0 1 35 1 54 1 76 1 77 1P1fb70a842a9791ea 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P1fc499cf21508ee0 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P20f48451390787d4 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2194838c99280c81 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P21b55a86550338f2 0 5 0 1 35 1 54 1 76 1 77 1P21deaa89a43c067c 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P2256d92f3d210aa3 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P230e29248d87d2ed 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P23a9fa9c59d7dd50 1 1 16 2 0 1 76 1 3 11 1 77 1 78 16P23aaf2065635ffe3 0 4 0 1 65 1 77 1 78 1P23bbb711701334b3 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P23e4df20040ea8d1 0 5 0 1 35 1 54 1 76 1 77 1P23f2375900dcb3ed 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P25d1ee26ded7d898 0 5 0 1 35 1 54 1 76 1 77 1P25e6fc27315b22e6 0 4 0 1 54 1 76 1 77 1P2744a6dc6316c222 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P27f5c9ed1b4383c4 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2819e03178ce0248 0 4 0 1 54 1 76 1 77 1P288d805f07211198 0 4 0 1 65 1 77 1 78 1P28ccfa58d2e071d4 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P28d9ff7401949313 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P28da7e696207246f 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P299f03ec4af96d2f 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P2a15c3a3e8115d15 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P2a9b6a8419759581 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P2aba0a5185224bf1 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P2b06eaff12c99a72 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P2b08c743728579a9 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P2bb842c457ca5b28 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P2bfbbd29dca9f1b8 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P2caf50c0843527a5 1 1 16 2 33 1 76 1 3 0 1 77 1 78 16P2cb0e00029409846 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2cb187ca707f484e 1 1 16 3 1 1 44 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2d3d4a492b969e54 0 4 0 1 54 1 76 1 77 1P2d802e87385f2d10 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2dab840600797264 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P2db2969c58ed1b2e 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2e28a9a72f1a297c 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P2f9737b8d27bf687 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P2ffcd9da2b3f3b32 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P30066af14f1c544c 0 4 0 1 65 1 77 1 78 1P306cab84a9600637 0 5 0 1 35 1 54 1 76 1 77 1P30b76ecb7f45c658 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P30cd35986f549ac3 1 1 16 4 1 1 38 1 46 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P310c2060579755b1 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P31700c718aaa8350 0 4 0 1 65 1 77 1 78 1P3179056c6fe056e6 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P3199c1c29d4f0c44 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P31ffae3114027485 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P323574c837fcb9dd 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P327e3305f53bea9d 1 2 16 2 0 1 78 1 16 2 1 1 77 1 2 79 1 80 1P32803d65c43ab53b 0 4 0 1 54 1 76 1 77 1P32c7c236e6afbdab 0 4 0 1 65 1 77 1 78 1P331eccad217daac2 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P33ceef4d403bc993 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P33e5b5d4f81a7aff 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P3410bcb72d1a89ac 0 4 0 64 13 64 88 64 89 64P341c11a52d6cabc2 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P345bd2807833a74e 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1P34f14cc2aa8812c7 0 4 0 1 54 1 76 1 77 1P3504768c15bc708a 0 5 0 1 35 1 54 1 76 1 77 1P352f47de4d6a3eb6 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P35deba9c725beb14 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P35f69810f76de5d6 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P36d0ba728dbb5bac 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P36ed40b899fab037 0 4 0 1 54 1 76 1 77 1P38307cea533cb74e 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P38425095b8cf3a4c 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P387052de38a44724 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P38c333b01ffd609d 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P38f8049bd1620855 1 2 16 3 0 1 45 1 78 1 16 3 1 1 44 1 77 1 2 79 1 80 1P3902a7af8611ec50 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P39194e941381b928 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P399dd1f0699692e8 1 1 16 2 1 1 77 1 11 41 1 43 1 56 1 57 1 58 1 67 1 68 1 69 1 70 1 78 1 79 16P39d224c04029d23d 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P39db501b4f8ecd25 0 9 1 1 56 1 59 1 67 1 68 1 69 1 70 1 77 1 78 1P3a61b876240b3fc9 0 4 0 1 65 1 77 1 78 1P3a8797a7eb6da6e4 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P3aa0aa4c60fda533 0 5 0 1 35 1 54 1 76 1 77 1P3acb08632b40dd6f 0 3 0 1 42 1 52 1P3c40b19306a95d04 1 2 64 2 0 1 88 1 64 2 35 1 89 1 2 90 1 91 1P3cb11a8ef1cf661b 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P3d101aa32a4dcf7b 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P3d6a4771295f4a76 0 9 2 1 53 1 57 1 68 1 69 1 70 1 71 1 78 1 79 1P3e0d379b628bbbfc 0 10 0 1 55 1 56 1 57 1 66 1 67 1 68 1 69 1 76 1 77 1P3ea56cc0820e8970 0 4 0 1 65 1 77 1 78 1P3ebf4a32d4021612 0 8 0 1 55 1 66 1 67 1 68 1 69 1 76 1 77 1P3f1e729a17f9b618 0 4 0 1 65 1 77 1 78 1P3f2948492fd1212c 0 9 0 1 55 1 58 1 66 1 67 1 68 1 69 1 76 1 77 1P3f6f80187979fdff 0 4 0 1 54 1 76 1 77 1P3f751c9fd9643b73 0 12 0 1 51 1 55 1 60 1 61 1 62 1 66 1 67 1 68 1 69 1 76 1 77 1N056e6c857585bbf4N05ea3c0d3df4e629N06cdecef8022f30fN072c30456f8e7bd3N08069f21d21cd8a1N085387053e513e52N088c572807e132b6N08e7c31920905893N0921e0941193cb70N0a0ce443331c2f76N0bdb9d8aba0dbaa9N0dec4d144442f21bN0e03d64a17738f08N0e800d4bdb4951f2N1023c18130008b3bN108516827ae635b8N1098305285cf9907N1160b1038b1f9724N11dfdd604de64e73N14795fb81351811cN16204604ca739f1eN163d866aec94b5c9N196a0b70c60c9777N1e4e3d1aecdf0567N1e9ec526edd8b46eN1eb9b98204da5bccN1ee841bf79da5994N203f3333b295e133N20a37f57fda03f8bN20a869372d416698N21d69376387db696N21e6aa7f9b0ec12aN222cb57a4a6b577fN25f92684f447692bN2b9b3d9a5f977549N2cf03b38accbdb5fN2d022e82c9836ee4N2fbadc7f55c47862N34c5b2bf4176ffefN34f1207097824158N3522225684f5b879N35f940d7355789b9N364ee3931159a994N37156410fbe4f4ddN39006e2a22030682N398a31e44a58df70N39f7f918bb8e6155N3a1560d7ea1f6930N3aea727dbd184edcN3b515871ad9fd71dN3c1d1d99adb32203N3c27df5cfdb6a309N3d03b4b1ed6ab7b6N3e1aa2b021f3b5e4N3ecf5e0cb73c8c80N3ef61bfd6e1c9e9b"%lxh.
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
Ltac2 gd_tbl_A_x509_parse_san_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.CrtStmts.SNAME"; "Stdlib.Lists.List.rev"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.NAME_SIZE"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "Stmts.x509_parse_san_postA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_X509_PARSE_SAN"].


Definition A_X509_PARSE_SAN : Z := 0xaeb08.       (* [comment removed for export] *)
Definition A_SMALLOC_2S : Z := 0x531fc.            (* [comment removed for export] *) (* [comment removed for export] *)

Section Stmts.
  Variable segs : list Segment.
  Variable R : art_layout.
  Variable HIA : artA segs R.
  Let AL := arl_AL R.

  (* [comment removed for export] *)
  Definition x509_parse_san_postA
      (PHI : Z -> Z) (FFR : Z -> Z -> Z) (CNT : Z -> Z)
      (h : HST segs R HIA) (LB LF : list blk)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SAN n lo slo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_parse_san_A ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VR,VHIA,)Lh',(5.Vsegs,VR,VHIA,)(1.$6.Lr,$6.(1.$6.Lt,$6.(1.$6.Ldn,$6.(1.(7.$8.)Lrest,(7.$8.)(1.(7.$6.)Lnodes,(7.$6.)(9.(:.$0.R18.(;.(<.(=.O19.O18.O17.O16.R17.R16.R15.O15.O14.R14.R13.R12.R11.R10.R?.R>.R=.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R<.R;.R:.R9.)O9.(>.O19.)O8.(?.(2.&40.))R8.(10.Vsegs,))R7.))(9.(:.(2.&40.)R14.(11.&40.R5.))(9.(9.(12.-3000.R5.)(13.R5.=))(9.(14.Vsegs,R8.)(9.(15.Vsegs,R8.O5.(16.&40.O18.))(9.(17.Vsegs,VAL,R8.O4.(16.&40.O18.))(9.(18.O1.R7.)(9.(19.Vsegs,VR,O1;.O1:.(16.&40.O18.)(16.&40.O18.)(1:.Vsegs,VR,VHIA,O1<.)(1;.(1<.$6.$6.)(1=.$6.$6.O7.(1>.O7.+50.))(1?.(1<.$6.$6.)))O2.R8.)(9.(:.$6.(20.Vsegs,VR,VHIA,R6.)(20.Vsegs,VR,VHIA,O1<.))(9.(:.$6.(1:.Vsegs,VR,VHIA,R6.)(1:.Vsegs,VR,VHIA,O1<.))(9.(:.$6.(21.Vsegs,VR,VHIA,R6.)(21.Vsegs,VR,VHIA,O1<.))(9.(22.Vsegs,VR,VHIA,R6.R7.)(9.Px,$6.P,(23.Vsegs,VR,VHIA,O1<.R1.)(23.Vsegs,VR,VHIA,R8.R2.)(9.(13.(24.Vsegs,VR,VHIA,R6.)(1>.(24.Vsegs,VR,VHIA,O1<.)A1.O1?.O6.))(9.(13.(25.Vsegs,VR,VHIA,R6.)(1>.(25.Vsegs,VR,VHIA,O1<.)A2.O1>.O6.O3.))(9.(13.(26.(27.$6.R1.))A1.O1=.O6.)(9.(28.Vsegs,R8.O7.(1;.$8.(29.(11.&40.R4.))R2.))(9.(:.$6.(26.(2:.R2.))+4<.)(9.(9.(13.=R4.)(13.R4.+7.))(9.P,(:.$6.R4.+4.)(1.(7.(2.&8.))Lp4,(7.(2.&8.))(1.(7.(2.&8.))Lj48,(7.(2.&8.))(1.(2.&8.)Lmg,(2.&8.)(1.(7.(2.&8.))Lpad7,(7.(2.&8.))(1.(7.(2.&8.))Lj8,(7.(2.&8.))(:.(7.$8.)R8.(1;.$8.(2;.#4.R5.)(2<.$8.(2=.R4.R9.R3.R2.)(1;.$8.(2;.#8.R1.)(1?.$8.))))))))))(9.P,(:.$6.R4.+4.)(2>.Vsegs,L,(7.$8.)$2?.R9.(2<.$30.(31.(32.$6.R2.))O1;.)R4.R2.)(9.P,(33.(:.$6.R4.+4.))(:.(7.$6.)R2.(1?.$6.))(9.P,(33.(:.$6.R5.=))(:.(7.$6.)R2.(1?.$6.))(9.(34.$6.R1.)(9.Px,$6.P,(35.$6.R1.R2.)PB,$6.Pk,$6.P,(35.(1<.$6.$6.)(1=.$6.$6.R2.R1.)O1;.)(36.(13.(1>.R5.$37.)R3.)(13.(1>.R3.R2.)R5.))(38.Vsegs,VR,VHIA,R6.(2<.$30.(31.(32.$6.R1.))O1;.)O1:.R8.)))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition x509_parse_san_stmtA
      (PHI : Z -> Z) (FFR : Z -> Z -> Z) (CNT : Z -> Z) (STK : Z) (LFM : nat) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_parse_san_A ()) "Ph,(5.Vsegs,VR,VHIA,)PLB,(7.$30.)PLF,(7.$30.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(39.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PSB,$6.PSAN,$6.PBUF,$6.Psp0,$6.Pslen,$6.Plo,$6.Pslo,$6.Pd,$6.Pbs,(7.(2.&8.))Ptgw,(2.&40.)Ppdw,(2.&40.)P,(38.Vsegs,VR,VHIA,R31.R30.R2?.R=.)P,(22.Vsegs,VR,VHIA,R32.R=.)P,(3:.(27.$30.R31.)O2.)P,(28.Vsegs,R10.R>.(3;.R5.R4.R:.R;.))P,(:.$6.(3<.R?.+8.)=)P,(12.=R10.)P,(3=.Vsegs,VAL,(23.Vsegs,VR,VHIA,R37.)R13.R11.+18.)P,(3>.(3?.VR,)(2<.$30.R37.(40.R36.))R=.R12.+18.)P,(13.(16.&40.R35.)R13.)P,(13.(1>.R14.+20.)(41.+2.+2?.))P,(42.Vsegs,R17.R13.R=.)P,(35.(1<.$6.$6.)(1=.$6.$6.R14.(26.(27.(2.&8.)R>.)))R3;.)P,(13.R15.R14.)P,(13.=R14.)P,(13.(1>.R16.R15.)(1>.R17.(26.(27.(2.&8.)R11.))))P,(12.(1>.R18.(26.(27.(2.&8.)R12.)))(41.+2.+2?.))P,(12.=R19.)P,(12.(26.(27.(2.&8.)R14.))(41.+2.+1>.))P,(28.Vsegs,R1?.R1<.(1;.$8.(2;.#50.(43.(2.&8.)(11.&8.=)#50.))(1?.$8.)))P,(:.$6.(3<.R1=.+8.)=)P,(12.=R1>.)P,(3=.Vsegs,VAL,(23.Vsegs,VR,VHIA,R46.)R22.R1?.+50.)P,(44.(3?.VR,)(2<.$30.R46.(40.R45.))R1<.(20.Vsegs,VR,VHIA,R47.)R20.+50.)P,(13.(1>.R21.+50.)R1=.)P,(36.(13.(1>.R22.+50.)R23.)(13.(1>.R23.+18.)R22.))P,(36.(13.(1>.R23.+50.)R22.)(13.(1>.R22.(26.(27.(2.&8.)R1<.)))R23.))P,(36.(13.(1>.R25.+18.)R23.)(13.(1>.R23.(26.(27.(2.&8.)R1=.)))R25.))P,(15.Vsegs,R28.R21.(16.&40.R48.))P,(17.Vsegs,VAL,R29.R21.(16.&40.R49.))P,(13.(45.VR,)R22.)P,(13.R23.R24.)P,(13.R25.(46.(16.&40.R4<.)O3.))P,(13.(16.&40.R4=.)(20.Vsegs,VR,VHIA,R51.))P,(:.$6.(3<.(16.&40.R4>.)+10.)=)P,(13.(16.&40.R4?.)(41.+2.+2?.))P,(14.Vsegs,R30.)P,(:.(2.&40.)R4?.(11.&40.(47.VR,)))P,(34.$6.(48.(1<.$6.$6.)$6.(49.$6.$6.)R55.))P,(13.(1>.(24.Vsegs,VR,VHIA,R57.)A1.O6.R2=.)$4:.)P,(4;.Vsegs,R34.(45.VR,)(1:.Vsegs,VR,VHIA,R58.)(16.&40.R4>.)(16.&40.R54.)R2;.)P,(13.(1>.(25.Vsegs,VR,VHIA,R59.)A2.O5.R2?.R2<.)$4<.)P,(:.(2.&40.)R4>.(11.&40.R34.))P,(:.(2.&40.)R4>.(11.&40.R34.))(4=.Vsegs,(4>.O6.O5.O4.R5<.R5;.R5:.R59.R58.R57.R56.R52.R51.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3:.R39.R35.R32.R31.R30.R2?.R38.R37.)(;.(<.(=.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.)R3:.(11.&40.O1.)R39.(?.(2.&40.))R38.(10.Vsegs,))R37.))")
(* [comment removed for export] *).
End Stmts.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2S.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NA1 : 0 <= arl_need_amem R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Variable STKn : Z.
  Hypothesis STKn0 : 0 <= STKn.

  (* [comment removed for export] *)
  Definition STKps : Z := 176 + 48 + STKn + arl_need_smalloc R + arl_need_amem R + arl_need_bcmp R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (SB SAN BUF sp0 slen lo slo : Z) (bs : list byte) (tgw pdw : word).
  Hypothesis ALB : SB mod 8 = 0. Hypothesis SB0 : 0 < SB.
  Hypothesis CRSB : client_range L (LB ++ fdata LF) lo SB 24.
  Hypothesis SBHI : bv_unsigned sp <= SB. Hypothesis SB47 : SB + 32 <= 2^47.
  Hypothesis BIN : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis W1 : BUF <= sp0. Hypothesis W2 : 0 <= slen. Hypothesis W3 : sp0 + slen <= BUF + Z.of_nat (length bs).
  Hypothesis B47 : BUF + Z.of_nat (length bs) < 2^47. Hypothesis BUF0 : 0 < BUF. Hypothesis BSMALL : Z.of_nat (length bs) < 2^30.
  Hypothesis ALS : SAN mod 8 = 0. Hypothesis SAN0 : 0 < SAN.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SAN 80.
  Hypothesis SANLO : SAN + 80 <= lo.
  Hypothesis DSS : SAN + 80 <= SB \/ SB + 24 <= SAN.
  Hypothesis DSB : SAN + 80 <= BUF \/ BUF + Z.of_nat (length bs) <= SAN.
  Hypothesis DBB : SB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SB.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKps.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 511)%nat.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold STKps in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(SAN, SAN + 80)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_parse_san_A ()) "Lms,$4?.(1.$6.LFB,$6.(1.$6.Lsp1,$6.(1.(5.$50.VR,VHIA,)Lh1,(5.$50.VR,VHIA,)(1.P,(2.&40.)(3.(2.&8.))Lm1,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx10,(2.&40.)(1.(2.&40.)Lx11,(2.&40.)(1.(2.&40.)Lx12,(2.&40.)(1.(2.&40.)Lx13,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Lx28,(2.&40.)(1.(2.&40.)Lx29,(2.&40.)(1.(2.&40.)Lx30,(2.&40.)(1.(2.&40.)Lx31,(2.&40.)(1.(7.(2.&8.))Ljunk1,(7.(2.&8.))(1.(2.&40.)Ll1,(2.&40.)(1.(2.&40.)Ll2,(2.&40.)(1.(2.&40.)Ll3,(2.&40.)(1.(2.&40.)Ll4,(2.&40.)(1.(2.&40.)Lj16,(2.&40.)(1.(2.&40.)Lj24,(2.&40.)(1.(2.&40.)Lj48,(2.&40.)(9.(:.$4?.R1<.(<.(=.(11.&40.+:>;7<.)(11.&40.R1:.)Vgp,Vtp,R17.R16.R15.Vsp,(11.&40.R1:.)R14.R13.R12.R11.R10.R?.R>.R=.(11.&40.R1;.)(11.&40.VSAN,)(11.&40.VSB,)Vs5,Vs6,Vs7,Vs8,(11.&40.R1;.)(11.&40.(51.(52.VR,)))Vs11,R<.R;.R:.R9.)VF,(11.&40.+:>;;4.)Vfc,(?.(2.&40.))R18.(10.$50.)))(9.(9.(13.(46.(16.&40.Vsp,)+;0.)R1:.)(13.R1:.(46.(16.&40.Vsp,)+:0.)))(9.(:.$6.(3<.R1:.+20.)=)(9.(38.$50.VR,VHIA,R19.VLB,(1;.(1<.$6.$6.)(1=.$6.$6.R1;.+100.)VLF,)R18.)(9.(:.P,$6.Sp(23.$50.VR,VHIA,R19.)(23.$50.VR,VHIA,Vh,))(9.(:.$6.(20.$50.VR,VHIA,R19.)(20.$50.VR,VHIA,Vh,))(9.(:.$6.(1:.$50.VR,VHIA,R19.)(1:.$50.VR,VHIA,Vh,))(9.(:.$6.(21.$50.VR,VHIA,R19.)(21.$50.VR,VHIA,Vh,))(9.(:.$6.(24.$50.VR,VHIA,R19.)(24.$50.VR,VHIA,Vh,))(9.(:.$6.(25.$50.VR,VHIA,R19.)(25.$50.VR,VHIA,Vh,))(9.Pmo,$4.(53.(22.$50.VR,VHIA,R1:.R1.)(22.$50.VR,VHIA,Vh,R1.))(9.(:.$6.(3<.R1;.+40.)=)(9.(54.VR,VLB,VLF,R1;.+100.)(9.(28.$50.R18.R1;.(1;.$8.(2;.#18.R8.)(1?.$8.)))(9.(28.$50.R18.(1>.R1;.+20.)(1;.$8.(55.R7.)(1?.$8.)))(9.(28.$50.R18.(1>.R1;.+40.)(1;.$8.(55.R6.)(1?.$8.)))(9.(28.$50.R18.(1>.R1;.+60.)(1;.$8.(55.R5.)(1?.$8.)))(9.(28.$50.R18.(1>.R1;.+80.)(1;.$8.(55.R4.)(1?.$8.)))(9.(28.$50.R18.(1>.(56.R1;.+3.)(51.(52.VR,)))(57.#20.))(9.(28.$50.R18.(1>.(16.&40.Vsp,)-68.)(1;.$8.(55.Vs11,)(1;.$8.(55.Vs10,)(1;.$8.(55.Vs9,)(1;.$8.(55.Vs8,)(1;.$8.(55.Vs7,)(1;.$8.(55.Vs6,)(1;.$8.(55.Vs5,)(1;.$8.(55.Vs4,)(1;.$8.(55.Vs3,)(1;.$8.(55.Vs2,)(1;.$8.(55.Vs1,)(1;.$8.(55.Vs0,)(1;.$8.(55.Vra,)(1?.$8.)))))))))))))))(9.(28.$50.R18.(1>.R1:.+10.)(1;.$8.(55.R3.)(1?.$8.)))(9.(28.$50.R18.(1>.R1:.+18.)(1;.$8.(55.R2.)(1?.$8.)))(9.(28.$50.R18.(1>.R1:.+30.)(1;.$8.(55.R1.)(1?.$8.)))(9.(15.$50.R18.R1:.(1>.(16.&40.Vsp,)-68.))(9.(15.$50.R18.Vlo,R1:.)(9.(14.$50.R18.)(9.(28.$50.R18.VSB,(1;.$8.(29.Vtgw,)(1;.$8.(29.Vpdw,)(1;.$8.(55.(11.&40.Vslen,))(1;.$8.(55.(11.&40.Vsp0,))(1?.$8.))))))(9.(28.$50.R18.VSAN,(1;.$8.(2;.#50.(43.(2.&8.)(11.&8.=)#50.))(1?.$8.)))(9.(42.$50.R18.VBUF,Vbs,)(9.(3=.$50.(52.VR,)(23.$50.VR,VHIA,Vh,)R18.VSB,+18.)(9.(3=.$50.(52.VR,)(23.$50.VR,VHIA,Vh,)R18.VSAN,+50.)(9.(36.(13.(1>.R1;.+100.)VSB,)(13.(1>.VSB,+18.)R1;.))(9.(36.(13.(1>.R1;.+100.)VSAN,)(13.(1>.VSAN,+50.)R1;.))(9.(58.$50.VR,VHIA,Vh,VLB,VLF,(16.&40.Vsp,)(16.&40.Vsp,)(1;.(1<.$6.$6.)(1=.$6.$6.VSAN,(1>.VSAN,+50.))(1?.(1<.$6.$6.)))Vm,R18.)(9.(17.$50.(52.VR,)R18.Vslo,R1:.)(17.$50.(52.VR,)R18.R1:.(16.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 DBB; try lx_pin1 DSS; try lx_pin1 ALS; try lx_pin1 BSMALL; try lx_pin1 BUF0; try lx_pin1 B47; try lx_pin1 ALB.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01]0@D10823604468.150D10963609986.161D12658639931.113D12660902694.150D18607476203.151D20553579080.152D31526457809.113D31539044048.161D3254889317.150 D32604263327.162D33194539134.113D39411162312.151D46039808504.161D47738891291.114D47739035658.161D50254960491.152D51038213418.152D52026568122.152D52026568122.153D52026568122.154D52356502921.161D52356618648.114D560907438.115  D60098666067.161D60098777666.114D62011770180.162D62011770188.115L1156686087.1   L14558062586.3  L15756354262.7  L16810015495.1  L19959024712.1  L19980016842.7  L20858515662.0  L21980071943.1  L2333530698.141 L2333536794.141 L24524441946.114L25985555144.1  L27729706458.176L27907327850.1  L29738741675.1  L32463525127.1  L3801083770.3   L39076636629.0  L39618635427.2  L39972639317.0  L40753528314.3  L43055154860.112L43300649301.0  L44032381512.1  L47738694412.1  L48117620906.100L48132302231.142L50790731766.13 L51052909836.177L54437681876.11 L56378876778.10 L58790154276.11 L61437265048.2  L63192237729.0  L66747997337.0  L7040749983.115 L7715476710.114 L9356559645.18  L9873114841.13  P40545941446.152P43107987128.150P43107987128.152P47262632184.150Q10523111615.118Q1530342990.152 Q23927511187.122Q23927511190.118Q24505182154.120Q29212174011.117Q31021924279.150Q33271078526.164Q35653441506.106Q38248895666.123Q3908583467.118 Q40271359350.152Q41599682109.120Q42437284299.165Q42439168719.150Q42439382242.124Q43880146030.123Q47230721786.118Q47313632828.117Q47313632828.164Q47738888970.117Q47740986934.121Q50796826103.152Q52350325685.121Q52356617865.117Q59865520189.124Q59871812884.165Q60109315147.106Q6192914196.150 Q62011770187.122Q62011770190.118Q64683599819.124Q64685695714.165Q66570664691.117Q66570664691.164Q67038703949.150Q67517027822.117Q67517027822.164Q9350548487.133 00000O00P00b01A01B01C01D01E01F01m02?02@02A02S03503603U04:04;04`05B05T05j06Q06h07H07X07\07h08608:08?08W08X08\08]08^09H09M09k0:00:40:80:D0:E0:O0:P0:\0<U0<V0<[0<`0=V0>Q0?90?[0@G0@a0AI0AQ0AR0AS0B10BF0CB0D70D]0E>0E_0FE0FU0G00GC0Gb0H00H?0Hc0Hd0IF0IT0IU0Im0J;0JV0K10KG0KX0Ki0Kj0Kk0L:0LI0M@0MO0M^0M_0M`0N40NH0NU0Nb0OE0Om0On0Oo0Pn0Po0Q00QLS2LF2sp3BUF2bs3LFB3sp13H214LFB'FS2LF2sp3BUF2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H214LFB'FFFFFS1R3HIA2LF2sp2bs3LFB3sp13H214LFB'2h12FBS2LF2sp3BUF2bs3LFBFFS2LF2sp3SAN2bs3LFBS2LF2sp3SAN2bs3LFB3sp13H214LFB'2FBFS2LF2sp2bs3LFB3sp13H193H214LFB'S2LF2sp2SB2bs3LFB3sp13H214LFB'3x142HxFS2LF2sp2SB2bs3LFB3sp13H214LFB'3x142HxS2LF2sp3SAN2bs3LFB3sp13H214LFB'2FBS2LF2sp3SAN2bs3LFBS1R3HIA1h2LF2sp2bs3LFBS1R2LF2sp2lo2bs3LFB3LOS3sp13H214LFB'2FBS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2bs3LFB3sp13H214LFB'2FBS1R2LF2sp2bs3LFBS2FBS2sp3sp13SP1S1R2lo3LOS3ALOS2FBS3sp1S1R3HIA1h2sp3TOP3sp13SP1SS2spFFS2LF2sp2bs3SPA3LFB3SPR3sp13H173H183H193H21S3sp1S2LF2sp2bs3LFB3sp13H214LFB'2FBS3SANS2FBS2FBS2sp3sp13SP1SS3sp14SP1MSS2sp3sp13SP1S1R3NS13NA13NB14STKn5STKn02LF2sp2SB3SAN3BUF3sp04slen2lo2bs3SB04SBHI2W12W22W34SAN05SANLO3DSB3SLO3LFB3LOS3BCE5BUFLO3ALO3SPRSS3sp1S3SANS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS3ALOS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS3ALO4LFB'S1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3LOSS2LF2sp2bs3LFB3sp13H193H214LFB'2FBS1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3sp13SP1S1R3BUF2lo2bs3LOS3BCE4ALO0S1R3NA13NB14STKn5STKn02sp2lo3SLO3sp13SP1S2LF3LFBSSS2LF2sp2bs3LFB3SPR3sp13H173H21S2LF2sp2SB3SAN2bs3LFBS1R3NS13NA13NB14STKn5STKn02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R3NS13NA13NB14STKn5STKn02sp2lo3slo4SLOL3SLO3sp13SP1S2LF2sp2SB2lo2bs4SBHI3LFB3sp13SP14LFB'S2LF3SAN2lo2bs5SANLO3LFB3sp14LFB'S2LF3SAN2lo2bs5SANLO3LFB3sp14LFB'S2LF2sp2SB2lo2bs4SBHI3LFB3sp13SP14LFB'S1R2LF2sp2bs3LFBS2LF2sp2bs3LFB3sp13H194LFB'S1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS2LF2SB2bs3LFBS2LF3SAN2bs3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOP4LFB'FS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFB4LFB'S2LF2SB2bs3LFBS1R2LF3slo2bs4SLOS3LFB4LFB'S1R2LF3slo2bs4SLOS3LFB4LFB'S1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS1R2LF2bs3LFB3ALOFFS2LF3SAN2bs3LFBS2LF3SAN2bs3LFBS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS4LFB'S2LF3SAN2bs3LFBS2LF3SAN2bs3LFBFFS1R2LF2lo2bs3LFB3LOSS2LF2bs3LFB3sp14LFB'S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOP4LFB'FFS1R3NS13NA13NB14STKn5STKn02LF2sp2lo2bs3SLO3LFB3LOS3sp13SP14LFB'FFS2LF2bs3LFB3sp13H203H214LFB'". (* [comment removed for export] *)
  #[using="LOS LFB TPV SPH SPA TOP SLO SLOL SLOS DSB SANLO CWS SAN0 W3 W2 W1 BIN SB47 SBHI CRSB SB0 STKn0 STKn NB1 NA1 NS1 SM2 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_parse_san_A ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(38.$50.VR,VHIA,Vh,VLB,VLF,Vm,)P,(28.$50.Vm,VSB,(1;.$8.(29.Vtgw,)(1;.$8.(29.Vpdw,)(1;.$8.(55.(11.&40.Vslen,))(1;.$8.(55.(11.&40.Vsp0,))(1?.$8.))))))P,(28.$50.Vm,VSAN,(1;.$8.(2;.#50.(43.(2.&8.)(11.&8.=)#50.))(1?.$8.)))P,(42.$50.Vm,VBUF,Vbs,)P,(15.$50.Vm,Vlo,(16.&40.Vsp,))P,(17.$50.(52.VR,)Vm,Vslo,(16.&40.Vsp,))P,(14.$50.Vm,)P,(3=.$50.(52.VR,)(23.$50.VR,VHIA,Vh,)Vm,VSB,+18.)P,(3=.$50.(52.VR,)(23.$50.VR,VHIA,Vh,)Vm,VSAN,+50.)(59.$50.(52.VR,)(23.$50.VR,VHIA,Vh,)$5:.(<.(=.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(11.&40.VSB,)(11.&40.VSAN,)R13.R12.R11.R10.R?.R>.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R=.R<.R;.R:.)VF,(11.&40.$5;.)Vfc,(?.(2.&40.))Vm,(10.$50.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH HSB HSAN HBUF ST SS MI OSB OSAN.
  unfold A_X509_PARSE_SAN.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_2S in SM2.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, Z.of_nat (length bs)) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  assert (BUFLO : BUF + Z.of_nat (length bs) <= lo) by (pose proof (art_lo asegs R HIA) as ALO0; clear - BCE ALO0 LOS; lia).
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO NS1 NA1 NB1 STKn0; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  carve_frame 160%nat ST.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 525%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -160) ST ltac:(clear - SP1 SLO NS1 NA1 NB1 STKn0; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340476 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 160);
                  [ exact HHc | exact LFB' | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NB1 STKn0; lia); exact ST1
                  | exact LOS | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NB1 STKn0; lia); clear - SLO SP1 NS1 NA1 NB1 STKn0; lia
                  | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NA1 NB1 STKn0; lia); clear - SP1 TOP; lia
                  | assumption | exact TPV | reflexivity ])
      end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      (* [comment removed for export] *)
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 2)) with 32%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 2)) with 256%nat in FRM by reflexivity.
      replace (64 * 2 ^ 2) with 256 in FRSH, HH1 by reflexivity.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaebb4] [] 525%N). lx_tree.
  lxr_leaf. lx_carry.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [24; 8; 8; 24; 8; 24; 8; 24; 8; 112; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HL1 FRM3. chunk_split FRM3 1%nat RZ1 FRM4.
      chunk_split FRM4 1%nat HL2 FRM5. chunk_split FRM5 1%nat RZ2 FRM6. chunk_split FRM6 1%nat HL3 FRM7. chunk_split FRM7 1%nat RZ3 FRM8.
      chunk_split FRM8 1%nat HL4 FRM9. clear G1 RZ1 RZ2 RZ3 FRM9.
      replace (FB + 24 + 8) with (FB + 32) in HL1 by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24) with (FB + 64) in HL2 by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 24) with (FB + 96) in HL3 by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 24 + 8 + 24) with (FB + 128) in HL4 by (clear; lia).
      cb8_to_c8 HL1 (@nil cell). cb8_to_c8 HL2 (@nil cell). cb8_to_c8 HL3 (@nil cell). cb8_to_c8 HL4 (@nil cell).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL NS1 NA1 NB1 STKn0; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa ST2x (bv_unsigned sp + -104); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 16) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp16 SLOT16].
      cb8_to_c8 SLOT16 (@nil cell).
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 24) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp24 SLOT24].
      cb8_to_c8 SLOT24 (@nil cell).
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 48) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp48 SLOT48].
      cb8_to_c8 SLOT48 (@nil cell).
      pose proof (fresh_apart_client _ LB LF lo SB 24 FB 256 FRSH CRSB ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APB.
      assert (CRSN : client_range L (LB ++ fdata LF) lo SAN 80) by (eapply client_range_inside; [exact CWS| intros b Hb; exact Hb| clear; lia| clear; lia]).
      pose proof (fresh_apart_client _ LB LF lo SAN 80 FB 256 FRSH CRSN ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APS.
      idtac "S1P".
      apply evtA_done. unfold S1P. exists FB, sp1, h1, m3.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
