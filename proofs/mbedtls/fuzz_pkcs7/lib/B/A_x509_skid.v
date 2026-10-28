(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_skid_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007fb38b3e8e9a70 0 5 0 1 37 1 58 1 71 1 72 1P00baf7986d8a148e 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0136b6f42dce7097 0 4 0 1 58 1 71 1 72 1P0180412f0bf8f003 0 4 0 1 63 1 71 1 72 1P018870f885e90c22 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P02a4186fc8c92e99 0 5 0 1 37 1 58 1 71 1 72 1P02dfd7c3765b151f 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P030e291dd4d18b65 0 4 0 1 58 1 71 1 72 1P03ccd796287d3048 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0452359f40e66a6c 0 4 0 1 63 1 71 1 72 1P0497b7d3ed674242 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P051483bdd80a7ced 0 6 0 1 59 1 60 1 63 1 71 1 72 1P05735908cb9ae2ab 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0639c17ada903ecc 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P067e7c430aa57158 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P06b91c4f6f4c744b 0 5 0 1 37 1 58 1 71 1 72 1P06e55d8a94f9f489 0 4 0 1 63 1 71 1 72 1P077daee2b82abdac 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P07f7854fc8d69532 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P083c06c021e88fd6 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P088d25763d781e4b 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P092e41fbe1409859 0 4 0 1 58 1 71 1 72 1P095ec17987bd354e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P096000e2a0c6b940 0 5 0 1 37 1 58 1 71 1 72 1P0981ecdfc3698875 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P098cff46dcaefa94 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0996fc1342ed7970 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P09cb2e964d246b27 0 4 0 1 63 1 71 1 72 1P0a2ebf871dfb2a2a 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0af3046d4ed308c8 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P0b4ba94eaffbf75d 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0b8f84314c96fbd4 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0d280e1c0c738882 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P0d759d742c4d6b27 0 4 0 1 63 1 71 1 72 1P0db50f8d6f9c5b55 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0dca89053ae68924 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P0e53ac56f9862372 0 4 0 1 63 1 71 1 72 1P0e7d50ca9b194b1e 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P0f53aa8dbe3775d7 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0f93b791c1d73893 0 4 0 1 58 1 71 1 72 1P1041b5d2fa98636a 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P106424e7409aca65 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P116d454ae3ca2485 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P123703375a7abb2b 0 5 0 1 37 1 58 1 71 1 72 1P12e899dab12272c4 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P13022fca69c07365 0 6 0 1 59 1 60 1 63 1 71 1 72 1P135ee2ba424d435f 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1378498b5e0e5766 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P157bb9c87a7aa3f2 0 4 0 1 63 1 71 1 72 1P15f650ae6e7917d7 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P15fadada9e038c63 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P1652af9369deb560 0 4 0 1 58 1 71 1 72 1P18244bffd99ae1e1 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P18c0953e8bf219b0 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P18c7ed55cfdb2bfb 0 6 0 1 59 1 60 1 63 1 71 1 72 1P18d5d6812933bf81 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1a8c9226f3bbccf5 0 3 0 1 43 1 49 1P1b15a8c8b9c541dd 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1c07b44cd71c86b4 0 4 0 1 58 1 71 1 72 1P1d4781c08d77d04b 0 4 0 1 58 1 71 1 72 1P1d72af86acc34f9b 0 4 0 1 63 1 71 1 72 1P1dbd105561e236ec 0 5 0 1 37 1 58 1 71 1 72 1P1dec351b8a0881a1 0 4 0 1 58 1 71 1 72 1P1eadad35efd7f3a5 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P20212786bdb660b8 0 6 0 1 59 1 60 1 63 1 71 1 72 1P205d5d27dc4dfc85 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P210825709379122b 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P213aa6230aa8dfec 0 5 0 1 37 1 58 1 71 1 72 1P21fd2869a0569a02 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2200ec60d8a02147 0 6 0 1 59 1 60 1 63 1 71 1 72 1P232aabaec24d982b 0 4 0 1 58 1 71 1 72 1P23765bd8ce853440 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P23c09a6be3910cbd 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P23e25a19d56ca368 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P251f825d5b86c168 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P253392c521c6ed8e 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P26b77a43a0c82efe 0 4 0 1 63 1 71 1 72 1P2744c188b0c2c5d6 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P274a04121acac41d 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P279f2b0501d06972 0 5 0 1 37 1 58 1 71 1 72 1P283aedc731aa4e83 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P28736740469a8d29 0 3 0 1 44 1 52 1P28b6ab1c0b025b81 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2a9da1499ef7f1c4 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2b24ae4725a947d9 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P2b50e14643e3233a 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2be3b84f4ad17116 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P2bf435e72c5cac8a 0 4 0 1 58 1 71 1 72 1P2c3fa1839e44cb96 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2cc4f7b12cf6f0b0 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2daec9bd3dc1e2d8 0 5 0 1 37 1 58 1 71 1 72 1P2daefe7979492b42 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P2ff0edc571755268 0 5 0 1 37 1 58 1 71 1 72 1P30e8378b443caa41 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P313cc8ce03379c3e 0 5 0 1 37 1 58 1 71 1 72 1P31437b0352b08327 0 4 0 1 58 1 71 1 72 1P31e6fe67bf277dac 0 6 0 1 59 1 60 1 63 1 71 1 72 1P325fdb1543b9d39c 0 4 0 1 63 1 71 1 72 1P326a3b78e90cbf39 0 5 0 1 37 1 58 1 71 1 72 1P331511b8b213120a 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P332bfa02f9103db0 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P33dfc49e030a09ed 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P342128c1bc940896 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P344a47e0a7a40676 0 4 0 1 63 1 71 1 72 1P348a8d7fcf515d75 0 6 0 1 59 1 60 1 63 1 71 1 72 1P35084c524d09549a 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3559203144ef26dd 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P35eef284900cc262 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P36090fb01fa0e9fc 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P366aef4081e3ba97 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P37b585a907125934 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P38d41511adde9871 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P391e0f218ec6f74e 0 4 0 1 63 1 71 1 72 1P392e28a20a0f35bb 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P39bb45d1d2426354 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3acb9619e6b8fa95 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3b0a996a8cd04b75 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3b4fc94a451eb4e0 0 4 0 1 58 1 71 1 72 1P3c5a6c88da3e0668 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3c706d444f7feba3 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P3ed1ffbc2438bd9c 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3ef5e8aa99b93b1c 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3f8030b31f8edd68 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3fa9614e11a9ec5c 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16N00e599cb0339ad53N02db7802fbd7ac9fN04e340175a8e4063N0570370aef8b96bdN070c2f00619b5e14N07e31fc12b792bbaN080d7d45a86a95c6N0a57186440c1caecN0db861c127f47881N0dcb4fa0d07f964bN0ddca2ca2c94e783N0e29e7e344c6d3a5N0e40bdae6bd89bdaN11abd8ad918a3d71N17cc99323900d3aaN18e9fdc1ac43e706N1a6812cec70fd146N1a79228ee3134c06N1bf3853dbca19e28N1c6bceb56f4b3614N1c7ae13db2b58ec8N1cc635a423f7f665N1d18346e6dc25d81N1dd77e37c5392c59N2133e10d7aaf8596N23b501f52774cdc3N24a7e94da9f8bb6aN2553ade4a7d453f0N290c71ea864bfbe0N29cf29bf97fc4137N2a0a3d81070b8287N2a4e019b8adde411N2c8e1be1a3d0f27cN2d3f3389434466efN2d5cacee4fe07682N2f0ce7da1f367433N2ff97e012c97431cN30202eb66d25d012N32039228a1e3e4d3N321ee77d166ce399N32fe335f64a83fb2N33babffc38d6429aN340baaf970031d3dN367238f302ba843aN37fabacaeca7f915N383c3d440d48dc79N393c1084ca4838d9N39487f8aee0fef18N3a92998c63c06022N3e2d02dd89fc2d52N3eb74ca8cc362151"%lxh.
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
Ltac2 gd_tbl_A_x509_skid () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_skid_A.x509_skid_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_skid_A.A_X509_SKID"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_skid_A.x509_skid_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP SK P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SK \/ SK + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ SK + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SK.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SK mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SKB : 0 < SK /\ SK + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_SKID_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SK + 24 <= lo \/ bv_unsigned sp <= SK.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo SK 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SK 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_SKID_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_skid_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SK P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (SK, SK + 24)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.

  Ltac rw_at_hyp :=
    match goal with
    | H : rw_cells _ ?m ?A' ?cs |- rw_cells _ ?m ?A _ =>
        first [ exact H | replace A with A' by (clear; lia); exact H ]
    end.
  Ltac bw_side :=
    first
      [ eassumption
      | lazymatch goal with
        | |- rw_cells _ _ _ _ => rw_at_hyp
        | |- crange _ _ _ => solve_crange
        | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
        | |- wcover _ _ _ _ _ _ _ => solve_wcover
        | |- shadow_free _ _ _ _ _ _ _ =>
            first [ match goal with WL : wlow _ _ _ |- _ => apply (shadow_free_of_wlow _ _ _ _ _ _ _ WL); qlia end
                  | match goal with WL : wlow _ _ _, FR : fresh_apart _ _ _ _ _, HHx : HM _ _ _ _ _ _ _ |- _ =>
                      eapply (shadow_free_of_fresh' _ _ _ _ _ _ _ _ _ _ _ _ _ WL FR HHx); qlia end ]
        | |- forall b, In b _ -> In b _ =>
            let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
            first [ exact Hb | apply fdata_cons_sub; exact Hb | right; exact Hb ]
        | |- forall x, _ <= x < _ -> _ \/ in_block _ x =>
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            first [ left; clear_disj; lia
                  | right; match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; clear - Hx; lia] end
                  | right; exists (x - (x - _), 64) ]
        | |- _ \/ _ => first [ solve [clear_mods; clear_disj; lia] | pqlia ]
        | |- _ => first [ qlia | pqlia ]
        end ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0@D10639329459.125D18607476203.164D2455714710.190 D27392810573.190D32457002573.190D3254889317.163 D3373657269.190 D33956323578.165D33956323578.166D33956323578.167D37713024309.126D41440366531.190D46793042006.125D48254281722.165D48254281722.166D48254281722.167D50254960491.165D52070850065.126D53232575014.165D53232575014.166D53232575014.167D560907438.127  D58077997354.165D60098777666.126D60111245650.125D62011770188.127D68405212918.190D6909863155.190 L15151186337.0  L15756354262.7  L17921795213.183L19013159470.0  L19980016842.7  L29738741675.1  L35228767239.1  L3551623394.2   L35680140202.3  L36180999398.119L3876079316.5   L39076636629.0  L39332637397.0  L39618635427.2  L40228640085.0  L43055370171.117L48117620907.105L50790731766.8  L52249874585.0  L52255793882.180L56854270298.122L57355539152.169L58071656716.181L58790154276.6  L59257759329.3  L59308677456.15 L60558678699.1  L6203936179.1   L63738252715.1  L64009471222.1  L7040749983.123 L9356559645.13  L9873114841.7   P1056307012.163 P1056307012.165 P32198570244.163P32198570244.165P36462068749.164P36465839390.163Q10523111608.131Q10651763882.133Q10651763890.129Q12660624644.135Q1530342990.165 Q21829627469.190Q23927511185.131Q23927511197.136Q27944911788.190Q31021924279.163Q31805155683.190Q32436491433.190Q32681887700.131Q33196749121.135Q33963892682.190Q35653441506.111Q37702541083.134Q37702541086.130Q38248895676.137Q40228749922.190Q40271359350.165Q42439168719.163Q42439382240.138Q43880146016.137Q46805771343.133Q46805771351.129Q47230721789.131Q48119867062.190Q49077563264.190Q50165000274.130Q50796826103.165Q52064556090.130Q52064556095.134Q59865520191.138Q60109315147.111Q60740903729.129Q6192914196.163 Q62011770181.136Q62011770185.131Q64683599817.138Q67026483294.164Q67038703949.163Q6909863155.190 Q9356560156.146 Q9646450869.190 00000D00E00F00e01D01E01F01m02T02U02i03H03\03]03^03_03`04404504604704S05305P05m06C06D06c06d07207307407L07P07T07[07e08908L08M08N08X08Y09409S09d09e0:D0;<0;=0;`0<60<B0<U0<Y0<^0<b0<f0=N0>=0>Y0?P0@G0A>0B50B]0B^0Bn0C<0CJ0CY0Co0D=0D\0Do0EL0Ek0F^0F_0F`0Fo0G^0H@0HN0H\0Hj0Hk0I>0IT0Ij0J;0JI0JW0Jh0KG0Kd0L50LP0L^0Ll0Lm0MA0MR0Ma0Mn0N;0N^0OA0Od0P20PI0PbS2LF2sp2PP2SK2bs3LFBFFS2LF2sp2PP2SK2bs3LFB3sp13H222FBS2LF2sp2PP2SK2bs3LFB3sp13H222FBFFS2LF2sp2PP2SK3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP2SK3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP2SK2bs3LFBS2LF2sp2PP2SK2bs3LFB3sp13H222FBS2LF2sp2PP2SK2bs3LFBFFFFS2LF2sp2PP2SK2bs3LFBFFFS1R3HIA1h2LF2sp2PP2SK2bs3LFBS2LF2sp2PP2SK2bs3LFB3sp13H203H22S1R2LF2sp2PP2SK2lo2bs3LOS3LFBS1R2LF2sp2PP2SK2lo2bs3LOS3LFBS1R2LF2sp2PP2SK2bs3LFBFS2LF2sp2PP2SK2bs3LFB3sp13H222FBSS1R2lo3LOS3ALOFSS1R3HIA1h2sp3TOP3sp13SP1S2FBS2spS2bs2EQS2FB2x22HxS2LF2sp2PP2SK2bs3LFBS2sp2lo3SLO3sp13SP1SSS3sp14SP1MSS2LF2sp2PP2SK2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSSS2LF2sp2PP2SK2bs3LFB3sp13H222FBS2LF2sp2PP2SK2bs3PPB3SKB3SPA3LFB3SPR3sp13H183H193H203H22FS2LF2sp2PP2SK2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S2sp3sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS3sp1S2FBS2bsS2LF2sp2PP2SK2bs3SKB3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2SK1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2SK1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'FFS2LF3BUF2bs3LFBS2LF2sp2PP2SK2bs3PPB3SKB3LFB3SPR3sp13H222FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2SK2bs3LFBS2LF2SK2bs3LFBS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S2LF2PP2SK2bs3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2SK2bs3LFBS2LF2SK2bs3LFBFS1R2LF2lo2bs3LOS3LFBS2LF2PP2SK2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_skid ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ptg0,(0.&40.)Pln0,(0.&40.)Pq0,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VSK,(4.$5.(9.R5.)(4.$5.(9.Vpad,)(4.$5.(6.R4.)(4.$5.(6.R3.)(8.$5.))))))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VSK,+18.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSK,VP,VEND,Vlo,Vslo,Vpad,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R19.R18.R17.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VSK,)R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until q0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_SKID.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 177%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64);
                  [ exact HHc | exact LFB | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
                  | exact LOS | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SLO3 SP1; lia
                  | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SP1 TOP; lia
                  | assumption | exact TPV | reflexivity ])
      end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      (* [comment removed for export] *)
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 0)) with 64%nat in FRM by reflexivity.
      replace (64 * 2 ^ 0) with 64 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [24; 8; 8; 16; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HLEN FRM3. chunk_split FRM3 1%nat FD2 G2.
      replace (FB + 24 + 8) with (FB + 32) in HLEN, FD2, G2 by (clear; lia).
      replace (FB + 32 + 8) with (FB + 40) in FD2, G2 by (clear; lia). replace (FB + 40 + 16) with (FB + 56) in G2 by (clear; lia).
      cb8_to_c8 HLEN (@nil cell).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 1%nat FRa SPILL end.
      replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -88); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -88) sp1 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo SK 24 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_skid_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_skid ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.=)$23.)(24.$2.R5.R4.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  unfold x509_skid_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
