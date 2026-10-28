(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_ecp_group_free P_ecp_keypair_init P_ecp_group_load P_ecp_grp_id_list P_pk_ecparams_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_pk_ecc_set_group A_pk_ecparams_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0045053d7cdae9ef 0 4 0 1 60 1 71 1 73 1P0048544069e7fd6a 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P005d70534cdd77fc 0 3 0 1 39 1 62 1P00bfac245d069e3e 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P00f74db94091908f 0 3 0 1 41 1 49 1P0336e397f3dd9045 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P033be929c65551af 0 6 0 1 41 1 49 1 51 1 59 1 60 1P035f7f366755c5da 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P03ec6d139f1d2969 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P042f234558231311 0 3 0 1 33 1 70 1P048221f13fecfe7f 0 6 0 1 41 1 49 1 51 1 59 1 60 1P04a09dd48fa2f5e2 0 4 0 1 48 1 59 1 60 1P0579a3c4a80ddc80 1 1 32 3 0 1 91 1 94 1 10 49 2 54 2 73 2 75 2 81 2 82 2 83 2 92 2 93 2 95 64P057d677098a3bc3e 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P05a1463fd25c9ac6 0 3 0 1 33 1 70 1P05ae1e89109111a6 0 5 0 1 60 1 71 1 72 1 73 1P069cbeaeb88fb850 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P07c0e5b3818ec5a0 1 1 32 3 0 1 92 1 95 1 10 50 2 55 2 74 2 76 2 82 2 83 2 84 2 93 2 94 2 96 64P0881183b56973bec 0 3 0 1 33 1 70 1P08ee2920bb3f36a3 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P08ee711b8fd68012 0 6 0 1 41 1 49 1 51 1 59 1 60 1P09206cbdc22bf7b7 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P09e788cbd98399e9 1 1 16 3 0 1 93 1 94 1 9 55 1 74 1 76 1 82 1 83 1 84 1 92 1 95 1 96 16P0a107abd69755dec 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P0b09023c981592bb 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P0b4106acf60fcad9 0 3 0 1 33 1 70 1P0b481aefec3f50ce 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P0b948f814a3f9069 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P0bced1108a18896c 0 3 0 1 33 1 70 1P0bd63549e00f5cbf 0 6 0 1 41 1 49 1 51 1 59 1 60 1P0c6d1c155a54f537 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P0c8444021ba3cf2c 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P0cca975cd4387e76 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P0ccc5bf59ecae174 1 1 64 2 17 1 91 1 3 0 1 92 1 93 64P0cf2d4df5e362833 0 5 0 1 60 1 71 1 72 1 73 1P0da1b38c3bf0d4ff 0 6 0 1 41 1 49 1 51 1 59 1 60 1P0e2219abd57c5938 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P0e420983acbb3bff 0 3 0 1 33 1 70 1P0e7f53ee7614aea9 0 5 0 1 52 1 63 1 64 1 65 1P0fafdc51ac3f3ffd 1 1 32 3 0 1 92 1 95 1 10 50 2 55 2 74 2 76 2 82 2 83 2 84 2 93 2 94 2 96 64P0feb2a1ee36d56f9 1 1 64 2 49 1 70 1 3 0 1 69 1 71 64P103fed7a83b31572 0 5 0 1 60 1 71 1 72 1 73 1P10a3e15d99aaf0b0 0 4 0 1 21 1 77 1 78 1P10e22838250d6a27 0 5 0 1 60 1 71 1 72 1 73 1P10e7808fb6fcb721 0 4 0 1 48 1 59 1 60 1P110ca9048194a5c0 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P1185d3186ea7aec1 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P12ef78ff1a60ba62 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P1368c2d8831176bc 1 1 32 3 0 1 92 1 95 1 10 50 2 55 2 74 2 76 2 82 2 83 2 84 2 93 2 94 2 96 64P146cdae5650402e6 0 4 0 1 21 1 77 1 78 1P148bf4eb7a6eac51 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P14e7ba409a1d3b5a 0 6 0 1 41 1 49 1 51 1 59 1 60 1P1529aa6d502e369b 0 3 0 1 33 1 70 1P162481bb63671f79 0 4 0 1 48 1 59 1 60 1P162e576d9ea42fd4 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P16a3eeb4114cd0c3 0 2 0 1 34 1P1724c695e35a09db 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P178c3b7dfa4b2a90 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P17c831bb466e76bd 1 1 64 2 0 1 69 1 3 2 1 70 1 71 64P17f6d8de8c947fe4 0 5 0 1 60 1 71 1 72 1 73 1P18984344fe2a57bf 0 4 0 1 48 1 59 1 60 1P190c59607087ef8e 0 6 0 1 41 1 49 1 51 1 59 1 60 1P19a59d4379d49627 0 4 0 1 48 1 59 1 60 1P19d186f3d5295cee 0 4 0 1 48 1 59 1 60 1P1a8611d8e2f15537 0 3 0 1 33 1 70 1P1b2411d945c610b2 0 7 0 1 49 1 73 1 81 1 83 1 91 1 92 1P1b2f9fdde8d35a80 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P1b32173dc88b3a29 0 5 0 1 60 1 71 1 72 1 73 1P1b9d462269f7dbb4 0 4 0 1 48 1 59 1 60 1P1d3f6c3a09efe742 0 3 0 1 33 1 70 1P1f0b0bb81fdb31f4 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P1f6cb916df571c19 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P201af2b0cf3fc6cd 0 3 0 1 33 1 70 1P20cbc71bff89c91c 0 6 0 1 41 1 49 1 51 1 59 1 60 1P20e986d12e4fb40b 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P2128eb1b56d02df9 0 4 0 1 48 1 59 1 60 1P21d61fd3160e491c 0 2 0 1 33 1P21e8553828d6e34b 0 5 0 1 60 1 71 1 72 1 73 1P21f6fd996abcca32 0 3 0 1 33 1 70 1P239d992b46a965f6 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P244b2563f33a38c6 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P24aea92e66e5729a 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P24ecb77c87062db1 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P26f58c5e6ccf3f7c 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P2797ddce500ad7fa 0 6 0 1 41 1 49 1 51 1 59 1 60 1P28de756b60910ba0 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P294ebef50bba78ae 0 9 0 1 49 1 53 1 55 1 64 1 65 1 66 1 70 1 71 1P29e53ef1ae16c184 0 6 0 1 41 1 49 1 51 1 59 1 60 1P2a243f236a380f70 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P2a5354493c6c2aca 0 5 0 1 60 1 71 1 72 1 73 1P2b40f582a6c1562c 0 4 0 1 48 1 59 1 60 1P2bd1e208d2cde0bd 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P2c5160866ef0ddcc 1 1 64 2 0 1 91 1 3 6 1 92 1 93 64P2cb45b01eb8f6574 0 6 0 1 41 1 49 1 51 1 59 1 60 1P2d55daac6ec7aceb 0 3 0 1 33 1 70 1P2d584275a205d384 0 7 0 1 22 1 60 1 71 1 73 1 77 1 78 1P2d8571e0f8ce03e6 0 3 0 1 31 1 40 1P2e86eb990afbd2e1 0 4 0 1 21 1 77 1 78 1P2e9e9e58e8d650fc 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P2ed04d37693b1454 0 3 0 1 33 1 70 1P2f07518073cf0866 0 7 0 1 22 1 60 1 71 1 73 1 77 1 78 1P2f5c78c14c148763 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P2fa793b5c1b2d49f 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P2fb10142de847d6c 0 6 0 1 41 1 49 1 51 1 59 1 60 1P2ff1fe5d6ff37e56 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P31498fd8aa521d5c 0 4 0 1 48 1 59 1 60 1P315b3bcc4e4bbf99 0 4 0 1 48 1 59 1 60 1P315dc565d96f5bea 0 6 0 1 41 1 49 1 51 1 59 1 60 1P317d007cc45b6973 1 2 16 2 0 1 61 1 16 2 1 1 60 1 2 62 1 63 1P31ea47dbbed02c31 1 2 16 3 1 1 26 1 60 1 16 3 0 1 27 1 61 1 2 62 1 63 1P32524a8ad83bb3cc 0 7 0 1 22 1 60 1 71 1 73 1 77 1 78 1P32a86cecde297a27 0 4 0 16 3 16 59 16 60 16P32dec147eb3d327b 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P3302bad9bea8de38 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P3311b10d610948d9 0 5 0 1 60 1 71 1 72 1 73 1P33c588312037b9d4 0 5 0 1 60 1 71 1 72 1 73 1P33dbf3895e9d65b8 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P347e31ffa40597b2 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P34a6a4b82e52f1fb 0 4 0 1 48 1 59 1 60 1P34df4e4d153294e4 1 1 16 3 0 1 93 1 94 1 9 55 1 74 1 76 1 82 1 83 1 84 1 92 1 95 1 96 16P34f241b93225bb81 1 1 16 3 0 1 92 1 93 1 9 54 1 73 1 75 1 81 1 82 1 83 1 91 1 94 1 95 16P34f84ab0176e7080 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P34fdb101c5beaa30 0 5 0 1 60 1 71 1 72 1 73 1P352c877382185f9f 0 4 0 1 48 1 59 1 60 1P3583e4d1b49e005b 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P36583c91ac818963 1 1 16 3 0 1 92 1 93 1 4 68 2 91 2 94 2 95 32P368cdc653a4f1ac3 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P36910350148858a3 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P37082c5dac28ff22 0 6 0 1 41 1 49 1 51 1 59 1 60 1P38b03f7f22eeb545 1 1 16 2 1 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P390ced615f9b995f 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P399561eff38c1516 0 8 0 1 28 1 52 1 63 1 64 1 65 1 69 1 70 1P39ae24fc3ebc21b9 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P39e79c0c6b9e6f71 1 1 16 3 1 1 26 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P3afae1096cfa8265 0 6 0 1 27 1 39 1 62 1 69 1 70 1P3b17cd5c263708a6 1 1 16 3 0 1 93 1 94 1 9 55 1 74 1 76 1 82 1 83 1 84 1 92 1 95 1 96 16P3b90bdc286272a15 0 7 0 1 41 1 49 1 50 1 51 1 59 1 60 1P3c8f83e8341b57ff 1 1 16 4 1 1 28 1 37 1 60 1 8 40 1 42 1 44 1 50 1 51 1 52 1 61 1 62 16P3ccb7119caf5bbfb 0 4 0 1 48 1 59 1 60 1P3e6d56a5e3f68b31 1 1 32 3 0 1 70 1 73 1 10 29 1 49 1 53 1 55 1 64 1 65 1 66 1 71 1 72 1 74 32P3ed4cfd13b1536e6 0 6 0 1 73 1 81 1 83 1 91 1 92 1P3f1a977652b470e3 1 1 16 2 0 1 59 1 3 4 1 60 1 61 16P3f2a8610245b2ea6 0 5 0 1 60 1 71 1 72 1 73 1P3f5d31b51fd50e13 0 5 0 1 60 1 71 1 72 1 73 1P3ff24a1fbbb4f831 1 1 64 2 1 1 69 1 3 0 1 70 1 71 64N000c80f821d3cd5eN007bce30dc2d1391N00a7a3287c13eadaN0106f61f26743703N010ccc83c3b6d5beN01a51d85526f2386N01da88c3b5d44ea6N0210c147be5dc146N0371d03219ea5991N039db433d40b4ef8N039e93bcfa9a6cf2N0415689b61000e1dN046f106f827a45a5N051ad03c691255cdN0699b056e3bc98f8N06ac5b14aa0dfaecN071c952b6c34b2f8N07460b1d752c560fN074b56a0906845ebN08750c6893f64304N08ae329f528bc705N093ed0fa6508be0cN09ed08c5aef25e3fN0a9b8e5e12225b11N0abe60fe6b11d168N0acc9ad4141ee09dN0bbc3cc200f20bbcN0c22a95823266d50N0c624fb40b62f2deN0c89261e0356fd2fN0dbf263607637af0N0e1f5d751698b9cfN0e771bd5327cdcabN107ca5d7f1bc44ffN1136400e3a1536e6N115917271f3d6992N1177053035bef9c6N1183c28cc111a3a7N129bdcd00a625811N12f39da4f5b6d8aaN12f93ed304da8341N1334797a53939000N134e8f173065d14bN138b6798bc3d5113N15250d5ce76ed7ceN153bf32b43e249f1N15820442bc55a245N15d7ae654d6f6d4fN15e9713444b4e6a2N1652ff7748cdb34eN1746347bcde7df5eN183316cd80b0cc93N18d7d12524679c69N1a1bf3ee446f02e5N1a84b5510445d09fN1aaf3518cae00c62N1b5936b8793200afN1b60557ff8ebd70fN1c57600374c1f8f1N1d88a3b499f7a495N1e17b564b4834d19N1ed8ba5b11dad5bbN1f026e1a8af5e5bcN1f9115cf3a1f04f9N1f9151d93f362a01N212940c2726ec162N2232e6ce8befdfe1N229587e134e1e5edN23d1ba7de9971b7eN249f2c432d11f581N24c9b494bfe81966N2580307834a31b18N25c5280804afa636N25cd4092045519b5N25dcab71e198194dN26677c1a1200afa5N281c25067329a9f7N2824157c87d3b9f0N28ae85bf45d20329N28f2d6284e50c0f4N294805aa00b24302N29a3c639ea6e21b8N29b2bed16db67cdbN2ab50e4952ad94ebN2b0709f038ce88cbN2bdee848959b9a53N2d18816a14de6f8eN2d1f3d35f10f840dN2e45cfcf68468a8fN2f25e07870317835N2f3f827f0a25cbdfN2f60b0ced30f71f9N2fd0b34a2253ffdcN2fe3c1e52f3bf0c3N306284baf526a22bN3145a25be85994a8N314c38e80e2acba5N32836fe0c1c10e69N32e6fb1c5fac7dc9N34607dd033e827b9N34be3e53cf96194aN3523d0158f6cef04N3591ea51238f1387N3622c23767f6bad6N368cbda49c49269bN36ec2f7b662ab450N36f4194cdabfe647N379d72d589a470c1N3892d37caee86267N39717a91305cf944N39f27cd824f1d1f3N3a5e2abdfbd8bb32N3a62a832f8449d7eN3b56d22785a016e5N3bb0407dfc962b4fN3c240715798cac2bN3c6e0d22ee5e1013N3cee1d66a49e430aN3d002f682bbd397dN3d5afec8ace2ec45N3d6a663a84c5771fN3dc76bf6b7b4621a"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_pk_ecparams_A () : Init.string Init.list := ["Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "EP_SH0"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkEP.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_stmt.A_PK_USE_ECPARAMS"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "WalkEP.Call.EPOST"].


Definition A_SMALLOC_4_EP : Z := 0x53544.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_EP : Z := 0xf5ea8.             (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition EP_SH0 : list cell := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_A ()) "(0.$1.(2.$1.(3.(4.&8.+?1.))#4.)(0.$1.(2.$1.(3.(4.&8.+?8.))#18.)(0.$1.(2.$1.(3.(4.&8.+?2.))#8.)(0.$1.(5.$1.(3.(4.&8.+?8.))(5.$1.(3.(4.&8.+?2.))(5.$1.(3.(4.&8.+?2.))(5.$1.(3.(4.&8.+?2.))(6.$1.)))))(0.$1.(5.$1.(3.(4.&8.+?8.))(5.$1.(3.(4.&8.+?2.))(5.$1.(3.(4.&8.+?2.))(5.$1.(3.(4.&8.+?2.))(6.$1.)))))(0.$1.(5.$1.(3.(4.&8.+?8.))(5.$1.(3.(4.&8.+?2.))(6.$1.)))(0.$1.(2.$1.(3.(4.&8.+?8.))#18.)(0.$1.(2.$1.(3.(4.&8.+?2.))#8.)(5.$1.(3.(4.&8.+4.))(5.$1.(3.(4.&8.+?3.))(6.$1.)))))))))))")
(* [comment removed for export] *).

Ltac cb4_to_c4 H pre :=
  lazymatch type of H with
  | rw_cells ?sg ?mx ?A _ => apply (EcpFacts.rw_cells_CB4_C4 sg mx A pre) in H; cbn [app] in H
  end.

Section WalkEP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_EP.
  Hypothesis SM4 : arl_smalloc R 4 = A_SMALLOC_4_EP.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PKA PAR lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 640 - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF + 1 < 512)%nat.
  Hypothesis PAL8 : PAR mod 8 = 0.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_EP in UARG; unfold A_SMALLOC_4_EP in SM4;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation SHB FB := (Z.shiftr FB 3 + al_sb AL).

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_A ()) "Lms,$7.(8.$9.LFB,$9.(8.$9.Lsp1,$9.(8.(:.$;.VR,VHIA,)Lh1,(:.$;.VR,VHIA,)(8.P,(<.&40.)(=.(<.&8.))Lm1,P,(<.&40.)(=.(<.&8.))(8.(<.&40.)Lt0,(<.&40.)(8.(<.&40.)Lt1,(<.&40.)(8.(<.&40.)Lt2,(<.&40.)(8.(<.&40.)La4,(<.&40.)(8.(<.&40.)La5,(<.&40.)(8.(<.&40.)La6,(<.&40.)(8.(<.&40.)La7,(<.&40.)(8.(<.&40.)Lt3,(<.&40.)(8.(<.&40.)Lt4,(<.&40.)(8.(<.&40.)Lt5,(<.&40.)(8.(<.&40.)Lt6,(<.&40.)(8.(<.&40.)Lw0,(<.&40.)(8.(<.&40.)Lw1,(<.&40.)(8.(<.&40.)Lw2,(<.&40.)(8.(>.(<.&8.))Ljref,(>.(<.&8.))(8.(>.(<.&8.))Ljgrp,(>.(<.&8.))(8.(>.(<.&8.))Ljslots,(>.(<.&8.))(8.(<.&40.)Lpj,(<.&40.)(8.(<.&40.)Llj,(<.&40.)(8.(<.&40.)Lvj,(<.&40.)(8.(<.&40.)Lvj',(<.&40.)(8.(<.&40.)Lgj,(<.&40.)(8.(<.&40.)Lgj',(<.&40.)(?.(10.$7.R1<.(11.(12.(4.&40.+;0;=0.)(4.&40.R1:.)Vgp,Vtp,R17.R16.R15.Vsp,(4.&40.R1:.)(4.&40.(13.VPAR,+3.))(4.&40.->.)(4.&40.=)(4.&40.-=.)R14.R13.R12.R11.(4.&40.R1;.)(4.&40.VPKA,)(4.&40.(14.(13.R1;.+3.)(15.(16.VR,))))(4.&40.(15.(16.VR,)))(4.&40.VPAR,)Vs7,Vs8,(4.&40.R1;.)Vs10,Vs11,R10.R?.R>.R=.)VF,(4.&40.+;0=98.)Vfc,(17.(<.&40.))R18.(18.$;.)))(?.(?.(19.(1:.(1;.&40.Vsp,)+110.)R1:.)(19.R1:.(1:.(1;.&40.Vsp,)+100.)))(?.(10.$9.(1<.R1:.+20.)=)(?.(1=.$;.VR,VHIA,R19.VLB,(5.(1>.$9.$9.)(1?.$9.$9.R1;.+400.)VLF,)R18.)(?.(10.P,$9.Sp(20.$;.VR,VHIA,R19.)(20.$;.VR,VHIA,Vh,))(?.(10.$9.(21.$;.VR,VHIA,R19.)(21.$;.VR,VHIA,Vh,))(?.(10.$9.(22.$;.VR,VHIA,R19.)(22.$;.VR,VHIA,Vh,))(?.(10.$9.(23.$;.VR,VHIA,R19.)(23.$;.VR,VHIA,Vh,))(?.(10.$9.(24.$;.VR,VHIA,R19.)(24.$;.VR,VHIA,Vh,))(?.(10.$9.(25.$;.VR,VHIA,R19.)(25.$;.VR,VHIA,Vh,))(?.Pmo,$26.(27.(28.$;.VR,VHIA,R1:.R1.)(28.$;.VR,VHIA,Vh,R1.))(?.(10.$9.(1<.R1;.+40.)=)(?.(29.VR,VLB,VLF,R1;.+400.)(?.(2:.$;.R18.R1;.(5.$1.(2;.R<.)(5.$1.(2;.R;.)(5.$1.(2;.R:.)(6.$1.)))))(?.(2:.$;.R18.(14.R1;.+20.)(5.$1.(2<.#<0.R9.)(6.$1.)))(?.(2:.$;.R18.(14.R1;.+120.)(5.$1.(2;.R6.)(6.$1.)))(?.(2:.$;.R18.(14.R1;.+140.)(5.$1.(2;.R5.)(6.$1.)))(?.(2:.$;.R18.(14.R1;.+160.)(5.$1.(2=.R4.)(5.$1.(2=.R3.)(6.$1.))))(?.(2:.$;.R18.(14.R1;.+170.)(5.$1.(2<.#<0.R8.)(6.$1.)))(?.(2:.$;.R18.(14.R1;.+270.)(5.$1.(2=.R2.)(5.$1.(2=.R1.)(6.$1.))))(?.(2:.$;.R18.(14.(13.R1;.+3.)(15.(16.VR,)))$2>.)(?.(2:.$;.R18.(14.(14.(13.R1;.+3.)(15.(16.VR,)))+50.)(5.$1.(2<.#30.(2.(<.&8.)(4.&8.=)#30.))(6.$1.)))(?.(2:.$;.R18.(14.(1;.&40.Vsp,)-68.)(5.$1.(2;.Vs11,)(5.$1.(2;.Vs10,)(5.$1.(2;.Vs9,)(5.$1.(2;.Vs8,)(5.$1.(2;.Vs7,)(5.$1.(2;.Vs6,)(5.$1.(2;.Vs5,)(5.$1.(2;.Vs4,)(5.$1.(2;.Vs3,)(5.$1.(2;.Vs2,)(5.$1.(2;.Vs1,)(5.$1.(2;.Vs0,)(5.$1.(2;.Vra,)(6.$1.)))))))))))))))(?.(2:.$;.R18.(14.R1:.+8.)(5.$1.(2<.#88.R7.)(5.$1.(2;.(4.&40.R1;.))(6.$1.))))(?.(2?.$;.R18.R1:.(14.R1:.+8.))(?.(2?.$;.R18.(14.R1:.+98.)(14.(1;.&40.Vsp,)-68.))(?.(2?.$;.R18.Vlo,R1:.)(?.(30.$;.R18.)(31.$;.VR,VHIA,Vh,VLB,VLF,(1;.&40.Vsp,)(32.VR,)(6.$33.)Vm,R18.))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 mo0.   (* [comment removed for export] *)
  #[using="PAL8 LFB TPV SPA TOP SLO LOS NEEDR NS1 SM4 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_A ()) "Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)P,(1=.$;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2?.$;.Vm,Vlo,(1;.&40.Vsp,))P,(30.$;.Vm,)P,(?.(19.=VPAR,)(34.VPAR,(35.+2.+40.)))(36.$;.(16.VR,)(20.$;.VR,VHIA,Vh,)$37.(11.(12.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(4.&40.VPAR,)(4.&40.VPKA,)R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(4.&40.$38.)Vfc,(17.(<.&40.))Vm,(18.$;.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI PARR.
  unfold A_PK_USE_ECPARAMS.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  carve_frame 256%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x53544] [] 726%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 272 <= sp1 <= bv_unsigned sp - 256) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1' end.
      destruct (stk_split asegs m1' lo sp1 (bv_unsigned sp + -256) ST ltac:(first [ clear - SP1 SLO NS1 NES; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 341316) with (Z_to_bv 64 (arl_smalloc R 4)) by (rewrite SM4; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1' |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 4) with (lo := lo) (sz := 640); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | reflexivity | exact TPV | exact LOS | exact ST1
                  | (first [ clear - LFB; lia | lx_side_lia ])
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
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _).
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 4) with 1024 in *. change (8 * 2 ^ 4) with 128 in FSH. change (Z.to_nat 1024) with 1024%nat in FRM. change (Z.to_nat 128) with 128%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 1024 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (1024 / 8) with 128 in SBND, APS. change (1024 - 40) with 984 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -256) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -256 + 152) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -256) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 152) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STa SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 152) 144 STa ltac:(clear; lia)) as [STlo [jslots SLOTS]].
      replace (sp1 + 152 - Z.of_nat 144) with (sp1 + 8) in STlo, SLOTS by (clear; lia). clear STa.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 1024 junkf [] [8; 8; 8; 8; 192; 64; 8; 24; 8; 24; 4; 4; 8; 192; 64; 4; 4; 392]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      repeat (match type of FRM with context [CB ?n ?bs] => match bs with context [junkf] => let j := fresh "jb" in set (j := bs) in FRM; clearbody j end end).
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat REFC FRM3. chunk_split FRM3 1%nat G1 FRM4.
      chunk_split FRM4 1%nat PCL FRM5. chunk_split FRM5 1%nat G2 FRM6. chunk_split FRM6 1%nat LCL FRM7. chunk_split FRM7 1%nat G3 FRM8.
      chunk_split FRM8 2%nat VCL FRM9. chunk_split FRM9 1%nat G4 FRM10. chunk_split FRM10 1%nat GRPC FRM11. chunk_split FRM11 1%nat G5 FRM12.
      chunk_split FRM12 2%nat GIDC FREST.
      lazymatch type of REFC with rw_cells _ _ ?a _ => replace a with (FB + 32) in REFC by (clear; lia) end.
      lazymatch type of PCL with rw_cells _ _ ?a _ => replace a with (FB + 288) in PCL by (clear; lia) end.
      lazymatch type of LCL with rw_cells _ _ ?a _ => replace a with (FB + 320) in LCL by (clear; lia) end.
      lazymatch type of VCL with rw_cells _ _ ?a _ => replace a with (FB + 352) in VCL by (clear; lia) end.
      lazymatch type of GRPC with rw_cells _ _ ?a _ => replace a with (FB + 368) in GRPC by (clear; lia) end.
      lazymatch type of GIDC with rw_cells _ _ ?a _ => replace a with (FB + 624) in GIDC by (clear; lia) end.
      clear FLNK FREST G1 G2 G3 G4 G5.
      cb8_to_c8 FHD (@nil cell). cb8_to_c8 PCL (@nil cell). cb8_to_c8 LCL (@nil cell).
      cb4_to_c4 VCL (@nil cell). lazymatch type of VCL with rw_cells _ _ _ (?c1 :: _) => cb4_to_c4 VCL [c1] end.
      cb4_to_c4 GIDC (@nil cell). lazymatch type of GIDC with rw_cells _ _ _ (?c1 :: _) => cb4_to_c4 GIDC [c1] end.
      (* [comment removed for export] *)
      change 128%nat with (80 + 48)%nat in FSH. rewrite zcells_app in FSH.
      apply rw_cells_app in FSH. destruct FSH as [FSH80 FSHR]. rewrite cells_size_zcells in FSHR. change (Z.of_nat 80) with 80 in FSHR.
      cbn [zcells] in FSH80. apply zcells_CB in FSHR; [| clear; lia].
  (* [comment removed for export] *)
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xb0d98] [] 726%N). lx_tree.
  lxr_leaf. lx_carry.
  match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 11 eexists. do 3 eexists. exists jb3, jb12, (firstn 136 (skipn 0 (cbytes (CB 144 jslots)))). do 6 eexists.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact REFC|]. split; [exact PCL|]. split; [exact LCL|]. split; [exact VCL|]. split; [exact GRPC|]. split; [exact GIDC|].
      split; [unfold EP_SH0; cbn [repeat app]; exact FSHX|].
      split; [exact FSHR|].
      split; [exact SAVE|]. split; [exact SLOTS|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
      all: match goal with |- ?gg => idtac "PRO-LEFT:" gg end.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (a0v : word)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_A ()) "Lms,$7.(8.P,(<.&40.)(=.(<.&8.))Lm',P,(<.&40.)(=.(<.&8.))(8.(:.$;.VR,VHIA,)Lh4,(:.$;.VR,VHIA,)(8.(<.&40.)Lt0,(<.&40.)(8.(<.&40.)Lt1,(<.&40.)(8.(<.&40.)Lt2,(<.&40.)(8.(<.&40.)La1,(<.&40.)(8.(<.&40.)La2,(<.&40.)(8.(<.&40.)La3,(<.&40.)(8.(<.&40.)La4,(<.&40.)(8.(<.&40.)La5,(<.&40.)(8.(<.&40.)La6,(<.&40.)(8.(<.&40.)La7,(<.&40.)(8.(<.&40.)Lt3,(<.&40.)(8.(<.&40.)Lt4,(<.&40.)(8.(<.&40.)Lt5,(<.&40.)(8.(<.&40.)Lt6,(<.&40.)(?.(10.$7.R11.(11.(12.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,O1.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(39.Vra,)Vfc,(17.(<.&40.))R10.(18.$;.)))(?.(30.$;.R10.)(?.(2?.$;.R10.Vlo,(1;.&40.Vsp,))(?.(31.$;.VR,VHIA,O8.O7.VLF,(1;.&40.Vsp,)(32.VR,)O3.O5.R10.)(?.(31.$;.VR,VHIA,O8.O6.VLF,(1;.&40.Vsp,)(32.VR,)O2.O4.R10.)(?.(10.P,$9.Sp(20.$;.VR,VHIA,R?.)(20.$;.VR,VHIA,O8.))(?.(10.$9.(21.$;.VR,VHIA,R?.)(21.$;.VR,VHIA,O8.))(?.(10.$9.(22.$;.VR,VHIA,R?.)(22.$;.VR,VHIA,O8.))(?.(10.$9.(23.$;.VR,VHIA,R?.)(23.$;.VR,VHIA,O8.))(?.(10.$9.(24.$;.VR,VHIA,R?.)(24.$;.VR,VHIA,O8.))(?.(10.$9.(25.$;.VR,VHIA,R?.)(25.$;.VR,VHIA,O8.))(?.Pmo,$26.(27.(28.$;.VR,VHIA,R10.R1.)(28.$;.VR,VHIA,O8.R1.))(1=.$;.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Hypothesis SF5 : arl_setf5 R = 0x6b330.
  Hypothesis NSH : arl_need_setsh R <= arl_need_rt R.

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 PAR; try lx_pin1 PKA; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 SM4; try lx_pin1 UARG.   (* [comment removed for export] *)
  #[using="NSH SF5 LFB TOP SLO LOS NEEDR NS1 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_A ()) "Ph3,(:.$;.VR,VHIA,)PLBa,(>.$3:.)PLBb,(>.$3:.)Pm0,P,(<.&40.)(=.(<.&8.))Pm2x,P,(<.&40.)(=.(<.&8.))Pmm,P,(<.&40.)(=.(<.&8.))PWA,(>.$33.)PWB,(>.$33.)PFB,$9.Psp1,$9.Pxra,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Pa0v,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Ps3v,(<.&40.)Ps5v,(<.&40.)Ps6v,(<.&40.)Ps7v,(<.&40.)Ps8v,(<.&40.)Ps10v,(<.&40.)Ps11v,(<.&40.)Pw0,(<.&40.)Pw1,(<.&40.)Pw2,(<.&40.)Pv1,(<.&40.)Pv2,(<.&40.)Pv3,(<.&40.)Pv4,(<.&40.)Pv5,(<.&40.)Pv6,(<.&40.)Pv7,(<.&40.)Pv8,(<.&40.)Pv9,(<.&40.)Pv10,(<.&40.)Pv11,(<.&40.)Pv12,(<.&40.)Pv13,(<.&40.)Pv14,(<.&40.)Pv15,(<.&40.)Pv16,(<.&40.)Pv17,(<.&40.)Pv18,(<.&40.)P,(1=.$;.VR,VHIA,R36.R34.(5.(1>.$9.$9.)(1?.$9.$9.R2>.+400.)VLF,)R31.)P,Px,$9.P,(20.$;.VR,VHIA,Vh,R1.)(20.$;.VR,VHIA,R39.R2.)P,(10.$9.(21.$;.VR,VHIA,R38.)(21.$;.VR,VHIA,Vh,))P,(10.$9.(22.$;.VR,VHIA,R39.)(22.$;.VR,VHIA,Vh,))P,(?.(19.(1:.(1;.&40.Vsp,)+110.)R31.)(19.R31.(1:.(1;.&40.Vsp,)+100.)))P,(10.$9.(1<.R32.+20.)=)P,(10.$9.(1<.R34.+40.)=)P,(29.VR,R3<.VLF,R35.+400.)P,(29.VR,R3<.VLF,R36.+400.)P,(3;.(20.$;.VR,VHIA,Vh,)R37.+400.)P,PB,$9.Pj,$9.P,(3<.(1>.$9.$9.)(1?.$9.$9.R2.R1.)VLF,)(3=.(19.(14.R3;.+400.)R3.)(19.(14.R3.R2.)R3;.))P,Pb',$3:.P,(3<.$3:.R1.R41.)(3<.$3:.R2.R41.)P,(2:.$;.R3=.R3:.(5.$1.(2;.R21.)(5.$1.(2;.R20.)(5.$1.(2;.R1?.)(6.$1.)))))P,(2:.$;.R3>.(14.(13.R3;.+3.)(15.(16.VR,)))$2>.)P,(2:.$;.R3?.(14.(14.(13.R3<.+3.)(15.(16.VR,)))+50.)(5.$1.(2<.#30.(2.(<.&8.)(4.&8.=)#30.))(6.$1.)))P,(2:.$;.R40.(14.(1;.&40.Vsp,)-68.)(5.$1.(2;.Vs11,)(5.$1.(2;.Vs10,)(5.$1.(2;.Vs9,)(5.$1.(2;.Vs8,)(5.$1.(2;.Vs7,)(5.$1.(2;.Vs6,)(5.$1.(2;.Vs5,)(5.$1.(2;.Vs4,)(5.$1.(2;.Vs3,)(5.$1.(2;.Vs2,)(5.$1.(2;.Vs1,)(5.$1.(2;.Vs0,)(5.$1.(2;.Vra,)(6.$1.)))))))))))))))P,(2:.$;.R41.(14.R3=.+8.)(5.$1.(2;.R22.)(5.$1.(2;.R21.)(5.$1.(2;.R20.)(5.$1.(2;.R1?.)(5.$1.(2;.R1>.)(5.$1.(2;.R1=.)(5.$1.(2;.R1<.)(5.$1.(2;.R1;.)(5.$1.(2;.R1:.)(5.$1.(2;.R19.)(5.$1.(2;.R18.)(5.$1.(2;.R17.)(5.$1.(2;.R16.)(5.$1.(2;.R15.)(5.$1.(2;.R14.)(5.$1.(2;.R13.)(5.$1.(2;.R12.)(5.$1.(2;.R11.)(6.$1.))))))))))))))))))))P,(2?.$;.R42.R3>.(14.R3>.+8.))P,(2?.$;.R43.(14.R3?.+98.)(14.(1;.&40.Vsp,)-68.))P,(2?.$;.R44.Vlo,R40.)P,(30.$;.R45.)P,(31.$;.VR,VHIA,R4;.R4:.VLF,(1;.&40.Vsp,)(32.VR,)R45.R48.R46.)P,(31.$;.VR,VHIA,R4<.R4:.VLF,(1;.&40.Vsp,)(32.VR,)R45.R48.R47.)(36.$;.(16.VR,)(20.$;.VR,VHIA,R4=.)(3>.R4=.R4<.R4;.R4:.R49.R47.R46.R2>.)(11.(12.R43.(4.&40.R44.)Vgp,Vtp,R42.R41.R40.Vsp,(4.&40.R44.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.(4.&40.R45.)R33.(4.&40.(14.(13.R45.+3.)(15.(16.VR,))))R32.R31.R30.R2?.(4.&40.R45.)R2>.R2=.R37.R36.R35.R34.)VF,(4.&40.+;1310.)Vfc,(17.(<.&40.))R48.(18.$;.)))")
(* [comment removed for export] *).
  Proof.
  clear PAL8. intros until v18.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH FSHR SAVE SLOTS STlo SThi STbelow MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 1024) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR NER TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 1024 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (1024 / 8) with 128 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  unfold EP_SH0 in FSH.
  cbn [repeat app] in FSH.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x6b330] [] 726%N). lx_tree.
  lxr_leaf. lx_carry.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into ma end.
  (* [comment removed for export] *)
  lazymatch goal with FSa : rw_cells _ ma (SHB FB) ?cs1, FSb : rw_cells _ ma (SHB FB + 80) ?cs2 |- _ =>
  pose proof (proj2 (rw_cells_app asegs ma (SHB FB) cs1 cs2) (conj FSa ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact FSb))) as FSALL;
  clear FSa FSb end.
  cbn [app] in FSALL.
  assert (BLa : blocks_low R LBa LF) by (destruct PRES as (_ & _ & _ & K); exact K).
  assert (BLb : blocks_low R LBb LF) by (destruct PRES2 as (_ & _ & _ & K); exact K).
  assert (SFa : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB (8 * 128)).
  { eapply shadow_free_fresh; [exact FRSH| exact BLa| clear; lia| clear; lia| exact ALO| exact AP]. }
  assert (SFb : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB (8 * 128)).
  { eapply shadow_free_fresh; [exact FRSH3| exact BLb| clear; lia| clear; lia| exact ALO| exact AP]. }
  replace (Z_to_bv 64 439088) with (Z_to_bv 64 (if Z.eqb 0xf5 0 then arl_set00 R else if Z.eqb 0xf5 0xf5 then arl_setf5 R else arl_setf8 R))
  by (cbn [Z.eqb Pos.eqb]; rewrite SF5; reflexivity).
  change (presW asegs R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 ma) with (hidden (presW asegs R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 ma)) in PRES.
  change (presW asegs R HIA h3 LBb LF (bv_unsigned sp) (arl_stklo R) WB m2x ma) with (hidden (presW asegs R HIA h3 LBb LF (bv_unsigned sp) (arl_stklo R) WB m2x ma)) in PRES2.
  pose proof (artA_set_shadow asegs R HIA 0xf5) as SPEC.
  specialize SPEC with (h := h3).
  lazymatch goal with HHc : HM _ _ _ h3 LBb _ ma, STc : stk _ ma lo sp1, MIc : mem_inv _ ma |- _ =>
  callrt sp1 (eapply SPEC with (LB := LBb) (LF := (FB, 1024) :: LF) (A := FB) (s := SHB FB) (n := 128) (lo := lo); clear SPEC;
  rewrite ?(unsigned_lit sp1) by exact SP1R;
  first [ exact HHc | exact LOS | exact F8 | exact FSALL | exact STc | exact MIc | reflexivity
  | lazymatch goal with
  | |- _ \/ _ \/ _ => right; left; reflexivity
  | |- 0 < 128 => clear; lia
  | |- _ = shadow_of _ _ => unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear; lia
  | |- crange _ FB _ => exact CFB3
  | |- forall x, _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; right; exists (FB, 1024); split; [left; reflexivity| cbn; first [ clear - Hx; lia | lx_side_lia ]]
  | |- Z.of_nat _ = 128 => cbn; reflexivity
  | |- lo <= _ => first [ clear - SLO SP1 NEEDR NER NSH; lia | lx_side_lia ]
  | |- crange _ lo _ => eapply crange_sub; [exact SCS3| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]
  end
  | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SETSH-PRE-LEFT:" g end ])
  end.
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SETSH-LEFT:" g end.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  rename PC into MUs.
  rename PC0 into WMs.
  rename PC1 into MIs.
  rename PC2 into FSH5.
  rename PC3 into STs.
  rename POST into HHs.
  assert (ESH : shadow_of AL FB = SHB FB) by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3) with 8; clear; lia).
  pose proof MUs as MU'.
  rewrite <- ESH in MU'.
  unfold hidden in PRES, PRES2.
  apply (presW_munch_sh R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 ma mb FB 128 lo sp1) in PRES;
  [| exact MU'| exact WMs| exact CFB3| exact SFa| exact LOS| first [ clear - SP1; lia | lx_side_lia ]| first [ clear - ALO LOS SLO NEEDR NER; lia | lx_side_lia ]| exact F8].
  apply (presW_munch_sh R HIA h3 LBb LF (bv_unsigned sp) (arl_stklo R) WB m2x ma mb FB 128 lo sp1) in PRES2;
  [| exact MU'| exact WMs| exact CFB3| exact SFb| exact LOS| first [ clear - SP1; lia | lx_side_lia ]| first [ clear - ALO LOS SLO NEEDR NER; lia | lx_side_lia ]| exact F8].
  clear MU' FSALL.
  clear STbelow.
  transport_after_call asegs ma mb MUs WMs.
  clear MI.
  clear HH3.
  clear MUs WMs.
  (* [comment removed for export] *)
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 1024) :: LF) mb FB 1024 HHs ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 1024 - 8) with (FB + 1016) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 1024) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 1024) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NEEDR NER; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 8 + 144 <= p \/ p + 1 <= sp1 + 8).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR NER; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NEEDR NER; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NEEDR NER; lia | lx_side_lia ]]).
  clear HHs NCp NSp FHD.
  repeat match goal with H : rw_cells _ mb (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ mb (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
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
  chunk_to_stk SLOTS.
  chunk_to_stk SAVE.
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 8), STC : stk _ mf (sp1 + 152) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOTS; stk_merge_into ST0 STC; stk_merge_into ST0 SAVE;
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
  all: match goal with |- ?gg => idtac "EPI-LEFT:" gg end.
Qed.
  End Call.
End WalkEP.
