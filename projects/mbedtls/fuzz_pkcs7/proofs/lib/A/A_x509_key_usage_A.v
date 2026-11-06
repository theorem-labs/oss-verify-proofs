(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_bitstring.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_rt_facts A_asn1_get_bitstring.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA LxSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt LxA_sums.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007bcd1190429204 0 2 0 1 10 1P0113e340a471e8da 0 4 0 1 1 1 97 1 98 1P019ffd5a2112eda6 1 1 32 2 0 1 96 1 3 19 1 97 1 98 32P020e2f86eb113a6e 0 6 0 1 63 1 78 1 79 1 94 1 95 1P021771989caac614 1 1 4 3 0 1 97 1 98 1 5 2 1 46 1 96 1 99 1 100 4P0228304d46a1853a 0 4 0 1 91 1 101 1 102 1P0331649561afe2f3 0 2 0 1 1 1P034ed26c463ebefa 1 1 8 3 0 1 98 1 101 1 4 2 1 99 1 100 1 102 8P034ed548e55818c0 0 4 1 1 2 1 98 1 99 1P0374e14d1196baa4 0 2 0 1 91 1P03839a8f612ffd84 0 7 0 1 60 1 62 1 79 1 80 1 97 1 98 1P03b66307f17188bc 1 1 64 2 57 1 87 1 3 0 1 86 1 88 64P0468be28f7aca92e 2 103 1 1 4 3 1 1 115 1 116 1 5 0 1 102 1 114 1 117 1 118 4 1 1 4 3 2 1 114 1 117 1 4 0 1 115 1 116 1 118 4P04a742e73a769b86 1 1 16 3 0 1 96 1 97 1 5 45 1 65 1 95 1 98 1 99 16P04d4e535631c552f 0 4 1 1 3 1 99 1 100 1P05f2f15fd8fefa0a 1 1 16 3 0 1 97 1 98 1 4 46 2 96 2 99 2 100 32P05f8cdcd2cf1bf23 0 4 0 1 84 1 94 1 95 1P065a319a5cb05e9a 0 2 0 1 90 1P076070dfa5052d62 0 8 0 1 5 1 6 1 13 1 101 1 102 1 103 1 105 1P08074805e1d2a60d 1 1 16 3 0 1 96 1 97 1 5 45 1 65 1 95 1 98 1 99 16P083a8d9c7cd3de9f 1 1 32 3 0 1 97 1 98 1 4 66 1 96 1 99 1 100 32P09b6c795d8024b55 0 5 0 1 47 1 86 1 96 1 97 1P09e3bd109cdb0cc4 0 5 0 1 45 1 84 1 94 1 95 1P0a06e3a81cb440b2 0 5 0 1 47 1 86 1 96 1 97 1P0a6c35e4f13bcdd2 0 2 0 1 1 1P0ae706ad02f46615 1 1 32 3 0 1 96 1 97 1 4 65 1 95 1 98 1 99 32P0bc6b239500249f7 1 1 32 3 0 1 97 1 98 1 4 66 1 96 1 99 1 100 32P0bf1ec6c8ea831bd 0 5 0 1 47 1 86 1 96 1 97 1P0bf4604dc27d3ab8 0 4 0 1 91 1 101 1 102 1P0c8035f1c7dac688 1 1 16 3 0 1 98 1 99 1 4 47 2 97 2 100 2 101 32P0cf951a840d434a6 1 1 32 3 1 1 96 1 97 1 4 65 1 95 1 98 1 99 32P0cfcd51e5074b7a1 1 1 16 3 0 1 102 1 103 1 4 34 2 101 2 104 2 105 32P0d5a77f556528b7f 1 1 8 2 43 1 97 1 3 0 1 96 1 98 8P0efd8519a0544d88 0 2 0 1 9 1P0eff4099737c2052 1 1 32 3 0 1 95 1 96 1 4 64 1 94 1 97 1 98 32P0f297553719ea59c 1 1 8 3 0 1 100 1 103 1 5 2 1 67 1 101 1 102 1 104 8P104d922ae7edd4d2 0 5 0 1 45 1 84 1 94 1 95 1P1059b61588e35c0d 0 4 0 1 3 1 99 1 100 1P1084a4531c36f732 0 6 0 1 65 1 80 1 81 1 96 1 97 1P10a6aa45b8cdf3dc 1 1 8 3 1 1 99 1 100 1 5 2 1 48 1 98 1 101 1 102 8P117d0d9b786318ea 1 1 8 3 0 1 98 1 101 1 5 2 1 67 1 99 1 100 1 102 8P11b87d104cdd2223 1 1 16 3 0 1 97 1 98 1 4 46 2 96 2 99 2 100 32P11d87c0aa192f603 0 6 0 32 46 32 96 32 97 32 98 32 99 32P11ed32e5767904a4 2 103 2 86 1 1 4 3 3 1 97 1 100 1 6 0 1 48 1 87 1 98 1 99 1 101 4 1 1 4 3 2 1 98 1 99 1 5 0 1 47 1 97 1 100 1 101 4 2 86 1 1 4 3 3 1 97 1 100 1 6 0 1 48 1 87 1 98 1 99 1 101 4 1 1 4 3 2 1 98 1 99 1 5 0 1 47 1 97 1 100 1 101 4P120a1bf725a8b92f 0 5 0 1 45 1 84 1 94 1 95 1P126c5ce742055ec2 0 7 0 1 5 1 6 1 12 1 13 1 103 1 105 1P12bbfe8fc6f9d2e1 1 1 8 3 0 1 97 1 98 1 5 2 1 46 1 96 1 99 1 100 8P13034c27e44060e3 0 2 2 1 4 1P137d70cd56ae7f84 1 1 16 3 0 1 95 1 96 1 4 44 2 94 2 97 2 98 32P1390b5552886149f 1 1 32 3 0 1 97 1 98 1 4 66 1 96 1 99 1 100 32P13a08f96d4a54510 0 2 2 1 4 1P14afa5e2a2c1ab5c 1 1 16 3 0 1 96 1 97 1 5 45 1 65 1 95 1 98 1 99 16P150c013e21e9b506 1 1 8 3 1 1 99 1 100 1 5 2 1 48 1 98 1 101 1 102 8P15274d11c9860dba 0 6 0 1 44 1 75 1 77 1 94 1 95 1P1548f2ac0bb063a4 0 2 2 1 4 1P155f3ae0fff30055 0 4 0 1 91 1 101 1 102 1P156383842362884e 0 8 0 1 44 1 56 1 74 1 75 1 77 1 94 1 95 1P1629a7ab3a44e941 0 5 0 1 35 1 91 1 101 1 102 1P1651adf314533efd 0 7 0 16 44 16 64 16 94 16 95 16 96 16 97 16P1667df70e123d9ea 0 2 0 1 1 1P16b9686fa7b2ad82 0 4 1 1 2 1 98 1 99 1P1767a0ae6dc52a0e 0 4 0 1 91 1 101 1 102 1P17dd81d622a89b4f 0 5 0 1 33 1 76 1 86 1 87 1P1823bebff0f72394 0 7 0 16 46 16 66 16 96 16 97 16 98 16 99 16P188354c7f77b9d1e 0 4 1 1 3 1 99 1 100 1P197149cc4d7d6ff5 1 1 32 3 0 1 96 1 97 1 4 65 1 95 1 98 1 99 32P19d06ab831b00aa1 0 7 1 1 60 1 62 1 79 1 80 1 95 1 96 1P19ffd4c8a674a162 0 7 0 1 59 1 61 1 78 1 79 1 94 1 95 1P1a178edf1f09daa4 0 4 0 1 1 1 97 1 98 1P1a2bfaa4fe3a3598 0 4 0 1 84 1 94 1 95 1P1a33aaf312514fd0 1 1 32 2 18 1 96 1 3 0 1 97 1 98 32P1a5c2beac6eaa26c 1 2 32 3 1 1 98 1 99 1 32 8 48 1 62 1 64 1 81 1 82 1 87 1 97 1 100 1 2 101 2 102 2P1a8672c9124016c8 2 103 2 87 1 1 8 3 3 1 97 1 100 1 6 0 1 48 1 87 1 98 1 99 1 101 8 1 1 8 3 2 1 98 1 99 1 5 0 1 47 1 97 1 100 1 101 8 2 87 1 1 8 3 3 1 97 1 100 1 6 0 1 48 1 87 1 98 1 99 1 101 8 1 1 8 3 2 1 98 1 99 1 5 0 1 47 1 97 1 100 1 101 8P1a8fecb2ea6e4af9 0 2 0 1 2 1P1aba7166b6f81a66 0 2 0 1 9 1P1afff20adf33bd93 1 1 16 3 0 1 95 1 96 1 5 44 1 64 1 94 1 97 1 98 16P1b344475a69a38e5 1 1 32 3 1 1 98 1 99 1 4 67 1 97 1 100 1 101 32P1b5693fe7a551d6c 0 4 0 1 91 1 101 1 102 1P1b59ca31e137af95 0 2 0 1 12 1P1b763917033024a6 1 1 4 3 1 1 98 1 101 1 5 2 1 67 1 99 1 100 1 102 4P1c10970f656569eb 0 5 0 1 47 1 86 1 96 1 97 1P1c4f286cf286fbe1 1 2 32 3 1 1 98 1 99 1 32 8 48 1 62 1 64 1 81 1 82 1 87 1 97 1 100 1 2 101 2 102 2P1ceb1824542a73a8 0 8 0 1 44 1 56 1 74 1 75 1 77 1 94 1 95 1P1cf5166958c0eb90 1 1 32 3 1 1 96 1 97 1 4 65 1 95 1 98 1 99 32P1d69b97424a2706d 1 1 32 3 0 1 98 1 99 1 4 65 2 97 2 100 2 101 64P1db7644d6ac48a39 0 2 0 1 87 1P1e34a3dbdd4f8737 1 1 32 2 0 1 94 1 3 17 1 95 1 96 32P1e848b782cc5f860 0 3 0 1 78 1 79 1P1ed696beba4cd51e 1 1 16 3 0 1 96 1 97 1 4 45 2 95 2 98 2 99 32P1ef0e0943da13e37 0 4 0 1 2 1 100 1 101 1P1f2ff36162d3dd95 0 6 0 32 64 32 94 32 95 32 96 32 97 32P1f7fdf1f0862de35 0 2 0 1 12 1P20213dab7c215359 0 5 0 1 1 1 47 1 97 1 98 1P20282d560c8f2a40 0 4 0 1 91 1 101 1 102 1P205b4bceefd330be 0 7 0 1 6 1 7 1 13 1 14 1 104 1 106 1P20c4157c1cba5e38 0 4 0 1 91 1 101 1 102 1P211aa6761a85a9b8 1 1 32 3 1 1 96 1 97 1 4 65 1 95 1 98 1 99 32P212e0c4e6fb825ba 0 2 0 1 2 1P22740ed84a4bfe6d 0 2 0 1 1 1P22a3da9f43ab895d 0 8 0 1 46 1 58 1 76 1 77 1 79 1 96 1 97 1P22b4b6739f1906ba 1 1 4 2 0 1 111 1 3 38 1 112 1 113 4P22da7ab8d46910b3 0 2 2 1 4 1P23384a3db24d7ea8 1 1 4 2 0 1 111 1 3 38 1 112 1 113 4P23d7e724a8318327 0 5 0 1 3 1 49 1 99 1 100 1P246722316832585f 0 2 0 1 89 1P24678ca307df80ca 0 4 0 1 91 1 101 1 102 1P24c933b0d70beb89 0 2 0 1 11 1P2553741a655387c2 0 6 0 1 46 1 77 1 79 1 96 1 97 1P266d78ba3d1b674e 0 2 0 1 2 1P26b05c80845714e8 0 2 0 1 11 1P26b7eb698f84d562 0 4 0 64 9 64 94 64 95 64P26e54398458ad4d9 0 4 0 1 3 1 97 1 98 1P274c57d388e32524 0 6 0 32 66 32 96 32 97 32 98 32 99 32P275f2addc8a151a4 1 1 32 2 16 1 94 1 3 0 1 95 1 96 32P27f4a2f3af467c29 1 1 32 3 1 1 96 1 97 1 4 65 1 95 1 98 1 99 32P28beb3882e1beb2d 0 6 0 1 44 1 75 1 77 1 94 1 95 1P2915607f6e220510 0 4 0 1 76 1 86 1 87 1P294fd59813a18929 1 1 64 2 1 1 86 1 3 0 1 87 1 88 64P296b95e0d8a655cf 0 2 0 1 88 1P2973f09403bf200a 0 2 0 1 1 1P29eab9be209ff66a 1 1 32 3 0 1 96 1 97 1 4 65 1 95 1 98 1 99 32P2a4051f0ad070322 1 1 16 3 0 1 95 1 96 1 4 44 2 94 2 97 2 98 32P2b200d977aa3c443 1 1 16 3 0 1 87 1 88 1 4 32 2 86 2 89 2 90 32P2be58c5a2640001d 1 1 16 3 0 1 88 1 89 1 5 33 4 57 4 87 4 90 4 91 64P2bf3c4236b154ee2 0 4 0 4 59 4 111 4 112 4P2c2af7b8753dc7a0 0 3 0 1 78 1 79 1P2cdaf226351c729b 0 2 0 1 2 1P2d154771623bd00f 1 1 32 3 0 1 95 1 96 1 4 64 1 94 1 97 1 98 32P2e068f465985d035 0 4 0 1 3 1 99 1 100 1P2e466760d53902a8 0 4 0 1 91 1 101 1 102 1P2e4c61b6af0997e8 0 2 0 1 1 1P2e55a4da30e0383a 0 7 0 1 59 1 61 1 78 1 79 1 94 1 95 1P2e6bc574073b0e1b 2 120 2 103 1 1 4 3 2 1 115 1 118 1 6 0 1 64 1 103 1 116 1 117 1 119 4 1 1 4 3 3 1 116 1 117 1 5 0 1 63 1 115 1 118 1 119 4 2 103 1 1 4 3 2 1 115 1 118 1 6 0 1 64 1 103 1 116 1 117 1 119 4 1 1 4 3 3 1 116 1 117 1 5 0 1 63 1 115 1 118 1 119 4P2fb7072957bf314c 0 4 0 1 63 1 80 1 81 1P2fcfc3e1066c93b3 0 4 0 1 91 1 101 1 102 1P3003124d1361d1af 1 1 32 3 0 1 100 1 101 1 4 67 1 99 1 102 1 103 32P3027ff84c674d972 0 2 2 1 4 1P311f7d53f0554f34 1 1 32 3 0 1 95 1 96 1 4 64 1 94 1 97 1 98 32P31aec703b1198492 1 1 8 3 1 1 99 1 100 1 4 2 1 98 1 101 1 102 8P31eea66916d4c6eb 0 7 0 1 62 1 64 1 81 1 82 1 99 1 100 1P32a5f23b933a16eb 1 1 4 2 0 1 114 1 3 39 1 115 1 116 4P32ecb2e5b352ffd1 1 1 16 3 0 1 98 1 99 1 5 47 1 67 1 97 1 100 1 101 16P33683b531c0c0350 1 1 32 3 0 1 98 1 99 1 4 67 1 97 1 100 1 101 32P33a9489c870f9df9 0 2 0 1 9 1P347270c010c2c60d 0 5 1 1 3 1 68 1 99 1 100 1P34762378e81eab2e 3 102 0 2 1 1 2 1 3 85 0 2 1 1 3 1 0 6 0 1 4 1 49 1 88 1 98 1 99 1 0 5 0 1 3 1 48 1 98 1 99 1 3 85 0 2 1 1 3 1 0 6 0 1 4 1 49 1 88 1 98 1 99 1 0 5 0 1 3 1 48 1 98 1 99 1P3586de7c842c18ab 1 1 16 3 0 1 97 1 98 1 5 46 1 66 1 96 1 99 1 100 16P35a786f7a9bd9905 0 5 0 1 45 1 81 1 94 1 95 1P35bbd3b066cd26c3 1 2 64 2 0 1 94 1 64 2 65 1 95 1 2 96 1 97 1P360ec19e9108476d 0 4 0 1 91 1 101 1 102 1P363c50f7cd4d7e9b 1 1 32 3 1 1 96 1 97 1 4 65 1 95 1 98 1 99 32P363ee5db144d1772 1 1 4 2 0 1 114 1 3 39 1 115 1 116 4P36d8d331af06902d 0 7 1 1 60 1 62 1 79 1 80 1 95 1 96 1P371fbf2b82623122 1 1 8 3 1 1 98 1 101 1 4 2 1 99 1 100 1 102 8P375b1dada325a891 0 5 0 1 45 1 84 1 94 1 95 1P37e7d28d872f7cfb 0 2 1 1 3 1P3821796819e72d6b 1 1 16 3 0 1 96 1 97 1 5 45 1 65 1 95 1 98 1 99 16P383abc6dac7e09b7 1 1 64 2 0 1 96 1 3 4 1 97 1 98 64P38dc2af610f9f3bc 0 2 0 1 12 1P38f6998c975f6c79 0 2 0 1 1 1P392d2e1178997fe9 0 4 1 1 3 1 97 1 98 1P3a4c59b62fde34c5 1 1 32 3 0 1 87 1 90 1 4 57 1 88 1 89 1 91 32P3ac790dd381a22e3 0 7 1 1 60 1 62 1 79 1 80 1 95 1 96 1P3b288c6ece1e6602 0 2 0 1 1 1P3b66b54f028c3c5e 1 1 16 3 0 1 96 1 97 1 4 45 2 95 2 98 2 99 32P3b964f2f414a2fed 0 5 0 1 45 1 84 1 94 1 95 1P3c499be46bdbcbc5 1 1 4 3 0 1 99 1 100 1 5 2 1 48 1 98 1 101 1 102 4P3c50582142b80570 0 4 0 1 84 1 94 1 95 1P3d151cb7a1ec7603 1 1 32 3 0 1 96 1 97 1 4 65 1 95 1 98 1 99 32P3d1a904fef8c91b6 1 1 8 3 1 1 99 1 102 1 4 2 1 98 1 103 1 104 8P3db5ab47ca03d93c 0 5 0 1 3 1 47 1 97 1 98 1P3e748147d8d90dc3 0 2 0 1 12 1P3ef6484d5d31ba74 0 6 0 1 44 1 75 1 77 1 94 1 95 1P3fa145c3c30055a1 1 2 64 2 0 1 86 1 64 2 57 1 87 1 2 88 1 89 1P3fa4b08c931269e9 0 4 0 1 91 1 101 1 102 1P3fba9899b990f4fb 1 1 8 3 0 1 99 1 100 1 5 2 1 88 1 98 1 101 1 102 8N003b1738cde77127N00a1174e006efbe2N01360131e5d34d96N016880c180128486N01715de19073a301N01ae3727f4a9a6d8N01bb475923e90b1fN01be1bcef8e9960eN0209d22acf158c02N0221e2aceed5668aN0252af40ea08b1bcN026076adfda769edN02a611f9e66967daN031887109b38e6d0N036430f85778ccddN03b507da8bfe9f9fN04738f9288fe099aN0484837e63a765e3N04b37ef6d0ec91c2N054068e6599ae08cN057690f95480832dN0597a1b97e06d561N05a5d0381846720eN05f2abef28eb7355N0646b9a3b61230a9N06818506ab154f27N068ea6750bfb21bfN06b3930bcbe48fedN0736e4677e7215ceN076058122c58f030N078d1c94e0fcd7ffN079be264a4616729N08051506ade90813N080e55b7ab1a1178N083c32c9ff0e1247N086dfa8174a0b64aN08a560bde6212833N092200c03e0ea671N0945037abf89bc55N09563d10e5f969a6N09b9e0269652aec2N0a0de4d1e29c5381N0a25e1c154fee17dN0a8daaf3272d1e39N0ab2a850e58e179dN0ba537d14d396e5bN0bb29a480ef294efN0bb752d442870895N0bd203c34917d470N0beb2bc307c59966N0bf6f8a7154a48f7N0c00dd4d2d9235f4N0c2746e4fb837b34N0c323cbe45b76af0N0c553086cd261cc7N0c680e43d54f0bb8N0ca268a2d248e34fN0ccdde223948331eN0ce0a5366c5c95e3N0d0045e61b7e1af6N0d3afe5941f27983N0da8d1e2d2c2a592N0df57d5bdf4a74e9N0e258e73c63af1c1N0e4f128ec4a334eaN0e75b7c4fe5683a8N0e7c1f837bc2e858N0ea18e503b558aedN0ea75a9b275ef45cN0eaded5ae7841decN0eb4eff2dd28c59aN0ec2891fa0566d39N0f3f96b4387978bbN0f5ac66311d0546aN0f89c5b0889ff6c2N0fa1be952d7c9b15N0fb4b02350a8d160N0fe712fb3f9b5da9N103256b65128bcecN1057b313d9e6d6f2N1069866f235c8f90N10ab182f947fd363N10ac59e7e49f8d40N10b6ac31fed055ffN111ef0dc7f3469a6N111f097106b39830N11492ccbb51cb565N117fcea5a841f77fN118caef5897099e6N119d1d2b7e36a569N11b996f898ee9fe4N11c58e912989185cN11e48ebe423dece2N12282cdbd4ac9cb0N12297817f4bdfc57N13142015baefe99dN131fa3fc1c9dade4N13289dc3cfe2ca4bN133daa410f00aba4N1345f0f71c3439c8N1369a165cff897c4N139150932f5486f3N13a5eeee8480124fN14172f4b31cd8fd8N1496c276b579c15cN14a55cd94a060ea6N14ae02b0185f509aN14b395311dd3dcc9N14c07fd3b39d3584N14c3370fee18aacbN14fc4846e8d05b97N15e3686520e75e0fN161f38de3b1ae55cN1625233eaf244c1aN1673fa811257416eN16c745c44591809bN16e32d543b9e4b48N16e5be3f7213d521N16f26101a77cdd08N172bee23884441b5N17884438ab4de38cN17ad5283275ef4a4N17f6b7a436db11e9N1850785503ae6ceaN188491a79648a373N188d4fca207f64beN18fcd28cc6e21f49N191917fbff2955deN192035345b2cea92N19a67a3eee69b858N19b6ef7e80065e2fN19e2957bc6a9b713N1a08b67030e60628N1a2d77816e07d4d8N1a39a371adbd00a2N1a3dcef143d30186N1a487da6d0eeb330N1b2e05b48f93f488N1b89b0b91808d010N1bd579e466c2bfaaN1c4fdad60c557937N1c5327b03541f39aN1c8c98ecb388d9b2N1ceec3690846426aN1d422fb663e9b21dN1d6fb2b74f438161N1dd56aeade1339e5N1dde19ddd10db0f8N1e691fa8a9b15447N1f2153a2cef84befN1fe5d65bfd8480a2N200336cc92845c12N205d449ecf08e1f5N20770f884e47371eN20a70b1d5870acdeN20ae02598fa5ba96N20c739d73225fdcdN20cb2775ad6df21dN2106c02f56f6b4f4N2167d43b3bec8d9cN21818912b8bbf39cN21872a0c559a5e66N21906d27432aaadbN21df9a3fa032be31N21e64782f0561350N2236101dafa8b9d7N2238bd06081745ddN2279377c2ef37b7bN22ec80292756fa14N22edcb55c8514a16N231be8ff9fbf4ff8N234d01febd400ff3N23563776e973dabbN235d77c903648330N23b655bd93315230N23b67d2cc04ba26fN23d4bb6924bb1850N23d7aeedf9bd7edaN23ed5033cd110e00N23ef67957549abf9N241e49cda75e1d62N2426cd83cd35ead2N2427d8fe9b80e3e4N24374d9087fbabf5N24e2e1306344996aN25112c82ff0cc99dN255354d876fa1344N2571bd2118b3b38cN2592c7226763a6e7N2595c2febadc15bdN25abc8f2c2b13c68N25b62ece9250861eN25c28322b0fa6ad5N25d6ee13535a5f46N260673e74b51285fN2638471eb036c09eN264ba88a58b3e520N26909647d3e818b0N26f060e1a9e1b171N2705923176b3db62N270d4d573cb45eaaN27d03b6aeb8bdb72N288dd9c028b4c34aN2893ee5c68beb038N28a0ad1ec82828c1N28b82ab88fbcee6fN28bce82c445b0c92N28e5d0e29e96277cN294084bc0e70e267N2944d1c893fb87b1N297101d23c7e2a6dN29bae05491533b8dN2a5ff09a2c383b79N2a6bd3e8e3b2d4bcN2a739fdf7d7e388aN2a7cb51942efd114N2a826fe62c10021eN2a95869f706fa4bdN2abc52a0e762f2dcN2ad1eacd8a70b9f2N2b4b5bd6a9a53ed8N2b9c2d2032c6f450N2baa6780c6427ed4N2bbdff097211b704N2c4bb608696d2a93N2c5aab93b83af81cN2c60b1c4bea8fd72N2c74ce5f6afb42c6N2c8e66e5b09ee53eN2cab762a4ac7a1d9N2d1ed8afc6ff92d8N2d45f1ed0cedb14cN2dfd7d2543d3b7d8N2e3075d05a083ac4N2e4c4e6eb2bf9dbdN2ebcc1af4aa26d49N2f023fa437916897N2f1e85642313507eN2f3deaa655f3c18cN2f4bb21e11f47c32N2f8eaf0864d6f833N2fab01df366eefcdN2fab6420139d1718N2fb471745ad2d44fN2fbdac8d461f639bN2fc0e91835fed02eN2fc3a490d127736bN2fcbb34a9c252789N2ffce91894a12f0dN300ad276d4dd3599N309f42f4320f0926N30b29c0931da4b7eN30dc3e386fc02c2eN30e42c847f01f3fcN3117baa4115a811dN312172ad539b0418N314603e95fb9ce55N316e9acbdc10a027N317a3c905ec41f55N3182b51608316cc2N31868c3f860fc255N318b5c6e873f6c0dN31bfe2e2311e3d60N31fdc5659244f3bdN321bf2f0453ce99cN32841896e9cc3e41N32a6d8e691e89c96N32ba66a87267ff4fN32c0d7bfde4b529eN330c55b932dd34ebN341f3fb738313bd7N3424aec0ad2d0064N352fb4e210951c8fN3578243d7b9d8d9eN358889b697677bbdN35ff16c0011e75e7N3658158c0d43a937N36a5b9363a226064N36cb866bbcf8c727N36e890d4a1cb2091N370a53649a8bd0a5N3715330cf15f87e3N37b8cf254c4e65a9N37d1285d17969d4cN37d2f35d465ec710N37d6bf4db1a0b511N37f7fcc830393375N385fc035d9300637N38af0acd6695da84N38ffa0161573b41eN397a91d70244e94eN39d33b2508996542N3a38599b933a914fN3aa6993c239b6bd3N3b1690aa833faccfN3b84fc264f212b6bN3ba1d80c8e181e38N3bcba0f49835bfb2N3be7fed29f8d015dN3c5fb58a859f3bbfN3c78931f8030e35aN3c802fbebc642397N3c9ef8c4de2d75ffN3cab564006c856abN3cae8f09cc5f29b8N3cc18aeac86f9b37N3d6d547ba07e1290N3d7f873110babd71N3dad30d2ec579b4fN3db7f571402e22c4N3de4df2ad2cf2afeN3e40876a37ade81dN3e4cad9365e5c186N3e6ce50f20e6b158N3e8699f51dfaa661N3e9eb592046b453bN3ea5107ed31ffc8fN3ef867ebaea35861N3f01d8ed1b863e70N3f06ef431518b08cN3f595a2a3670877eN3f68f246283b9fc6N3f7a5413853327d9N3f8fd7585f6051f3"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_key_usage_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.presA"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "X509_KU_STACK_A"; "OSSVerify.KrLib.LibA.ARt.arl_need_smalloc"; "OSSVerify.KrLib.LibA.ARt.arl_need_amem"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "x509_ku_postA"; "stdpp.bitvector.definitions.bv_swrap"; "OSSVerify.KrLib.A.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.Lib.HeapIface.in_block"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.wlow"; "OSSVerify.KrLib.LibA.ARt.wcover"; "OSSVerify.KrLib.LibA.ARt.shadow_free"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "Walk.fctx"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.land"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.LibA.ARt.zcells"].


Definition A_X509_KEY_USAGE : Z := 0x0ae8b4.     (* [comment removed for export] *)
Definition A_SMALLOC_1U : Z := 0x52af8.             (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_AMEMSET_U : Z := 0x67ce4.              (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
Definition X509_KU_STACK_A : Z := 128.

Definition x509_ku_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP KU P END lo slo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.O1?.O1>.O1=.)Lh',(4.O1?.O1>.O1=.)(1.$5.Lr,$5.(1.$5.Lp',$5.(1.(2.&40.)Lv,(2.&40.)(6.(7.$0.R15.(8.(9.O19.O18.O17.O16.R14.R13.R12.O15.O14.R11.R10.R?.R>.R=.R<.R;.R:.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R9.R8.R7.R6.)O9.(:.O19.)O8.(;.(2.&40.))R5.(<.O1?.)))(6.(=.O1?.O1>.O1=.R4.O1;.O1:.R5.)(6.(7.P,$5.Sp(>.O1?.O1>.O1=.R4.)(>.O1?.O1>.O1=.O1<.))(6.(7.$5.(?.O1?.O1>.O1=.R4.)(?.O1?.O1>.O1=.O1<.))(6.(7.$5.(10.O1?.O1>.O1=.R4.)(10.O1?.O1>.O1=.O1<.))(6.(7.$5.(11.O1?.O1>.O1=.R4.)(11.O1?.O1>.O1=.O1<.))(6.(7.$5.(12.O1?.O1>.O1=.R4.)(12.O1?.O1>.O1=.O1<.))(6.(7.$5.(13.O1?.O1>.O1=.R4.)(13.O1?.O1>.O1=.O1<.))(6.Pmo,$14.(15.(16.O1?.O1>.O1=.R5.R1.)(16.O1?.O1>.O1=.O1<.R1.))(6.(17.O1?.O1>.O1;.O1:.(18.&40.O18.)(18.&40.O18.)(10.O1?.O1>.O1=.O1<.)(19.(1:.$5.$5.)(1;.$5.$5.O7.(1<.O7.+8.))(19.(1:.$5.$5.)(1;.$5.$5.O6.(1<.O6.+4.))(1=.(1:.$5.$5.))))O1.R5.)(6.(1>.O1?.R5.)(6.(1?.O1?.R5.O3.(18.&40.O18.))(6.(20.O1?.(21.O1>.)R5.O2.(18.&40.O18.))(6.(7.(2.&40.)R11.(22.&40.R3.))(6.(6.(23.-3000.R3.)(24.R3.=))(6.(25.O1?.R5.O7.(19.$26.(27.(22.&40.R2.))(1=.$26.)))(6.(25.O1?.R5.O6.(19.$26.(28.R1.)(1=.$26.)))(6.(24.O5.R2.)(24.R2.O4.)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_ku_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "Ph,(4.O4.O3.O2.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$5.PKU,$5.PP,$5.PEND,$5.PBUF,$5.Plo,$5.Pslo,$5.Pbs,(29.(2.&8.))Pv0,(2.&40.)P,(=.O4.O3.O2.R2>.R2=.R2<.R:.)P,(2<.(2=.$2:.R2=.)#200.)P,(25.O4.R<.R;.(19.$26.(27.(22.&40.R9.))(1=.$26.)))P,(25.O4.R=.R;.(19.$26.(28.R4.)(1=.$26.)))P,(2>.O4.R>.R9.R6.)P,(24.R:.R<.)P,(24.R=.R<.)P,(24.R=.(1<.R<.(2?.(2=.(2.&8.)R9.))))P,(23.(1<.R=.(2?.(2=.(2.&8.)R:.)))(30.+2.+3?.))P,(31.(24.(1<.R12.+8.)R11.)(24.(1<.R11.+4.)R12.))P,(31.(7.$5.(2?.(2=.(2.&8.)R<.))=)(31.(24.(1<.R13.+8.)R?.)(24.(1<.R?.(2?.(2=.(2.&8.)R<.)))R13.)))P,(31.(7.$5.(2?.(2=.(2.&8.)R=.))=)(31.(24.(1<.R13.+4.)R10.)(24.(1<.R10.(2?.(2=.(2.&8.)R=.)))R13.)))P,(7.$5.(32.R15.+8.)=)P,(7.$5.(32.R15.+4.)=)P,(6.(23.=R17.)(24.(1<.R17.+8.)(30.+2.+40.)))P,(6.(23.=R17.)(24.(1<.R17.+4.)(30.+2.+40.)))P,(23.=R15.)P,(1?.O4.R1;.R15.(18.&40.R3;.))P,(20.O4.(21.O3.)R1<.R15.(18.&40.R3<.))P,(24.R17.(33.(18.&40.R3=.)$34.))P,(24.R18.(33.(33.(18.&40.R3>.)+70.)(35.O3.)))P,(24.=(35.O3.))P,(24.R1:.(33.(33.(18.&40.R40.)+70.)(36.O3.)))P,(24.=(36.O3.))P,(24.(37.O3.)R1;.)P,(24.R1<.R1=.)P,(7.$5.(32.(18.&40.R44.)+10.)=)P,(24.(18.&40.R45.)(?.O4.O3.O2.R49.))P,(24.(18.&40.R46.)(30.+2.+2?.))P,(31.(24.(1<.R26.+8.)R21.)(24.(18.&40.R47.)R26.))P,(31.(24.(1<.R26.+4.)R22.)(24.(18.&40.R48.)R26.))P,(31.(7.$5.(2?.(2=.(2.&8.)R21.))=)(31.(24.(1<.R24.(2?.(2=.(2.&8.)R21.)))R23.)(24.(18.&40.R49.)R24.)))P,(38.(39.O3.)(3:.$2:.R4=.(3;.R4<.))R24.R29.+8.)P,(38.(39.O3.)(3:.$2:.R4>.(3;.R4=.))R25.R29.+4.)P,(38.(39.O3.)(3:.$2:.R4?.(3;.R4>.))R26.R27.(2?.(2=.(2.&8.)R24.)))P,(3<.(39.O3.)(3:.$2:.R50.(3;.R4?.))R27.(?.O4.O3.O2.R51.)R2<.+8.)P,(3<.(39.O3.)(3:.$2:.R51.(3;.R50.))R28.(?.O4.O3.O2.R52.)R2<.+4.)P,(1>.O4.R2?.)P,(7.(2.&40.)R4>.(22.&40.(3=.O3.)))P,(3>.O4.(21.O3.)(>.O4.O3.O2.R55.)R31.R30.+8.)P,(3>.O4.(21.O3.)(>.O4.O3.O2.R56.)R32.R30.+4.)P,(3>.O4.(21.O3.)(>.O4.O3.O2.R57.)R33.R2>.(2?.(2=.(2.&8.)R2;.)))P,(7.(2.&40.)R4<.(22.&40.R33.))P,(7.(2.&40.)R4<.(22.&40.R31.))P,(7.(2.&40.)R4<.(22.&40.R34.))(3?.O4.(21.O3.)(>.O4.O3.O2.R5;.)(40.O4.O3.O2.R5;.R5:.R59.R58.R57.R56.R55.R51.R50.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R39.R38.R36.R35.R34.R33.R31.R30.R37.)(8.(9.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.)R39.(22.&40.O1.)R38.(;.(2.&40.))R37.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GBS : asn1_get_bitstring_stmtA asegs AL A_ASN1_GET_BITSTRING.
  Hypothesis AMS : arl_amemset R = A_AMEMSET_U.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP KU P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= KU \/ KU + 4 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ KU + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= KU.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : KU mod 4 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis KUB : 0 < KU /\ KU + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_KU_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 112 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : KU + 4 <= lo \/ bv_unsigned sp <= KU.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo KU 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) KU 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_KU_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_ku_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP KU P END lo slo).
  Local Notation W := [(PP, PP + 8); (KU, KU + 4)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation FSHL := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

  (* [comment removed for export] *)
  Lemma swrap32_errsum' : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "Pr,$5.Pc,$5.P,(6.(23.-10000.R2.)(24.R2.=))P,(6.(24.(33.(30.+2.+40.)+10000.)R2.)(23.R2.(30.+2.+40.)))(7.$5.(41.&20.(1<.(32.R4.+10000000000000000.)R3.))(1<.R4.(33.R3.(30.+2.+40.))))")
(* [comment removed for export] *).
  Proof. intros. change 18446744073709551616 with (2^64). apply swrap32_errsum; assumption. Qed.

  (* [comment removed for export] *)
  Definition fctx (FB sp1 : Z) (h1 : HST asegs R HIA) (m0 mm : mem) (w0 w1 w2 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "(6.(=.$42.VR,VHIA,O6.VLB,(19.(1:.$5.$5.)(1;.$5.$5.O8.+80.)VLF,)O4.)(6.(7.P,$5.Sp(>.$42.VR,VHIA,O6.)(>.$42.VR,VHIA,Vh,))(6.(7.$5.(?.$42.VR,VHIA,O6.)(?.$42.VR,VHIA,Vh,))(6.(7.$5.(10.$42.VR,VHIA,O6.)(10.$42.VR,VHIA,Vh,))(6.Pmo,$14.(15.(16.$42.VR,VHIA,O6.R1.)(16.$42.VR,VHIA,Vh,R1.))(6.(7.$5.(11.$42.VR,VHIA,O6.)(11.$42.VR,VHIA,Vh,))(6.(7.$5.(12.$42.VR,VHIA,O6.)(12.$42.VR,VHIA,Vh,))(6.(7.$5.(13.$42.VR,VHIA,O6.)(13.$42.VR,VHIA,Vh,))(6.(6.(24.(33.(18.&40.Vsp,)+70.)O7.)(24.O7.(33.(18.&40.Vsp,)+60.)))(6.(7.$5.(32.O7.+20.)=)(6.(25.$42.O4.O8.(19.$26.(27.O3.)(19.$26.(27.O2.)(19.$26.(27.O1.)(1=.$26.)))))(6.(25.$42.O4.(1<.(43.O8.+3.)(44.(21.VR,)))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.=))(1=.$26.))))))))))))))))))(6.(46.(>.$42.VR,VHIA,Vh,)O8.+80.)(6.(7.$5.(32.O8.+20.)=)(6.(23.=O8.)(6.(24.(1<.O8.+80.)O7.)(6.(3<.(39.VR,)(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.O8.+80.)VLF,)))(37.VR,)(?.$42.VR,VHIA,Vh,)O8.+18.)(6.(3<.(39.VR,)(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.O8.+80.)VLF,)))(37.VR,)(?.$42.VR,VHIA,Vh,)(1<.O8.+20.)+58.)(6.Px,$5.P,(6.(24.O8.R1.)(23.R1.(1<.O8.+80.)))(31.(6.(24.(37.VR,)R2.)(23.R2.(?.$42.VR,VHIA,Vh,)))(47.(19.(1:.$5.$5.)(1;.$5.$5.O8.+80.)VLF,)R2.))(6.Pb,$2:.P,(48.$2:.R1.(3:.$2:.VLB,(3;.VLF,)))(48.$2:.R2.(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.O8.+80.)VLF,))))(6.(31.(24.(1<.O8.+80.)VPP,)(24.(1<.VPP,+8.)O8.))(6.(31.(24.(1<.O8.+80.)VKU,)(24.(1<.VKU,+4.)O8.))(6.(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.O8.+80.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))O8.)))(6.(1?.$42.O4.Vlo,O7.)(6.(24.Vlo,(33.O7.+10.))(6.(24.(1<.O8.+80.)(37.VR,))(6.(1?.$42.O4.O7.(1<.(18.&40.Vsp,)-58.))(6.(25.$42.O4.(1<.(18.&40.Vsp,)-58.)(19.$26.(27.Vs9,)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.)))))))))))))(6.(2>.$42.O4.VBUF,Vbs,)(6.(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)O4.VPP,+8.)(6.(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)O4.VKU,+4.)(6.(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)O4.VBUF,(2?.(2=.(2.&8.)Vbs,)))(6.(1>.$42.O4.)(6.(49.$42.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VKU,(1<.VKU,+4.))(1=.(1:.$5.$5.))))O5.O4.)(6.(4:.VR,VLB,VLF,)(6.(4;.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VKU,(1<.VKU,+4.))(1=.(1:.$5.$5.))))O8.+80.)(6.(4<.VR,VLB,VLF,(18.&40.Vsp,)(10.$42.VR,VHIA,Vh,)O8.+80.)(6.(20.$42.(21.VR,)O4.Vslo,O7.)(6.(20.$42.(21.VR,)O4.O7.(18.&40.Vsp,))(6.(4=.VR,VLB,VLF,O8.+80.)(7.$5.(32.O8.+40.)=)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac fctx_open D :=
    destruct D as (HH & ECS & ETOP & ESTK & HKI & EFLAG & EVOL & EFR & SP1 & SP1M & FH & FSH & CFB & FBAL & FB0 & FBS1
                   & FWH & FWD & FWS & SUBLF & AP1 & AP2 & AP4 & ST1 & SLO16 & SEPF & STK2 & SPILL & HBUF & OPP & OKU & OBUF & MI & PRES & WL & WCF & SFF
                   & SS1 & SS2 & FRSH & F64).
  (* [comment removed for export] *)
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  (* [comment removed for export] *)
  Ltac fctx_build :=
    lazymatch goal with |- fctx _ _ _ _ _ _ _ _ => idtac end;
    unfold fctx; spine; first [ eassumption | match goal with |- ?g => idtac "FCTX-LEFT:" g end ].

  Ltac fin_postA PRES :=
    apply evtA_done; unfold x509_ku_postA;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    [ lazymatch goal with |- HM _ _ _ _ _ _ _ => eassumption end | ..];
    (lazymatch goal with
     | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
     | _ => idtac end);
    (lazymatch goal with
     | |- presA _ _ _ _ _ _ _ _ _ _ => eapply presW_presA; exact PRES
     | |- rw_cells _ _ _ _ => idtac
     | |- forall mo, HK _ _ _ _ mo <-> _ =>
         first [ assumption
               | let mo' := fresh "mo" in intros mo';
                 repeat (eapply iff_trans; [ match goal with H : forall mo, HK _ _ _ _ mo <-> _ |- _ => apply H end | ]);
                 apply iff_refl ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01_0@D10592386202.167D10651570095.164D14207581283.164D2457697676.167 D29569067328.167D32458983511.167D32604263317.168D33572813991.165D3375868588.166 D36156712764.165D45717324573.166D46805315402.164D50466429785.165D53314967871.167D60098777666.165D60098975310.164D60109265000.167D60109265003.166D62011770188.166D62011770190.168D62011770191.167D62022258533.165D62022716265.164D6912107242.166 L13312155929.198L13424450173.148L1685717371.0   L18376345509.223L19546883928.148L20630677035.202L22372406257.202L24131365014.142L2438021207.2   L28641830579.2  L30218446521.222L30469992692.202L39268637205.0  L39332637397.0  L39540652971.1  L40027115473.5  L40100639701.0  L42411609006.0  L43889706745.152L48119718063.143L50542531495.2  L50790731766.8  L5162232212.2   L51878069071.2  L52511154273.3  L54479684273.150L57570196295.2  L61490559858.202L62018535662.1  L66232301891.3  L66571867724.8  L67028235242.10 L6912107233.142 L9877309020.8   P5152549648.213 P57577290179.214Q10523111605.175Q10592386192.174Q10651763882.178Q10651763890.171Q12658527488.180Q21721340009.175Q23925414032.182Q23927511196.175Q24131365014.176Q24131365019.173Q24133462168.181Q26030354684.212Q26032252593.185Q2759623548.172 Q30223088053.174Q30886270280.212Q32681887705.175Q33194651973.180Q33585395341.179Q33587492489.172Q34964698202.212Q34966725143.185Q35653441506.163Q36117321936.171Q38250992819.183Q4110986150.211 Q42439443119.212Q42441479395.187Q4279611329.212 Q43878048879.183Q46805771343.178Q46805771351.171Q47230721776.175Q50479010163.179Q50481107319.172Q52735241561.212Q54406581373.172Q5935758158.212 Q59865321072.212Q59867617340.187Q60109315147.163Q60740903729.171Q62009673032.182Q62011770180.175Q64133651577.212Q6910010095.181 Q6912107233.176 Q6912107244.173 Q7917062806.175 Q8699115497.212 Q8701272485.187 00000D00X00Y00Z00n01B01_02302402502I02]03103203O03l04I04f05<05R05h06>06T06h07A08F08G08b09g0:80:I0:P0:Q0:R0:f0:o0;00;10;50;J0;K0;L0;g0<?0<@0<Q0<R0<S0<T0<g0<h0=10=40=50=F0=_0=f0>B0>C0>D0>M0>T0>[0>b0>j0>k0?70?O0?V0?]0?d0@70@E0@F0@M0@Y0@Z0@b0@i0A00AF0AW0B20B30B:0BC0BW0Bf0Bo0C90C@0CG0CQ0CX0C_0Ck0D50D>0D?0D@0DM0DW0D]0Dc0Dl0E30E:0EA0EO0F80F\S2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp1FFS2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp1S1R3HIA2sp2PP2KU2bs2FB3sp12h1S2sp2PP2KU2bs2FB3sp1FFS2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp1FS1R2sp2PP2KU2lo2bs3LOS2FB3sp1S1R2sp2PP2KU2lo2bs3LOS2FB3sp1S1R2sp2PP2KU2lo2bs3LOS2FB3sp1S1R2sp2PP2KU2lo2bs3LOS2FB3sp1S1R2sp2PP2KU2bs2FB3sp1S1R2sp2PP2KU2bs2FB3sp1S1R2sp2PP2KU2bs2FB3sp1S1R2sp2PP2KU2bs2FB3sp1S1R2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp1S2sp2PP2KU2bs2FB3sp11p2PBS1R2sp2PP2KU2lo2bs3PPB3KUB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRSS2sp2PP2KU2lo2bs3SLO2FB3sp1S1R2sp2PP2KU2lo2bs3PPB3KUB3LOS2FB3sp14SP1M4FBAL3FB05SLO163ALO3ACV3SPRS1P3END2bs2p'3PPES1P3END2bs2p'3PPES2bs2FBFFS2sp2PP2KU2bs2FB3sp1S2bs1r2RRSSS2FBS2sp2lo3sp13SP15SLO16SSS1R3slo2bs4SLOS2FB3sp14SEPFS1R2sp2lo2bs3SLO3LOS3ALOFS1R2sp2lo3SLO3LOSFFFS2sp2bs2FB3sp14FBS1FS2bs1r2RRS1RFS1R2sp2lo3SLO3LOSS1R2sp2lo3SLO3LOS3sp13SP1S2bs2FBS2sp2lo3slo3SLO4SLOL3sp13SP1FFS1R2sp2bsS2bs2FBS2PP2bsS2PP2bsS3BUF2bsFS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2bs2FBS2bs2FBS2bs2FBS2sp2lo2bs3sp11p2PBS2sp2lo2bs3sp1FS2bs2FBS2bs2FB1p2PBFS3BUF2bsS2KU2bsS2KU2bsS2lo2bs3sp15SLO161p2PBS2lo2bs3sp15SLO16S1R3HIA1h2sp2lo2bs3TOP4HTOPFS2lo2bsS2bs1p2PBS1R3slo2bs4SLOS1p2PBS1R3slo2bs4SLOSS2bs1p2PBS2sp2lo2bsS2PP2bsS2PP2bsS1R2bs3ALOS2KU2bsS2KU2bsS2bs2FB1p2PBS2PP2KU2bsS2bs1p2PBFFS1R2lo2bs3LOSS2PP2KU2bsS1R2bsS1R2bsS2bs1p2PBS2bs2FBS2bs2FBS2bs2FBS1R2bs2FB4SEPFS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP1p2PBS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$42.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps9v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pj0,(2.&40.)Pr,$5.Pp',$5.Pv,(2.&40.)P,(4>.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)P,(25.$42.R1=.R20.(19.$26.(27.R5.)(1=.$26.)))P,(25.$42.R1>.VPP,(19.$26.(27.(22.&40.R4.))(1=.$26.)))P,(25.$42.R1?.VKU,(19.$26.(28.R4.)(1=.$26.)))P,(6.(24.VP,R6.)(24.R6.VEND,))P,(6.(23.-3000.R8.)(24.R8.=))(3?.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)(40.$42.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VKU,VP,VEND,Vlo,Vslo,R23.)(8.(9.R1>.(22.&40.R25.)Vgp,Vtp,R1=.R1<.R1;.Vsp,(22.&40.R25.)(22.&40.R9.)R1:.R19.R18.R17.R16.R15.R14.(22.&40.R26.)R13.R12.R11.R10.(22.&40.(1<.(43.R26.+3.)(44.(21.VR,))))(22.&40.R26.)R?.Vs10,Vs11,R>.R=.R<.R;.)VF,(22.&40.+:>:98.)Vfc,(;.(2.&40.))R22.(<.$42.)))")
(* [comment removed for export] *).
  Proof.
  intros until v.
  intros D SLOT0 HPP HKU PPE RR.
  fctx_open D.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xaeafc] [] 201%N). lx_tree.
  lxr_leaf. lx_carry.
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH5 end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  match goal with H : HM _ _ _ h1 LB _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h1 LB ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h2 & ROp & [old Hold] & CRp & NCp & KUp & HM2 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff2).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 128) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
  pose proof (nc_apart _ _ _ _ _ p PP 8 NCp CR1 SUB' LOS ltac:(clear; lia)) as NP1.
  pose proof (nc_apart _ _ _ _ _ p KU 4 NCp CR2 SUB' LOS ltac:(clear; lia)) as NP2.
  pose proof (nc_apart0 _ _ _ _ _ p BUF _ NCp CR4 SUB' LOS) as NP4.
  assert (NP5 : bv_unsigned sp + -88 + 88 <= p \/ p + 1 <= bv_unsigned sp + -88).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 8 <= p \/ p + 1 <= sp1).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp : wcover R LB LF (bv_unsigned sp) W p 1)
  by (eapply wcover_nc; [exact NCp| exact SUB'| clear - LOS SLO; lia]).
  rewrite ECS in CRp.
  clear HHe NCp KUp.
  (* [comment removed for export] *)
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM2.
  rewrite Z.eqb_refl in HM2.
  try (match goal with H : stk _ mf sp1 (bv_unsigned sp + -88) |- _ =>
        pose proof (stk_merge asegs mf lo sp1 _ ST1 H ltac:(clear - SP1 SLO16; lia)) as ST3; clear ST1 H end).
  try (match goal with H : rw_cells _ mf (bv_unsigned sp + -88) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
  assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)) by (eapply sshad_merge; [exact SS1| exact SS2| clear - SP1 SLOL SLO SLO16; lia]).
  lxr_stk_join. fin_postA PRES.
  all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0160@D31446675440.174D60109196847.174D61361298780.174D61720250755.174D62011970312.174K14102786961.174K44164039966.174K55850470009.174K63377080840.174L12163493815.162L14098457330.2  L14945499794.161L1685717371.0   L25810914902.173L28250535790.172L33809058945.172L34603895532.0  L38841996942.172L44168742175.3  L49432666050.163L53165657809.162L55345854604.159L55347554147.156L55837970831.2  L56078322866.2  L57892315391.158L62908422684.160L62909071722.158L63373022059.2  L64346457091.172P56076488309.174Q12757461271.168Q13337805592.170Q15930096381.168Q20743605642.172Q20880934901.168Q20883032012.172Q23212956655.170Q26030354684.174Q26295627581.172Q2960920480.171 Q29850408660.168Q31448688112.173Q32681824661.174Q32740602521.172Q34964698202.174Q35653441506.164Q36351088906.165Q40014758561.172Q40015103616.165Q40016855704.168Q42439443119.174Q43610542095.165Q47702638815.172Q50466311024.170Q50466478964.173Q50466906018.170Q51545819658.174Q55510299987.173Q56841782051.172Q56843879194.168Q59865321072.174Q60109315147.164Q61722493827.173Q63532090309.172Q63534187516.168Q67802285815.172Q68390477037.168Q8699115497.174 Q8945570120.170 00000e01c01d02Y03P04>04m05\06W07407507607707Z08D08j08k09Q09R0:_0;<0<`0>D0>E0>F0?_0@E0@k0@l0Be0Ch0DJ0DZ0Dg0EI0EJ0EK0E[0FM0FZ0G10G@0Gh0HS0Hc0IX0JA0Jc0K90KO0Ke0LX0Le0M90MI0MY0Mi0Mj0N:0N;0N<0N=0NS0O;0O<0O=0OZ0P:0QG0QTS2sp2PP2KU2bs1k3rem3acc2sh2FB3sp12Hk1b2HB5Ha_st5Hl_stS1R2sp2PP2KU2lo2bs3LOS1k3rem3acc2sh2FB3sp12Hk1b2HB5Ha_st5Hl_stFS2sp2PP2KU2bs1k3rem3acc2sh2FB3sp12Hk1b2HB5Ha_st5Hl_stS1R2sp2PP2KU2bs1k3rem3acc2sh2FB3sp12Hk1b2HB5Ha_st5Hl_stS2PP2KU2bs2D11k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stS2KU3BUF2bs2D51k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stS2KU2bs1k3rem3acc2sh2FB2Hk1b3AP22HB5Ha_st5Hl_stS2sp2KU2lo2bs3SLO3DS21k3rem3acc2sh2Hk4Hrem1b2HB5Ha_st5Hl_stS2sp2PP2KU2bs1k3rem2FB3sp12HkFFSS2sp2PP2KU3BUF2bs1k3rem1c2FB3sp12HkS2sp2PP2KU2bs1k3rem2sh2FB3sp12Hk4Hrem1b2KLS2sp2PP2KU3END2bs1k3rem1c2FB3sp12Hk2HESS2sp2PP2KU3BUF2bs1k3rem1c2FB3sp12Hk2HcFS2sp2PP2KU3END3BUF2bs2B32B43PPB3KUB4BUF01k3rem1c2FB3sp12Hk4Hrem2Hc2HE3FB03SPRS2sp2PP2KU2bs1k3rem2FB3sp12HkS1R2sp2PP2KU3END3BUF2lo2bs2B32B43PPB3KUB4BUF03LOS1k3rem1c2FB3sp12Hk4Hrem2Hc2HE3FB05SLO163ALO3ACV3SPRS1R2sp2PP2KU3END3BUF2lo2bs2B32B43PPB3KUB4BUF03LOS1k3rem1c2FB3sp12Hk4Hrem2Hc2HE3FB05SLO163ALO3ACV3SPRFFS1R2sp2PP2KU3END3BUF2lo2bs2B33PPB3KUB3LOS1k3rem1c2FB3sp12Hk4Hrem2HE3FB05SLO163ALO3ACV3SPRS2sp2PP2KU3BUF2bs1k3rem1c2FB3sp12Hk2HcS2sp2PP2KU3BUF2bs1k3rem1c2FB3sp12Hk2HcFS1R2sp2PP2KU3END3BUF2lo2bs2B32D12D42D53PPB3KUB3SLO3LOS3DS13DS23DS41k3rem1c2FB3sp12Hk4Hrem2Hc2HE3SP13FB05SLO163ALO3ACV3SPRS2sp2KU2lo2bs3SLO3DS21k3rem3acc2sh3sp12Hk4Hrem3SP11b2HB5Ha_st5Hl_stS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HES2KU2bs1k3rem2HkS2bs1k3rem2HkS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HEFFS2KU2bs1k3rem2HkS2sp2KU2lo2bs1k3rem3acc2sh3sp12Hk1b2HB5Ha_st5Hl_stS2bs1k3rem2HkS2KU2bs3KUB1k3rem2Hk2HBS2bs1k3rem1c2HkS2KU2bs1k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stS2PP2KU2bs1k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stS2KU2bs1k3rem2HkS2KU2lo2bs1k3rem3acc2sh3sp12Hk1b5SLO162HB5Ha_st5Hl_stS1R3HIA1h2sp2lo2bs3TOP1k3rem2Hk4Hrem4HTOPS3END3BUF2bs2B31k3rem1c2Hk4Hrem2HES3BUF2bs1k3rem1c2Hk2HcS3BUF2bs1k3rem1c2Hk2HcS3BUF2bs1k3rem1c2Hk2HcS1R2KU3slo2bs4SLOS1k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stS2bs1k3rem2HkS2KU2bs3KUB1k3rem2HkS2KU2bs1k3rem2HkS2KU2bs1k3rem2HkS2KU2bs1k3rem2HkFS2KU2bs1k3rem2HkFFFS1R2lo2bs3LOS1k3rem2HkS2KU2bs1k3rem3acc2sh2Hk1b2HB5Ha_st5Hl_stFFS2KU2bs3KUB1k3rem2Hk2HB5Ha_stS3BUF2bs4BUF01k3rem1c2Hk4Hrem2HcS1R3HIA1h2sp2KU3slo2bs3TOP1k3rem3acc2sh3sp12Hk4Hrem1b3SP14HTOP2HB5Ha_st5Hl_stS2bs1k3rem2Hk". (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "Pk,$4?.Prem,$5.Pc,$5.Premw,(2.&40.)Pacc,(2.&40.)Psh,(2.&40.)Pv,(2.&40.)PFB,$5.Psp1,$5.Ph1,(4.$42.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px17,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pj0,(2.&40.)Pp',$5.P,(7.$4?.(50.R1<.)R1=.)P,(24.+1.R1=.)P,(24.VBUF,R1=.)P,(24.(1<.R1>.R1?.)VEND,)P,(7.(2.&40.)R1>.(22.&40.R20.))P,(4>.R1;.R1:.R19.R18.R17.R16.R15.R14.)P,(25.$42.R18.R1;.(19.$26.(27.R8.)(1=.$26.)))P,(25.$42.R19.VPP,(19.$26.(27.(22.&40.R8.))(1=.$26.)))P,(25.$42.R1:.VKU,(19.$26.(28.R1?.)(1=.$26.)))P,(6.(24.VP,R:.)(24.R:.VEND,))(3?.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)(40.$42.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VKU,VP,VEND,Vlo,Vslo,R1=.)(8.(9.R18.(22.&40.R1?.)Vgp,Vtp,R17.R16.R15.Vsp,(22.&40.R1?.)(22.&40.R25.)(22.&40.(1<.(43.VKU,+3.)(44.(21.VR,))))R24.R22.R23.(22.&40.R25.)(22.&40.(1<.(51.VKU,+7.)+3.))R14.(22.&40.R20.)(22.&40.VKU,)R13.R12.R11.(22.&40.(1<.(43.R20.+3.)(44.(21.VR,))))(22.&40.R20.)(22.&40.(44.(21.VR,)))Vs10,Vs11,R10.R?.R>.R=.)VF,(22.&40.+:>:3<.)Vfc,(;.(2.&40.))R1<.(<.$42.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros rem c remw acc sh v FB sp1 h1 m0 mm w0 w1 w2 xra x5 x6 x7 x17 s4v s5v s6v x28 x29 x30 x31 j0 p'
                                   Hk Hrem Hc HE -> D SLOT0 HPP HKU PPE; [lia|].
    pose proof D as D0. fctx_open D.
    rt_facts.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP. rewrite ETOP, ESTK in HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_chk OBUF c 1.
    (* [comment removed for export] *)
    get_byte bs (c - BUF) b NB. read_at HBUF NB (c - BUF) RDb.
    shadow_byte OKU KU 4 as k4 RD4 HK4.
    zstep. clear RD4. zstep. clear RDb. zstep.
    shadow_merge_regs1 KU k4 HK4 5.
    (* [comment removed for export] *)
    do 7 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      eapply (IH (rem - 1) (c + 1)); first [ fctx_build | eassumption | reflexivity | lia | (f_equal; lia)
                                           | match goal with |- ?g => idtac "LOOP-IH-LEFT:" g end ].
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. zstep.
      eapply epi_walk with (r := 0); first [ fctx_build | eassumption | clear; lia | exact PPE
                                           | match goal with |- ?g => idtac "LOOP-END-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D10592385689.193D10592386202.172D10649662601.169D14209288005.169D2457697676.172 D29569067328.172D32458983511.172D32458985044.193D32604263317.173D33572813991.170D3375868588.171 D36156712764.170D45717324573.171D46807815276.169D50466429785.170D50480159773.193D53314967871.172D60096736616.169D60098777666.170D60109265000.172D60109265003.171D62010102746.193D62011769676.193D62011770188.171D62011770190.173D62011770191.172D62022258533.170D62024413263.169D6912107242.171 L13424450173.146L13631919790.208L19546883928.146L20596944330.208L20596944330.212L20596944330.213L24131365014.140L34866092019.264L34866092019.274L34866092019.276L36974783927.213L38502229919.213L43889706745.150L48119718063.141L54342432968.213L54479684273.148L60191618956.208L60191618956.212L60191618956.213L63641984554.208L68463460114.213L6912107233.140 L8945588633.213 Q10523111605.180Q10592386192.179Q10651763882.183Q10651763890.176Q12658527488.185Q21721340009.180Q23925414032.187Q23927511196.180Q24131365014.181Q24131365019.178Q24133462168.186Q26032252593.190Q2759623548.177 Q30223088053.179Q32681887705.180Q33194651973.185Q33585395341.184Q33587492489.177Q34966725143.190Q35653441506.162Q36117321936.176Q38250992819.188Q42441479395.192Q43878048879.188Q46805771343.183Q46805771351.176Q47230721776.180Q50479010163.184Q50481107319.177Q54406581373.177Q59867617340.192Q60109315147.162Q60740903729.176Q62009673032.187Q62011770180.180Q6910010095.186 Q6912107233.181 Q6912107244.178 Q7917062806.180 Q8701272485.192 00000K00f01A01B01C01^02902T03803S03T03U04004K04f04g04h05L06006T07807S08008M08j09G09d0:A0:\0;f0<K0=U0><0>c0?J0?X0@30@N0@i0AN0Ba0CC0Cb0ED0E^0FG0G00GY0H>0I\0Ij0JE0JU0Jc0K10K?0KN0KO0Kb0LA0LO0L]0Lk0M@0MA0MO0MP0M_0Mm0N;0NS0Nn0No0O=0OS0Od0P20P@0PQ0P_0Pm0Q>0Q?0QL0Q]0Qj0R70RE0RS0Ra0S60SaS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLFFS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS1R3HIA2sp2PP2KU2bs2FB3sp12h13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLFFS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLFFS1R2sp2PP2KU2lo2bs3LOS2FB3sp13jbs2JLS1R2sp2PP2KU2lo2bs3LOS2FB3sp13jbs2JLS1R2sp2PP2KU2lo2bs3LOS2FB3sp13jbs2JLS1R2sp2PP2KU2lo2bs3LOS2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2PP2KU2lo2bs3PPB3KUB3LOS2FB3sp13jbs4SP1M4FBAL3FB05SLO163ALO3SPR2JL1HS2sp2PP2KU2bs2FB3sp13jbs2JL5lxv143H37S1R2sp2PP2KU2lo2bs3PPB3KUB3LOS2FB3sp13jbs4SP1M4FBAL3FB05SLO163ALO3SPR2JL1HS2sp2PP2KU1P2bs2FB3sp13jbs2JL5lxv153H35S2sp2PP2KU1P2bs2FB3sp13jbs2JL5lxv153H38S2sp2PP2KU1P2bs2FB3sp13jbs2JL5lxv153H39S2bs2FB3jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JL5lxv163H24S1R2sp2PP2KU1P3BUF2lo2bs2B13PPB3KUB3LOS2FB3sp13jbs3FB05SLO163ALO3SPR2JL1H5lxv183H31S1R3slo2bs4SLOS2FB3sp13jbs4SEPF2JLS1R2sp2lo2bs3SLO3LOS3jbs3ALO2JLS1R2sp2PP2KU3END2lo2bs3PPB3KUB3LOS2FB3sp13jbs3FB05SLO163ALO3SPR2JL1H5lxv155lxv165lxv183H233H303H38S2sp2bs2FB3sp13jbs4FBS12JLS2sp2PP2KU3END2bs2FB3sp13jbs2JL5lxv153H34S2sp2PP2KU3END2bs2FB3sp13jbs2JL5lxv153H37S2sp2PP2KU3END2bs2FB3sp13jbs2JL5lxv153H38S2sp2PP2KU2bs2FB3sp13jbs2JL5lxv143H23S1R2sp2PP2KU3END2lo2bs3PPB3KUB3LOS2FB3sp13jbs3FB05SLO163ALO3SPR2JL1H5lxv155lxv165lxv183H303H38S2bs2FB3jbs2JLS2sp2PP2KU2bs2FB3sp13jbs2JLS1R2sp2bs3jbs2JLS2bs2FB3jbs2JLS2PP2bs3jbs2JLS2PP2bs3jbs2JLS3BUF2bs3jbs2JLFS1R3HIA1h2bs3jbs2JLS1R3HIA1h2sp2bs3TOP3jbs4HTOP2JLS2bs2FB3jbs2JLS2bs2FB3jbs2JLS2bs2FB3jbs2JLS2sp2lo2bs3sp13jbs2JLFS2bs2FB3jbs2JLFS3BUF2bs3jbs2JLS2KU2bs3jbs2JLS2KU2bs3jbs2JLS2lo2bs3sp13jbs5SLO162JLS1R3HIA1h2sp2lo2bs3TOP4HTOPFS2lo2bs3jbs2JLS1R3slo2bs4SLOS3jbs2JLS2sp2lo2bs3jbs2JLS2PP2bs3jbs2JLS2PP2bs3jbs2JLS1R2bs3jbs3ALO2JLS2KU2bs3jbs2JLS2KU2bs3jbs2JLS2PP2KU2bs3jbs2JLFS1R2lo2bs3LOSS2PP2KU2bs3jbs2JLS1R2bs3jbs2JLS1R2bs3jbs2JLS2bs2FB3jbs2JLS2bs2FB3jbs2JLS2bs2FB3jbs2JLS1R2bs2FB3jbs4SEPF2JLS1R3HIA1h2sp3slo2bs3TOP3sp13jbs3SP14HTOP2JL". (* [comment removed for export] *)
  Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage_A ()) "PFB,$5.Psp1,$5.Ph1,(4.$42.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Ps5v,(2.&40.)Ps7v,(2.&40.)Pjunk1,(29.(2.&8.))Pjbs,(29.(2.&8.))Pjunk2,(29.(2.&8.))Pj3,(29.(2.&8.))Pj4,(29.(2.&8.))Pj0,(2.&40.)Pv0,(2.&40.)P,(=.$42.VR,VHIA,R1;.VLB,(19.(1:.$5.$5.)(1;.$5.$5.R1=.+80.)VLF,)R19.)P,(7.P,$5.Sp(>.$42.VR,VHIA,R1<.)(>.$42.VR,VHIA,Vh,))P,(7.$5.(?.$42.VR,VHIA,R1=.)(?.$42.VR,VHIA,Vh,))P,(7.$5.(10.$42.VR,VHIA,R1>.)(10.$42.VR,VHIA,Vh,))P,Pmo,$14.(15.(16.$42.VR,VHIA,R20.R1.)(16.$42.VR,VHIA,Vh,R1.))P,(7.$5.(11.$42.VR,VHIA,R20.)(11.$42.VR,VHIA,Vh,))P,(7.$5.(12.$42.VR,VHIA,R21.)(12.$42.VR,VHIA,Vh,))P,(7.$5.(13.$42.VR,VHIA,R22.)(13.$42.VR,VHIA,Vh,))P,(6.(24.(33.(18.&40.Vsp,)+70.)R24.)(24.R24.(33.(18.&40.Vsp,)+60.)))P,(7.$5.(32.R25.+20.)=)P,(25.$42.R23.R27.(19.$26.(52.#18.R11.)(1=.$26.)))P,(25.$42.R24.(1<.R28.+18.)(19.$26.(52.#8.R?.)(1=.$26.)))P,(25.$42.R25.(1<.R29.+20.)(19.$26.(52.#18.R12.)(1=.$26.)))P,(25.$42.R26.(1<.R2:.+38.)(19.$26.(52.#40.R12.)(1=.$26.)))P,(25.$42.R27.(1<.R2;.+78.)(19.$26.(52.#8.R11.)(1=.$26.)))P,(25.$42.R28.(1<.(43.R2<.+3.)(44.(21.VR,)))(53.#10.))P,(46.(>.$42.VR,VHIA,Vh,)R2=.+80.)P,(7.$5.(32.R2>.+20.)=)P,(23.=R2?.)P,(24.(1<.R30.+80.)R2?.)P,(3<.(39.VR,)(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.R31.+80.)VLF,)))(37.VR,)(?.$42.VR,VHIA,Vh,)R31.+18.)P,(3<.(39.VR,)(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.R32.+80.)VLF,)))(37.VR,)(?.$42.VR,VHIA,Vh,)(1<.R32.+20.)+58.)P,Px,$5.P,(6.(24.R34.R1.)(23.R1.(1<.R34.+80.)))(31.(6.(24.(37.VR,)R2.)(23.R2.(?.$42.VR,VHIA,Vh,)))(47.(19.(1:.$5.$5.)(1;.$5.$5.R35.+80.)VLF,)R2.))P,Pb,$2:.P,(48.$2:.R1.(3:.$2:.VLB,(3;.VLF,)))(48.$2:.R2.(3:.$2:.VLB,(3;.(19.(1:.$5.$5.)(1;.$5.$5.R36.+80.)VLF,))))P,(31.(24.(1<.R35.+80.)VPP,)(24.(1<.VPP,+8.)R35.))P,(31.(24.(1<.R36.+80.)VKU,)(24.(1<.VKU,+4.)R36.))P,(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.R37.+80.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))R37.)))P,(1?.$42.R34.Vlo,R37.)P,(24.Vlo,(33.R38.+10.))P,(24.(1<.R3:.+80.)(37.VR,))P,(1?.$42.R37.R3:.(1<.(18.&40.Vsp,)-58.))P,(25.$42.R38.R3;.(19.$26.(27.R21.)(1=.$26.)))P,(25.$42.R39.(1<.(18.&40.Vsp,)-58.)(19.$26.(27.Vs9,)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.)))))))))))))P,(25.$42.R3:.VPP,(19.$26.(27.(22.&40.VP,))(1=.$26.)))P,(25.$42.R3;.VKU,(19.$26.(28.R23.)(1=.$26.)))P,(2>.$42.R3<.VBUF,Vbs,)P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R3=.VPP,+8.)P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R3>.VKU,+4.)P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R3?.VBUF,(2?.(2=.(2.&8.)Vbs,)))P,(1>.$42.R40.)P,(49.$42.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VKU,(1<.VKU,+4.))(1=.(1:.$5.$5.))))R42.R41.)P,(4:.VR,VLB,VLF,)P,(4;.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VKU,(1<.VKU,+4.))(1=.(1:.$5.$5.))))R47.+80.)P,(4<.VR,VLB,VLF,(18.&40.Vsp,)(10.$42.VR,VHIA,Vh,)R48.+80.)P,(20.$42.(21.VR,)R45.Vslo,R48.)P,(20.$42.(21.VR,)R46.R49.(18.&40.Vsp,))P,(4=.VR,VLB,VLF,R4;.+80.)P,(7.$5.(32.R4<.+40.)=)(3?.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)(40.$42.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VKU,VP,VEND,Vlo,Vslo,R4:.)(8.(9.(22.&40.+:>924.)(22.&40.R4<.)Vgp,Vtp,R48.R47.R46.Vsp,(22.&40.R4<.)R45.R44.R43.R42.R41.R40.R3?.R3>.(22.&40.R4=.)(22.&40.VKU,)(22.&40.VEND,)R39.(22.&40.VPP,)R38.(22.&40.R4=.)(22.&40.(44.(21.VR,)))Vs10,Vs11,R3=.R3<.R3;.R3:.)VF,(22.&40.+:>95<.)Vfc,(;.(2.&40.))R49.(<.$42.)))")
(* [comment removed for export] *).
  Proof.
  intros until v0.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 BSL FD2 G2 FSH CFB FBAL FB0 FBS1 FWH FWD FWS SUBLF AP1 AP2 AP4
  ST1 SLO16 SEPF STK2 SLOT0 SPILL HPP HKU HBUF OPP OKU OBUF MI PRES WL WCF SFF SS1 SS2 FRSH F64.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB _ _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  assert (JL : length jbs = 24%nat) by (destruct BSL as [[WF _] _]; cbn in WF; destruct WF as [WF _]; exact WF).
  cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_pre. lxr_path. lxr_abase. lxr_pose.
  (* [comment removed for export] *)
  lxa_auto [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_amemset0A 24 lxbs0 4; SUM_bitstring0A] [FB + 32].
  lx_pre. lx_run_tac (PLANS [0x0aea3c; 0x0aea98] [(0xaea0c, DJoin); (0xaea48, DJoin); (0xaea54, DJoin)] 201%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_amemset0A 24 lxbs0 4; SUM_bitstring0A]). lx_tree. all: lxa_unglob.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaea3c) _ _ _ (seg_rom _)] => lxr_leaf; lx_apply loop_walk | |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0xaea98) _ _ _ (seg_rom _)] => lxr_leaf; lx_apply epi_walk | |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx BODY: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
