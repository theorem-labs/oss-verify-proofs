(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P006944cbbd2243a3 1 1 16 2 0 1 95 1 4 25 1 68 1 96 1 97 16P0106327fb4f07fc4 0 2 0 1 5 1P010db0e1931c3408 1 1 16 3 0 1 99 1 100 1 4 68 1 98 1 101 1 102 16P013e10613dcb4b82 0 4 0 1 91 1 99 1 100 1P015a8d65d17231d8 1 1 32 3 0 1 93 1 96 1 4 67 1 94 1 95 1 97 32P016f6b0b8a5ebbf0 1 1 8 2 0 1 104 1 3 26 1 105 1 106 8P026a0cb0733dab3c 1 1 8 3 0 1 97 1 100 1 5 2 2 70 2 98 2 99 2 101 16P02b4f02cf3557f47 1 1 16 3 0 1 97 1 98 1 5 46 1 70 1 96 1 99 1 100 16P02d6e3ecaa0a7e13 0 2 0 1 2 1P035f26c0a13ebbc8 1 1 16 3 0 1 100 1 101 1 4 46 1 99 1 102 1 103 16P038c7160cce423c2 0 4 0 1 91 1 99 1 100 1P0416ca13ea8a3a8a 0 3 0 1 9 1 66 1P0509001fa370d9f0 1 1 16 3 0 1 100 1 101 1 4 46 1 99 1 102 1 103 16P05c314c25495e833 1 1 16 3 0 1 94 1 95 1 5 44 1 67 1 93 1 96 1 97 16P05eb66be58c0ee5e 0 4 0 1 91 1 99 1 100 1P064d7a6263c7853a 0 5 0 1 47 1 91 1 99 1 100 1P0669f3aff9b8924d 2 119 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8P06ae8a4199ae6dda 1 1 8 2 42 1 96 1 3 0 1 95 1 97 8P0757ee9a9e29ae6f 1 1 32 3 0 1 99 1 102 1 4 73 1 100 1 101 1 103 32P078e393ef979e12f 0 2 0 1 90 1P07d81867c1baf541 0 7 0 1 45 1 57 1 67 1 82 1 95 1 96 1P0832a79b8d354fc4 0 4 0 16 68 16 95 16 96 16P089c4ea0a582a8d4 1 1 16 3 0 1 100 1 101 1 4 35 1 99 1 102 1 103 16P0a1c54db98a132de 0 4 0 1 91 1 99 1 100 1P0a82a9f351150ccb 0 7 0 1 45 1 67 1 80 1 82 1 95 1 96 1P0c16e7247ce00892 1 1 16 3 0 1 100 1 101 1 4 46 1 99 1 102 1 103 16P0c1edba1125b9e7b 0 6 0 1 2 1 85 1 86 1 99 1 100 1P0c688667ed1ce086 0 6 0 1 1 1 46 1 68 1 96 1 97 1P0c8f2c5e8732b936 1 1 16 3 0 1 97 1 100 1 5 2 1 71 1 98 1 99 1 101 16P0cb641230ebc39ea 0 4 0 1 91 1 99 1 100 1P0d03515ef79f6c86 2 104 1 1 8 3 1 1 107 1 108 1 5 0 2 98 2 106 2 109 2 110 16 1 1 8 3 2 1 106 1 109 1 4 0 2 107 2 108 2 110 16P0d0ab8f1dc1daff9 1 1 32 3 0 1 98 1 101 1 4 70 1 99 1 100 1 102 32P0e3e72dcdd0e9608 0 4 0 16 68 16 95 16 96 16P0e87a0adce795731 1 1 16 3 1 1 97 1 100 1 5 2 1 71 1 98 1 99 1 101 16P0ea85c5f178ca1c7 1 1 32 3 0 1 95 1 98 1 4 69 1 96 1 97 1 99 32P0f324ec6755132fc 2 119 2 105 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8 2 105 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8P10d5a710f0bdc4cc 0 4 1 1 3 1 98 1 99 1P11bc966e5aab2810 0 5 0 1 46 1 90 1 98 1 99 1P1291b406d5e199de 0 4 0 8 52 8 104 8 105 8P13598ec4eadd63a4 1 1 16 3 1 1 97 1 100 1 5 2 1 71 1 98 1 99 1 101 16P137285dfd7495e38 0 4 0 8 52 8 104 8 105 8P141cec2bc639bda9 1 1 8 2 0 1 104 1 3 25 1 105 1 106 8P1461716618c15085 0 4 0 16 68 16 95 16 96 16P146f242ce97d3a57 1 1 8 3 1 1 97 1 100 1 5 2 2 70 2 98 2 99 2 101 16P1474ff631c062d37 0 6 0 1 3 1 48 1 70 1 98 1 99 1P1551be1b0bbf4755 0 4 0 8 50 8 104 8 105 8P1565330bfd0e8ac3 0 2 2 1 4 1P1579b9e055d8f511 0 2 0 1 2 1P1649e20c5e25a5ed 0 4 0 1 91 1 99 1 100 1P16aa783086fd9434 0 2 2 1 4 1P16aea5d52c923f2a 1 1 8 3 1 1 98 1 99 1 6 2 2 47 2 69 2 97 2 100 2 101 16P17626585091f511c 0 4 0 1 91 1 99 1 100 1P17900de88685467f 0 4 0 1 91 1 99 1 100 1P186c4ad957ea4efd 1 1 16 3 0 1 94 1 95 1 5 44 1 67 1 93 1 96 1 97 16P18ee4707d786f19b 0 4 0 1 91 1 99 1 100 1P19e8c809c0c554b9 0 4 0 1 90 1 98 1 99 1P1a72d61303371e4b 0 2 0 1 88 1P1b0fa8e1c3cbfc3a 0 2 0 1 91 1P1b34d9a480c9bc86 1 1 16 3 0 1 93 1 94 1 4 43 1 92 1 95 1 96 16P1ba5c4a46fc5a3bd 0 4 0 1 91 1 99 1 100 1P1bcd8d927a361e0e 0 2 0 1 67 1P1d0983f0be2df30a 1 1 32 3 0 1 93 1 96 1 4 67 1 94 1 95 1 97 32P1d8b68c4dacaabc1 2 104 1 1 8 3 1 1 107 1 108 1 5 0 2 98 2 106 2 109 2 110 16 1 1 8 3 2 1 106 1 109 1 4 0 2 107 2 108 2 110 16P1e1e456fc0b8e26f 1 1 32 3 0 1 96 1 99 1 4 70 1 97 1 98 1 100 32P1e52c533fd12d23a 0 4 1 1 3 1 98 1 99 1P1e7aaa494d8e3ee1 0 6 0 1 68 1 83 1 84 1 95 1 96 1P1eba99a24d8a1699 1 1 8 3 1 1 98 1 101 1 4 2 1 97 1 102 1 103 8P1ecd162f65ac6aa3 1 2 32 2 0 1 92 1 32 2 67 1 93 1 2 94 1 95 1P1f122f1c59003111 0 4 0 1 2 1 99 1 100 1P1f7158be0cb975ef 1 1 16 3 1 1 97 1 100 1 7 2 1 70 1 85 1 86 1 98 1 99 1 101 16P1ff48463545b3f27 1 1 16 3 0 1 99 1 100 1 4 45 1 98 1 101 1 102 16P20520e12ddd64675 1 1 16 3 0 1 94 1 95 1 5 44 1 67 1 93 1 96 1 97 16P212495e4a87770a7 1 1 8 3 1 1 98 1 99 1 5 2 1 47 1 97 1 100 1 101 8P2177d838f7473139 1 1 16 3 0 1 97 1 98 1 4 68 1 96 1 99 1 100 16P21d97fbea18c2138 0 2 1 1 2 1P22a0528b5818d3dc 0 4 0 1 84 1 92 1 93 1P22aa7c40ec361605 0 4 0 1 3 1 98 1 99 1P22b3583d09802529 1 1 16 3 0 1 96 1 97 1 5 45 1 67 1 95 1 98 1 99 16P231eedde382ae84a 0 4 0 1 3 1 98 1 99 1P235ed581dda1dd7c 2 104 1 1 8 3 1 1 107 1 108 1 5 0 2 98 2 106 2 109 2 110 16 1 1 8 3 2 1 106 1 109 1 4 0 2 107 2 108 2 110 16P23fdc888bc298746 2 119 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8P2472dc0a6d0e3fc8 1 1 16 3 0 1 97 1 98 1 5 46 1 68 1 96 1 99 1 100 16P2477f68387f934f7 0 2 0 1 89 1P24b22d20f3d26601 0 4 0 1 91 1 99 1 100 1P254277a6971804b8 0 2 1 1 2 1P25779ab116269601 0 5 0 1 45 1 66 1 72 1 84 1P25e98ec9d83fa8ce 0 4 0 1 91 1 99 1 100 1P26c9753d6a3aafeb 0 2 0 1 2 1P26ec1daa14a1b012 0 4 0 1 91 1 99 1 100 1P2728c2498ad911bb 0 2 0 1 2 1P2779e733a497e5cf 0 7 0 16 45 16 69 16 95 16 96 16 97 16 98 16P27a61be348eafc7c 0 2 0 1 5 1P27c40ba9eea26598 1 1 8 3 0 1 98 1 99 1 5 2 2 89 2 97 2 100 2 101 16P28d22131f678b18f 1 1 8 2 0 1 104 1 3 25 1 105 1 106 8P296ebe6cf33bd23d 1 1 8 3 1 1 97 1 100 1 4 2 1 98 1 99 1 101 8P2a50fa0096293439 0 5 0 16 20 16 67 16 95 16 96 16P2abb12b98d249a20 0 4 0 1 1 1 96 1 97 1P2ae0811467e81851 1 1 8 3 0 1 98 1 99 1 4 2 1 97 1 100 1 101 8P2c29b9265dd56e97 0 5 0 1 47 1 91 1 99 1 100 1P2c60165c9f5eb7f4 1 1 32 2 70 1 96 1 3 0 1 95 1 97 32P2ca7c335e3936c3b 0 2 2 1 4 1P2cd8765cb64e7aab 0 6 0 16 67 16 95 16 96 16 97 16 98 16P2cf689e2dfdd8af3 1 1 8 3 0 1 99 1 102 1 8 2 64 48 64 89 64 97 64 98 64 100 64 101 64 103 512P2d8d223b832c2f9b 0 5 0 1 36 1 91 1 99 1 100 1P2dc82203e7263ad9 0 4 0 1 1 1 96 1 97 1P2f319ee303278aab 0 7 0 16 45 16 67 16 95 16 96 16 97 16 98 16P2f9faabb70ea96be 1 1 32 3 0 1 93 1 96 1 4 67 1 94 1 95 1 97 32P2fd4715128b545a3 0 4 0 1 91 1 99 1 100 1P3004590dd3ad3621 1 1 8 3 0 1 98 1 99 1 6 2 1 47 1 69 1 97 1 100 1 101 8P30f05aef4c72ebfa 2 119 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8 2 104 1 1 8 3 2 1 107 1 110 1 6 0 4 58 4 99 4 108 4 109 4 111 32 1 1 8 3 3 1 108 1 109 1 5 0 1 57 1 107 1 110 1 111 8P312af3e50253050c 1 1 16 3 0 1 94 1 95 1 5 44 1 67 1 93 1 96 1 97 16P316e9eb9db3494ce 0 7 0 16 45 16 69 16 95 16 96 16 97 16 98 16P31d4d062d87571dc 0 2 0 1 1 1P31f522f65402d718 0 2 0 1 67 1P324f89edbd75476c 0 4 0 1 91 1 99 1 100 1P32c52a125db85da3 1 1 8 3 0 1 97 1 100 1 6 2 1 48 1 89 1 98 1 99 1 101 8P34594905c2e3a951 1 1 16 3 1 1 97 1 100 1 7 2 1 70 1 85 1 86 1 98 1 99 1 101 16P347bb6da3bf3c279 0 2 0 1 1 1P35167ecaf8d6a58a 1 1 8 3 1 1 98 1 99 1 6 2 1 47 1 69 1 97 1 100 1 101 8P354500f89bc5968b 0 2 0 1 5 1P354d8b8b02a3b5e8 2 105 1 1 8 3 1 1 107 1 108 1 5 0 2 98 2 106 2 109 2 110 16 1 1 8 3 2 1 106 1 109 1 4 0 2 107 2 108 2 110 16P359851b36d93702e 1 1 16 3 0 1 100 1 101 1 5 46 1 73 1 99 1 102 1 103 16P35a31e1a08f3fae6 0 4 0 1 91 1 99 1 100 1P35bf9a5eb006e8df 0 2 0 1 67 1P372d792c618b8058 0 4 0 32 7 32 92 32 93 32P37a0c5e8786e3939 0 4 0 1 91 1 99 1 100 1P382697919bdf425a 1 1 32 3 0 1 93 1 96 1 4 67 1 94 1 95 1 97 32P3864a4ffbf35b663 0 5 1 16 3 16 71 16 98 16 99 16P389160271c889a7a 0 4 0 1 91 1 99 1 100 1P3935ccc90503b4d2 0 5 0 16 1 16 69 16 96 16 97 16P3950744396242c2b 0 2 0 1 92 1P39944470fadb554e 0 4 0 1 91 1 99 1 100 1P39cf283de2eb512f 0 4 0 1 91 1 99 1 100 1P3a5146021fe1c800 0 4 0 1 91 1 99 1 100 1P3a7822a954dc76b7 0 4 0 8 52 8 104 8 105 8P3a9dc68b99cb071e 0 5 0 1 44 1 84 1 92 1 93 1P3add4b4d7b86783b 0 2 0 1 2 1P3afbea27206537d1 0 2 0 1 6 1P3b8e43006baa96a6 1 1 8 2 0 1 104 1 3 25 1 105 1 106 8P3c2174578698e7c5 0 7 0 16 45 16 67 16 95 16 96 16 97 16 98 16P3e811a706070e38c 0 4 0 1 91 1 99 1 100 1P3efdf81ebe9080a2 1 1 8 3 1 1 97 1 100 1 4 2 2 98 2 99 2 101 16N000f1086fac53d76N001c40d6e65efa16N003b3e824fd7abc6N0091269482aa7f24N016d37435b200727N01ebf8de1b431d01N023c579aaa4938dfN0248999f7e9ff51aN025c10814f279ce8N02b6b4794406e8d2N030a930304fc2125N04297af1d07d9916N048edba855e078d6N04ea849bffbc079bN05c953bd6429fa63N05d81483537945a7N05ed23bbe7b4ac02N06d86b569b3a10dcN06db2c5e8b81a46dN0702cf8bf424707cN0739fc758795619bN078abda0d589e10eN07c281c2a4ecb170N07c76d23e8ab2eaaN07dc7483b04b9e27N07dd4f9e4d3d2320N080fc9614026988aN082c81cf2c0ebb08N086a082fee07be18N08a0605caf5ac007N08b2b9fb6dc38c51N08cdec0e0bb8327aN094842c775878a5cN09bffdaa2468ab94N09c8cbba36422241N09d69d40e4b8386cN09d892b3d32beccfN0a19f71039beb443N0aa49b90bdafda0cN0aef9a39013c447eN0af13607e82bf1edN0b23bce9c62c230eN0b457a9e2f40f78cN0bf9b118072cf107N0c190e5b19abe184N0c2e4a3fb671cf11N0c67bf90b72ef94aN0cb73c78a833cb7dN0cba2c617f359486N0cd9173560bd33bcN0cf6e69d155691feN0d1f88ae07f5c852N0d54f7ae0eac39e7N0e8a359630de97b8N0eae29888a1bb03fN0ec08c1f7f1cced1N0f04eed903c7325eN0f0b5d3641a4297bN0f22178db453725eN0f371206c26a521bN0f6d91ed55d49cb1N0f8008333ce06c68N0fddddd56e5fbccdN0ff7441b9164ee4bN103ad415f708d4daN10c69a8cdf000846N10cc7e10b62770e6N10ce2135519ed63aN11b07d9bf317b9f2N11ccd51256673ad4N11e8a26b2443fae0N1211168b8b9360f4N122064b9b8df285cN1232f7f759808b5dN123fafbfb1825f90N12a068d1876f3b91N134a92b555fd6062N13ad77174662ff02N140ef2357aecf3b4N14a1712a1aaa0fbeN14a17729a9666d03N152d4523f2723c05N153ccb9f1592458dN1583c8ec68cfd68aN159023125624312eN15b39a16756eae78N15f98d1967814437N15fea5c8c65e10bcN16b81e8704b94fb8N16be10fe66fab69bN16c45004681118dcN16de45f8083cecebN170ac86d4cebead6N175d8e2283191fb6N17abc4f20afaec9cN17ed7d5f770ea512N1854d0fc72d01698N196e787262b5715fN199f18722e351256N19bb0548d4119a60N19d804362c73ddddN19e229686fd0d12bN19ec58762728c3b1N1a08ebd07c3d8a38N1ad3e5aad0ca6a76N1b4b9eb42492f60bN1b512447c7520377N1c8a24297c4f306bN1ccbc0d372b0abf0N1cf50a89c0b933c1N1d04bbe8695b9c6aN1d53d41cd55e4eeaN1da68af7c3322fc1N1dafe0ef7b00cb2fN1df1badf3bf295bdN1dfe9798e070672fN1e37204e39e6c120N1edcacd62f778928N1f7ab37c82245706N1ff175ff3567642aN20019092ef280363N20a4f4f20696b3ddN20bdc75bde54814dN20c08a6af6dc8ee7N20dfc8ce3001e9f2N20f2b2dad5cc3220N21153e296dfdb5fdN213db01407f1cd3dN218d295259bb747cN21d785a83bcbffa0N21ef90590b8e6f73N2238e7adee6e43a5N22f02c626007c126N22fc8eaab20aadc1N22fcdd9ab69273adN23386aa1b95cc459N234d389c2552698cN23531332867b52ceN23735205a0029359N23989800bd67c9d7N23fb6ac71a1e489fN246bd094ba351035N247d7033a27bd8caN2502e675b81ba59cN2518faeb8d224f58N25a4663a5efce09eN25be138a3a079635N25dc316cd4ebd71cN26383ed8c1187b2cN272954ed15d56c7fN278fef595d66210aN27d982f38ff4ac7fN28df0a7d11f745f2N292a815f1b5d077fN295dbc35671207e8N29ad959c0d6e07a4N29c24a1aa40c6ad5N29e09167ae370fcbN29e1745accd266dcN29fb04d2b2647203N2a0fa03a7c793dacN2a2b7ed44b27aeb6N2b6c73746410ffa6N2b8fd26bb1fda351N2bb3bdbcf4237440N2bf1665fe4aec618N2c300b86361145c1N2c43bc969dda6ddeN2cfaafc04053d49aN2d3a38037ff7a58eN2d46bcfb5ca2075fN2d4fd77359b78b30N2d519c1a51dbc738N2d561e66ab5e380fN2d65ea2d8b19bebdN2d9dc94224c024c6N2de2a79ba5ae0718N2e17fbaaf4828bb2N2e60f8cfbce5570fN2e68f062d12c68ffN2f0ed0cc24483f4fN2f1afd4037ea5751N2f25913ca38437f2N2f6926107a2a9d46N2f9665d6042a9ecaN2f9df987a24a675fN2fb8600a766a510cN2fc0c596d2eaf53cN3038c21ee32728f3N30b6cfffbf91f952N30fb0fdec29f6d73N30fb3de62937b6a8N311be063679f077eN31711b2f6111bd32N31a27506ff9a6a8cN31dd4172a33313b9N31ddf7c0081fceeeN31f76eeae156661aN3229da1676f0076cN3262223e59ad42a8N326360b4b3c21c98N32d2fb0b4f5030d7N32da590476f0287eN32ec88824a8ab605N32fb5d14c292c51bN3312211feef4faa8N33a1976f59f5f45dN33c1c9f9fcd2ebf4N33cc7595308dded4N33cdd9e249d60f51N33f742d7e6dbd9bbN34219adfd9b9b859N345615e85a79fb5cN345a44df3d25b5dfN347cc0d4f4920316N352bcdd8ea0046c6N3593d101c06a4008N35a5aa210d68b7f3N35f52b42f5730edcN361383960a7eb16fN3625bc65b2402cb8N379b82f88cf6ec61N37b12487177afb2dN382e5f2ae67d6828N38a8f60e012bef65N38ae059199d3da76N38dc39c595cbe76aN394df9d219bdd258N394ff76cce913963N39d2c0f2451c4e48N3a51315ddb93b898N3a88af8efd3ff8c3N3ac4ec3124f9af51N3b5aedb832690302N3b6e4aedb69c5ae9N3b829e923d78aa3cN3bcf9c0f36fb3cfeN3c36ea6ae06d8adeN3c683c1c0c597b4dN3c6ea7f636111e7aN3c814bc5f8d8d0dfN3c9a65d947a63090N3ca5fb814780f649N3cdc060163a776b1N3d63a559acf820b7N3f4ab0b09080cf18N3f7d9273bc3085d9N3fb0787480933229N3fd8ca6d658b7682"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_getsig_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "PKCS7_GETSIG_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "pkcs7_getsig_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wlow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "Walk.PATH"].


Definition A_PKCS7_GETSIG : Z := 0x099474.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PKCS7_GETSIG_STACK_A : Z := 4208.

Definition pkcs7_getsig_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SIGB P END lo slo : Z) (pad : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig_A ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.O20.O1?.O1>.)Lh',(4.O20.O1?.O1>.)(1.$5.Lr,$5.(1.$5.Lp',$5.(1.(2.&40.)Ltg,(2.&40.)(1.$5.Llen,$5.(1.$5.Lq,$5.(6.(7.$0.R17.(8.(9.O1:.O19.O18.O17.R16.R15.R14.O16.O15.R13.R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(:.O1:.)O9.(;.(2.&40.))R7.(<.O20.)))(6.(=.O20.O1?.O1>.R6.O1<.O1;.R7.)(6.(7.P,$5.Sp(>.O20.O1?.O1>.R6.)(>.O20.O1?.O1>.O1=.))(6.(7.$5.(?.O20.O1?.O1>.R6.)(?.O20.O1?.O1>.O1=.))(6.(7.$5.(10.O20.O1?.O1>.R6.)(10.O20.O1?.O1>.O1=.))(6.(7.$5.(11.O20.O1?.O1>.R6.)(11.O20.O1?.O1>.O1=.))(6.(7.$5.(12.O20.O1?.O1>.R6.)(12.O20.O1?.O1>.O1=.))(6.(7.$5.(13.O20.O1?.O1>.R6.)(13.O20.O1?.O1>.O1=.))(6.Pmo,$14.(15.(16.O20.O1?.O1>.R7.R1.)(16.O20.O1?.O1>.O1=.R1.))(6.(17.O20.O1?.O1<.O1;.(18.&40.O19.)(18.&40.O19.)(10.O20.O1?.O1>.O1=.)(19.(1:.$5.$5.)(1;.$5.$5.O8.(1<.O8.+8.))(19.(1:.$5.$5.)(1;.$5.$5.O7.(1<.O7.+18.))(1=.(1:.$5.$5.))))O1.R7.)(6.(1>.O20.R7.)(6.(1?.O20.R7.O4.(18.&40.O19.))(6.(20.O20.(21.O1?.)R7.O3.(18.&40.O19.))(6.(7.(2.&40.)R13.(22.&40.R5.))(6.(6.(23.-7?.R5.)(24.R5.=))(6.(25.O20.R7.O8.(19.$26.(27.(22.&40.R4.))(1=.$26.)))(6.(25.O20.R7.O7.(28.R3.O2.R2.R1.))(6.(6.(24.O6.R4.)(24.R4.O5.))P,(7.$5.R5.=)(6.(7.(2.&40.)R4.(22.&40.+4.))(6.(24.(1<.O6.+2.)R2.)(6.(24.=R3.)(7.$5.(1<.R2.R3.)R5.))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pkcs7_getsig_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig_A ()) "Ph,(4.O4.O3.O2.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$5.PSIGB,$5.PP,$5.PEND,$5.PBUF,$5.Plo,$5.Pslo,$5.Pbs,(29.(2.&8.))Ptg0,(2.&40.)Ppad,(2.&40.)Plen0,$5.Pq0,$5.P,(=.O4.O3.O2.R31.R30.R2?.R=.)P,(2<.(2=.$2:.R30.)#200.)P,(25.O4.R?.R>.(19.$26.(27.(22.&40.R<.))(1=.$26.)))P,(25.O4.R10.R>.(28.R7.R6.R5.R4.))P,(2>.O4.R11.R<.R9.)P,(24.R=.R?.)P,(24.R10.R?.)P,(24.R10.(1<.R?.(2?.(2=.(2.&8.)R<.))))P,(23.(1<.R10.(2?.(2=.(2.&8.)R=.)))(30.+2.+3?.))P,(31.(24.(1<.R15.+8.)R14.)(24.(1<.R14.+18.)R15.))P,(31.(7.$5.(2?.(2=.(2.&8.)R?.))=)(31.(24.(1<.R16.+8.)R12.)(24.(1<.R12.(2?.(2=.(2.&8.)R?.)))R16.)))P,(31.(7.$5.(2?.(2=.(2.&8.)R10.))=)(31.(24.(1<.R16.+18.)R13.)(24.(1<.R13.(2?.(2=.(2.&8.)R10.)))R16.)))P,(7.$5.(32.R18.+8.)=)P,(7.$5.(32.R18.+8.)=)P,(6.(23.=R1:.)(24.(1<.R1:.+8.)(30.+2.+40.)))P,(6.(23.=R1:.)(24.(1<.R1:.+18.)(30.+2.+40.)))P,(23.=R18.)P,(1?.O4.R1>.R18.(18.&40.R3>.))P,(20.O4.(21.O3.)R1?.R18.(18.&40.R3?.))P,(24.R1:.(33.(18.&40.R40.)$34.))P,(24.R1;.(33.(33.(18.&40.R41.)+70.)(35.O3.)))P,(24.=(35.O3.))P,(24.(36.O3.)R1<.)P,(24.R1=.R1>.)P,(7.$5.(32.(18.&40.R45.)+10.)=)P,(24.(18.&40.R46.)(?.O4.O3.O2.R4:.))P,(24.(18.&40.R47.)(30.+2.+2?.))P,(31.(24.(1<.R27.+8.)R22.)(24.(18.&40.R48.)R27.))P,(31.(24.(1<.R27.+18.)R23.)(24.(18.&40.R49.)R27.))P,(31.(7.$5.(2?.(2=.(2.&8.)R22.))=)(31.(24.(1<.R25.(2?.(2=.(2.&8.)R22.)))R24.)(24.(18.&40.R4:.)R25.)))P,(37.(38.O3.)(39.$2:.R4>.(3:.R4=.))R25.R2:.+8.)P,(37.(38.O3.)(39.$2:.R4?.(3:.R4>.))R26.R2:.+18.)P,(37.(38.O3.)(39.$2:.R50.(3:.R4?.))R27.R28.(2?.(2=.(2.&8.)R25.)))P,(3;.(38.O3.)(39.$2:.R51.(3:.R50.))R28.(?.O4.O3.O2.R52.)R2=.+8.)P,(3;.(38.O3.)(39.$2:.R52.(3:.R51.))R29.(?.O4.O3.O2.R53.)R2=.+18.)P,(1>.O4.R30.)P,(7.(2.&40.)R4?.(22.&40.(3<.O3.)))P,(3=.O4.(21.O3.)(>.O4.O3.O2.R56.)R32.R31.+8.)P,(3=.O4.(21.O3.)(>.O4.O3.O2.R57.)R33.R31.+18.)P,(3=.O4.(21.O3.)(>.O4.O3.O2.R58.)R34.R2?.(2?.(2=.(2.&8.)R2<.)))P,(7.(2.&40.)R4=.(22.&40.R34.))P,(7.(2.&40.)R4=.(22.&40.R32.))P,(7.(2.&40.)R4=.(22.&40.R35.))(3>.O4.(21.O3.)(>.O4.O3.O2.R5<.)(3?.O4.O3.O2.R5<.R5;.R5:.R59.R58.R57.R56.R52.R51.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3:.R39.R37.R36.R35.R34.R32.R31.R2>.R38.)(8.(9.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.)R3:.(22.&40.O1.)R39.(;.(2.&40.))R38.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
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
            (PP SIGB P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SIGB \/ SIGB + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ SIGB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SIGB.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SIGB mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SGB : 0 < SIGB /\ SIGB + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - PKCS7_GETSIG_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SIGB + 24 <= lo \/ bv_unsigned sp <= SIGB.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo SIGB 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIGB 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold PKCS7_GETSIG_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (pkcs7_getsig_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SIGB P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (SIGB, SIGB + 24)].

  Definition PATH (FB spv s2v sp1 : Z) (LF' : list blk) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig_A ()) "(31.(6.(7.$5.O3.=)(6.(7.(29.$2:.)O1.VLF,)(6.(7.$5.O4.O5.)(7.$5.O2.(1<.O5.+40.)))))(6.(7.$5.O3.O5.)(6.(7.(29.$2:.)O1.(19.(1:.$5.$5.)(1;.$5.$5.O5.+40.)VLF,))(6.(7.$5.O4.O2.)(6.(40.VR,VLB,VLF,O5.+40.)(7.$5.(32.O5.+40.)=))))))")
(* [comment removed for export] *).

  Ltac fin_postA PRES :=
    apply evtA_done; unfold pkcs7_getsig_postA;
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
     | |- _ = 0 -> _ => first [ assumption | intros _ ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  Definition epi_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig_A ()) "PFB,$5.Pspv,$5.Ps2v,$5.Psp1,$5.PLF',(29.$2:.)Ph1,(4.$41.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Plw,(2.&40.)Pjunk3,(29.(2.&8.))Pj3,(29.(2.&8.))Pj4,(29.(2.&8.))Pjsp,(2.&40.)Pr,$5.Pp',$5.Ptg,(2.&40.)Plen,$5.Pq,$5.P,(=.$41.VR,VHIA,R24.VLB,R25.R22.)P,(7.P,$5.Sp(>.$41.VR,VHIA,R25.)(>.$41.VR,VHIA,Vh,))P,(7.$5.(?.$41.VR,VHIA,R26.)(?.$41.VR,VHIA,Vh,))P,(7.$5.(10.$41.VR,VHIA,R27.)(10.$41.VR,VHIA,Vh,))P,Pmo,$14.(15.(16.$41.VR,VHIA,R29.R1.)(16.$41.VR,VHIA,Vh,R1.))P,(7.$5.(11.$41.VR,VHIA,R29.)(11.$41.VR,VHIA,Vh,))P,(7.$5.(12.$41.VR,VHIA,R2:.)(12.$41.VR,VHIA,Vh,))P,(7.$5.(13.$41.VR,VHIA,R2;.)(13.$41.VR,VHIA,Vh,))P,(6.(24.(33.(18.&40.Vsp,)+70.)R2>.)(24.R2>.(33.(18.&40.Vsp,)+60.)))P,(7.$5.(32.R2?.+20.)=)P,(25.$41.R2<.R33.(19.$26.(27.R17.)(19.$26.(27.R16.)(19.$26.(27.R15.)(1=.$26.)))))P,(25.$41.R2=.(1<.R34.+18.)(19.$26.(42.#8.R13.)(1=.$26.)))P,(25.$41.R2>.(1<.R35.+20.)(19.$26.(27.R16.)(1=.$26.)))P,(25.$41.R2?.(1<.R36.+28.)(19.$26.(42.#10.R16.)(1=.$26.)))P,(25.$41.R30.(1<.R37.+38.)(19.$26.(42.#8.R15.)(1=.$26.)))P,(25.$41.R31.(1<.(43.R38.+3.)(44.(21.VR,)))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.+?1.))(19.$26.(45.(22.&8.=))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(19.$26.(45.(22.&8.+?3.))(1=.$26.))))))))))P,(46.(>.$41.VR,VHIA,Vh,)R39.+40.)P,(7.$5.(32.R3:.+20.)=)P,(23.=R3;.)P,(24.(1<.R3<.+40.)R39.)P,(3;.(38.VR,)(39.$2:.VLB,(3:.R39.))(36.VR,)(?.$41.VR,VHIA,Vh,)R3=.+18.)P,(3;.(38.VR,)(39.$2:.VLB,(3:.R3:.))(36.VR,)(?.$41.VR,VHIA,Vh,)(1<.R3>.+20.)+18.)P,Px,$5.P,(6.(24.R40.R1.)(23.R1.(1<.R40.+40.)))(31.(6.(24.(36.VR,)R2.)(23.R2.(?.$41.VR,VHIA,Vh,)))(47.R3=.R2.))P,(31.(24.(1<.R40.+40.)VPP,)(24.(1<.VPP,+8.)R40.))P,(31.(24.(1<.R41.+40.)VSIGB,)(24.(1<.VSIGB,+18.)R41.))P,(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.R42.+40.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))R42.)))P,(1?.$41.R3<.Vlo,R42.)P,(24.Vlo,(33.R43.+10.))P,(24.R44.R42.)P,(31.(24.(1<.R46.+40.)(36.VR,))(7.$5.R45.R46.))P,(1?.$41.R40.R44.(1<.(18.&40.Vsp,)-50.))P,(25.$41.R41.(1<.R45.+8.)(19.$26.(27.R25.)(1=.$26.)))P,(25.$41.R42.(1<.(18.&40.Vsp,)-50.)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.))))))))))))P,(25.$41.R43.VPP,(19.$26.(27.(22.&40.R25.))(1=.$26.)))P,(25.$41.R44.VSIGB,(28.R25.Vpad,R24.R23.))P,(2>.$41.R45.VBUF,Vbs,)P,(6.(24.VP,R28.)(24.R28.VEND,))P,P,(7.$5.R2:.=)(6.(7.(2.&40.)R29.(22.&40.+4.))(6.(24.(1<.VP,+2.)R27.)(6.(24.=R28.)(7.$5.(1<.R27.R28.)R2:.))))P,(6.(23.-7?.R2;.)(24.R2;.=))P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R49.VPP,+8.)P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R4:.VSIGB,+18.)P,(3=.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)R4;.VBUF,(2?.(2=.(2.&8.)Vbs,)))P,(48.$41.(21.VR,)R4<.)P,(1>.$41.R4=.)P,(49.$41.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSIGB,(1<.VSIGB,+18.))(1=.(1:.$5.$5.))))R4?.R4>.)P,(4:.VR,VLB,VLF,)P,(4;.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VSIGB,(1<.VSIGB,+18.))(1=.(1:.$5.$5.))))R57.+40.)P,(4<.VR,VLB,VLF,(18.&40.Vsp,)(10.$41.VR,VHIA,Vh,)R58.+40.)P,(20.$41.(21.VR,)R52.Vslo,R58.)P,(20.$41.(21.VR,)R53.R57.(18.&40.Vsp,))P,(4=.R5;.R5:.R59.R58.R57.)(3>.$41.(21.VR,)(>.$41.VR,VHIA,Vh,)(3?.$41.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSIGB,VP,VEND,Vlo,Vslo,Vpad,R56.)(8.(9.R54.(22.&40.R5;.)Vgp,Vtp,R53.R52.R51.Vsp,(22.&40.R59.)(22.&40.R38.)R4?.R4>.R4=.R4<.R4;.R4:.R49.(22.&40.R5:.)R47.R48.R46.(22.&40.R5<.)(22.&40.(1<.(43.R5<.+3.)(44.(21.VR,))))R45.Vs9,Vs10,Vs11,R44.R43.R42.R41.)VF,(22.&40.+99624.)Vfc,(;.(2.&40.))R55.(<.$41.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02W0@D10598676144.187D14209286862.186D2459793318.187 D28642551204.186D3166451853.186 D31813559522.186D32452690557.187D32604263319.188D3388365348.186 D36119473504.186D45704737685.186D50143412074.187D53304480533.187D53743892199.186D60096735459.186D60098777666.187D62011770188.188D62022258533.187D62024414660.186D6899602018.186 L11868706321.213L13950455336.183L13950455460.211L15032546978.131L16197048706.134L16578761643.1  L1685717371.0   L16940174169.4  L17519266672.4  L17605293695.156L19546883930.156L19546999407.2  L20385569831.2  L20630677035.211L20630677159.183L2114001099.209 L21224591641.211L22372406141.183L22372406257.211L2333531081.143 L2333536794.143 L2339825649.138 L23665996118.3  L24387678245.243L26205700811.212L27116614917.131L28641830579.2  L30812544425.161L30814759948.161L31168734356.151L32722070143.214L33991810708.2  L34673318544.135L36299009017.136L36567293259.1  L39076636629.0  L39269760500.1  L39332637397.0  L39972639317.0  L4103369558.134 L4103370461.136 L4109651564.135 L4109651564.137 L42411609006.0  L43202358963.159L44067824659.2  L44857558292.2  L45053222038.213L48117620903.152L50790731766.8  L50876585809.5  L51767926.212   L51878069071.2  L52511154273.3  L53276290430.136L53528496537.210L53574471957.131L54009221120.133L54510159614.8  L55715474836.2  L56602807449.211L57570196295.2  L58797718987.210L59308636694.1  L59308636694.8  L59504824377.242L60544121036.8  L61490559858.211L61490559998.183L62018535662.1  L6203796531.137 L6377280537.209 L64186534961.133L64556264702.134L64824766027.211L66232301891.3  L66696405579.1  L66730930849.10 L66834449300.168L68040139772.2  L6899602796.134 L6899603304.134 L6912107235.151 L8285450102.135 L8287545983.136 L9395668121.208 L9631865259.133 L9631865646.132 L9631865646.133 L9633866540.2   L9877309020.8   P34003033104.235P36561248207.232P44846860176.236P55705235216.233P57577290179.234P66702450895.231Q10523111611.195Q10592386206.194Q10651763882.198Q10651763890.191Q12658527490.200Q23218748859.194Q23925414038.202Q23927511186.195Q26030354684.230Q26032252607.205Q31168734356.196Q31168734361.193Q31170831518.201Q31826220143.192Q32681887703.195Q33194651975.200Q33423269192.234Q34964698202.230Q34966725145.205Q35653441506.175Q36117321936.191Q36613016452.207Q38250992817.203Q4110986150.233 Q42439443119.230Q42441479405.207Q4279611329.230 Q43878048877.203Q4587995481.234 Q46805771343.198Q46805771351.191Q47230721790.195Q5935758158.230 Q59865321072.230Q59867617330.207Q59932040161.199Q59932040175.192Q60109315147.175Q60740903729.191Q62009673038.202Q62011770186.195Q62950270614.199Q62950270616.192Q64133651577.234Q6910010089.201 Q6912107235.196 Q6912107246.193 Q7166002686.192 Q7917062808.195 Q8699115497.230 00000F00G00H00I00J00K00a01@01A01B01X01n01o02002O02n03F03^04604L04o05805A05E05L05P05Q05\05k07408=08F08G08X08i09K09i0::0:K0:L0:M0:N0:W0;70;Y0;`0;a0<:0<;0<B0>60>70>>0>I0>J0>K0>O0>P0>Q0>R0>S0?00?M0?N0?a0?b0?c0@E0@]0@n0AC0A\0A]0A^0Ai0BB0BI0BP0Bk0Bl0CE0CF0Ch0Cl0DK0Dd0E50E>0EG0EJ0ER0Ek0F20F90F[0F\0F]0G60G\0G]0Gd0Gk0H20HB0HR0Hk0I60IA0IL0IT0J00J10J20J30J40J50J60J?0JF0JM0JT0J\0Jc0Jo0KG0KZ0Kh0Ko0L60L=0L>0L?0LG0LS0Li0M?0MZ0M[0NF0NM0NV0Nj0O90OB0OL0OX0O_0Of0P00P90P:0P;0PD0PM0PZ0Pf0Pl0Q20Q;0QD0QM0QT0Q[0Qb0Qn0Qo0RXS2sp2PP4SIGB2bs2FB3sp1FFFFFS2sp2PP4SIGB2bs2FB3sp1S1R3HIA2sp2PP4SIGB2bs2FB3sp12h1FFS2sp2PP4SIGB2bs2FB3sp1S2sp2PP4SIGB2bs2FB3sp1FFS1R2sp2PP4SIGB2lo2bs3LOS2FB3sp1S1R2sp2PP4SIGB2lo2bs3LOS2FB3sp1S1R2sp2PP4SIGB2bs2FB3sp1S1R2sp2PP4SIGB2bs2FB3sp1S1R2sp2PP4SIGB2bs2FB3sp1S2sp2PP4SIGB2bs2FB3sp1S2sp2PP4SIGB2bs2FB3sp12p'3len1q3H10S2bs1r2RRS2bs1r2RRS2bsS2bs2FBS2FBSS2sp2FB3SP1S1R2FB3spv4SEPFS1R2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS1R2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACV3SPRS2FB4FBALFS1P3END2bs2p'3PPES1P3END2bs2p'3PPES2sp2PP4SIGB2lo2bs2FB3s2v5SLO162H2S2sp2PP4SIGB2bs2FB3sp12H21p2PBS1P3END2bs2p'3PPES1P3END2bs2p'3PPEFFFS1r2RR2NES2sp2PP4SIGB2lo2bs3SLO2FB3sp12H2S2sp2PP4SIGB2lo2bs2FB3s2v5SLO162H2S2bs2FBFS3slo2bs2FB3spv2H01R4SLOSFS2bs2FBS1R2sp2PP4SIGB1P3END3BUF2lo2bs2B12B22B32D12D42D53PPB3SGB3SLO3LOS3DS13DS23DS42FB3sp12p'3len1q3SP13FB03ALO3ACV3SPR3H10FS2bs2FBS2bs2FB3sp1FSS2FBSSFFS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HSS2sp2bs2FB3sp14FBS1FFS2sp2PP4SIGB2lo2bs2FB3s2v5SLO162H2S1R2sp2lo2bs3SLO3LOS3ALOS1R2sp2lo3SLO3LOSS2sp2lo3sp13SP15SLO16S2sp2PP4SIGB2bs2FB3s2v2H2FFS2bs2FB3sp1S2sp2PP4SIGB2bs2FB3s2v2H2S2bs2FBS2bs2FBS2sp2lo3slo3SLO4SLOL2FB3SP1FS2sp2PP4SIGB2bs2FB3s2v2H2FS2sp2PP4SIGB2lo2bs2FB3s2v5SLO162H2S2KsS2sp2FB3sp13SP13FB04FBS13SPR2KsS2sp2PP4SIGB2bs2FB3sp12H2S1R2sp2lo3SLO3LOSS2bs1r2RRS2bs1r2RRS1RS2bs3sp1S2sp2PP4SIGB2bs2FB3s2v2H2S2bs2FBS2bs2FBS2sp2PP4SIGB2lo2bs2FB3s2v5SLO162H2FFS1R2sp2lo3SLO3LOS3sp13SP1S2sp2PP4SIGB2lo2bs2FB3s2v3SP15SLO162H2FS2bs2FBS2bs2FBS2bs2FBS2bs2FB3sp14FBS1S2bs2FB3sp14FBS1S2sp2PP4SIGB2bs2FB3s2v2H2S2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S2FB3FB0S2sp2lo3slo3SLO4SLOL3sp13SP1FFFFFFS1R2sp2bsS2bs2FBS2PP2bsS2PP2bsS3BUF2bsS2bs2FBS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2sp2lo2bs3sp11p2PBS2sp2lo2bs3sp1S2bs2FBS2bs2FBS2bs2FBFFS3BUF2bsS2bs2FB1p2PBS2lo2bs3sp15SLO161p2PBS2sp2lo2bs3SLO3sp13SP1S1R3HIA1h2sp2lo2bs3TOP4HTOPFS1R3HIA1h2sp3slo2bs3TOP3spv3sp13SP14HTOP2H8S2lo2bsS2bs1p2PBS1R3slo2bs4SLOS1p2PBS1R3slo2bs4SLOSS2bs1p2PBS2sp2lo2bsS2bs2FB1p2PBS2PP2bsS2PP2bsS1R2bs3ALOS2bs1p2PBFFS4SIGB2bsS4SIGB2bsS1R2lo2bs3LOSS2PP4SIGB2bsS1R2bsS1R2bsS4SIGB2bsS4SIGB2bsS2bs1p2PBS2bs2FBS2bs2FBS2bs2FBS2PP4SIGB2bsFS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP1p2PB". (* [comment removed for export] *)
  Lemma epi_walk : epi_stmt.
  Proof.
  unfold epi_stmt.
  intros until q.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 HL FD2 G2 FSH CFB FBAL FB0 FBS1 FWH FWD FWS AP1 AP2 AP4
  ST1 SLO16 SPV1 SEPF STK2 SLOT SPILL HPP HSG HBUF PPE HR0 RR OPP OSG OBUF AB MI PRES WL WCF SFF SS1 SS2 HPATH.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB LF' _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  unfold buf_cells in HSG.
  (* [comment removed for export] *)
  try unfold PATH in *. lxr_path. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x99660] [(0x99638, DSplit)] 167%N). lx_tree.
  { (* [comment removed for export] *)
    lxr_leaf. lx_carry. lx_cond Ks.
    (* [comment removed for export] *)
    destruct HPATH as [(Es2 & ELF & Espv & Esp1)|(Es2 & _)]; [| exfalso; rewrite Es2 in Ks; clear - Ks FB0 FBS1 SP1 SPR; lia].
    subst LF' spv sp1.
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHZ end).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    try (match goal with H : rw_cells _ mf FB _ |- _ => release_frame H ST1 (FB + 24) end).
    try (match goal with H : rw_cells _ mf (FB + 24) _ |- _ => release_frame H ST1 (FB + 32) end).
    try (match goal with H : rw_cells _ mf (FB + 32) _ |- _ => release_frame H ST1 (FB + 40) end).
    try (match goal with H : rw_cells _ mf (FB + 40) _ |- _ => release_frame H ST1 (FB + 56) end).
    try (match goal with H : rw_cells _ mf (FB + 56) _ |- _ => release_frame H ST1 (FB + 64) end).
    try (match goal with H : stk _ mf (FB + 64) (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge asegs mf lo (FB + 64) _ ST1 H ltac:(clear - SP1 FB0 SLO16; lia)) as ST3; clear ST1 H end).
    try (match goal with H : rw_cells _ mf (bv_unsigned sp + -80) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
    assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)).
    { eapply sshad_merge; [exact SS1| | clear - SP1 FB0 SLOL SLO; lia]. eapply sshad_merge; [| exact SS2| clear - SP1 FB0; lia]. eapply (sshad_of_chunk_sh asegs AL mf 8 FB); [exact FSHZ| reflexivity| clear - FBAL; lia| clear - FB0; lia]. }
    lxr_stk_join. fin_postA PRES.
  }
  { (* [comment removed for export] *)
    lxr_leaf. lx_carry. lx_cond Ks.
    (* [comment removed for export] *)
    destruct HPATH as [(Es2 & _)|(Es2 & ELF & Espv & FRSH & F64)]; [exfalso; rewrite Es2 in Ks; clear - Ks; lia|].
    subst LF' spv s2v.
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH5 end).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    match goal with H : HM _ _ _ h1 LB _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h1 LB ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
    as (p & h2 & ROp & [old Hold] & CRp & NCp & NSp & HM2 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff2).
    replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
    clear G1 G2.
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
    clear Hold.
    assert (SUB' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 64) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
    pose proof (nc_apart _ _ _ _ _ p PP 8 NCp CR1 SUB' LOS ltac:(clear; lia)) as NP1.
    pose proof (nc_apart _ _ _ _ _ p SIGB 24 NCp CR2 SUB' LOS ltac:(clear; lia)) as NP2.
    pose proof (nc_apart0 _ _ _ _ _ p BUF _ NCp CR4 SUB' LOS) as NP4.
    assert (NP5 : bv_unsigned sp + -80 + 80 <= p \/ p + 1 <= bv_unsigned sp + -80).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 8 + 8 <= p \/ p + 1 <= sp1 + 8).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp : wcover R LB LF (bv_unsigned sp) W p 1)
    by (eapply wcover_nc; [exact NCp| exact SUB'| clear - LOS SLO; lia]).
    rewrite ECS in CRp.
    clear HHe NCp NSp.
    zstep.
    zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    cbn [lb_remove fst Z.eqb] in HM2.
    rewrite Z.eqb_refl in HM2.
    try (match goal with H : stk _ mf sp1 (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge asegs mf lo sp1 _ ST1 H ltac:(clear - SP1 SLO16; lia)) as ST3; clear ST1 H end).
    try (match goal with H : rw_cells _ mf (bv_unsigned sp + -80) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
    assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)) by (eapply sshad_merge; [exact SS1| exact SS2| clear - SP1 SLOL SLO SLO16; lia]).
    lxr_stk_join. fin_postA PRES.
  }
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac apply_epi := eapply epi_walk; try eassumption; try reflexivity.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@D10592386202.178D10649661698.175D14209286862.175D2457697676.178 D28640501509.176D32458983511.178D32604263317.179D3375868588.177 D45717324573.177D46807814631.175D50132923712.178D53314967871.178D59942523331.176D60096735459.175D60098777666.176D60109265000.178D60109265003.177D62011770188.177D62011770190.179D62011770191.178D62022258533.176D62024414660.175D62960757940.176D6912107242.177 L15036806567.120L15047373953.148L16197048706.123L17519266672.4  L17605293693.148L19546883928.148L23685514924.199L25508944538.199L27112486400.120L27240710106.199L27830338971.202L30812544425.152L30814759948.152L31168734358.142L31567655464.199L32080660980.1  L34671222686.151L34673318544.124L36299009017.125L37663906510.199L39269760500.1  L4103369558.123 L4103370461.125 L4105466835.152 L4105466839.150 L4109651564.124 L4109651564.126 L4109651564.151 L4109651564.153 L43202358961.150L44774792700.199L48119718063.143L48132302231.158L53276290430.125L53570212368.120L54009221120.122L56498654708.1  L59308586248.2  L59314873579.2  L59314873579.3  L59314873579.4  L59314873579.5  L59314873579.7  L59314873579.9  L59314988138.2  L60558678699.1  L6203796531.126 L6203796539.153 L62849479133.198L64186534961.122L64556264702.123L6897506275.151 L6897506281.150 L6899602796.123 L6899603304.123 L6912107233.142 L8285450102.124 L8287545975.152 L8287545983.125 L9631865259.122 L9631865646.121 L9631865646.122 L9633962922.150 L9633962927.149 Q10523111605.186Q10592386192.185Q10596479275.202Q10598676921.209Q10651763882.189Q10651763890.182Q12658527488.191Q19559500513.202Q23204067484.209Q23218748853.185Q23925414032.193Q23927511196.186Q26028057501.211Q26032252593.196Q31168734358.187Q31168734363.184Q31170831512.192Q31826220141.183Q32681887705.186Q33194651973.191Q34966725143.196Q34979309371.211Q35653441506.163Q36117321936.182Q36613016457.210Q36613016458.198Q38250992819.194Q40251617896.202Q42441479392.210Q42441479395.198Q43878048879.194Q46805771343.189Q46805771351.182Q47230721776.186Q59867617340.198Q59867617343.210Q59929943017.190Q59932040173.183Q60109315147.163Q60740903729.182Q62009673032.193Q62011770180.186Q62948173470.190Q62950270618.183Q6910010095.192 Q6912107233.187 Q6912107244.184 Q7166002684.183 Q7917062806.186 Q9631752990.202 00000J00d00e00f00g01A01d01e02?02Y03303403N04104T05705Z06606R06n07J07f08@08Z08^08b08i0980:P0;h0<O0=50=<0>X0?20?K0?L0?S0@80@<0@C0@J0@U0AA0AE0AF0AG0AH0AI0Af0BC0B`0C=0CP0D60DN0Df0E10E80E?0EC0EI0EJ0EK0EL0EM0EN0EO0EP0ET0E\0Ed0FI0FP0FW0F^0Fe0Fl0G30G:0GJ0GZ0Gj0H50H@0HK0HV0Ha0Hj0I10I80I?0IF0IM0IU0Jl0K30K:0KF0K^0Kl0L:0LA0LH0LO0LP0LQ0LY0Lo0ME0M`0Ma0NM0O80O?0OF0OU0Od0On0P50P<0PF0PG0PH0PQ0PZ0Pg0Q30Q90Q?0QH0QQ0QX0Q_0Qf0R20R30R>S2sp2PP4SIGB2bs2FB3spv3sp1S2sp2PP4SIGB2bs2FB3spv3sp1FFFS2sp2PP4SIGB2bs2FB3spv3sp1S1R3HIA2sp2PP4SIGB2bs2FB3spv3sp12h1FS2sp2PP4SIGB2bs2FB3spv3sp1S2sp2PP4SIGB2bs2FB3spv3sp1S2sp2PP4SIGB2bs2FB3spv3sp1FS2sp2PP4SIGB2bs2FB3spv3sp1S1R2sp2PP4SIGB2lo2bs3LOS2FB3spv3sp1S1R2sp2PP4SIGB2lo2bs3LOS2FB3spv3sp1S1R2sp2PP4SIGB2lo2bs3LOS2FB3spv3sp1S1R2sp2PP4SIGB2lo2bs3LOS2FB3spv3sp1S1R2sp2PP4SIGB2bs2FB3spv3sp1S1R2sp2PP4SIGB2bs2FB3spv3sp1S1R2sp2PP4SIGB2bs2FB3spv3sp1S1R2sp2PP4SIGB2bs2FB3spv3sp1S1R2sp2PP4SIGB2bs2FB3spv3sp1S2sp2PP4SIGB2bs2FB3spv3sp1S2sp2PP4SIGB2bs2FB3spv3sp1S2bsS2bsS2bs2FBS1R2FB3spv4SEPFS1R2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS2FB3spv3sp13SP14SP1M4FBAL3FB05SLO164SPVA3ALO3ACV3SPRS1R2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS2FB3spv3sp13SP14SP1M4FBAL3FB05SLO164SPVA3ALO3ACV3SPRS2sp2PP4SIGB3END2bs2FB3spv3sp14lxv03H47S2sp2PP4SIGB2bs2FB3spv3sp13lxv3H423H49S2bs2FBS1R2sp2PP4SIGB1P2lo2bs3PPB3SGB3SLO3LOS2FB3spv3sp13SP13FB05SLO163ALO3SPR2H94lxv04lxv13H443H46S2sp2PP4SIGB2bs2FB3spv3sp1S3slo2bs2FB3spv2H01R4SLOSFS2bs2FBS2sp2PP4SIGB1P2bs2FB3spv3sp14lxv03H48S2FBS2bs2FBS2bs2FBS2bs2FB3sp1S2sp2PP4SIGB3END2bs2FB3spv3sp14lxv04lxv13H45S2FBFFFFS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HS2sp2bs2FB3sp14FBS1S2sp2PP4SIGB2bs2FB3spv3sp13lxv3H503H42S1R2sp2lo2bs3SLO3LOS3ALOS1R2sp2lo2bs3SLO3LOS3ALOS2bs2FB3sp1S2bs2FBS2bs2FBS2FBS1i2HiFFFFFFFS2FBS2bs3sp1S2bs3sp1S2sp2PP4SIGB1P2bs2FB3spv3sp14lxv03H46S2bs2FBS2bs2FBS2bs2FBS2bs2FBS2bs2FBS2bs2FBS2bs2FBS2bs2FB3sp14FBS1S2bs2FB3sp14FBS1S2bs2FB3sp14FBS1S2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S1R2sp2bsS2bs2FBS2bs2FBS2bs2FBS2PP2bsS2PP2bsS3BUF2bsS1R2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS2FB3spv3sp13SP14SP1M4FBAL3FB05SLO164SPVA3ALO3SPR2H9S2bs2FBS2bs2FBS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2sp2lo2bs3sp1S2sp2lo2bs3sp1S2bs2FBS2bs2FBS2bs2FBFFS3BUF2bsS2sp2lo2bs3SLO3sp13SP1S2sp2lo2bs3SLO3sp13SP1S1R3HIA1h2sp2lo2bs3TOP4HTOPFS1R3HIA1h2sp3slo2bs3TOP3spv3sp13SP14HTOP3H16S1R3HIA1h2sp3slo2bs3TOP3spv3sp13SP14HTOP2H8S2lo2bsS2bs2FBS1R3slo2bs4SLOSS1R3slo2bs4SLOSS2sp2lo2bsS2PP2bsS2PP2bsS1R2bs3ALOFFS4SIGB2bsS4SIGB2bsS1R2lo2bs3LOSS2PP4SIGB2bsS1R2bsS1R2bsS4SIGB2bsS4SIGB2bsS2bs2FBS2bs2FBS2bs2FBS2PP4SIGB2bsFS2bs2FB3FB0". (* [comment removed for export] *)
  Lemma body_walk : forall (FB spv s2v sp1 : Z) (LF' : list blk) (h1 : HST asegs R HIA) (m0 m : mem)
      (x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 s5v s8v : word)
      (junk1 junk2 j3 j4 : list byte) (tg0 : word) (len0 q0 : Z),
    HM asegs R HIA h1 LB LF' m -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) ->
    hflag asegs R HIA h1 = hflag asegs R HIA h -> havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 -> sp1 mod 32 = 0 ->
    rw_cells asegs m FB [CB 24 junk1] -> rw_cells asegs m (FB + 24) [CB 8 j3] ->
    rw_cells asegs m (FB + 32) [CB 24 junk2] -> rw_cells asegs m (FB + 56) [CB 8 j4] ->
    rw_cells asegs m (Z.shiftr FB 3 + al_sb AL) (zcells 8) ->
    crange CS FB 64 -> FB mod 32 = 0 -> 0 < FB -> FB + 64 <= sp1 ->
    client_wrange L (LB ++ fdata LF') (arl_stklo R) (htop asegs R HIA h) FB 24 ->
    client_wrange L (LB ++ fdata LF') (arl_stklo R) (htop asegs R HIA h) (FB + 32) 24 ->
    (forall x, FB <= x < FB + 64 -> (arl_stklo R <= x < htop asegs R HIA h) \/ in_block LF' x) ->
    (forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata LF')) ->
    (FB + 64 <= PP \/ PP + 8 <= FB) -> (FB + 64 <= SIGB \/ SIGB + 24 <= FB) ->
    (Z.of_nat (length bs) = 0 \/ FB + 64 <= BUF \/ BUF + Z.of_nat (length bs) <= FB) ->
    stk asegs m lo spv -> lo <= spv - 16 -> spv mod 16 = 0 -> spv <= sp1 -> (FB + 64 <= arl_stklo R \/ spv = FB) ->
    stk asegs m sp1 (bv_unsigned sp + -80) -> rw_cells asegs m (sp1 + 8) [C8 (Z_to_bv 64 FB)] ->
    rw_cells asegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] ->
    rw_cells asegs m SIGB [C4 tg0; C4 pad; C8 (Z_to_bv 64 len0); C8 (Z_to_bv 64 q0)] -> bytes_at asegs m BUF bs ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m SIGB 24 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    abase asegs AL m -> mem_inv asegs m ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m0 m ->
    wlow R LB LF -> wcover R LB LF (bv_unsigned sp) W FB 64 ->
    shadow_free R LB LF (bv_unsigned sp) (hstkhi asegs R HIA h) FB 64 ->
    sshad asegs AL m slo spv -> sshad asegs AL m sp1 (bv_unsigned sp) ->
    PATH FB spv s2v sp1 LF' ->
    evtA asegs AL CS (POSTA m0)
      (MS (mkR (Z_to_bv 64 0x0994e0) (Z_to_bv 64 spv) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1)
              x10 (Z_to_bv 64 END) x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 s2v) (Z_to_bv 64 PP) (Z_to_bv 64 SIGB) s5v (Z_to_bv 64 FB) s8v (Z_to_bv 64 (al_sb AL)) s9 s10 s11
              x28 x29 x30 x31)
          F (Z_to_bv 64 0x99520) fc None m (seg_rom asegs)).
  Proof.
  intros until q0.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 FD G2 FSH CFB FBAL FB0 FBS1 FWH FWD FWS SUBLF AP1 AP2 AP4
  ST1 SLO16 SPVA SPV1 SEPF STK2 SLOT SPILL HPP HSG HBUF OPP OSG OBUF AB MI PRES WL WCF SFF SS1 SS2 HPATH.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB LF' _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  cbn [zcells] in FSH.
  pose proof (sums_asn1G_ok AL IMG) as LXSUMS.
  (* [comment removed for export] *)
  try unfold PATH in *. lxr_path. lxr_abase. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x99588] [(0x99594, DJoin)] 167%N). lx_tree.
  lxr_leaf. lx_carry.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : rw_cells _ m4 (FB + 32) _ |- _ => chunk_split H 1%nat HLEN FD2 end.
  replace (FB + 32 + 8) with (FB + 40) in FD2 by (clear; lia).
  match goal with H : rw_cells _ m4 (Z.shiftr FB 3 + al_sb AL) ?cs |- _ => rename H into FSH4 end.
  frame_aobj FSH4 (FB + 32) 1%nat as OLEN.
  (* [comment removed for export] *)
  try unfold PATH in *. lxr_path. lxr_abase. lxr_pose.
  lx_pre. lx_run_tac (PLANS [0x099624] [(0x99594, DJoin)] 167%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA]). lx_tree.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x99624) _ _ _ (seg_rom _)] => lxr_leaf; lx_apply epi_walk | |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx BODY: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
