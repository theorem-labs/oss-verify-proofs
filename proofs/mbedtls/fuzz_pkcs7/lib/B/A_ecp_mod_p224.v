(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_journey A_mpi_grow A_mpi_core_mla A_mpi_core_add A_ecp_red_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAEcpSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P005a5ffa128234eb 1 1 4 1 0 1 2 103 1 115 1P0095db4504d267c9 0 2 0 1 4 1P01ac2414b09cfe13 1 1 4 1 0 1 2 81 1 93 1P01b323c2fb2979cb 1 2 16 3 0 1 124 1 125 1 16 9 76 1 87 1 96 1 105 1 106 1 109 4 110 1 123 1 126 1 2 127 1 128 1P024c57122a6e56c1 0 2 0 1 1 1P0273a6333734aaee 1 1 4 1 0 1 3 56 1 79 1 91 1P0285e1d78f7adff0 1 1 4 1 0 1 3 68 1 91 1 101 1P02a1e664ece0958e 1 1 16 2 0 1 82 1 3 7 1 83 1 84 16P02a9b3822886ec40 1 1 4 1 0 1 2 103 1 115 1P02b673aa16e687e6 1 1 4 1 0 1 2 93 1 105 1P02d6f5fb6282798c 0 2 0 1 3 1P02e05f6c3f1401b3 0 2 0 1 4 1P02ebe1950a03b875 1 1 16 2 77 1 124 1 3 0 1 123 1 125 16P02ee3f52149aa3ea 0 4 0 8 56 8 82 8 83 8P0350b36d51d786c9 1 2 16 2 0 1 92 1 16 2 50 1 93 1 2 94 1 95 1P0377cc54a3c20243 0 2 0 1 3 1P038f135b85665017 1 2 16 2 0 1 104 1 16 2 62 1 105 1 2 106 1 107 1P03d95bd69fa35486 0 2 0 1 81 4P03f5a96d9ff8924d 1 1 8 2 0 1 82 1 3 1 1 83 1 84 8P0400584a38bef70b 1 2 16 3 0 1 117 1 118 1 16 9 71 1 82 1 91 1 100 1 101 1 104 4 105 1 116 1 119 1 2 120 1 121 1P044bb64e688fa9d6 0 2 0 1 91 4P04500ec6da7fd8ce 1 2 16 2 0 1 105 1 16 2 61 1 106 1 2 107 1 108 1P04d4c2dbca814a20 0 2 0 1 3 1P056cc9cc32d7b6ad 1 1 4 1 0 1 2 99 1 111 1P058a4752015f0a0a 1 1 4 1 0 1 2 109 1 123 1P058e1a1305434612 1 1 4 1 0 1 2 103 1 115 1P05a12a7fe167f7fa 1 1 4 1 0 1 2 93 1 103 1P06b246063ffeaf4b 0 2 0 1 89 4P07718df646dbfb2c 0 2 0 1 4 1P07cf17da8978b726 1 1 4 1 0 1 2 72 1 82 1P07fd2909d48eec00 0 2 0 1 1 1P081ff61f468d0f40 1 1 16 2 0 1 92 1 4 45 1 79 4 91 1 93 16P082113f5f48529b4 1 1 4 1 0 1 2 80 1 90 1P0881b7d437343466 1 1 4 1 0 1 3 58 1 81 1 91 1P08cbfb4a215dcbcd 1 1 4 1 0 1 2 103 1 115 1P08d37aa75f826181 0 2 0 1 81 4P08ea2a780c6db8d5 1 2 16 3 0 1 117 1 118 1 16 9 71 1 82 1 91 1 100 1 101 1 104 4 105 1 116 1 119 1 2 120 1 121 1P09174ec327edee0a 0 2 0 1 3 1P09644e47ec139601 0 3 0 1 80 1 103 1P098ae9f117c63462 1 1 4 1 0 1 2 82 1 92 1P09be605ff1fcce5c 0 2 0 1 83 4P0a01792920ce07b5 0 2 0 1 4 1P0a39c4a525c99fcb 0 5 0 16 47 16 81 64 91 16 92 16P0a9142193d9270ce 1 1 4 1 0 1 2 77 1 87 1P0aa45c70e011bbbd 0 2 0 1 4 1P0aa4626483d3a2f7 0 3 0 1 84 1 107 1P0ae452d4b1f0fd02 0 4 0 16 39 16 123 16 124 16P0b420f4e0c5b26e0 2 75 1 1 8 3 2 1 121 1 124 1 4 0 2 122 2 123 2 125 16 1 1 8 3 1 1 122 1 123 1 5 0 1 109 4 121 1 124 1 125 8P0badd8bb8f0fc95d 0 2 0 1 4 1P0c85f89b05e58568 1 2 16 3 0 1 117 1 118 1 16 9 71 1 82 1 91 1 100 1 101 1 104 4 105 1 116 1 119 1 2 120 1 121 1P0c8d46e703f8f88c 1 2 16 2 0 1 105 1 16 2 63 1 106 1 2 107 1 108 1P0c9899a090f1ef23 0 2 0 1 105 1P0ca4c1d8737058c9 1 1 4 1 0 1 2 107 1 119 1P0ccd070227b3eb28 1 2 16 3 0 1 117 1 118 1 16 9 71 1 82 1 91 1 100 1 101 1 104 4 105 1 116 1 119 1 2 120 1 121 1P0d0d72c445e02913 1 1 8 3 1 1 125 1 128 1 4 2 2 126 2 127 2 129 16P0e1ed77f1b8415fc 1 1 4 1 0 1 2 97 1 107 1P0f054b345efa7e7e 1 1 16 9 44 1 55 1 64 1 73 1 74 1 77 4 78 1 87 1 90 1 4 0 1 88 1 89 1 91 16P0f240e9f17441643 2 69 1 1 8 3 2 1 117 1 120 1 4 0 2 118 2 119 2 121 16 1 1 8 3 1 1 118 1 119 1 5 0 1 105 4 117 1 120 1 121 8P0f6fbd420027f1df 1 2 16 2 0 1 88 1 16 2 46 1 89 1 2 90 1 91 1P10bc23e00f832d46 0 8 0 4294967296 17 4294967296 19 4294967296 22 4294967296 23 1 25 1 28 1 114 1P10ec23383a652d2b 2 69 1 1 8 3 2 1 117 1 120 1 4 0 2 118 2 119 2 121 16 1 1 8 3 1 1 118 1 119 1 5 0 1 105 4 117 1 120 1 121 8P11567fff0b907759 1 2 16 2 0 1 111 1 16 2 67 1 112 1 2 113 1 114 1P116524597e61c4ea 0 2 0 1 72 4P1182c9766b38d37b 1 1 8 3 0 1 126 1 127 1 5 2 1 111 4 125 1 128 1 129 8P11d1713157f73d2d 1 1 4 1 0 1 3 70 1 93 1 105 1P11d28a832b0f0b42 1 1 4 1 0 1 2 85 1 123 1P122fb919bb76879f 1 2 16 3 0 1 121 1 122 1 16 9 75 1 86 1 95 1 104 1 105 1 108 4 109 1 120 1 123 1 2 124 1 125 1P1279e8014b79dc84 1 1 16 2 0 1 104 1 4 57 1 91 4 103 1 105 16P12e473404f053c42 1 1 16 2 0 1 94 1 4 49 1 83 4 93 1 95 16P1300e89f8ac5d64c 0 2 0 1 3 1P13098eab75520a64 1 1 4 1 0 1 2 74 1 84 1P1357ce57ca06ba11 0 2 0 1 86 1P13abf97effc8dd23 1 2 16 2 0 1 93 1 16 2 51 1 94 1 2 95 1 96 1P14633640bc2e677e 1 1 16 2 0 1 106 1 4 61 1 95 4 105 1 107 16P149f3fe0a70c1139 1 2 16 2 0 1 103 1 16 2 59 1 104 1 2 105 1 106 1P15666135738fd584 0 2 0 1 3 1P15c7c9b269462a41 1 1 4 1 0 1 3 64 1 87 1 97 1P15c82a666d5b6c7b 0 7 0 1 76 1 96 1 105 1 109 4 123 1 124 1P1617360491190576 0 5 0 1 75 1 86 4 126 1 127 1P162876041f14a41e 2 69 1 1 8 3 2 1 117 1 120 1 4 0 2 118 2 119 2 121 16 1 1 8 3 1 1 118 1 119 1 5 0 1 105 4 117 1 120 1 121 8P16761c051f162311 1 1 4 1 0 1 2 99 1 111 1P1695bb4c8ec91d51 1 1 4 1 0 1 2 107 1 119 1P16ddf9fad682e7ea 0 3 0 1 80 1 103 1P170b308ab193b081 0 6 0 1 87 1 106 1 110 1 123 1 124 1P1737d7837483b09d 0 4 0 1 23 1 25 1 28 1P17fbee55a5a4ace2 1 1 4 1 0 1 3 58 1 81 1 93 1P180ccbbfd7a37503 1 1 4 1 0 1 2 83 1 93 1P18d8405f6c6685f4 0 2 0 1 3 1P18ee1508ff422f66 1 1 4 1 0 1 2 103 1 115 1P1917f54a8d61d879 0 2 0 1 4 1P194f805bb9b2d742 1 1 4 1 0 1 3 76 1 99 1 111 1P19619f291c46bd5f 0 2 0 1 79 4P196efb00065751ac 0 2 0 1 4 1P19daa99ffa8867e5 1 1 4 1 0 1 2 87 1 97 1P1a2858a8bfd3d7fd 1 2 16 2 0 1 110 1 16 2 68 1 111 1 2 112 1 113 1P1a2ec2a0a1432677 0 2 0 1 2 1P1a6836e0cd32ab1b 1 2 16 2 0 1 89 1 16 2 45 1 90 1 2 91 1 92 1P1adb1ac0f7a93acc 1 1 4 1 0 1 2 100 1 110 1P1aeccd7e4cd211a2 1 1 4 1 0 1 3 60 1 83 1 93 1P1af772bedeb902e4 0 2 0 1 3 1P1b118f75eec34e1f 0 2 0 1 4 1P1b5d2836609f0f1b 1 1 4 1 0 1 2 103 1 115 1P1b76efa9f9033040 0 2 0 1 4 1P1c0faf5213704d60 0 2 0 1 99 4P1c138f37599a765d 0 2 0 1 1 1P1c15a983de77638e 1 1 4 1 0 1 3 86 1 109 1 123 1P1c2e6b4f43fae227 1 1 4 1 0 1 2 109 1 123 1P1ce31a81e7e1cf72 1 2 16 2 0 1 95 1 16 2 53 1 96 1 2 97 1 98 1P1d358fd3f213f920 0 2 0 1 3 1P1d3dc38d2f6ed195 1 2 16 2 0 1 91 1 16 2 49 1 92 1 2 93 1 94 1P1da8514cfe2e125a 0 2 0 1 93 4P1df1fe5d1a5f17ae 0 2 0 1 72 4P1e51a067169decba 1 1 4 1 0 1 2 92 1 102 1P1e98ca96db5badd1 2 75 1 1 8 3 2 1 121 1 124 1 4 0 2 122 2 123 2 125 16 1 1 8 3 1 1 122 1 123 1 5 0 1 109 4 121 1 124 1 125 8P1ecd92aa408b7d5c 0 3 0 1 86 4 109 4P1f0e70ca8bac36a6 0 2 0 1 4 1P1f8505b9657535d3 1 1 4 1 0 1 2 91 1 101 1P1fd02c197e96363a 0 2 0 1 120 1P20103f81f52e30cd 0 2 0 1 1 1P2073a1aa8fb6d377 0 2 0 1 120 1P2109fd8014859e19 0 5 0 16 38 16 72 64 82 16 83 16P216c045bf4071411 1 1 4 1 0 1 2 107 1 119 1P21996858f5e7ef73 0 4 0 1 24 1 26 1 27 1P22079a48a68e6e9d 0 2 0 1 95 4P22a13da8f9059e1d 1 1 4 1 0 1 2 78 1 88 1P22fedbf18be32b3d 0 2 0 1 85 1P23054389da52214b 1 1 4 1 0 1 2 107 1 119 1P2373e0e36fae85b6 0 2 0 1 89 4P244d16ae8d59ed5a 1 1 16 2 0 1 82 1 3 7 1 83 1 84 16P24a3f6da114ca104 1 2 16 2 0 1 100 1 16 2 58 1 101 1 2 102 1 103 1P24d5bea2b2b7fa4a 0 5 0 16 75 16 85 64 123 16 124 16P24fc7fb327ae38a0 0 2 0 1 119 1P25661c4394af66cc 1 2 16 2 0 1 90 1 16 2 48 1 91 1 2 92 1 93 1P258625c8254bfc23 0 2 0 1 79 4P2586d299f1f0f525 0 2 0 1 3 1P25b2680a08a378c7 1 1 4 1 0 1 2 103 1 115 1P25b324ba16554c19 1 1 4 1 0 1 3 70 1 93 1 103 1P25be847aa050a030 1 2 16 3 0 1 121 1 122 1 16 9 75 1 86 1 95 1 104 1 105 1 108 4 109 1 120 1 123 1 2 124 1 125 1P25c78c5051a46888 0 2 0 1 4 1P2711154946d9bfdf 0 2 0 1 1 1P272a7018c6020be6 1 1 4 1 0 1 2 107 1 119 1P2831ad0978248480 0 2 0 1 4 1P2894723a046cba24 0 2 0 1 4 1P28bcfe01fed96d0a 1 1 4 1 0 1 2 81 1 91 1P28eef779fbfadb2c 0 2 0 1 1 1P28f4a36221f3412d 2 69 1 1 8 3 2 1 117 1 120 1 4 0 2 118 2 119 2 121 16 1 1 8 3 1 1 118 1 119 1 5 0 1 105 4 117 1 120 1 121 8P2933bede9a006da6 0 3 0 1 80 1 103 1P294fc5fc25971095 0 2 0 1 77 4P297c6cfe0b1d7eab 0 5 0 1 84 1 102 1 123 1 124 1P2a035ce89a86c6f4 1 1 16 2 0 1 83 1 4 38 1 72 4 82 1 84 16P2a164e129b4163c5 0 2 0 1 119 1P2a550134cfd547a3 1 2 16 3 0 1 124 1 125 1 16 9 76 1 87 1 96 1 105 1 106 1 109 4 110 1 123 1 126 1 2 127 1 128 1P2a7f1aaf7dae6763 0 3 0 1 86 4 109 4P2a80023ad1754f08 1 1 4 1 0 1 3 54 1 77 1 87 1P2aa809f161eabb99 1 1 4 1 0 1 2 90 1 100 1P2b21813a49e8f1e1 1 2 16 2 0 1 102 1 16 2 60 1 103 1 2 104 1 105 1P2ba9d9358ab1545c 0 2 0 1 72 4P2baed1a760928e0d 1 1 4 1 0 1 2 79 1 91 1P2bd5f7d7fd5cba19 1 1 4 1 0 1 2 99 1 111 1P2bec057174f02cc5 0 5 0 1 90 1 103 1 123 1 124 1P2c2bf5e2de6f93b4 0 6 0 1 87 1 106 1 110 1 123 1 124 1P2c42ed11bb93dd7c 0 2 0 1 77 4P2c5e105739c75d55 0 4 0 1 98 1 123 1 124 1P2c91c2d933bf7c38 1 1 16 2 0 1 123 1 3 40 1 124 1 125 16P2ce402e5ea09e79a 0 3 0 1 84 1 107 1P2d041174d026108a 1 2 16 3 0 1 125 1 126 1 16 9 77 1 88 1 97 1 106 1 107 1 110 4 111 1 124 1 127 1 2 128 1 129 1P2d36fab0e460af62 0 2 0 1 3 1P2d66a9bbc4a12947 0 7 0 1 77 1 97 1 106 1 110 4 126 1 127 1P2ee24af95b4abcc4 1 2 16 2 0 1 91 1 16 2 47 1 92 1 2 93 1 94 1P2f8d0bab9ccddb1d 1 2 16 2 0 1 101 1 16 2 57 1 102 1 2 103 1 104 1P2f98344a42e89ebf 0 5 0 16 59 16 93 64 103 16 104 16P2fb3c8390551c284 1 1 16 9 43 1 54 1 63 1 72 1 73 1 76 4 77 1 86 1 89 1 4 0 1 87 1 88 1 90 16P30042c78425a245b 1 1 4 1 0 1 2 93 1 103 1P300e6c190acb3619 0 2 0 1 4 1P303a4b9538cf53ed 1 2 16 2 0 1 93 1 16 2 49 1 94 1 2 95 1 96 1P30926479086b8f5c 0 2 0 1 95 4P30c7b27ae2d0bfd6 0 2 0 1 85 4P316107b705b96594 1 1 16 2 0 1 112 1 4 65 1 99 4 111 1 113 16P316da03fcc10e46b 1 1 4 1 0 1 2 94 1 104 1P31ab225865e4d016 0 5 0 16 47 16 81 64 93 16 94 16P31b7bd6d02ac75f9 0 2 0 1 85 4P31d13b3634c1c34d 0 3 0 1 84 1 107 1P3220052737da9189 1 1 16 2 0 1 96 1 4 51 1 85 4 95 1 97 16P322c5b35597ed6fd 0 2 0 1 4 1P326d3b1544d0fcbc 0 2 0 1 3 1P32845043fecc76bf 0 2 0 1 4 1P3314de2f4bc85491 1 1 4 1 0 1 2 107 1 119 1P33cb42cb7c5483f2 0 2 0 1 3 1P33de871126abaf0c 1 1 16 2 0 1 90 1 4 43 1 77 4 89 1 91 16P33e6691923e5c181 1 2 16 3 0 1 121 1 122 1 16 9 75 1 86 1 95 1 104 1 105 1 108 4 109 1 120 1 123 1 2 124 1 125 1P340d13d67c559094 1 1 16 2 0 1 106 1 4 59 1 93 4 105 1 107 16P34172d4b0c6a3249 1 1 16 2 1 1 125 1 4 76 1 110 4 124 1 126 16P362e485b701c11c0 1 1 4 1 0 1 3 66 1 89 1 101 1P367cbe86da09993e 0 2 0 1 119 1P367e4b2f684fdb1c 1 1 8 3 0 1 125 1 128 1 4 2 2 126 2 127 2 129 16P37938adc4bb4c459 0 2 0 1 105 1P37a0628a3444ca71 0 2 0 1 2 1P37afe1cf1c6eb48e 1 2 16 2 0 1 103 1 16 2 61 1 104 1 2 105 1 106 1P3850cbf826e59f89 1 1 16 2 0 1 102 1 4 55 1 89 4 101 1 103 16P398866f300aa684c 1 1 4 1 0 1 2 103 1 115 1P398f4294fb477717 1 1 4 1 0 1 3 74 1 97 1 107 1P3a90c518ed0b1b57 0 4 1 1 2 1 125 1 126 1P3a99a12e382414a1 0 3 0 1 80 1 103 1P3b13983d8847a951 0 5 0 1 84 1 102 1 123 1 124 1P3b4f8de6b501c715 1 1 4 1 0 1 2 83 1 93 1P3bd4dd85ae3ba7ef 0 2 0 1 4 1P3c01b1cdfe3023c6 2 75 1 1 8 3 2 1 121 1 124 1 4 0 2 122 2 123 2 125 16 1 1 8 3 1 1 122 1 123 1 5 0 1 109 4 121 1 124 1 125 8P3c11e1b41b3ff09f 0 4 0 1 98 1 123 1 124 1P3c826d1f7af767b2 0 2 0 1 4 1P3cd2102671fc9b57 0 2 0 1 4 1P3d02966225f1f16d 0 2 0 1 3 1P3d460f40844f14b2 1 1 4 1 0 1 3 76 1 99 1 111 1P3d6bde9e825985e5 1 1 4 1 0 1 2 81 1 91 1P3d73f02008240d17 0 2 0 1 93 4P3d8b6625b7c828fa 1 1 4 1 0 1 2 93 1 105 1P3e3034805082210c 0 2 0 1 91 4P3e63ad433d479a12 0 7 0 1 76 1 96 1 105 1 109 4 123 1 124 1P3e7100ec47ad2cf0 1 1 4 1 0 1 2 81 1 93 1P3ec49de29e7b5923 0 8 0 4294967296 18 4294967296 20 4294967296 21 4294967296 24 1 26 1 27 1 113 1P3eef89b886720d90 1 1 4 1 0 1 2 89 1 101 1P3f1f092f041cea72 0 2 0 1 1 1P3f7ea5d9dbb94b58 1 1 4 1 0 1 3 51 1 74 1 84 1P3f7eb707f2f93365 0 2 0 1 4 1N0052708f2c298710N0083c385692d9850N008b203a24bbef30N00ac2f56f7508a59N015688544f4d5e21N018bc59e6b8a4481N01badcabcc2f4014N02554c63a61698c6N027ac1bd333e06b6N02a09ae0ad3eea8fN02c59df78377139eN02d8c20680ee7f97N031d9a1ded18680aN03404bb1bd724a24N034d3dc7f65a343fN0372f8a030750272N03c85f8cfb28227cN04243e94676efdb0N04930ed7d1a1f48cN052a862ce6086093N053e9d89e7e60811N06657953f3b4489cN06ff9052ad5091ebN070ddb74f6cac547N0761b590c54f2531N078a7a696971be60N07978139a3c18ab1N0799587dee277b7fN07bb8bf34925a54fN07c75e1e453d40d7N083edd3b8159dcefN08920fd2c5278e34N08b2d3a6cd0e9a8bN08d1c746ae1d6ab8N08d717bdc4946c6cN08f01c00c3c14c01N09827770dbbb3b2dN099b79e7583bf715N09c91416d64c039bN0a13885ba1418ff2N0aa4152fe19cf573N0ace1ab77e145465N0b16b1b3be222df6N0b42f418f9854360N0b69fef9b3c3d128N0b6a0fe6bb49fdcbN0b85aaf543183ee5N0b877c543f04ecbdN0bb988c61d1bf49dN0c8521a20358aacdN0c97bdaff938878cN0cea514c6a76e529N0d1e1a45a8e7d597N0d938ca47e44d9b0N0e09d88a310785ebN0e1202d08c88a8b0N0e34b8d98622d5c1N0e8f5628b293e697N0ebc612c4122bb88N0f2441b75281fc39N0f2af2cdb298040bN0f39bd958406ad75N0f4f036cee7f6d1aN0f5cdefdfe753b90N0f93f32c5a814c82N0f9963289f265668N0fd8ff8e7907b173N0fde83b06833966eN1054b88d9c2a2925N1148340e18faa9b6N11d492df40a97113N121b558bacb3ced9N121f887d5114a613N129216fd13b076abN12e35e852a1079a1N1307eacd852e25cfN13143a58f63efe54N1353f020ab00f2e9N138bc8db79a64c50N13917882ab8b8ae9N13d3fb8535f59d39N1408124a01c7f3a1N1442e8d57dbde4c5N14bff2a3018012e9N151e2646ffd1a57fN15470334292521deN15c78e8a446a8c9aN16108c123b7e47edN16165fc57da91e0aN167933d6c1da95cdN16b356cf1545f9c7N16c29ae7fdec786bN17552ebb8e0c3e3bN17be421bfa8a949bN17c82d601e2e4acdN17ec8c71085f4c25N17ed3828ef989200N17fc55dfdf1fb64aN1804e09a797658f6N1870e67f308696a6N18c69d17e30b685dN1928949f491976e4N19fda5e63aeda866N1a68c595bff0b293N1a8eababb7002a36N1ad2ec07110c7c88N1b24288625faf90cN1c0ba1596f59aef8N1ccc5a16dec57d75N1cd7d5c32fb5f1ceN1ce1a85ae708257bN1d1ed02f86f031edN1d63580389bcbc68N1d831a1c886e68bdN1e862ed924b7d96dN1f5695f759e3a372N1f7eef9003735dafN1fff87c2da6a5cc2N20924cb8cb8c66bdN20d84ebbb0ec2bc9N20e8dab4883c28efN214789ec1172cac0N215543185fc3c310N21a3ed7b7f98db4dN2214b73d73538b35N2269020b74d87faaN229349b9ceac2bcaN22c063e808f2b162N230a98f54aa550aaN233ada4c02f17f30N23f3732817d7be2cN23f52e760b1158f0N2433d0f2a3741d80N2469b745a9040cf4N24a7494df6659d89N251b280c042c0ad3N253b0330c92509cdN253c79513399e688N254acdaad1d82943N25e348e0d8df7bdeN2756c9ae7c491a37N27594706ce0f4dafN279b0a8742ba9fefN27b3cce561eb25a5N27ef58cc5e35ce76N28328b18c2c45cbcN28ab7c6edd1a576bN28ea37a0df4bf17fN28f24f40c16a8adcN29078187a63c5744N2917b4f9191914d2N2939feb5fef36ba7N29431d9e4e0ab0d9N29871e26f1fc22b5N29da3e054f7d672aN2a1d45ca8adb957dN2a62ffd2ce76525fN2b264881f9819238N2b4cbe15482bee42N2beec83f399874aeN2c98ff106f4780c0N2cbe80210884ee15N2cf5fd02ce745bb6N2d53455ffb176147N2d8c141ef9d92d2eN2d8ebcb46d7e28e0N2da95f687ba5c844N2dfe9be8714dfff3N2f0356b240c81a51N2f0bc66edf95f4b6N2f173a0338b26112N2f9c36488b0d96a5N3012a37c73d3daedN3014382e3bbc87d8N3053772a79e4f18cN3063da605fccd6d4N30e45e0da2af0390N3114820c939035e9N3116cb79e4742976N312e0b6e4a66d28bN3142a3caa434b02fN314afe00c0804a0bN315aba225f25d547N318a39751006f31fN318e13e5fabd9ab9N31a021cfacf512dbN31ae7609f7c8c90cN31dfc703ae158eecN323abb8b49d04430N3399f212c1473cf8N339eec556a372ffdN33aeb328e10dae02N33fb4dcecec34353N3418faf9ebda036cN3434dd2abd495179N344e7dec1d238ac6N344eb3056a12a174N348b01ca19fe40f2N34992e65e580995eN34fd4018946c611cN3548e51eca016ccbN3584a6613023a533N35c81677dd3db9b3N35dc12afc63a8d38N3649b9d9daa60281N3703008ddb905734N3723c889511b0bd4N3729d039dcfd5201N376d3b31837b4b52N37963d205744a45dN389bebb1a4c3178aN38f1285fba101878N397cf5cbf441bc18N3a0a917bf22da82cN3ad03c0113e2dd3bN3b75b0713f861ea6N3b9dace489769534N3baa6fc0a44d7a54N3bd2757247ad900bN3bf2cd10506584ceN3c29733e1bedfe5cN3c832c6a43c26e49N3ca041142a8893b9N3d27c4f140823cabN3d4db120ace1d981N3d4e79eabbb0991bN3ebe652e32240470N3ee30d325a300951N3ef7e62cc3ed3a26N3f9ea02afa1df030N3fcb9ffd953a114bN3fdfe638d5e0e0fd"%lxh.
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
Ltac2 gd_tbl_A_ecp_mod_p224 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.P.P_ecp_red.reducer_R"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.red_FRn"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "RED.RFRAME"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RED.RPOST"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "A_ECP_MOD_P224"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_GROW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_red_lib.A_ASAN_MEMSET_EC"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_reducer_stmtA"].


Definition A_ECP_MOD_P224 : Z := 0xd4a00.   (* [comment removed for export] *)

Section RED.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis GROW : mpi_grow_stmtA_sz asegs R HIA A_MPI_GROW.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_EC.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own) (lo d : Z).
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Definition RFRAME : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 96 RFRAME.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + grow_PHI 14 <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + red_FRn d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_RED <= C24MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 192 - arl_need_ecp R.

  Definition RPOST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p224 ()) "(0.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(3.+>.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)(4.+>.)(5.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 96 RFRAME []).
  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L21887662552.132L29428324939.5  L33510041944.132L34289808772.1  L35663928186.7  L50809750179.1  L60098763854.3  L66083662040.132L9962237875.132 Q15643598972.131Q32655747964.131Q3830178207.131 Q39939305631.131Q44648563964.131Q51235551740.131Q66521824799.131Q9843086111.131 00000700I00P00T00i00m01701>01E01L01S01k02C02J02Q02i03AS2ra2spS1R2lo3LOS3ALO3ACPS2ra2spS2spS1R3HIA1h2sp2lo3TOP1HS2spS1R2lo3LOSS2ra2spS2ra2spS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  Lemma r_ret : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p224 ()) "Pxs3,(:.&40.)Pxs4,(:.&40.)Pxs5,(:.&40.)Pxs6,(:.&40.)Pxs7,(:.&40.)Pxs8,(:.&40.)Pxs9,(:.&40.)Pxs10,(:.&40.)Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pr,$6.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs0,(:.&40.)Pxs1,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$>.(?.$9.)R19.R18.R17.R16.R15.R14.)P,(3.+>.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R14.R15.)P,(10.R1;.(4.+>.))P,(10.R1;.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1;.Vmo,)$13.(14.(15.R16.(16.&40.(17.(18.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.R12.R11.(16.&40.R17.)R10.R?.R>.R=.R<.R;.R:.R9.R25.R24.R23.R22.R21.R20.R1?.R1>.Vs11,R8.R7.R6.R5.)VF,(16.&40.+=4>28.)Vfc,(19.(:.&40.))R19.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    do 12 zstep.
    zstep.
    replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold RPOST.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 96 RFRAME JC); [exact J| exact HR| exact HK9| exact MF9| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@D24996680996.151D30200628036.150D42631060527.150D62022258533.151L23305025156.0  L23643762344.4  L2397676628.0   L24471929311.6  L26227934071.0  L2975768925.2   L29773195157.0  L34289808772.1  L35663928186.7  L39307103286.4  L42633816569.1  L53028994992.1  L56080884112.5  L60098763854.3  L60283674290.6  L62912154502.2  00000M00c01701M01N01[01\02302402;02<02@02U02b02g02k03@03J03\03cS1R3HIA2ra2sp1X3xs02hc3pXc2xsS2ra2sp1X3xs01N3pXc2xsS2ra2sp1X3xs03pXc2xsS1R2ra2sp1X3xs03pXc2xsSS1X1N3pXc3XPcSS2sp2lo1N3pXc4LOSP4XLScSS1N3pXcSS2spS1R3HIA1h2sp2lo3TOP1HS2sp1X2lo3DSXS3pXcS2spS1N2xs4LEN14lxws4LENXS1R2lo3LOSS2sp2lo1N3pXc1a2NOS2sp2lo". (* [comment removed for export] *)
  Lemma r_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p224 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+60.$>.(?.$9.)R16.R15.R14.R13.R12.R11.)P,(1;.$1<.(1=.R12.)$1>.)P,(10.+>.(1?.R13.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+>.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R18.)(27.R18.)(1?.R18.)(28.R18.)R4.(29.R18.)(1=.R18.)))P,(10.R1:.(4.+>.))P,(10.R1:.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1:.Vmo,)$13.(14.(15.R16.(16.&40.(17.(18.&40.Vsp,)-60.))Vgp,Vtp,R15.R14.R13.(16.&40.VX,)(16.&40.(2:.(2;.VR,)))(16.&40.=)R12.R11.R10.R?.R>.R=.R<.R;.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=4:50.)Vfc,(19.(:.&40.))R18.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 96 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA hc.
    flat constr:((xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0)) 7%nat. intros ND1 LEN1 NR1 SG1' CX1 OWN0 OWN1.
    destruct dXc as [X' sg N pXc xs pad' own]. pose proof J0 as JX.
    pose proof JX as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]; cbn [app] in HH1. clear JX.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' own.
    unfold mpi_cells in CX1.
    flat constr:((OWN1 ltac:(discriminate))) 10%nat. intros _ N1 XIN XPAL XARR P0 PC PI OP P47. clear OWN0 OWN1.
    pose proof (XLS1 ltac:(discriminate)) as XLSc; pose proof (XP1 eq_refl) as XPc.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS; pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    assert (CWP : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) pXc (4 * N))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    pose proof LEN1 as LENX.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) in ST1, FR1 by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as ABm. pose (lxi := lxA_img (arl_AL R) IMG).
    lx_pre. lxe_pose. lxe_sums [SUM_amemsetWinA 4 5] [pXc; N].
    lx_pre. lx_run_tac (PLANS [0xd4e28] [(0xd4a68, DJoin); (0xd4a88, DJoin); (0xd4ab0, DJoin); (0xd4ac8, DJoin); (0xd4ad4, DJoin); (0xd4afc, DJoin); (0xd4b1c, DJoin); (0xd4b3c, DJoin); (0xd4b50, DJoin); (0xd4b80, DJoin); (0xd4ba0, DJoin); (0xd4bc0, DJoin); (0xd4bd4, DJoin); (0xd4c04, DJoin); (0xd4c24, DJoin); (0xd4c48, DJoin); (0xd4c88, DJoin); (0xd4c9c, DJoin); (0xd4cdc, DJoin); (0xd4cf0, DJoin); (0xd4d34, DJoin); (0xd4d40, DJoin); (0xd4d6c, DJoin); (0xd4d8c, DJoin); (0xd4da4, DJoin); (0xd4dc0, DJoin); (0xd4dd8, DJoin)] 2000%N [SUM_amemsetWinA 4 5]). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    1: {
      (* [comment removed for export] *)
      rename XARR into XARRo; rename LENX into LENXo.
      lazymatch goal with H : u32arr asegs ?mx pXc ?l |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        rename H into XARR;
        assert (LENX : Z.of_nat (length l) = N)
          by (first [ lazymatch goal with HL : Z.of_nat (length l) = _ |- _ => rewrite HL; rewrite ?upd_length; exact LENXo end
                    | rewrite ?upd_length; exact LENXo ]);
        try (lazymatch goal with HL : Z.of_nat (length l) = Z.of_nat (length _) |- _ => clear HL end);
        clear XARRo LENXo;
        (* [comment removed for export] *)
        set (lxws := l) in XARR, LENX; clearbody lxws; lxe_leaf_gc end.
      lazymatch goal with H : munch _ mc ?mx, H' : wmono asegs mc ?mx |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MU; rename H' into WM end.
      flat constr:(J0box) 2%nat. flclear J0box. intros J0 _.
      (match goal with STq : stk asegs ?mq lo (bv_unsigned sp + -96) |- _ => pose proof STq as STM; replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in STM by (clear; lia) end).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
      assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
      { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 96) by (clear - NO; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] (bv_unsigned sp - 96) 96).
      { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] X 16).
      { cbn. split; [clear - XPc; lia| split; [clear - DSX; lia| exact I]]. }
      match goal with MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
        pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ mF _ J0 MU WM MIq STM HHq HWF DJF DJX XARR LENF) as J9 end.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J9.
      lazymatch goal with |- aevtA _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply r_ret with (r := r0) end; [exact J9| apply HR0; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]| exact BV| exact BF].
    }
    1: {
      (* [comment removed for export] *)
      rename XARR into XARRo; rename LENX into LENXo.
      lazymatch goal with H : u32arr asegs ?mx pXc ?l |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
        rename H into XARR;
        assert (LENX : Z.of_nat (length l) = N)
          by (first [ lazymatch goal with HL : Z.of_nat (length l) = _ |- _ => rewrite HL; rewrite ?upd_length; exact LENXo end
                    | rewrite ?upd_length; exact LENXo ]);
        try (lazymatch goal with HL : Z.of_nat (length l) = Z.of_nat (length _) |- _ => clear HL end);
        clear XARRo LENXo;
        (* [comment removed for export] *)
        set (lxws := l) in XARR, LENX; clearbody lxws; lxe_leaf_gc end.
      lazymatch goal with H : munch _ mc ?mx, H' : wmono asegs mc ?mx |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MU; rename H' into WM end.
      flat constr:(J0box) 2%nat. flclear J0box. intros J0 _.
      (match goal with STq : stk asegs ?mq lo (bv_unsigned sp + -96) |- _ => pose proof STq as STM; replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in STM by (clear; lia) end).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
      assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 96).
      { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 96) by (clear - NO; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] (bv_unsigned sp - 96) 96).
      { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -96)] X 16).
      { cbn. split; [clear - XPc; lia| split; [clear - DSX; lia| exact I]]. }
      match goal with MIq : mem_inv asegs mF, HHq : HM asegs R HIA hc LBc LF mF |- _ =>
        pose proof (xa_limbs _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ _ mF _ J0 MU WM MIq STM HHq HWF DJF DJX XARR LENF) as J9 end.
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J9.
      lazymatch goal with |- aevtA _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply r_ret with (r := r0) end; [exact J9| apply HR0; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]| exact BV| exact BF].
    }
    all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@D21329468335.115D21329468335.116D23379772182.116D29470973055.150D35881667587.115D35881667587.116D8024673716.153 L14061208185.0  L16073620949.23 L17831472998.9  L21765854580.112L21887662552.111L23653214524.7  L27775132660.112L2800494986.0   L29010569984.153L33510041944.112L34290115814.111L35653441506.7  L37742712464.153L39582424848.23 L40290687782.1  L40834179097.117L41942189128.1  L42243864115.23 L43059266230.109L45290914134.23 L51815831204.6  L5261871668.3   L53028994992.1  L54748384003.112L59308632561.1  L59411595710.2  L60098763854.3  L60322900010.0  L62998051744.23 L63619888707.6  L64491265552.2  L66083662040.112L9716869748.111 L9962237875.112 P51809162158.153Q15643324129.111Q18696506101.117Q21800401414.117Q23512175082.113Q25160350961.117Q25513505925.114Q25513505925.115Q25664719138.117Q27668705378.114Q27668705378.115Q31226872993.117Q31396957457.117Q32655500769.112Q35016271767.117Q35715139857.117Q35765334355.112Q35765334355.113Q3830427394.112 Q39939554818.112Q4141071397.117 Q44648843873.112Q49698585326.113Q49698585326.114Q51235796833.112Q51809162158.153Q5286263674.151 Q5286263674.152 Q53972118266.117Q61800308129.117Q6414620453.117 Q64253126389.117Q66522067074.112Q67426116409.115Q67528989526.115Q67528989526.116Q7190931988.153 Q7190997782.118 Q9843367298.111 00000k01l02j02k03S04D04Z04[04k05K05X05e06?06L06M06N06[06h07@07V07Z07]08508908O08d09009109;09?09L09P09S09]09^0:10:I0:O0:\0:i0;60;70;B0;Z0;[0;f0<>0<[0=>0=?0=a0>F0>_0?00?;0?T0?U0?`0?k0@;0@K0@L0@W0@m0AC0AN0AO0AP0AQ0Aj0Ak0BC0BD0BT0C60CX0D@0E90F20FBS1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_st2s1S1R2ra2sp2s21X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stFS1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s2S2ra2sp2s02s12s21X3xs0SS1R3HIA1h2sp3TOPS2sp1X2sX2nX2pX3xs04padX4ownX2XLS2ra2sp1X3xs0S2ra2sp1X3xs0S1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X3xs0SFS2ra2sp1X3xs0S2ra2sp1X3xs0S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp2s02s12s21X3xs0S2spS1XS1R2ra2sp2s02s12s21X3xs0S2spS1R2sp2lo4SLO23NER3SPRS2ra2sp1X3xs02lo4LOSPS2sp3SPA3SPRFS1X2X03X16S2spS2ra2sp1X3xs0S2KRS1dS1R2lo3LOSSS1R3HIA1h2sp1d4BUDFS1R2sp2lo4SLO25NEEDR3NERS1d2D0S2ra2sp1X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0FS2sp3xs02loS1R2ra2s02s12s23xs04IMG'FS2sp3xs02HBS1R2ra2s02s12s23xs04IMG'S2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s2FS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s1S1R2ra2s02s12s23xs05ALWF'S2ra2s02s12s23xs0S2sp3xs02loS1R2ra2s02s12s23xs05ALWF'FS2sp3xs02HBS2sp3xs02HBS2sp3xs02lo4LOSPS2sp3xs02lo4LOSPFS2sp3xs02loS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stS2sp3xs02loFFFS1R2ra2s02s12s23xs05ALWF'FS1R2ra2s02s12s23xs04IMG'FS2sp3xs02lo4LOSPS2sp2s23xs02lo4LOSP2HB5Ha_st5Hl_stS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s2S1R2ra2sp2s02s12s23xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS1R2ra2sp2s02s12s23xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS2sp3xs02lo4LOSP". (* [comment removed for export] *)
  Lemma r_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p224 ()) "Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)P,(2<.$1.VR,VHIA,Vh,Vmo,)P,(2=.$1.Vm,Vlo,(18.&40.Vsp,))P,(2>.$1.Vm,)P,(2?.$1.(2;.VR,)(30.$1.VR,VHIA,Vh,)Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(31.$1.$13.(32.(14.(15.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(16.&40.VX,)R?.R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.$33.)Vfc,(19.(:.&40.))Vm,(1:.$1.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK ST MI OXA. unfold A_ECP_MOD_P224.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 96 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    flat constr:(OXA) 2%nat. intros OX _. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 96%nat ST.
    do 13 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold RFRAME in *.
    change (rw_cells asegs m1 (bv_unsigned sp + -96) RFRAME) in FR. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in FR by (clear; lia).
    pose proof ST as ST1. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in ST1 by (clear; lia).
    fold RFRAME in FR.
    pose proof (xa_start _ _ _ _ _ _ _ _ _ _ _ _ JC m1 HH MI ST1 FR OX MU WM) as J0.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m1 HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    clear MU WM. pose proof (munch_refl ([] : list ivl) m1) as MU; pose proof (wmono_refl asegs m1) as WM.
    zstep. zstep. zstep. clear GOT GSB AB.
    do 2 zstep.
    zstep.
    pose proof (xa_X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as MX1.
    flat constr:(XW) 2%nat. flclear XW. intros CW DXP.
    clear MU WM.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. pose proof GROW as CP. unfold mpi_grow_stmtA_sz in CP.
      eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 14) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by qlia; try eassumption; try reflexivity.
      all: try (split; [eapply client_wrange_sp_mono; [| exact CW]; clear; lia| exact DXP]).
      all: try (split; [exact OX| intros EST; exfalso; exact (NST EST)]).
      all: try (eapply uw_obj_uwc; [exact UWX| rewrite unsigned_lit by (clear - X0 X16; lia); clear; lia]).
      all: try (intros ON; destruct (XLS ON) as [XL|XL]; [left; exact XL| right; clear - XL; lia]).
      all: unfold grow_PHI, grow_FR, red_FRn, calls_FR, fr_charge, C24_GROW, C24_ECP_RED in *; unfold AVOL_CALL in *;
           try (clear - LOS SLO SLO2 NEEDR NER NRM NRF NRA SPA SPR BUD BUDF C24H D0 LOSP TOP; lia).
      all: match goal with |- ?g => idtac "GROW-PRE-LEFT:" g end. }
    intros ms' mo' (mo1 & [HK1 MF1] & PO). unfold mpi_binop_postA in PO.
    flat constr:(PO) 37%nat. flclear PO. intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 m2 mo2 h2 LB2 dX2 r E MI2 ST2 MF2 HP2 HT2 HS2 HF2 HK2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2 GR.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    pose proof ST2 as ST2'. replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in ST2' by (clear; lia).
    pose proof (grow_R_keep _ _ _ _ _ _ GR OUT2) as BK.
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -96) (grow_PHI 14) (grow_FR d) J0 ltac:(clear - SLO2 NER NEEDR; lia)
                  ltac:(unfold grow_PHI; unfold AVOL_CALL; clear; lia) ltac:(unfold grow_FR, calls_FR, fr_charge; clear - D0; lia)
                  MI2 ST2' HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 BK FRA2) as J1.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU; pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      destruct GR as [[(R0 & _)|(RF & EQ)] FRg]; [exfalso; apply KR; rewrite R0; reflexivity|]. subst r dX2.
      eapply r_ret; [exact J1| apply reducer_R_fail| unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
    - destruct GR as [[(R0 & GSG & GN & GPD & GLM & GID)|(RF & EQ)] FRg]; [| exfalso; subst r; clear - KR; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in KR; vm_compute in KR; lia].
      subst r.
      destruct (grow_ok_facts asegs m2 LB2 LB dX dX2 14 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia)) as (GO & GNN & _).
      eapply r_body; [exact J1| exact GO| rewrite GNN; clear; lia| | unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
      intros ws r Hr Hne.
      exact (reducer_R_ok 14 dX dX2 LB LB2 ws r asegs m2 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia) (conj Hr Hne)).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24356290505.0L43712168371.600000100BSS1R2sp2lo3SLO3NER". (* [comment removed for export] *)
Lemma A_ecp_mod_p224_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p224 ()) "PR,$34.PHIA,(35.$1.R1.)P,(36.(2;.R2.))P,(37.$1.R3.R2.$38.)P,(1;.$6.(39.R4.)$3:.)P,(10.=(3;.R5.))P,Ph,(7.$1.R6.R5.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(:.&40.)(;.(:.&8.))P,(3<.$1.R:.R9.R4.R3.R2.R1.)(3=.$6.(3>.(3?.$6.$6.)$6.(40.$6.$6.)R4.))P,(20.(10.(41.(42.R7.))(43.(42.R7.)))(10.(44.(42.R7.))(45.(42.R7.))))P,Pa,$6.P,(1;.$46.(47.$1.(48.R1.))$49.)P,(20.(10.=R2.)(21.R2.(23.+2.+40.)))(20.(10.(41.(42.R;.))R3.)(21.R3.(45.(42.R;.))))(4:.$1.R9.R8.$33.+>.+<0.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG GROW AMS NEEDR HND DIMG ROIMG. unfold ecp_reducer_stmtA.
  intros until d. intros HH HK LFB MX NST XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  pose proof (arl_need_ecp_rt R) as NER.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 96 (RFRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR NER; lia. }
  eapply r_main; first [ exact JC | eassumption | eapply uwc_nonneg; exact UW | clear - SLO NEEDR NER; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
