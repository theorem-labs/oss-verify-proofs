(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_red.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_journey A_mpi_grow A_mpi_core_mla A_mpi_core_add A_ecp_red_lib.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA LxSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt LxAEcpSums.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 TacA.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02536f06d38d25ce 1 1 4 1 0 1 3 80 1 103 1 115 1P02c32ef9420d4db1 0 2 0 1 4 1P02eaac66c8288693 1 1 4 1 0 1 2 88 1 100 1P039297b9256752f6 1 2 16 2 0 1 96 1 16 2 52 1 97 1 2 98 1 99 1P03a5aec369b6ed7b 0 4 0 1 116 1 139 1 140 1P03cff4a8fd48edd2 1 2 16 2 0 1 87 1 16 3 42 1 76 4 86 1 2 88 1 89 1P0409745517f754ae 1 2 16 2 0 1 102 1 16 2 60 1 103 1 2 104 1 105 1P04198ed48372e017 0 2 0 1 76 4P04511aae19569aac 1 1 4 1 0 1 3 66 1 89 1 99 1P04d38033210da849 2 99 1 1 8 3 2 1 137 1 140 1 4 0 2 138 2 139 2 141 16 1 1 8 3 1 1 138 1 139 1 5 0 1 127 4 137 1 140 1 141 8P055ad73a98ac429a 0 2 0 1 4 1P055be3e9d04372d2 0 2 0 1 4 1P055f5c0ff06084f0 1 1 16 2 0 1 96 1 4 49 1 83 4 95 1 97 16P0587fb03610b741d 1 1 4 1 0 1 2 101 1 111 1P05cb0824ae68173e 1 2 16 2 0 1 95 1 16 2 51 1 96 1 2 97 1 98 1P065bb5869c243a69 0 2 0 1 3 1P066b660dc0504a50 1 1 4 1 0 1 2 83 1 95 1P06923e3a37d84af5 0 3 0 1 102 1 125 1P06a937f4b4921f1b 0 2 0 1 1 1P078d573d05236382 1 1 4 1 0 1 2 85 1 97 1P07e10e49666b6cf4 0 6 0 1 105 1 124 1 128 1 139 1 140 1P080bccc17190379a 1 1 4 1 0 1 2 91 1 103 1P08fc3c81c3479a76 1 1 16 3 40 1 74 4 84 1 3 0 1 85 1 86 16P090eff07fc8cc078 1 1 4 1 0 1 2 84 1 96 1P094ec0c7b165126c 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P0950c279ade39156 1 1 4 1 0 1 2 123 1 133 1P096616fd08390e67 0 7 0 1 95 1 115 1 124 1 128 4 142 1 143 1P09ada8c0ad3e05a7 0 2 0 1 4 1P09eaa0ce9e93a089 1 1 16 2 0 1 116 1 4 69 1 103 4 115 1 117 16P0a336ad91b1c91dd 1 1 4 1 0 1 2 125 1 135 1P0a56296fd38cfd15 0 8 0 1 20 1 22 1 24 1 26 1 27 1 29 1 31 1P0a853a4418735cf3 1 1 4 1 0 1 2 125 1 135 1P0a9817b8b22c3a79 0 12 0 16 94 16 105 16 114 16 123 16 124 16 127 64 128 16 139 16 140 16 141 16 142 16P0b22c14c8ede80cf 1 2 16 2 0 1 109 1 16 2 67 1 110 1 2 111 1 112 1P0b4a8bb5d3b7d1bc 0 2 0 1 4 1P0b59b8946c50ebb9 0 2 0 1 1 1P0b804b2a9adc95f6 0 4 1 1 2 1 141 1 142 1P0bcce09df4dba149 0 2 0 1 91 4P0c07764857154e45 0 2 0 1 2 1P0c1683f7ac81716f 1 1 4 1 0 1 2 123 1 133 1P0c7ef284a25d24cd 0 4 0 8 58 8 84 8 85 8P0ca44c468447b3f8 1 1 4 1 0 1 2 87 1 99 1P0d0370671210c848 0 2 0 1 4 1P0d083532a258e15f 1 2 16 2 0 1 97 1 16 2 55 1 98 1 2 99 1 100 1P0dad9de0716f5a3e 1 1 16 2 0 1 98 1 4 53 1 87 4 97 1 99 16P0db821eecf468657 1 2 16 2 0 1 95 1 16 2 51 1 96 1 2 97 1 98 1P0dd041bc366afb07 1 1 16 2 95 1 140 1 3 0 1 139 1 141 16P0df61c77ba2bc910 1 1 4 1 0 1 2 103 1 139 1P0e1f837c348d4621 0 6 0 1 105 1 124 1 128 1 139 1 140 1P0ebaf1236eb50b98 1 1 4 1 0 1 2 123 1 133 1P0f0386f4065a2d36 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P0f2b45a8a5636128 1 2 16 2 0 1 115 1 16 2 71 1 116 1 2 117 1 118 1P0f47182d368cff53 0 2 0 1 3 1P0f6471ae9659c4c9 0 2 0 1 81 4P0fd6c5325fc9879c 1 1 4 1 0 1 2 78 1 88 1P0fef711571e9d030 0 2 0 1 3 1P10a5fe9d08efa260 0 2 0 1 74 4P10aec85f41e679a8 0 12 0 16 94 16 105 16 114 16 123 16 124 16 127 64 128 16 139 16 140 16 141 16 142 16P10bf1f47be23b0c3 0 2 0 1 76 4P10e31ae0153deef3 1 2 16 3 0 1 137 1 138 1 16 3 1 1 136 1 139 1 2 140 1 141 1P1102e4876f57f2bc 1 1 4 1 0 1 2 74 1 84 1P114f519ade9e0258 1 1 4 1 0 1 3 68 1 91 1 103 1P121389a7d7fa209c 1 1 16 2 0 1 104 1 4 57 1 91 4 103 1 105 16P125185cc8e88b144 2 99 1 1 8 3 2 1 137 1 140 1 4 0 2 138 2 139 2 141 16 1 1 8 3 1 1 138 1 139 1 5 0 1 127 4 137 1 140 1 141 8P1290ead7946251da 0 3 0 1 102 1 125 1P12c8c6bfaa3172a5 0 3 0 1 102 1 125 1P138b6ac1cbe81787 1 2 16 3 0 1 137 1 138 1 16 3 1 1 136 1 139 1 2 140 1 141 1P140f70b88e647cb5 1 1 8 3 1 1 141 1 144 1 4 2 2 142 2 143 2 145 16P14b8a2a5ab2f519c 1 1 4 1 0 1 3 74 1 97 1 107 1P14c5ede2137a7202 0 2 0 1 1 1P1511e37156662c1a 1 1 4 1 0 1 2 95 1 107 1P15230510243b0be6 0 2 0 1 4 1P156250e50db34098 1 2 16 2 0 1 103 1 16 2 59 1 104 1 2 105 1 106 1P15930ab882dd4e42 0 2 0 1 4 1P15e35f6aab067f1e 1 1 16 3 0 1 141 1 142 1 10 95 1 106 1 115 1 124 1 125 1 128 4 129 1 140 1 143 1 144 16P1614732afc34d271 1 1 8 2 0 1 84 1 3 1 1 85 1 86 8P16be854cd3b2067e 0 2 0 1 87 4P16c512ab94d509dc 0 12 0 4294967296 13 4294967296 16 4294967296 18 4294967296 19 4294967297 21 4294967297 23 4294967297 25 1 28 4294967297 30 1 32 1 118 1P16eb86a8ddaa0b37 0 8 0 1 19 1 21 1 23 1 25 1 28 1 30 1 32 1P16f9bbc7a4853c07 0 2 0 1 87 4P170aed48771ef3ac 1 1 4 1 0 1 2 125 1 135 1P172a547391d7b9ea 1 1 16 3 0 1 140 1 141 1 10 94 1 105 1 114 1 123 1 124 1 127 4 128 1 139 1 142 1 143 16P176d1cda60852f84 0 2 0 1 95 4P178444ca1b255268 0 2 0 1 3 1P17900c8ec55ff075 0 2 0 1 123 1P17fec65468d0948b 1 2 16 2 0 1 92 1 16 2 50 1 93 1 2 94 1 95 1P181935714820ab73 1 1 4 1 0 1 2 81 1 93 1P181d4dd5ea80b942 0 2 0 1 4 1P184b999d28ac12a3 0 7 0 1 95 1 115 1 124 1 128 4 142 1 143 1P1876ba31b83fd4a7 0 12 0 16 47 16 58 16 67 16 76 16 77 16 80 64 81 16 90 16 91 16 92 16 93 16P18938af70a20f4fa 1 1 4 1 0 1 3 82 1 105 1 115 1P1900ba0f66d33e94 0 5 0 1 93 1 104 4 142 1 143 1P1911177ae233f30b 1 1 4 1 0 1 2 99 1 111 1P192730d7c5c48144 0 2 0 1 103 4P193cd674a881c99f 0 3 0 1 100 1 123 1P195c5aae49cb74a9 0 2 0 1 2 1P198eeaa5bb8fc2b0 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P19bffe4b0952aeab 0 2 0 1 3 1P19c13a2966b3a352 1 1 4 1 0 1 2 96 1 108 1P19e68038f5d4305f 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P1a3b9c4dfa652ea8 1 1 4 1 0 1 2 105 1 115 1P1a5fb0b77f6af09e 0 2 0 1 3 1P1aa7b2fe0d63e883 1 1 16 2 1 1 141 1 4 94 1 128 4 140 1 142 16P1acdda74f79805c3 0 2 0 1 83 4P1afa265d13d885f3 0 2 0 1 135 1P1aff2eeebfd0ff0c 0 2 0 1 4 1P1b2eab10cdb42a51 0 2 0 1 1 1P1b7fd956463bd8cc 0 7 0 1 94 1 114 1 123 1 127 4 139 1 140 1P1bc068ba377b4956 2 96 1 1 8 3 2 1 135 1 138 1 4 0 2 136 2 137 2 139 16 1 1 8 3 1 1 136 1 137 1 5 0 1 125 4 135 1 138 1 139 8P1bf824019c6373e7 2 99 1 1 8 3 2 1 137 1 140 1 4 0 2 138 2 139 2 141 16 1 1 8 3 1 1 138 1 139 1 5 0 1 127 4 137 1 140 1 141 8P1c468802db632e91 1 1 4 1 0 1 2 125 1 135 1P1cc0b560446f3150 1 1 4 1 0 1 2 125 1 135 1P1cdea97c1d72c590 0 12 0 4294967296 14 4294967296 15 4294967296 17 4294967296 20 4294967297 22 4294967297 24 4294967297 26 1 27 4294967297 29 1 31 1 117 1P1d1fbf2ae4422730 0 3 0 1 104 4 127 4P1dc80abc86938a65 1 1 16 2 0 1 104 1 4 57 1 91 4 103 1 105 16P1e0a23bd10ae11ef 1 1 4 1 0 1 2 125 1 135 1P1e9cdaeccc53786f 0 2 0 1 95 4P1eae18fe74047a87 0 3 0 1 4 1 12 1P1ec1078d73cdebdc 0 5 0 16 65 16 99 64 111 16 112 16P1ed181c45908925f 0 2 0 1 135 1P1eda8292a1075db4 0 2 0 1 99 4P1f32bcb044cb43e9 1 1 4 1 0 1 3 58 1 81 1 93 1P1f724bd338c3bd41 0 2 0 1 4 1P1f8c71ea93843738 0 2 0 1 87 4P2024917f7c39c7fd 1 2 16 2 0 1 108 1 16 2 64 1 109 1 2 110 1 111 1P20382d2622eba9f9 1 1 16 2 0 1 114 1 4 69 1 103 4 113 1 115 16P2069a88ad1926654 0 2 0 1 3 1P2070588b5c556f5b 0 2 0 1 4 1P2072969916450197 0 2 0 1 4 1P20b84ef0304a1f47 1 2 16 2 0 1 107 1 16 2 63 1 108 1 2 109 1 110 1P21118323540b6265 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P218403bda6b400ee 2 96 1 1 8 3 2 1 135 1 138 1 4 0 2 136 2 137 2 139 16 1 1 8 3 1 1 136 1 137 1 5 0 1 125 4 135 1 138 1 139 8P21ac9262a43de32f 1 1 4 1 0 1 2 74 1 84 1P21df5f5f7a67c0a6 1 1 4 1 0 1 3 64 1 87 1 99 1P2241105e66689dd8 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P224d33058102e90f 1 1 4 1 0 1 3 62 1 85 1 97 1P2275fb48905c3d5c 0 2 0 1 99 4P234e7f6cfac96517 0 2 0 1 3 1P2409f45524c8d751 0 2 0 1 103 4P2455b40c75a0728e 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P24b28a31e40812ea 0 2 0 1 4 1P24fb6627adeceaf3 2 96 1 1 8 3 2 1 135 1 138 1 4 0 2 136 2 137 2 139 16 1 1 8 3 1 1 136 1 137 1 5 0 1 125 4 135 1 138 1 139 8P24ff5054df6c3fcd 1 2 16 2 0 1 110 1 16 2 68 1 111 1 2 112 1 113 1P25a9b86a5bcd4481 1 1 4 1 0 1 2 103 1 115 1P25aa1e2f20da569c 0 3 0 1 102 1 125 1P25d7ec37e3b5ea10 0 6 0 1 105 1 124 1 128 1 139 1 140 1P25e239f049fc69f7 1 1 4 1 0 1 2 87 1 99 1P2639dcafbe882b1f 0 7 0 1 94 1 114 1 123 1 127 4 139 1 140 1P265e5f9ca1b25b27 0 2 0 1 4 1P26d3d57c75482730 1 2 16 2 0 1 111 1 16 2 67 1 112 1 2 113 1 114 1P26ed7de835194bb2 1 1 4 1 0 1 3 70 1 93 1 105 1P27159d604d7bf247 1 1 16 2 0 1 106 1 4 61 1 95 4 105 1 107 16P271ca6a4d20de414 1 1 4 1 0 1 2 123 1 133 1P276b73cd59f9b0cc 1 1 4 1 0 1 2 99 1 111 1P27966d5da8fdaed7 1 1 16 2 0 1 84 1 3 6 1 85 1 86 16P2832eb97dcbc7b35 0 2 0 1 83 4P2852340e586c960c 1 2 16 3 0 1 135 1 136 1 16 3 1 1 134 1 137 1 2 138 1 139 1P2868b2979bd7e5e6 1 2 16 2 0 1 103 1 16 2 59 1 104 1 2 105 1 106 1P2889557f9463c753 1 1 4 1 0 1 2 89 1 99 1P28983665d25c69bb 1 2 16 2 0 1 113 1 16 2 71 1 114 1 2 115 1 116 1P2906dd00e1db14cc 1 1 4294967296 1 0 1 2 2 1 123 1P2942733b37e2ce42 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P29693294694a1925 1 1 16 3 40 1 74 4 84 1 3 0 1 85 1 86 16P2972e70b92e9601a 0 5 0 1 102 1 120 1 139 1 140 1P29ef398aad28f4b2 1 1 4 1 0 1 2 125 1 135 1P2a7f98b7c132393e 1 1 4 1 0 1 2 91 1 103 1P2a82854ba73eea3d 1 1 4 1 0 1 2 97 1 107 1P2abdb650089791f7 0 2 0 1 136 1P2aee8bdaf2dac752 0 5 0 1 102 1 120 1 139 1 140 1P2b015ffe5b5e108e 1 1 4 1 0 1 2 104 1 114 1P2b1abf01f4ebc4b2 0 2 0 1 2 1P2bab967ffda266bd 1 1 4 1 0 1 3 72 1 95 1 107 1P2bde67f7aca5febb 0 2 0 1 1 1P2c97e38bf2161026 1 1 4 1 0 1 3 104 1 127 1 139 1P2ca2a2a73011bff4 0 2 0 1 103 1P2ce71cdf4e0cb4ef 1 1 16 2 0 1 108 1 4 61 1 95 4 107 1 109 16P2d04c2fa4bc270d8 0 3 0 1 100 1 123 1P2d6e81f2df078bdb 0 2 0 1 1 1P2d9f6dc2712e21f7 1 1 4 1 0 1 2 107 1 119 1P2dd9c7005498e0c2 0 2 0 1 3 1P2e01693b8a75cdb3 0 2 0 1 95 4P2e0ae27bf1176420 1 2 16 2 0 1 93 1 16 2 49 1 94 1 2 95 1 96 1P2e26ae438cde0a81 0 2 0 1 4 1P2e7658e31e1b5f19 1 1 4 1 0 1 3 84 1 107 1 119 1P2ea360284c29cd4b 1 1 4 1 0 1 2 123 1 133 1P2ec63ebd804320cf 1 1 16 2 0 1 100 1 4 53 1 87 4 99 1 101 16P2ef2ba018e967990 0 2 0 1 136 1P2efec6dd88ac36f8 0 2 0 1 4 1P2f213751f3ffd2e5 1 2 16 2 0 1 118 1 16 2 76 1 119 1 2 120 1 121 1P2fb25466bb56c42e 1 1 4 1 0 1 2 95 1 107 1P2fb8964a5459f3f1 1 1 4 1 0 1 2 127 1 139 1P2fc139d986c0eb04 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P30072646e2596ee0 1 1 4 1 0 1 2 93 1 105 1P3049789bd3cb8c4f 0 6 0 1 105 1 108 1 128 1 139 1 140 1P30b26a142b885200 1 1 4 1 0 1 3 55 1 78 1 88 1P30b9788a5965a98a 1 1 4 1 0 1 3 78 1 101 1 111 1P30ca879e8d1684fd 0 2 0 1 4 1P30e3172a964bfb26 0 5 0 16 49 16 83 64 95 16 96 16P313dbc4f6f9b2404 1 1 4 1 0 1 2 92 1 102 1P31a6f2c73dcf1415 1 1 16 2 0 1 94 1 4 47 1 81 4 93 1 95 16P31e48c719de94248 1 1 4294967296 1 0 1 3 4 1 12 1 131 1P322d42b405d65cbe 2 99 1 1 8 3 2 1 137 1 140 1 4 0 2 138 2 139 2 141 16 1 1 8 3 1 1 138 1 139 1 5 0 1 127 4 137 1 140 1 141 8P323ed4fd38045487 1 1 16 2 0 1 110 1 4 65 1 99 4 109 1 111 16P33332aaf45257d1a 0 2 0 1 135 1P333569bc75e79e7a 0 3 0 1 100 1 123 1P337f7a16c422dc9a 0 3 0 1 104 4 127 4P33e4882fb596eecb 1 1 4 1 0 1 2 127 1 139 1P342302ca82f8d4c2 1 2 16 3 0 1 135 1 136 1 16 3 1 1 134 1 137 1 2 138 1 139 1P346e919d9577bfee 1 1 4 1 0 1 2 83 1 95 1P3475b3ff84cbaa48 0 6 0 1 105 1 124 1 128 1 139 1 140 1P34878a3d065bdf27 0 12 0 16 48 16 59 16 68 16 77 16 78 16 81 64 82 16 91 16 92 16 93 16 94 16P34af4d880881b6c1 1 2 16 2 0 1 139 1 16 2 55 1 140 1 2 141 1 142 1P34b09d24df48f1f5 1 2 16 2 0 1 114 1 16 2 72 1 115 1 2 116 1 117 1P34cec31d04e6a6b7 0 2 0 1 4 1P353fb6da39213b29 1 1 4 1 0 1 2 82 1 92 1P358f0ccaf01fbc7b 0 2 0 1 123 1P3645a3fc4432ed95 0 2 0 1 3 1P368768727b1d2685 0 2 0 1 91 4P36988c270cd3f221 0 2 0 1 104 1P375050ffaabad201 1 1 4 1 0 1 2 123 1 133 1P37526b2226d5c233 0 2 0 1 3 1P3762e0f65a051a98 0 2 0 1 103 4P377e3009655ea055 1 2 16 2 0 1 99 1 16 2 55 1 100 1 2 101 1 102 1P37df790c83cb13e2 0 2 0 1 1 1P38002e5a5faebbc7 0 2 0 1 1 1P385aad5905a8c4f8 1 1 4 1 0 1 2 123 1 133 1P385e28d9d9d15c43 0 2 0 1 4 1P387596cc18b0267b 0 2 0 1 3 1P3875d8f301b11e43 1 1 4 1 0 1 2 100 1 110 1P38c8fefcce0ace95 0 2 0 1 4 1P3971489cda801c67 0 2 0 1 91 4P39a77875ea8f9881 1 1 16 2 0 1 86 1 3 8 1 87 1 88 16P39d05e7cfb7b3a44 1 1 16 3 0 1 141 1 142 1 10 95 1 106 1 115 1 124 1 125 1 128 4 129 1 140 1 143 1 144 16P39d5c99fe6d4199c 1 1 4 1 0 1 2 123 1 133 1P3a0404dae4499eca 1 1 4 1 0 1 3 76 1 99 1 111 1P3a158315b47564e3 0 4 0 16 54 16 139 16 140 16P3a4ebb5702ae492b 1 1 16 3 0 1 135 1 136 1 10 91 1 102 1 111 1 120 1 121 1 124 4 125 1 134 1 137 1 138 16P3a57622e877ce2fe 0 2 0 1 81 4P3a93128c422bfb1f 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P3a9db021cbc31a41 1 1 4 1 0 1 2 108 1 118 1P3afc295b419b588a 0 2 0 1 83 4P3b0d687f7bbe8b36 1 1 4 1 0 1 3 60 1 83 1 95 1P3b145e856b9d56e9 0 5 0 16 93 16 103 64 139 16 140 16P3b5f9f0d9b015da2 1 1 4 1 0 1 2 74 1 84 1P3b92f5097c18f34f 0 2 0 1 74 4P3ba284f35c5806c6 0 2 0 1 3 1P3bae14713aacd101 1 2 16 2 0 1 100 1 16 2 56 1 101 1 2 102 1 103 1P3bc128d5eb6f8185 0 2 0 1 3 1P3be1b26aae4b0610 0 2 0 1 3 1P3c1d869c29eb6c19 0 2 0 1 3 1P3c3c16d37ba9a0a5 0 2 0 1 4 1P3c4671be1dbd61c1 1 1 16 2 0 1 84 1 3 6 1 85 1 86 16P3c79cbad57cb32d8 2 96 1 1 8 3 2 1 135 1 138 1 4 0 2 136 2 137 2 139 16 1 1 8 3 1 1 136 1 137 1 5 0 1 125 4 135 1 138 1 139 8P3cb996df72fe8204 0 3 0 1 100 1 123 1P3d2c3428f062798e 1 1 4 1 0 1 3 51 1 74 1 84 1P3d3537df28f71644 0 2 0 1 4 1P3d75054e4c6c8f35 0 2 0 1 4 1P3d7dd42b18eef777 1 2 16 2 0 1 105 1 16 2 63 1 106 1 2 107 1 108 1P3d9d1d5e0df757d4 0 2 0 1 99 4P3dee8e7507a21399 1 1 4 1 0 1 2 125 1 135 1P3e20628e5eca2e55 1 1 8 3 0 1 141 1 144 1 4 2 1 142 1 143 1 145 8P3e9ef387d91d3fa6 1 1 16 3 0 1 137 1 138 1 10 93 1 104 1 113 1 122 1 123 1 126 4 127 1 136 1 139 1 140 16P3f6b138fadcdbd2f 1 1 8 3 0 1 142 1 143 1 5 2 1 129 4 141 1 144 1 145 8P3ff449f4caf885fe 1 1 4 1 0 1 2 103 1 115 1N000a9b1677395fecN001dd0dde454e882N0035ab4b27a7eaaeN0072f3680e85b2f0N00c40711e3ba636eN00c93fc8a7c8de45N00ea4f8b932d6aecN00ee3bbe3c567491N00f1564d54cdf429N00f4fe29b3fc9613N0104dd49b0ab72caN011247f175a41b04N0117687869a267b2N01e8cd0f6b85fa45N01ee07a8107d307dN0211201e724112d9N0213bc27393f563bN023d29791a22ad00N02766ffa829a8e45N02805eaaacc7192cN028274a1ee4fa3f5N02b95b9ace92e502N02c49d9f44cd2218N03546bfe194f441bN03cae3b92a4dd7f2N03d8e0d7991b36f4N04623648708c5f10N04967e4a88d9a695N04e23ee8f4b5b1dfN053d91ee42cd44daN0551440d1e5d3c5aN056f1a404eef4f75N0579bc9622eb4083N05877989a612fe41N059499347de86db4N05a56683c015db1eN05b2a2a0b89c6f30N061258437db5c998N06261f1e90898378N06fc8778853385eaN070d94ae5d6d77b1N074e53a3f9a31a22N07680c0cb4fbbf40N076ab72a0aff540aN07ae7e97007fc3efN07ddef9468651807N07f01d49ff59f625N08393db4ce993fecN08b930aada355300N08d4bdc2987c900bN091a0b8e98c0eff3N0924b1c1540846efN0929733f117b0429N09371abbb0103834N0a205e2fa832f7a6N0a78a4253b4ab3a2N0aade00c3a731d90N0aea9e218ef6335cN0b0c6813ef16613aN0b85b6a463299d97N0ba4aee8f67e6e19N0bb5700ff30deda4N0becacf1de87d22eN0bfe5462e2924d95N0c0b2e2be6fe10e7N0c2a413b7914e4c6N0c359cbbb54e7de8N0c368de269f4e690N0c7ccca1953ab60eN0c9f78340f36195aN0d00fbdef2191d71N0d0abcb581270316N0d4987abaa86a256N0d6b28751477adf9N0dad1d2e87e66aa5N0dbb4a73b6dc9816N0e0361d765fad024N0e0cfab84ab2afc6N0e42f5c2ddb8f075N0ef35259022eb583N0efd6d4d2c75b7cdN0f265d952d2abcb3N0f31d808f11b9252N0f50233202ba21e8N0f67d3d637affaf1N0fb02f37312c57c5N0fedc02bb93ebdd9N103f5f6c4ca1fdcfN105351d752ded422N10b87d394579500aN10d50e2a40d2f195N1101b31b5fe8fd92N110d70cddb1466a1N1165a5974e882c75N11cec611a0cc194bN1201a576fae171f0N120658f7e2658e2aN12067e7d8e45c27eN121dcd23dbc013b2N12696e8de1aa818bN12dc60396fe1ff35N12f620b785de519bN13b384dc98368411N13ead14b1a804b57N14147c68ac8486d9N14390bd769edb99aN1482b1012c0f9733N14a2a51fca009559N14aff5bc948ba3b9N151265ad9cbee2bbN1554045fbd621f41N15568ff3f648a503N1563d08ba5c55ce6N158aeff16e01b2e8N15e213e60433b059N15f88576a14dff5cN161d32b69c192890N163ff2254ca1bc99N169a607fa8a906a2N16b05317108806b5N175d29d090094406N1760b33cfc4a2e66N17b1ce2161d3c90cN17ccfdca6e8866e4N17e5890c2588f6e2N181e35a3ad9661d8N182a2d4f275928e0N188a9caba9075a9fN188f9f804a3a397dN1927fbf1c1573fefN1952909f2c481e81N195dce37ef51ca52N19cb775d4aa27ea6N1a37ddd23cdff70dN1a530b749c69d23dN1a73c075ae11b53dN1a82a2fa3ad8e911N1aa1147f6302918eN1aaa360e3ebf631bN1b11e7efc61867d2N1b6373bfd982888eN1bb690043afc4761N1bd7b535e392a041N1bea573108164aa7N1c455705afa67d05N1c56f680aad1ebc0N1c5fcb49efa43a01N1cda4483d94f3517N1ce2e2554b783d69N1d4fe3dd79ff2618N1d6c1b2331c9b035N1d70f9c1a611b854N1ddb987c768b2a34N1e086e571183de37N1e45fdddd4d54f12N1e684817a9341a0aN1e8e42ef0de870a2N1ed6fdf1cf2e3101N1eebea46fe9f5296N1f4fde6a8c742025N1fb631a0691bfc66N1ff712eccae25425N1ffd8da364616655N2005887380f3bed3N2011800b7137be6fN2042065a729b0a3aN204b52e99fb5364bN209221011f5f43ebN20ef20a4cb9f5c9eN20f5a9a03753c0feN2135cd079dd116bbN21d35c83f7c96882N21e6428127c13b40N222a5a5ae46d204cN22ba542206ffe8b1N2323d83618d90037N2349759ba8a9b9c4N2355a3ae9cafb6abN2369a498b1fa8d6cN23f1e9ff01318d0bN2411edb7f3a7f289N2417bd3a5044578cN242ef73123c2253dN244cae1191824ec2N247b36ce93725e60N248e35b3fd8d25edN24969f9f1c04e7edN25200fa17fbac504N2531f75e227d6191N25a7e984c7f9a4f7N25f6e6e217725c42N260ac4b342970b3dN260fa370ba2ada03N262e9f7003ee69c6N2639c491d27808c9N263d43f793349812N26bc3635f1e83e4cN26d739484cffb99cN26ea7a400bde0f6bN26fa3f697b3ca954N27f69e2ac0367ee2N27fd252670127007N286a1d641a8a14c4N289e03d1e1c67bb9N28d8a69c646a9b4dN290af5e1c45c8b26N29239c8c56a9536bN2956d80ee1fc16c2N2978c42c4bfa26cbN299ca8de2cfdc8dcN29e01c6fa92e1a50N29ffca77e6d5d65aN2a18514911f8218dN2a4d4acf4f9dad05N2a920526ac30dcd4N2b024aed36e6cfe7N2b37e73c2aa7c9e3N2b44c6b95ad92aaeN2b5dab43d400e6a7N2b7d2c31314b5ea6N2baaadeae062e1beN2be188fe90232100N2c04712e6f7ec7bbN2c3d752a256183aaN2c55255e50e69bacN2c82ed8879a0f6b9N2d115cf093417893N2d72029cc1840476N2db07875b5af8566N2de0cc1db4d40db7N2e2cc97790f9d884N2e39a397388c14a7N2e7a0c41cc80cd2aN2ec7b7af5e5a88dbN2eeeeb70c4fbbb66N2fcdb7b8392faa37N2fcf764cc2709593N3045f6f26241810fN30480871079004d3N30685258e45377a7N30fdc88f8ae035faN311ffd296913ff67N314d9c2b1c3d6d60N315aa039ce76aefdN31820086f116fb80N319795cd49bf82e9N32aac854e73e0605N32f12af25716c540N33180f69fa7a619eN332617a64f291186N334328ede1797616N335e5b077bce5603N336b5b4add9b3484N3373a291bc46a4fbN33951be626d4a609N33e025360d28c113N340e2ddb7e02f26cN341d3a306870c993N342048563479bd98N343e4c67eaaa3e96N3498dff8bc327bbfN34a11f6b51aadcd4N35072ba4f937c111N351d71fca987070fN3560859c867b052dN3572143571d74c18N3575ed8cf4ff34d0N35a2118ffa8ded84N35cf6e8b67e3a540N35ed8217eb4a13b0N35eeb195200ceb66N36040678672c126dN360e3226b3845a2aN363b076608e25a43N366f9030bf8d18f1N36b707b614d28321N36e22ad47cff5959N370b051749d9975dN3715cb12a86092ffN3718d0cd5afaa78cN37278865100711acN37285b7eec9699d5N375075074779f44fN37561868bdab6713N376ea131b682d52eN377e861db6dc9f30N388931bde10e9a86N38ae1bda1b6d75a9N38e1da705b805a7eN391c2a58c4a014fcN39e315bb65fb354fN39fb91c54f83936eN3a1c2ad042d567a7N3a2f0c706cfdaf7bN3a48380c40de9c1aN3a9897e32d3bfd0aN3ae4bfd2aedbf177N3b14dd79cbd7bdafN3b86e1e8a6785d5eN3b8765470eb2d885N3be0d065ab8e1822N3c4d7f1b4afd5d44N3cb17857d5c55a01N3d0950e02aa14046N3d1d23457a19cea8N3d565bfef6403eaeN3de318a8242a1d38N3df22fc07ec880bcN3e92bfda81058b5cN3e9e276a05493771N3eb7eb95eb3b3ba5N3f2092d4bda6cb5cN3f32f7421723ff92N3f4bd7f83d6e6e71N3fa27d3c69985193N3fab2628f69fcfdaN3fb0fe20b4012ceb"%lxh.
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
Ltac2 gd_tbl_A_ecp_mod_p256 () : Init.string Init.list := ["OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_ecp_red.reducer_R"; "OSSVerify.KrLib.A.A_mpi_stmtA.grow_PHI"; "OSSVerify.KrLib.A.A_ecp_stmtA.red_FRn"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "RED.RFRAME"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "RED.RPOST"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "A_ECP_MOD_P256"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_GROW"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_ecp_red_lib.A_ASAN_MEMSET_EC"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibA.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_reducer_stmtA"].


Definition A_ECP_MOD_P256 : Z := 0xd22b8.   (* [comment removed for export] *)

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
  Definition RFRAME : list cell := [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 72 RFRAME.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + grow_PHI 16 <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + red_FRn d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_RED <= C24MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - arl_need_ecp R.

  Definition RPOST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p256 ()) "(0.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(3.+10.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)(4.+10.)(5.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 72 RFRAME []).
  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@L11518786483.137L12561043416.137L1860589272.137 L29428324939.5  L35559589539.1  L35663928186.7  L44590266200.137L48151489112.137L51728444760.137L53544459352.137L5422860760.137 L60098763854.3  L65018332548.1  L9000864984.137 Q15643598972.136Q18366170748.136Q21879891999.136Q27585188988.136Q27906956191.136Q30415318815.136Q31271277308.136Q32655747964.136Q33918012703.136Q36425601695.136Q3830178207.136 Q39939305631.136Q41152143740.136Q44648563964.136Q51235551740.136Q59842863100.136Q66521824799.136Q9843086111.136 00000700>00E00W00[01001701>01E01L01S01]01a01h01o02602N02U02m03E03L03S03k04C04[05305:05A05H05O05g06?S2ra2spS2ra2spS2ra2spS1R2lo3LOS3ALO3ACPS2spS1R3HIA1h2sp2lo3TOP1HS2ra2spS2ra2spS2ra2spS2ra2spS2ra2spS1R2lo3LOSS2spS2ra2spS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2sp2loS2sp2loS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  Lemma r_ret : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p256 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pr,$6.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs0,(:.&40.)Pxs1,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxs4,(:.&40.)Pxs5,(:.&40.)Pxs6,(:.&40.)Pxs7,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+48.$>.(?.$9.)R1>.R1=.R1<.R1;.R1:.R19.)P,(3.+10.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R19.R1:.)P,(10.R20.(4.+10.))P,(10.R20.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R20.Vmo,)$13.(14.(15.R1;.(16.&40.(17.(18.&40.Vsp,)-50.))Vgp,Vtp,R1:.R19.R18.R17.R16.(16.&40.R1<.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.+=26=0.)Vfc,(19.(:.&40.))R1>.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 72) with (bv_unsigned sp + -72) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    do 9 zstep.
    zstep.
    replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold RPOST.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 72 RFRAME JC); [exact J| exact HR| exact HK9| exact MF9| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@D24996680996.159D30200628036.158D42631060527.158D62022258533.159L13240751286.4  L23305025156.0  L23643762344.4  L2397676628.0   L26227934071.0  L28650703512.1  L2975768925.2   L29773195157.0  L35360615903.6  L35663928186.7  L42633816569.1  L46806116484.6  L56080884112.5  L57654672646.2  L60098763854.3  L60283674290.6  L64400777550.1  L65018332548.1  L9751400643.7   00000M00c01701M01Z01[01h01i01j01n02502602M02b02g03?03T03[03e04704;04?04WS1R3HIA2ra2sp1X3xs02hc3pXc2xsS2ra2sp1X3xs01N3pXc2xsS2ra2sp1X3xs03pXc2xsS1R2ra2sp1X3xs03pXc2xsS2sp1X2lo3DSXSS1X1N3pXc3XPcSSS2spS1N3pXcSS2sp2lo1N3pXc4LOSP4XLScS1R3HIA1h2sp2lo3TOP1HS3pXcS1R2sp2lo4SLO25NEEDR3NERS1N2xs4LEN14lxws4LENXS2sp2loS1R2lo3LOSS2sp2lo1N3pXc1a2NOS2spS2spS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  Lemma r_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p256 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxs4,(:.&40.)Pxs5,(:.&40.)Pxs6,(:.&40.)Pxs7,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+48.$>.(?.$9.)R1;.R1:.R19.R18.R17.R16.)P,(1;.$1<.(1=.R17.)$1>.)P,(10.+10.(1?.R18.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+10.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R1=.)(27.R1=.)(1?.R1=.)(28.R1=.)R4.(29.R1=.)(1=.R1=.)))P,(10.R1?.(4.+10.))P,(10.R1?.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1?.Vmo,)$13.(14.(15.R1;.(16.&40.(17.(18.&40.Vsp,)-50.))Vgp,Vtp,R1:.R19.R18.(16.&40.VX,)(16.&40.(2:.(2;.VR,)))(16.&40.=)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=22?<.)Vfc,(19.(:.&40.))R1=.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 72 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
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
    unfold RFRAME in FR1. replace (bv_unsigned sp - 72) with (bv_unsigned sp + -72) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -72) 8 ST1 ltac:(clear - SLO2 NER NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -72 - Z.of_nat 8) with (bv_unsigned sp + -80) in STc, SLOT by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as ABm. pose (lxi := lxA_img (arl_AL R) IMG).
    lx_pre. lxe_pose. lxe_sums [SUM_amemsetWinA 4 5] [pXc; N].
    lx_pre. lx_run_tac (PLANS [0xd26d0] [(0xd2308, DJoin); (0xd231c, DJoin); (0xd2334, DJoin); (0xd234c, DJoin); (0xd2364, DJoin); (0xd237c, DJoin); (0xd2394, DJoin); (0xd23ac, DJoin); (0xd23c4, DJoin); (0xd23dc, DJoin); (0xd23f4, DJoin); (0xd240c, DJoin); (0xd2424, DJoin); (0xd243c, DJoin); (0xd2454, DJoin); (0xd246c, DJoin); (0xd2484, DJoin)] 1000%N [SUM_amemsetWinA 4 5]). lx_tree.
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
      (* [comment removed for export] *)
      lazymatch type of SLOT with rw_cells _ _ ?a ?cs0 => let n := eval cbv in (length cs0) in
        lazymatch goal with H : rw_cells asegs ?mx a ?cs |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
          let n' := eval cbv in (length cs) in
          tryif constr_eq n n' then idtac else
           (rewrite <- (firstn_skipn n cs) in H; apply rw_cells_app in H; cbn [firstn skipn cells_size csize Nat.add] in H;
            let H2 := fresh "FRl" in (flat constr:(H) 2%nat; flclear H; intros H H2)) end end.
      flat constr:(J0box) 2%nat. flclear J0box. intros J0 _.
      (lazymatch goal with SL : rw_cells asegs ?mq (bv_unsigned sp + -80) ?cs , STq : stk asegs ?mq lo (bv_unsigned sp + -80) |- _ =>
          assert (STM : stk asegs mq lo (bv_unsigned sp - 72));
          [ eapply stk_merge; [exact STq| | clear - SLO2 NER NEEDR LOSP; lia];
            replace (bv_unsigned sp - 72) with (bv_unsigned sp + -80 + Z.of_nat (cells_size cs)) by (cbn; clear; lia);
            apply stk_of_rw_cells; exact SL | ] end).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
      assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 72).
      { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 72) by (clear - NO; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] (bv_unsigned sp - 72) 72).
      { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] X 16).
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
      (* [comment removed for export] *)
      lazymatch type of SLOT with rw_cells _ _ ?a ?cs0 => let n := eval cbv in (length cs0) in
        lazymatch goal with H : rw_cells asegs ?mx a ?cs |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
          let n' := eval cbv in (length cs) in
          tryif constr_eq n n' then idtac else
           (rewrite <- (firstn_skipn n cs) in H; apply rw_cells_app in H; cbn [firstn skipn cells_size csize Nat.add] in H;
            let H2 := fresh "FRl" in (flat constr:(H) 2%nat; flclear H; intros H H2)) end end.
      flat constr:(J0box) 2%nat. flclear J0box. intros J0 _.
      (lazymatch goal with SL : rw_cells asegs ?mq (bv_unsigned sp + -80) ?cs , STq : stk asegs ?mq lo (bv_unsigned sp + -80) |- _ =>
          assert (STM : stk asegs mq lo (bv_unsigned sp - 72));
          [ eapply stk_merge; [exact STq| | clear - SLO2 NER NEEDR LOSP; lia];
            replace (bv_unsigned sp - 72) with (bv_unsigned sp + -80 + Z.of_nat (cells_size cs)) by (cbn; clear; lia);
            apply stk_of_rw_cells; exact SL | ] end).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
      assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 72).
      { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 72) by (clear - NO; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] (bv_unsigned sp - 72) 72).
      { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -72)] X 16).
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01W0@D23777476479.151D3399625391.115 D3399625391.116 D35881667587.115D35881667587.116D39362881534.153D64007302964.154L1069357860.11  L13645206873.0  L14211003605.23 L15302269400.112L1645697276.7   L20000353974.1  L22446743512.112L25214214772.112L28270746970.2  L28703503462.9  L29010569984.154L31225147636.112L34705680216.112L35653441506.7  L37246946676.111L37742712464.154L3949578456.111 L40290687782.1  L40374333670.111L40834179097.118L41843875160.112L42243864115.23 L43059266230.109L44323821200.23 L49283344500.112L51454941784.112L5261871668.3   L55310518004.112L55428471946.0  L56000673578.0  L5699067096.112 L57818804596.112L58591023192.112L59308632561.1  L59411595710.2  L60098763854.3  L61321319284.112L62998051744.23 L63261865046.23 L63829069812.112L64400777550.1  L64491265552.2  L67280348888.112L67351568884.112L6935467336.1   L9751400643.6   L9751400643.7   P1071308334.154 P28277381200.153Q1071308334.154 Q15643324129.111Q17530203490.114Q17530203490.115Q18365925601.112Q18696506101.118Q21800401414.118Q21879645826.112Q25160350961.118Q25513505925.114Q25513505925.115Q25664719138.118Q26058579734.119Q26058645012.154Q27584944865.112Q27907200258.112Q28277381200.153Q30415036802.112Q31226872993.118Q31271525473.112Q31396957457.118Q32655500769.112Q33918256002.112Q35016271767.118Q35715139857.118Q36425882626.112Q3830427394.112 Q39939554818.112Q41152393185.112Q4141071397.118 Q44648843873.112Q45994268794.152Q45994268794.153Q49698585326.113Q49698585326.114Q51235796833.112Q5300226131.112 Q5300226131.113 Q53972118266.118Q59843137889.112Q61800308129.118Q6414620453.118 Q64253126389.118Q66522067074.112Q67528989526.115Q67528989526.116Q9843367298.111 00000100l02?02g03g04L05105205305C05P05j05n06;06H06I06i06j07707D07\07i08N08[08^08k09R09_0:50:]0:a0:n0;;0;E0;R0;S0;T0;a0;n0<;0<?0<B0<L0<Y0<l0=80=E0=I0=O0=\0=i0=m0>E0>]0>^0?[0?\0?g0@I0A@0AK0B20B30BC0Bj0CG0D90D:0EB0FJ0FU0Fe0Ff0G60G^0Gi0HI0HT0Hd0IL0IM0I]0Im0J=0JH0JI0JT0JU0JV0Jl0KB0KM0KX0Kc0LK0LV0LW0M>0M?0MO0N10Nh0O8FS1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2ra2sp2s02s12s22s32s42s52s62s71X3xs0S2ra2sp2s02s12s22s32s42s52s62s71X3xs0FSS1R3HIA1h2sp3TOPS2ra2sp1X3xs0S1X2sX2nX2pX3xs04padX4ownXS2spS2ra2sp1X3xs0S2ra2sp1X3xs0FS2sp1X2sX2nX2pX3xs04padX4ownX2XLFS2ra2sp1X3xs0S2ra2sp1X3xs0S1R3HIA1h2sp2lo3TOP4HTOPS2ra2sp1X3xs0S2ra2sp2s02s12s22s32s42s52s62s71X3xs0S2ra2sp1X3xs0S1XS2ra2sp1X3xs0S1R2ra2sp2s02s12s22s32s42s52s62s71X3xs0S2ra2sp1X3xs0S1R2sp2lo4SLO23NER3SPRS1R2ra2sp1X3xs02lo4SLO25NEEDR2X03NER3SPRS2spS2ra2sp1X3xs0S2ra2sp1X3xs0S1X2X03X16S2ra2sp1X3xs0SSS2ra2sp1X3xs0S2ra2sp1X3xs0S2ra2sp1X3xs0S2KRS1dS1R2lo3LOSS2ra2sp1X3xs0S1R3HIA1h2sp1d4BUDFS2sp3SPA3SPRS2ra2sp1X3xs0S2spS1d2D0S2ra2sp1X3xs0S2ra2sp1X3xs0S2spS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERFS1R2ra2sp2s02s12s22s32s42s52s62s71X3xs02lo4SLO25NEEDR3DSX3NERFS2sp3xs02loS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp3xs02loS1R2ra2s02s12s22s32s42s52s62s73xs04IMG'FS2sp3xs02lo4LOSPS1R2ra2s02s12s22s32s42s52s62s73xs04IMG'S2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7FS1R2ra2sp2s02s12s22s32s42s52s62s73xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS1R2ra2sp2s02s12s22s32s42s52s62s73xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS2sp3xs02loS2sp3xs02lo4LOSPFS2sp3xs02lo4LOSPS1R2ra2s02s12s22s32s42s52s62s73xs05ALWF'S2sp3xs02loS2ra2s02s12s22s32s42s52s62s73xs0S2sp3xs02loS2sp3xs02lo4LOSPS1R2ra2s02s12s22s32s42s52s62s73xs05ALWF'FS2sp3xs02lo4LOSPS2sp3xs02lo4LOSPS2sp3xs02lo4LOSPS2sp3xs02loFS2sp3xs02loFFS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stS2sp3xs02loS2sp3xs02HBS2sp3xs02HBS1R2ra2s02s12s22s32s42s52s62s73xs05ALWF'S2sp3xs02loFS1R2ra2s02s12s22s32s42s52s62s73xs04IMG'FS2sp3xs02lo4LOSPS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp3xs02lo4LOSP". (* [comment removed for export] *)
  Lemma r_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p256 ()) "Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)P,(2<.$1.VR,VHIA,Vh,Vmo,)P,(2=.$1.Vm,Vlo,(18.&40.Vsp,))P,(2>.$1.Vm,)P,(2?.$1.(2;.VR,)(30.$1.VR,VHIA,Vh,)Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(31.$1.$13.(32.(14.(15.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(16.&40.VX,)R?.R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.$33.)Vfc,(19.(:.&40.))Vm,(1:.$1.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK ST MI OXA. unfold A_ECP_MOD_P256.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 72 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    flat constr:(OXA) 2%nat. intros OX _. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold RFRAME in *.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -80) ([CB 8 jk] ++ RFRAME)) in FR end.
    apply rw_cells_app in FR. flat constr:(FR) 2%nat. flclear FR. intros SLOT FR. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp - 72) in FR by (clear; lia).
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 72)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NER NEEDR LOSP; lia].
      lazymatch type of SLOT with rw_cells _ _ _ ?cs => replace (bv_unsigned sp - 72) with (bv_unsigned sp + -80 + Z.of_nat (cells_size cs)) by (cbn; clear; lia) end.
      eapply stk_of_rw_cells. exact SLOT. }
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
      eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 16) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; try eassumption; try reflexivity.
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
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 72)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NER NEEDR LOSP; lia].
      lazymatch goal with SL : rw_cells asegs m2 (bv_unsigned sp + -80) ?cs |- _ => replace (bv_unsigned sp - 72) with (bv_unsigned sp + -80 + Z.of_nat (cells_size cs)) by (cbn; clear; lia);
        eapply stk_of_rw_cells; exact SL end. }
    pose proof (grow_R_keep _ _ _ _ _ _ GR OUT2) as BK.
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -80) (grow_PHI 16) (grow_FR d) J0 ltac:(clear - SLO2 NER NEEDR; lia)
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
      destruct (grow_ok_facts asegs m2 LB2 LB dX dX2 16 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia)) as (GO & GNN & _).
      eapply r_body; [exact J1| exact GO| rewrite GNN; clear; lia| | unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
      intros ws r Hr Hne.
      exact (reducer_R_ok 16 dX dX2 LB LB2 ws r asegs m2 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia) (conj Hr Hne)).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L22948286281.0L33824432691.600000100BSS1R2sp2lo3SLO3NER". (* [comment removed for export] *)
Lemma A_ecp_mod_p256_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p256 ()) "PR,$34.PHIA,(35.$1.R1.)P,(36.(2;.R2.))P,(37.$1.R3.R2.$38.)P,(1;.$6.(39.R4.)$3:.)P,(10.=(3;.R5.))P,Ph,(7.$1.R6.R5.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(:.&40.)(;.(:.&8.))P,(3<.$1.R:.R9.R4.R3.R2.R1.)(3=.$6.(3>.(3?.$6.$6.)$6.(40.$6.$6.)R4.))P,(20.(10.(41.(42.R7.))(43.(42.R7.)))(10.(44.(42.R7.))(45.(42.R7.))))P,Pa,$6.P,(1;.$46.(47.$1.(48.R1.))$49.)P,(20.(10.=R2.)(21.R2.(23.+2.+40.)))(20.(10.(41.(42.R;.))R3.)(21.R3.(45.(42.R;.))))(4:.$1.R9.R8.$33.+10.+;0.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG GROW AMS NEEDR HND DIMG ROIMG. unfold ecp_reducer_stmtA.
  intros until d. intros HH HK LFB MX NST XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  pose proof (arl_need_ecp_rt R) as NER.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 72 (RFRAME ra s0 s1 s2 s3 s4 s5 s6 s7)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR NER; lia. }
  eapply r_main; first [ exact JC | eassumption | eapply uwc_nonneg; exact UW | clear - SLO NEEDR NER; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
