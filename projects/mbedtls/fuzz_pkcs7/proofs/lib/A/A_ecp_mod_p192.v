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
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00073091849baaf8 0 2 0 1 153 1P002d85d853a8d515 0 4 0 1 2 1 143 1 145 1P0074da3e0bebdbba 0 3 0 1 20 1 127 1P00d9c29ea0ae7eb3 0 2 0 1 4 1P016db82238bd2425 1 1 4 1 0 1 2 84 1 94 1P018264b9038f35c6 0 2 0 1 1 1P0188c31735c86218 1 2 16 2 0 1 107 1 16 2 63 1 108 1 2 109 1 110 1P0193d328c1e0d81c 0 2 0 1 115 1P0245ff1934b85953 1 2 16 3 0 1 153 1 154 1 16 3 1 1 152 1 155 1 2 156 1 157 1P028e81f017ec2d5e 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P02aa62b0dbde3855 0 2 0 1 115 1P02c7bff34958b1ae 0 2 0 1 95 4P0304bf653d40917a 0 2 0 1 117 1P032d46e2784f8689 0 2 0 1 1 1P0336f5519a4ffd5d 0 2 0 1 115 1P03f10001ed6a91eb 0 5 0 1 120 1 138 1 155 1 156 1P0425c836ca50ed5f 0 7 0 1 112 1 132 1 141 1 145 4 155 1 156 1P0436253e2d87eee4 0 2 0 1 1 1P047516f3deb7a64e 0 3 0 1 131 1 133 1P047fa14f93cb0a1d 1 1 8 3 0 1 157 1 160 1 4 2 1 158 1 159 1 161 8P04c55dd4bd5ed926 0 3 0 1 113 1 115 1P052a499bec7c0753 1 1 4 1 0 1 2 81 1 91 1P054257f6671f7ebe 0 2 0 1 142 1P0562baaefe32e2df 0 2 0 1 4 1P058d8300ae944952 0 2 0 1 3 1P05980431084b3116 0 2 0 1 139 1P05bf90bfb8ab4018 0 2 0 1 126 1P05f2b68b6b4f45a4 1 1 8 2 0 1 84 1 3 1 1 85 1 86 8P06250fba4202a1e5 0 4 0 1 134 1 155 1 156 1P0677544440eaa287 0 2 0 1 133 1P067cc7ad19d7e96a 1 1 4 1 0 1 2 145 1 155 1P069774f4508ed130 0 3 0 1 4 1 28 1P069ac07163dc4359 0 2 0 1 1 1P06aa9b11e2348ad8 0 2 0 1 145 1P06df0f29ae002bf1 0 3 0 1 12 1 147 1P06e1d220d527b654 0 2 0 1 4 1P0713a9f16dc5f56f 0 2 0 1 81 4P071e369f8935f24a 1 1 4 1 0 1 2 91 1 103 1P0738fe7c2e48a769 0 2 0 1 2 1P076dcb2c44756dd9 0 2 0 1 147 1P0800d26c345723e9 0 2 0 1 137 1P0861006b523c678f 1 1 4 1 0 1 3 64 1 87 1 99 1P086e9134d5a422c2 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P08eb8090cc4e9a13 0 2 0 1 127 1P09315dc4e2b7e78b 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P093913abefd40000 0 6 0 1 123 1 142 1 146 1 155 1 156 1P0948bdb82c4c98c9 0 2 0 1 3 1P09846a680b44ded1 0 2 0 1 113 1P0a1a91bb024ae34c 0 2 0 1 2 1P0a4fbdbc4cec48b7 0 2 0 1 2 1P0a5d146101e3ad08 0 2 0 1 4 1P0a69c36dad47283a 0 2 0 1 3 1P0aa5510f90b99cff 0 2 0 1 4 1P0aadf826510bea5a 1 2 16 2 0 1 105 1 16 2 63 1 106 1 2 107 1 108 1P0ad1e3f8d4b74cfd 0 2 0 1 2 1P0adcf5856d64194a 0 3 0 1 2 1 131 1P0add3073500226d5 0 6 0 1 123 1 126 1 146 1 155 1 156 1P0b2b4c8b49d92813 0 2 0 1 4 1P0b4389aafca8078e 0 2 0 1 3 1P0b6b711bbe968cec 1 1 16 3 0 1 156 1 157 1 10 112 1 123 1 132 1 141 1 142 1 145 4 146 1 155 1 158 1 159 16P0b74f1c80d63b9d1 1 1 4 1 0 1 2 88 1 98 1P0bcd59616992ef65 0 2 0 1 76 4P0bd56d783a04d55c 0 3 0 1 121 1 123 1P0bee3355ad2cbd77 0 2 0 1 127 1P0cb35fe20b0df7f8 1 1 4 1 0 1 2 74 1 84 1P0cdd276c39931177 0 2 0 1 116 1P0cf551f6de294c1d 0 5 0 1 2 1 4 1 6 1 127 1P0d109d90bece3fe2 0 2 0 1 11 1P0d1cfa47df09f445 0 2 0 1 135 1P0d223a8d89054c2d 0 3 0 1 2 1 151 1P0d49461dbbc613e6 1 1 16 2 0 1 84 1 3 6 1 85 1 86 16P0d6f0ba0a4033ac4 0 2 0 1 147 1P0d93f2f78cefa934 1 1 4 1 0 1 2 95 1 107 1P0de7c0b63e9607f2 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P0dfbc7ae20236d5c 0 2 0 1 129 1P0e205f0fd2031895 1 2 16 2 0 1 102 1 16 2 60 1 103 1 2 104 1 105 1P0e668a77b6c6ec67 0 2 0 1 144 1P0e8cb0fa468c6e22 2 127 1 1 8 3 2 1 153 1 156 1 4 0 2 154 2 155 2 157 16 1 1 8 3 1 1 154 1 155 1 5 0 1 143 4 153 1 156 1 157 8P0ef0d9f23da63bca 0 2 0 1 121 1P0f6ac7f0c3a4a110 1 1 4 1 0 1 2 121 1 155 1P0fd8d8c286b695fc 0 3 0 1 2 1 153 1P0fdce32def481927 0 2 0 1 4 1P101c0aa1ccd6afc8 1 1 4 1 0 1 2 85 1 95 1P1028a55a7de5d8b4 0 2 0 1 3 1P10352cfcc7906979 0 2 0 1 12 1P10653552042d0b70 0 2 0 1 125 1P1090c7a9c6298b4e 0 2 0 1 4 1P10c154647565cf6f 1 2 16 2 0 1 93 1 16 2 49 1 94 1 2 95 1 96 1P11532b961d3d35ae 1 2 16 2 0 1 95 1 16 2 51 1 96 1 2 97 1 98 1P119cae759e8abc9b 0 2 0 1 139 1P11c1391176eafb10 0 2 0 1 1 1P11d1959fdab78784 0 2 0 1 127 1P11d295b17662a8e9 2 127 1 1 8 3 2 1 153 1 156 1 4 0 2 154 2 155 2 157 16 1 1 8 3 1 1 154 1 155 1 5 0 1 143 4 153 1 156 1 157 8P11f257eaa9911198 0 2 0 1 1 1P1210b98cd82d0f46 1 1 4 1 0 1 3 72 1 95 1 107 1P122862ac765a26b0 1 1 4 1 0 1 3 62 1 85 1 95 1P122af9d60a988909 0 2 0 1 3 1P1276999973200fb4 0 3 0 1 135 1 137 1P12948556cfb4647d 0 2 0 1 91 4P1315278ebeff840a 1 2 16 2 0 1 98 1 16 2 56 1 99 1 2 100 1 101 1P13178401beff9c1b 0 2 0 1 3 1P1351ede568558d72 1 1 4 1 0 1 2 95 1 107 1P13619f769f2a221b 0 2 0 1 145 1P1396bcf7b09a4cef 1 1 4 1 0 1 2 89 1 99 1P13b39800d4e8140a 1 1 4 1 0 1 2 78 1 88 1P13f9fa0ce2ac6422 0 4 0 16 72 16 155 16 156 16P1423ac3f770cd1fb 0 2 0 1 115 1P1429c992b89d7622 0 2 0 1 91 4P143dbf51c7078dbc 1 2 16 2 0 1 99 1 16 2 55 1 100 1 2 101 1 102 1P1464012df3d0e2f2 0 3 0 1 12 1 147 1P14844d45e9532988 0 2 0 1 4 1P14a1df9808b8b7f4 0 12 0 16 47 16 58 16 67 16 76 16 77 16 80 64 81 16 90 16 91 16 92 16 93 16P14b0896e06975117 0 2 0 1 87 4P14cc09cf3025573b 0 3 0 1 16 1 115 1P14dd3d51f0b570a3 2 127 1 1 8 3 2 1 153 1 156 1 4 0 2 154 2 155 2 157 16 1 1 8 3 1 1 154 1 155 1 5 0 1 143 4 153 1 156 1 157 8P159f170831ed7613 1 2 16 2 0 1 103 1 16 2 59 1 104 1 2 105 1 106 1P15a27507f0f64abe 0 7 0 1 113 1 133 1 142 1 146 4 158 1 159 1P15b92eff1e062a3d 0 2 0 1 3 1P15e1d162b947c748 1 2 16 2 0 1 94 1 16 2 52 1 95 1 2 96 1 97 1P160560deae750f1e 0 2 0 1 131 1P1629bacc3fa102f8 0 2 0 1 95 4P1668f740d86ddd5b 0 2 0 1 3 1P168699ef22fbe48b 0 6 0 1 123 1 142 1 146 1 155 1 156 1P16b5fa56b580eab9 0 2 0 1 113 1P16bd150aa1248a62 1 2 16 3 0 1 153 1 154 1 16 3 1 1 152 1 155 1 2 156 1 157 1P16f8650d3b3aea05 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P171823668a33de30 1 2 16 2 0 1 155 1 16 2 73 1 156 1 2 157 1 158 1P1736786b3f836d4e 0 4 1 1 2 1 157 1 158 1P1782e7105c9dd7c1 0 6 0 1 123 1 142 1 146 1 155 1 156 1P178da7c079fe1516 0 2 0 1 95 4P178e691da0097b0f 1 1 4 1 0 1 2 141 1 151 1P180133f2886f8330 0 2 0 1 143 1P18314c894b538ac8 0 2 0 1 113 1P18370a6f5c70c4ba 1 1 4 1 0 1 2 99 1 111 1P1839336379389202 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P1842a5abe181eb86 1 1 4 1 0 1 2 141 1 151 1P187d05e73e7fa1bf 1 1 4 1 0 1 2 141 1 151 1P18c4d1f9f01564a0 0 2 0 1 1 1P18da49a3946168de 0 2 0 1 114 1P18f197720e49fb3f 0 2 0 1 1 1P18f36ba431320319 0 3 0 1 4 1 143 1P1929382f6ac830b7 0 5 0 16 61 16 95 64 107 16 108 16P1936650ca9ba05f4 0 3 0 1 2 1 6 1P194f431716f08ea0 0 2 0 1 127 1P1983ec0257f4393d 0 2 0 1 141 1P19bbb932fd49d520 1 1 4 1 0 1 2 141 1 151 1P19dc667eb225cfef 0 3 0 1 2 1 151 1P19f2438a29760df1 1 1 4 1 0 1 3 60 1 83 1 95 1P1a334bae0a3282ea 0 3 0 1 151 1 153 1P1a707a9a95dfde34 0 2 0 1 4 1P1a720f2a010c7b1e 1 1 4 1 0 1 3 74 1 97 1 107 1P1a797084e9b86ecb 2 133 1 1 8 3 2 1 157 1 160 1 4 0 2 158 2 159 2 161 16 1 1 8 3 1 1 158 1 159 1 5 0 1 147 4 157 1 160 1 161 8P1ae112d7d470b929 0 2 0 1 113 1P1aecd36216cceaa1 1 1 16 2 1 1 157 1 4 112 1 146 4 156 1 158 16P1afe0745b8e75b15 0 2 0 1 4 1P1b3334199ae73e77 0 2 0 1 4 1P1bd65888236159c8 0 6 0 1 123 1 142 1 146 1 155 1 156 1P1c33326ce236425b 0 4 0 8 58 8 84 8 85 8P1c49533a848a588f 0 2 0 1 85 4P1c62a1a89faefaef 1 1 4 1 0 1 3 51 1 74 1 84 1P1c79560a925dc79c 0 3 0 1 147 1 149 1P1ced5c95d54e8ca0 0 3 0 1 118 1 141 1P1cf2b7c195033aaf 0 3 0 1 149 1 151 1P1dc9ea61273bd6fa 0 5 0 1 2 1 4 1 6 1 127 1P1e0718aeb0275555 1 1 4 1 0 1 2 87 1 99 1P1e76b9d433f0f62e 0 2 0 1 143 1P1e9c18b8dd54db46 0 4 0 1 2 1 4 1 6 1P1ed144aefdca2b37 0 3 0 1 2 1 145 1P1ed5819b8429ba2d 1 1 16 2 0 1 86 1 3 8 1 87 1 88 16P1eeca1484e1bc4f1 1 1 4 1 0 1 3 70 1 93 1 103 1P1f1787d6eda1ecce 1 1 16 2 0 1 84 1 3 6 1 85 1 86 16P1f518590afa9051b 0 2 0 1 125 1P1fac5d3a1f9ff8a2 0 3 0 1 2 1 18 1P1fc9ab7746cba666 0 2 0 1 1 1P1fe22179765e7040 1 1 16 2 0 1 104 1 4 57 1 91 4 103 1 105 16P201f33f740332f5d 0 2 0 1 87 4P2027e97144110c64 0 3 0 1 111 1 113 1P205fc46e538a0f4d 0 2 0 1 111 1P208210108914842f 0 3 0 1 127 1 129 1P20911266e7e6e881 0 5 0 1 2 1 133 1 135 1 137 1P20acbc24c633827b 0 3 0 1 4 1 143 1P20ed0cf0c2a318fb 0 2 0 1 4 1P213c4df63f4d7e34 0 2 0 1 85 4P21961a2495e87024 1 1 16 2 0 1 98 1 4 53 1 87 4 97 1 99 16P21b6544e823c6bc4 0 2 0 1 3 1P21c5c7d9e8d5a848 0 2 0 1 4 1P2223d96cc3327365 0 2 0 1 121 1P2237e8afdcf3384d 0 3 0 1 118 1 141 1P225a8caf0941cb25 0 2 0 1 118 1P227e294e6b986c18 1 2 16 2 0 1 97 1 16 2 55 1 98 1 2 99 1 100 1P22aa892c9c543c89 0 2 0 1 74 4P22ac3aa1b6b46485 0 5 0 1 111 1 122 4 158 1 159 1P22becd6b7e8eeba5 0 5 0 1 4 1 6 1 121 1 123 1P230ca27adfd03b23 1 1 4 1 0 1 2 93 1 103 1P2313480042655954 0 2 0 1 4 1P23864290659d998e 0 2 0 1 74 4P23e3e319457be6f5 1 2 16 2 0 1 106 1 16 2 64 1 107 1 2 108 1 109 1P23ef53fc99ff3f36 0 2 0 1 3 1P2421ea07815e0f0b 1 1 4 1 0 1 2 145 1 155 1P242a2f3a9ae0c166 1 1 16 2 0 1 106 1 4 61 1 95 4 105 1 107 16P246d5e5374bc9ff1 0 2 0 1 91 4P248d9735ba04dde5 0 2 0 1 2 1P24b37fb6db3fbb6d 0 2 0 1 147 1P24fbb5587099a4ee 0 2 0 1 4 1P25aa24ffe6363eb5 1 1 4 1 0 1 2 145 1 155 1P25dc3acc7505d902 0 3 0 1 115 1 117 1P26f9e8d451b89b13 0 2 0 1 131 1P274b061dfc9f67d6 0 3 0 1 137 1 139 1P27acedb9160ac71b 1 1 8 3 0 1 158 1 159 1 5 2 1 147 4 157 1 160 1 161 8P27c8e2fb40507018 1 1 16 3 0 1 156 1 157 1 10 112 1 123 1 132 1 141 1 142 1 145 4 146 1 155 1 158 1 159 16P27ecac075e6697b7 1 1 4 1 0 1 2 83 1 95 1P27f7aabb562485c2 0 5 0 16 111 16 121 64 155 16 156 16P287e7e038a6fa0a8 1 1 4 1 0 1 2 74 1 84 1P289ce4a47d9c593b 0 2 0 1 115 1P28a74d80a56e35fc 0 2 0 1 117 1P29045bf8bb28978d 0 2 0 1 4 1P29098f1ba3e17694 0 2 0 1 81 4P2945ecac3b876f5f 0 2 0 1 3 1P297735b7c2687ec3 0 2 0 1 3 1P29ac75930ac94599 0 3 0 1 147 1 149 1P29ed810beea8364a 1 1 4 1 0 1 2 92 1 102 1P29f348762edf3293 0 3 0 1 139 1 141 1P2a123f0e7754215d 0 2 0 1 141 1P2a1a7a1a40fe80d0 1 1 4 1 0 1 2 141 1 151 1P2a6503c2264751c6 0 3 0 1 132 1 134 1P2a684e78ebaf436e 1 2 16 2 0 1 85 1 16 3 40 1 74 4 84 1 2 86 1 87 1P2a9af80ec200a40d 0 7 0 1 113 1 133 1 142 1 146 4 158 1 159 1P2b2f1685d25ce379 0 3 0 1 22 1 113 1P2b94462bb72c7dd9 0 2 0 1 127 1P2c20185e11a3f10f 0 2 0 1 135 1P2c575fbd29590a89 0 2 0 1 121 1P2c733d77c21b8dd1 0 3 0 1 122 4 145 4P2c89a573746851de 1 1 4 1 0 1 2 145 1 155 1P2c98876de9dfe242 1 1 4 1 0 1 3 76 1 99 1 111 1P2ca14cc197896ed4 0 2 0 1 1 1P2cb6e05c198381bb 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P2d1818881b083ac7 1 1 4 1 0 1 2 141 1 151 1P2d9e6825bc81f0fa 0 2 0 1 115 1P2e01cd2e6cf3965c 0 2 0 1 114 1P2e28da4a9da47dbf 0 2 0 1 3 1P2e40b0e75e205c2b 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P2e8b014e9e5b81c6 0 2 0 1 127 1P2ea70327f20a26c9 0 3 0 1 122 1 145 1P2ec3efac0a55eea2 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P2ed09f5aa9895c13 1 1 4 1 0 1 2 100 1 110 1P2ee3586fd2c218f9 1 1 4 1 0 1 3 66 1 89 1 99 1P2f2b527186d42c5d 1 1 16 2 0 1 96 1 4 51 1 85 4 95 1 97 16P2f71d359a76a24d3 0 3 0 1 118 1 141 1P2fa6e60f1ea64d2f 1 1 4 1 0 1 2 145 1 155 1P2fc84cbec81bd2fb 0 2 0 1 4 1P304e1fac5d15388b 0 5 0 1 120 1 138 1 155 1 156 1P3050f4da6932337e 0 2 0 1 123 1P30cdad891f1bd790 0 2 0 1 3 1P30d2dd01754fdd62 1 1 16 3 0 1 153 1 154 1 10 109 1 120 1 129 1 138 1 139 1 142 4 143 1 152 1 155 1 156 16P30e7ef95e97d75e1 0 2 0 1 124 1P310209632cedd41c 1 1 4 1 0 1 2 83 1 95 1P311d7435443f20fd 0 2 0 1 111 1P317b873adcd8cce6 0 2 0 1 141 1P31a70c052d1f51c6 0 3 0 1 2 1 135 1P31c647bbe0927db5 0 12 0 16 112 16 123 16 132 16 141 16 142 16 145 64 146 16 155 16 156 16 157 16 158 16P32210db6ebba050c 1 1 4 1 0 1 2 141 1 151 1P3229d2e9093387ed 0 3 0 1 122 1 145 1P32571da8addfb30d 0 2 0 1 3 1P3265dba2dc1249b7 1 1 4 1 0 1 2 96 1 106 1P32ac494b4bb3a467 1 1 4 1 0 1 3 55 1 78 1 88 1P32b2403dd936badb 0 3 0 1 2 1 143 1P32cd52c3cd9eb1d8 1 1 4 1 0 1 2 82 1 92 1P332788ba27af3f39 1 1 4 1 0 1 2 141 1 151 1P334a952d107b07bd 0 3 0 1 2 1 6 1P335d6ce537b63e83 0 2 0 1 1 1P339efff0657edc71 0 3 0 1 145 1 147 1P33b14df75b83130f 1 2 16 2 0 1 95 1 16 2 53 1 96 1 2 97 1 98 1P33eda44a639881a5 1 2 16 2 0 1 87 1 16 3 42 1 76 4 86 1 2 88 1 89 1P34127ad792efbab3 0 2 0 1 113 1P34238a5dd6d49edb 0 2 0 1 4 1P346f61c7ded5aadc 0 2 0 1 130 1P347007de6146e06b 0 2 0 1 3 1P34ad82878571c667 0 7 0 1 112 1 132 1 141 1 145 4 155 1 156 1P34fd05af748ea59d 0 3 0 1 122 4 145 4P3518019b2fd50e13 1 1 16 3 40 1 74 4 84 1 3 0 1 85 1 86 16P356998480541ef81 0 3 0 1 119 1 121 1P35c66a309f34aa32 1 1 16 2 0 1 96 1 4 49 1 83 4 95 1 97 16P360a8df28357c91a 0 2 0 1 115 1P362475db6d81eab7 1 1 4 1 0 1 3 58 1 81 1 91 1P363e077b1edfb9b0 2 127 1 1 8 3 2 1 153 1 156 1 4 0 2 154 2 155 2 157 16 1 1 8 3 1 1 154 1 155 1 5 0 1 143 4 153 1 156 1 157 8P36bc3b13b525bfc7 0 2 0 1 4 1P36d27ebd4e85298a 1 1 4 1 0 1 2 91 1 103 1P36fe3dc62b8a449b 1 1 16 2 113 1 156 1 3 0 1 155 1 157 16P373cbdd4fe0f59aa 0 5 0 1 2 1 4 1 6 1 18 1P37603272b46195f3 1 2 16 2 0 1 103 1 16 2 59 1 104 1 2 105 1 106 1P37911392348de49b 1 1 4 1 0 1 3 68 1 91 1 103 1P37d540136a01c98f 0 2 0 1 1 1P3824b2901f1a30a2 0 2 0 1 1 1P384d3e21897ccdb1 1 2 16 2 0 1 92 1 16 2 50 1 93 1 2 94 1 95 1P3873a6057ab6446c 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P3887b699b29e53b9 0 2 0 1 113 1P388de79a2e75af8f 0 2 0 1 2 1P395f093da20f3514 0 2 0 1 2 1P3960895d46d9d676 0 2 0 1 4 1P39ac053ee88f0460 1 1 4 1 0 1 2 145 1 155 1P39e20c7f7aa13e37 0 3 0 1 118 1 141 1P39ed24c502ae5eb3 1 1 4 1 0 1 2 97 1 107 1P3a7fe52c1cb95d8e 0 2 0 1 1 1P3ab812cbeababd27 0 2 0 1 143 1P3b06e05d32893a96 2 133 1 1 8 3 2 1 157 1 160 1 4 0 2 158 2 159 2 161 16 1 1 8 3 1 1 158 1 159 1 5 0 1 147 4 157 1 160 1 161 8P3b081538dc1415b6 0 2 0 1 4 1P3b8659ce5f6ee4d0 1 1 16 2 0 1 100 1 4 53 1 87 4 99 1 101 16P3b9617ec86f8e2e4 0 2 0 1 119 1P3baeefbf57cb83f2 1 2 16 2 0 1 110 1 16 2 68 1 111 1 2 112 1 113 1P3bf675808fa4a09d 0 2 0 1 4 1P3c4ce79b778414e0 1 1 8 3 1 1 157 1 160 1 4 2 2 158 2 159 2 161 16P3c58d516153add4e 1 1 16 2 0 1 94 1 4 47 1 81 4 93 1 95 16P3ca49e4e609f2e87 0 2 0 1 87 4P3ce289fbff281fd5 1 1 4 1 0 1 2 74 1 84 1P3d015b75bd847918 1 1 4 1 0 1 3 122 1 145 1 155 1P3d83a0e6617b5bc0 0 5 0 16 57 16 91 64 103 16 104 16P3dbf902633c8304a 0 2 0 1 149 1P3dc4c0a7f071be3e 0 2 0 1 83 4P3e05d47716b059a4 1 1 4 1 0 1 2 87 1 99 1P3e520fda611d7631 1 1 16 3 0 1 157 1 158 1 10 113 1 124 1 133 1 142 1 143 1 146 4 147 1 156 1 159 1 160 16P3e9833409d5de9a5 0 2 0 1 151 1P3ea3ead1db8d7f92 0 3 0 1 152 1 154 1P3f1593897176b70d 0 3 0 1 112 1 114 1P3f27efbda8e09389 0 2 0 1 2 1P3f54f5210860f1c3 0 2 0 1 122 1P3f9c84b46f20694f 0 2 0 1 76 4P3fae9842f565e950 0 12 0 16 48 16 59 16 68 16 77 16 78 16 81 64 82 16 91 16 92 16 93 16 94 16N00040339c7535120N0014a296e0092efeN00651be2115fa34bN00735c2dda977cc3N007c4d1020dbbb04N009125dd6a0fb64dN00a5163fdf22b095N0108225d71b0ac09N01181be2c29d22a2N01587c58f573b325N019d5b34869d7670N01bbcf2366fcbc43N01bc136b93b42e4cN01d5a095f463735bN020af4f711c0b485N02188a4e75676fa4N023bb3c1b0d02c15N023d862c68f493d8N0265212d406b86e3N02adae3addf2697eN02b024a41e7c6b2aN02d183714bf4f376N03100e46252c5c84N035b5b1085198f44N03d13dde7c99cfc7N044608826c067923N0485940e0b61b537N04df9e5ba9d5f1ddN054cdd25ee967c12N0566120b6ff65080N0569126b80ff2ee8N05b5746fa5b1f635N05bfaeab9210dd25N05dfa6cceb41bd2eN0620a77fde57c56dN0650d2b80384c689N0694fc07e1af335eN0695f61c560bda3bN06978251ae36dba6N06e4a6140a7bd6e1N06ebaac88ddcea2aN06efb7419e26c850N078cdd502ee73d0dN07d75516049c5b54N081edc2526d39126N08a64678b39decafN08ede77b97f02682N08f4cfa18dccf81bN08f76defde6e7b28N0952425eca86a835N096cf1b9bf6a160aN09bcd022b569d0a2N09c76e756f596159N09ee38a74cbcde56N0a21e7962f9ce9dfN0a2201d5ad535017N0a3218bfc7b8eaddN0a4d4acc745d2084N0a5362f58bf347e1N0a599b3b9c16b89fN0a739e35f6d001a9N0ac0397731b94721N0aca64fb4ac872b7N0b1e4fd33a986a49N0b85ca8f160c2edaN0bdd6fc07fc4933eN0be5f07e9ce3c419N0c10a76ba9e39d21N0c3f4b2a32dfa029N0c429743fc9a74adN0c759cb6fe3a08e9N0c82c28983c3fc88N0c901e49d0984b47N0c93e2f6af0b8931N0c9b6a0fb7532b2bN0cc5faa274130344N0d1c9ddbd878d47dN0d525603c015947eN0d6053baa3b46e68N0d9f40524db2e5c5N0dba6f208e16602bN0ded15f5cbbd52e7N0e19a19c03744ecaN0e3457329aed8cdeN0e65c77121ee7ee6N0e958e1d0f6c427bN0edf8b96befb856dN0ee9c819389693d6N0f09ee5b8c0bcf2fN0f36316dc46e8cadN0f8de94a5650199eN0fdb55822c96270dN0ff2b0e0c40a1e10N1009624f8d8cb025N10214959d2af0519N102f404cb729a478N106f7408e76f0786N10d345d958834d16N10f134e1b573380aN10f3d318e62686dcN1140ae6417b848f7N11457d74c7cfd29aN11755d9db9dc25b8N1181583e06769a57N1182e0ac85140313N11ac891f5c5a75afN125c23a2ff3c6be7N126f9657cf29463dN128ff68c59cf15ecN12b0c5d84cf24ce0N12e6803fa8e48facN12f079a4c54279b5N12faa4eaddba036fN1327e56dd129d6b0N133729705011eefcN1339c6dbf6b3b1c0N133cfe669c0d8a58N137ba6ff2c4320b7N1381b75cd6e63cbaN13c070be367cec4eN13d1b460c6bd146aN144023e76cdb0a87N14ec8785dceed310N150782408583a5a5N155a3fc83749f109N155d804ef8df71fbN156d9aeeafdbb129N15ad7d218114663fN15b686f7448b5e1eN15b71f79b28ddd38N15ca7e607f39debcN15d2ea26360a07c0N161284ea3c78f814N163ccb5508e10ba8N16ab7ea1c91e2642N1717de696e0af15eN1727311fbb33a85fN17561aea2ec9d66cN17a9733300b397f9N17c966c62e6a6946N17ddb66669bdfbadN17e7c6f0bfd112d3N1815cd3253240650N1830a31d44076625N183734c856c9c03aN1868c5979e90285aN1882376d6f533edbN18910c74261265fcN1894e1b3f2b8da39N189e7603b8d6dfe0N18a71f9204057f28N18bb63ce6630498eN1967991e6c6b5241N1997b0f10eb8966bN19d34298599215a6N19fa26120af7398eN1a2ae8c43d712aa4N1a8d9f60f49e253eN1a95c7efb365be43N1aabef0c8e36ec02N1b36d6150ad204e4N1b38444fb1c822f3N1b5719f7270efeddN1bb13a6f9da78ac0N1bd722b9c62cf259N1bf437836c248675N1c600d446412f2c3N1c6dc74eb37928ddN1c9c3f176ad7e905N1cb1a8a18c156535N1cc6d8c02e954f24N1d0230d142b876e6N1d1ce998a0d7ea5bN1d200a059d7abf6eN1d7d5d58d5dce1fcN1dfce0cf12bc3b3cN1e9ee8d6f7a776e2N1ec6fc10f37578d0N1ee2d032195d68abN1f08efd58e116a26N1f0d354a1e25d7cdN1f65f89c364dd71eN1fdb261070b0a7b9N1ff407d2ea0aeff6N1ffc7cee11daa133N20006c1a84a11286N20009fa35b0749ccN2013cf41a7727be4N202ad494c172c01bN202c75946c6286b7N206d3eb0f249ac51N207f9981f2ec3a58N20c819cd5e421c62N212220d670efb23bN212e74e706c8e25aN21ceca8dcba6ecf0N21f25590c79e502dN220373b89a50661eN2211687aeb4c3054N2212cb9f5fb7921dN222e94eef7e05a82N22362f2d284b9b25N2255dd5de0590f80N2261f9be3e5685e2N226a9cb3718f88e3N22d541cadaebc8a8N230cff4b854bb3b8N2366a8276ba4dab4N236e5c27a7af6cf2N23a4c6466f4c67e1N23a8e44efc83933cN23a972ecc80557dcN23aab958252b5117N241bf4f560ea701aN241de7434d7d85b7N2430afe389144708N245dbc5fd5447d69N24bd5b93e4ccde7eN24dce587a15e7d7cN24f3461ebda4da59N250bbef00cd5de26N250e6fde1fd3deafN2512ed56b58ae0cbN25338f11b1b98ff8N255b675f6922aa25N257067142070162dN25fefe7d8461cb41N261402d6fad8def1N2675a06c3dd33bd8N267d8d1714648f0eN26e7e2373beb6bdcN26f993552b2335c6N270fc182b81cb05aN275cfb0cc024ba1fN27ab340a9b09cfbbN27e934d0498e140aN281bb3172d74ca06N2825c7031e13bc9eN283c6d4e4db7b6e0N28c542cd4dda5ae7N2902a4c5029bea10N29074826e7188341N29891b632ab02da3N29d96c1d57e9711eN2a4abb75cc165e1aN2a536cda69c26bb1N2aad7bddbf3485f8N2aefd2519e3cd9d2N2b1da10c9ef8cfb9N2b37cc04e1501bdeN2b3ee296fe1b58feN2b9b919533086589N2bb694f4e8add903N2bb91845d2cb1437N2c0c7b8dfc74e534N2c22f9c193b1609fN2c3271c9cc7b4b05N2c32866f0b84a235N2c625d5c40eba134N2cc6ba1deac06466N2cfb05cd1feeb5a2N2d18098246af84d3N2d1e3c8047bf8a23N2d3fb4a48aca9dd1N2d5f8fba0e4e2bddN2d61270020117ff7N2d6e669d795e77afN2d7170ef6bdd5ad8N2dc5b218cbb13bb1N2ea315af7c0939b5N2eb6cc2246d06db5N2ed12a1f99c33df8N2ed4f13ef6635837N2f124c1bb0e956deN2f3daabfa57d2002N2f4ae944782b0c01N2f4e9e60f2f56ef9N2f61e0990a54b9d8N2fcbe3045e2ed364N2fd6155fc724621fN2ff77ce865f92c8aN304e7d93dd4b26c9N3077103b8d8535e1N30a399b50190ab1eN30d42f4671922444N30e69c75e7e1326cN30f74eefaab3cc92N312925c273d884b5N3157d73201598d82N315ddca59a6c6e5fN31a86585dcf52712N31bbdfee4040b4f3N31e7906066a96957N3217dcad29cc5abbN3237c1c115c80838N324f031b4b5988e5N32835c4950a8f26dN329b556bae926808N32b050b108b1bb4fN32b5a15b88389c8fN32c0cd7c871a3113N32c2010e95ad007dN32cbfd3bc03d19bfN335faba656b360c4N336aa01036fb895eN33ac11e82f50eabeN33aec3c3976cfa51N33e0a77c7e2c665eN3463bffd34c2f0fdN3498c90a85efaaa5N34c8223a50910329N34e821f1b3a4b801N351b352a6ccbefdeN35383b1dda9dc0f6N3585d4691f1fbfccN35c791533ba642dcN35c9c00d188c73c6N35caeecdc624708fN35d5a374b1fd22e1N36110aab95f1492eN361273f1e9a1f23dN361a7f46f1991a87N36352e947533bbe7N364367901c65e3dcN366f112e7cf06c51N36714570ffb0082eN367244a0bfc24c25N367cb50d78de729aN36a906535d32c5a1N36e4c2f0a91b982dN36ee9c75ecc3475dN36fcd0c1a65e3e60N374fcc501bce518cN37709f1c5dc5f5b6N37fa83afca318955N3819b3a2aa605bdfN38283139f002d3dcN387cfa26b037ebb1N38b94bb20f89eb59N38f4ae2bf8ce9fe4N3915f6124fe9c0a2N39291911626217d3N392973c0b76c5da8N395685fcad25d586N3969327f92e27976N3974408e739ce83bN3989cd0ee22ee60eN39f5a8b9eb81cddeN3a0330fb1effed43N3a80d94c48e607ceN3a9bcb35aa71bc6dN3aa68ee96818aad2N3ac38a88cc889432N3acc729ad6c9446aN3ae16d3c82ee1fc4N3b12746f0237e0e5N3b4e44cfad15f9bdN3b531265681595f7N3b606f6537cfb1a9N3bc724aa45fd9dc6N3c265ff089326625N3c387db753b6d608N3c541bd9bbc7d291N3c82c7afc3a7bb02N3c8b763ebbf41ef1N3cb727abe3961c5fN3cc8f5e32ff781daN3cd3b95ccf854fccN3cfd5e1058074743N3d237a2b5f324527N3d76c3e85df7eb85N3d7e609feb20580bN3d860087f85202e6N3d9379850cf3fbe7N3daec8593964d32dN3e121ca986c81bbbN3e3a2d7e7016f72cN3e7ca6d8ced7266dN3e98be02cdf909eaN3ea3d604ad2812f2N3ea8cf3c2cc0a911N3ede412a89ce1c6bN3f1f2ae11323efb8N3f2ef9d21e8ea5e0N3f47bf7f7cad88beN3f4c020e82e91fcbN3fd16938f3e8a6aaN3fe6ffcc1c32726c"%lxh.
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
Ltac2 gd_tbl_A_ecp_mod_p192 () : Init.string Init.list := ["OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_ecp_red.reducer_R"; "OSSVerify.KrLib.A.A_mpi_stmtA.grow_PHI"; "OSSVerify.KrLib.A.A_ecp_stmtA.red_FRn"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.A.A_mpi_journey.XJA"; "RED.RFRAME"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "RED.RPOST"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "A_ECP_MOD_P192"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_GROW"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_ecp_red_lib.A_ASAN_MEMSET_EC"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.LibA.ARt.HM"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_reducer_stmtA"].


Definition A_ECP_MOD_P192 : Z := 0xd1aa4.   (* [comment removed for export] *)

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
  Definition RFRAME : list cell := [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo 40 RFRAME.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis D0 : 0 <= d.
  Hypothesis BUD : havol asegs R HIA h + grow_PHI 12 <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + red_FRn d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_RED <= C24MAX.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 144 - arl_need_ecp R.

  Definition RPOST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p192 ()) "(0.$1.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(3.+<.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,)(4.+<.)(5.Vd,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo 40 RFRAME []).
  Ltac basic_factsA hc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (arl_need_ecp_rt R) as NER;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L23050452915.133L29428324939.5  L31826389380.1  L35663928186.7  L36792457560.133L60098763854.3  L61322865240.133L62784354520.133L66187946659.1  L66361310168.133Q15643598972.132Q18366170748.132Q32655747964.132Q33918012703.132Q3830178207.132 Q39939305631.132Q44648563964.132Q51235551740.132Q66521824799.132Q9843086111.132 00000700I00M00b00i01301:01A01E01L01S01Z01a02902Q02i03003703O03gS2ra2spS1R2lo3LOS3ALO3ACPS2spS1R3HIA1h2sp2lo3TOP1HS2ra2spS1R2lo3LOSS2ra2spS2ra2spS2spS2ra2spS2sp2loS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2sp2loS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  Lemma r_ret : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p192 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pr,$6.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxs0,(:.&40.)Pxs1,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.$>.(?.$9.)R1:.R19.R18.R17.R16.R15.)P,(3.+<.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R15.R16.)P,(10.R1<.(4.+<.))P,(10.R1<.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1<.Vmo,)$13.(14.(15.R17.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R16.R15.R14.R13.R12.(16.&40.R18.)R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.+=1=;<.)Vfc,(19.(:.&40.))R1:.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until xt6. intros J HR HV HF. basic_factsA hc.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1]. cbn [app] in HH1.
    pose proof (hm_top asegs R HIA hc LBc LF mc HH1) as HTOP.
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; pose proof (hm_top asegs R HIA h LB LF m HH); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc mo) as KINV.
    unfold RFRAME in FR1. replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in FR1, ST1 by (clear; lia).
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    do 5 zstep.
    zstep.
    replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by (clear; lia). rewrite ?(Z_to_bv_bv_unsigned sp).
    zstep.
    apply aevtA_done. intros mo9 [HK9 MF9]. unfold RPOST.
    eapply (xa_post asegs R HIA h LB LF m dX sp lo 40 RFRAME JC); [exact J| exact HR| exact HK9| exact MF9| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@D24996680996.155D30200628036.154D42631060527.154D62022258533.155L23643762344.4  L2397676628.0   L25953659214.1  L29307822744.1  L2975768925.2   L29773195157.0  L31826389380.1  L33452166838.4  L35663928186.7  L42633816569.1  L44910557663.6  L56080884112.5  L60098763854.3  L60283674290.6  L61162467078.2  L67112202884.6  L67930364611.7  00000M00c01701M01Z01[01_01c01j01k01o02<02Q02V02m03B03L03^03e04=04US1R3HIA2ra2sp1X3xs02hc3pXc2xsS2ra2sp1X3xs01N3pXc2xsS2ra2sp1X3xs03pXc2xsS1R2ra2sp1X3xs03pXc2xsS1X1N3pXc3XPcSS2spS2spS1N3pXcSS2spS2sp1X2lo3DSXS1R3HIA1h2sp2lo3TOP1HS3pXcS2sp2lo1N3pXc4LOSP4XLScS1N2xs4LEN14lxws4LENXS1R2lo3LOSS2sp2lo1N3pXc1a2NOS2sp2loS1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NER". (* [comment removed for export] *)
  Lemma r_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p192 ()) "Pv,$6.Pf,$6.Phc,(7.$1.VR,VHIA,)PLBc,(8.$9.)Pmc,P,(:.&40.)(;.(:.&8.))PdXc,$<.Pxra,(:.&40.)Pxt0,(:.&40.)Pxt1,(:.&40.)Pxt2,(:.&40.)Pxa1,(:.&40.)Pxa2,(:.&40.)Pxa3,(:.&40.)Pxa4,(:.&40.)Pxa5,(:.&40.)Pxa6,(:.&40.)Pxa7,(:.&40.)Pxs2,(:.&40.)Pxs3,(:.&40.)Pxt3,(:.&40.)Pxt4,(:.&40.)Pxt5,(:.&40.)Pxt6,(:.&40.)P,(=.$1.VR,VHIA,Vh,VLB,VLF,Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+28.$>.(?.$9.)R17.R16.R15.R14.R13.R12.)P,(1;.$1<.(1=.R13.)$1>.)P,(10.+<.(1?.R14.))P,Pws,(8.(:.&40.))Pr,$6.P,(20.(21.(22.(23.+2.+1?.))R1.)(10.R1.=))P,(24.(1;.$6.R2.$25.))(3.+<.(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VLB,R3.(2.(26.R19.)(27.R19.)(1?.R19.)(28.R19.)R4.(29.R19.)(1=.R19.)))P,(10.R1;.(4.+<.))P,(10.R1;.(5.Vd,))(11.$1.(12.$1.VR,VHIA,R1;.Vmo,)$13.(14.(15.R17.(16.&40.(17.(18.&40.Vsp,)-30.))Vgp,Vtp,R16.R15.R14.(16.&40.VX,)(16.&40.(2:.(2;.VR,)))(16.&40.=)R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(16.&40.+=1:=8.)Vfc,(19.(:.&40.))R19.(1:.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6; intros J0 EO HNK HR0 BV BF.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 40 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
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
    unfold RFRAME in FR1. replace (bv_unsigned sp - 40) with (bv_unsigned sp + -40) in ST1, FR1 by (clear; lia).
    destruct (stk_carve asegs mc lo (bv_unsigned sp + -40) 8 ST1 ltac:(clear - SLO2 NER NEEDR; lia)) as [STc [junk SLOT]].
    replace (bv_unsigned sp + -40 - Z.of_nat 8) with (bv_unsigned sp + -48) in STc, SLOT by (clear; lia).
    pose proof (munch_refl [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -40)] mc) as MU; pose proof (wmono_refl asegs mc) as WM.
    pose proof (conj J0 I) as J0box. clear J0 HV1 HFR1 FRS1 FRA1 HPX1 OUT1 NM1 MX1 XP1 XLS1 NS1 HCS1 HF1.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA hc LBc LF mc HH1) as ABm. pose (lxi := lxA_img (arl_AL R) IMG).
    lx_pre. lxe_pose. lxe_sums [SUM_amemsetWinA 4 5] [pXc; N].
    lx_pre. lx_run_tac (PLANS [0xd1dbc] [(0xd1ae8, DJoin); (0xd1afc, DJoin); (0xd1b14, DJoin); (0xd1b2c, DJoin); (0xd1b44, DJoin); (0xd1b5c, DJoin); (0xd1b74, DJoin); (0xd1b8c, DJoin); (0xd1ba4, DJoin); (0xd1bbc, DJoin); (0xd1bd4, DJoin); (0xd1bec, DJoin); (0xd1c08, DJoin)] 1000%N [SUM_amemsetWinA 4 5]). lx_tree.
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
      (lazymatch goal with SL : rw_cells asegs ?mq (bv_unsigned sp + -48) ?cs , STq : stk asegs ?mq lo (bv_unsigned sp + -48) |- _ =>
          assert (STM : stk asegs mq lo (bv_unsigned sp - 40));
          [ eapply stk_merge; [exact STq| | clear - SLO2 NER NEEDR LOSP; lia];
            replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size cs)) by (cbn; clear; lia);
            apply stk_of_rw_cells; exact SL | ] end).
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
      lazymatch type of XARR with u32arr _ _ _ ?l => assert (LENF : length l = length xs) by (clear - LENX LEN1; lia) end.
      assert (HWF : forall a, ~ outside [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -40)] a -> (LHeap = LHeap /\ pXc <= a < pXc + 4 * N) \/ lo <= a < bv_unsigned sp - 40).
      { intros a NO. cbn [outside fst snd] in NO. assert (D : pXc <= a < pXc + 4 * N \/ lo <= a < bv_unsigned sp - 40) by (clear - NO; lia).
        destruct D as [D|D]; [left; split; [reflexivity| exact D]| right; exact D]. }
      assert (DJF : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -40)] (bv_unsigned sp - 40) 40).
      { cbn. split; [clear - XLSc LOSP; lia| split; [clear; lia| exact I]]. }
      assert (DJX : disjoint_from [(pXc, pXc + 4 * N); (lo, bv_unsigned sp + -40)] X 16).
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@D11189028015.115D11189028015.116D27424736052.154D2780322814.153 D35881667587.115D35881667587.116D9071893887.151 L10628195786.0  L11741095640.111L14093208217.0  L19354909044.112L21156439898.2  L25382082548.112L25953659214.1  L26924648792.112L28119579349.23 L29010569984.154L31378308326.111L31392867444.112L32455322384.23 L35653441506.7  L36541772284.7  L37414286068.112L40290687782.1  L40456704234.0  L40834179097.118L42243864115.23 L43059266230.109L43442376564.111L43654564952.112L48799365648.154L49631015752.1  L5261871668.3   L59308632561.1  L59360765542.9  L59411595710.2  L59499841752.112L60098763854.3  L61277434550.1  L62673485092.7  L62998051744.23 L64491265552.2  L67930364611.6  L67930364611.7  L7510805464.112 L808409686.23   P21162517072.153P62675925038.154Q14793205526.119Q14793270804.154Q15643324129.111Q18365925601.112Q18696506101.118Q21162517072.153Q21800401414.118Q25160350961.118Q25513505925.114Q25513505925.115Q25604052563.112Q25604052563.113Q25664719138.118Q31226872993.118Q31396957457.118Q32655500769.112Q33918256002.112Q35016271767.118Q35715139857.118Q37821600610.114Q37821600610.115Q3830427394.112 Q39939554818.112Q4141071397.118 Q44648843873.112Q49698585326.113Q49698585326.114Q51235796833.112Q53972118266.118Q61800308129.118Q62675925038.154Q6414620453.118 Q64253126389.118Q64706984570.152Q64706984570.153Q66522067074.112Q67528989526.115Q67528989526.116Q9843367298.111 00000k02202K02d03L04@04A04B04O04P04]04^04k04o05<05L05M05Z05g05k06C06]06j06m06n07I07_08G08T08a09:09>09H09L09l09o0:<0:F0:J0:K0:^0:d0;<0;T0;a0;m0<^0<_0=[0>W0>b0>m0?H0?I0?J0?e0@B0@h0A30A>0A?0A[0Ao0B:0BJ0Bf0Bg0CI0D40DD0DT0DU0D`0E60EL0EW0F30F40F50FP0FQ0FR0FS0Fc0GE0H00H@S1R2ra2sp1X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_stS1R2ra2sp2s01X3xs02lo4SLO25NEEDR3LOS2X03NER3SPR2HB5Ha_st5Hl_st2s12s22s3S2ra2sp2s02s12s22s31X3xs0S2ra2sp2s02s12s22s31X3xs0S1R3HIA1h2ra2sp1X3xs03TOP2HB5Ha_st5Hl_stS1R3HIA1h2ra2sp2s01X3xs03TOP2HB5Ha_st5Hl_st2s12s22s3FSS2ra2sp1X3xs0SS2ra2sp1X3xs0FS2ra2sp1X3xs0S2spS2ra2sp1X3xs0S1R3HIA1h2sp3TOPFS2ra2sp1X3xs0S2ra2sp1X3xs0S2spS1R3HIA1h2sp2lo3TOP4HTOPS1X2sX2nX2pX3xs04padX4ownXS2ra2sp1X3xs0S1XSS1R2ra2sp2s02s12s22s31X3xs0S1R2sp2lo4SLO23NER3SPRS1R2ra2sp1X3xs02lo4SLO25NEEDR2X03NER3SPRS2ra2sp1X3xs0S2ra2sp1X3xs0S2ra2sp2s02s12s22s31X3xs0S2spS1X2X03X16S2KRS2sp1X2sX2nX2pX3xs04padX4ownX2XLS1dS2ra2sp1X3xs0S1R2lo3LOSS2spFS1R3HIA1h2sp1d4BUDFS1d2D0S1R2sp2lo4SLO25NEEDR3NERS1R2sp2lo4SLO25NEEDR3NERS2ra2sp1X3xs0S2sp3SPA3SPRS1R2ra2sp2s02s12s22s31X3xs02lo4SLO25NEEDR3DSX3NERFS1R2ra2sp2s02s12s22s33xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS1R2ra2sp2s02s12s22s33xs02lo4SLO25NEEDR3LOS4SP643ALO3ACP3NERS2sp3xs02loS2sp3xs02loS1R2ra2s02s12s22s33xs04IMG'FFS1R2ra2s02s12s22s33xs04IMG'S2ra2sp3xs02lo2HB5Ha_st5Hl_stS2sp2s03xs02lo2HB5Ha_st5Hl_st2s12s22s3S2sp3xs02HBS2sp3xs02HBFS1R2ra2s02s12s22s33xs05ALWF'S2ra2s02s12s22s33xs0S2sp3xs02loS2sp3xs02lo4LOSPS1R2ra2s02s12s22s33xs05ALWF'FS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s3S2sp3xs02lo4LOSPS2sp3xs02lo4LOSPFS2sp3xs02loS2sp3xs04SP642HB5Ha_stS2sp3xs04SP642HB5Ha_stS2sp3xs02loS1R2ra2s02s12s22s33xs05ALWF'FFS1R2ra2s02s12s22s33xs04IMG'FFFS2sp3xs02lo4LOSPS2ra2sp3xs02lo4LOSP2HB5Ha_st5Hl_stS2sp2s03xs02lo4LOSP2HB5Ha_st5Hl_st2s12s22s3S2sp3xs02lo4LOSP". (* [comment removed for export] *)
  Lemma r_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p192 ()) "Pt0,(:.&40.)Pt1,(:.&40.)Pt2,(:.&40.)Pa1,(:.&40.)Pa2,(:.&40.)Pa3,(:.&40.)Pa4,(:.&40.)Pa5,(:.&40.)Pa6,(:.&40.)Pa7,(:.&40.)Pt3,(:.&40.)Pt4,(:.&40.)Pt5,(:.&40.)Pt6,(:.&40.)P,(2<.$1.VR,VHIA,Vh,Vmo,)P,(2=.$1.Vm,Vlo,(18.&40.Vsp,))P,(2>.$1.Vm,)P,(2?.$1.(2;.VR,)(30.$1.VR,VHIA,Vh,)Vm,(2.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,))(31.$1.$13.(32.(14.(15.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(16.&40.VX,)R?.R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(16.&40.$33.)Vfc,(19.(:.&40.))Vm,(1:.$1.))Vmo,))")
(* [comment removed for export] *).
  Proof.
    intros until t6; intros HK ST MI OXA. unfold A_ECP_MOD_P192.
    jc_open; pose proof (jca_facts asegs R HIA h LB LF m dX sp lo 40 RFRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR);
      cbn [md_addr md_n md_limbs] in X0, X16, XAL, DSX, LEN, NR.
    basic_factsA h.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
    flat constr:(OXA) 2%nat. intros OX _. cbn [md_addr] in OX.
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    do 6 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold RFRAME in *.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jk :: _) =>
      change (rw_cells asegs m1 (bv_unsigned sp + -48) ([CB 8 jk] ++ RFRAME)) in FR end.
    apply rw_cells_app in FR. flat constr:(FR) 2%nat. flclear FR. intros SLOT FR. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp - 40) in FR by (clear; lia).
    assert (ST1 : stk asegs m1 lo (bv_unsigned sp - 40)).
    { eapply stk_merge; [exact ST| | clear - SLO2 NER NEEDR LOSP; lia].
      lazymatch type of SLOT with rw_cells _ _ _ ?cs => replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size cs)) by (cbn; clear; lia) end.
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
      eapply CP with (h := h) (LB := LB) (LF := LF) (dX := dX) (v := 12) (lo := lo) (d := d);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by qlia; try eassumption; try reflexivity.
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
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2, HP2 by qlia. cbn [md_addr] in HP2.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    presA_transport HP2.
    assert (ST2' : stk asegs m2 lo (bv_unsigned sp - 40)).
    { eapply stk_merge; [exact ST2| | clear - SLO2 NER NEEDR LOSP; lia].
      lazymatch goal with SL : rw_cells asegs m2 (bv_unsigned sp + -48) ?cs |- _ => replace (bv_unsigned sp - 40) with (bv_unsigned sp + -48 + Z.of_nat (cells_size cs)) by (cbn; clear; lia);
        eapply stk_of_rw_cells; exact SL end. }
    pose proof (grow_R_keep _ _ _ _ _ _ GR OUT2) as BK.
    pose proof (xa_binop _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ (bv_unsigned sp + -48) (grow_PHI 12) (grow_FR d) J0 ltac:(clear - SLO2 NER NEEDR; lia)
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
      destruct (grow_ok_facts asegs m2 LB2 LB dX dX2 12 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia)) as (GO & GNN & _).
      eapply r_body; [exact J1| exact GO| rewrite GNN; clear; lia| | unfold grow_PHI; unfold AVOL_CALL; clear; lia| unfold grow_FR, red_FRn, calls_FR, fr_charge; clear - D0; lia].
      intros ws r Hr Hne.
      exact (reducer_R_ok 12 dX dX2 LB LB2 ws r asegs m2 MX2 OUT2 ltac:(split; [left; repeat split; assumption| exact FRg]) ltac:(clear; lia) (conj Hr Hne)).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24484290889.0L3554009139.6 00000100BSS1R2sp2lo3SLO3NER". (* [comment removed for export] *)
Lemma A_ecp_mod_p192_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p192 ()) "PR,$34.PHIA,(35.$1.R1.)P,(36.(2;.R2.))P,(37.$1.R3.R2.$38.)P,(1;.$6.(39.R4.)$3:.)P,(10.=(3;.R5.))P,Ph,(7.$1.R6.R5.)PLB,(8.$9.)PLF,(8.$9.)Pm,P,(:.&40.)(;.(:.&8.))P,(3<.$1.R:.R9.R4.R3.R2.R1.)(3=.$6.(3>.(3?.$6.$6.)$6.(40.$6.$6.)R4.))P,(20.(10.(41.(42.R7.))(43.(42.R7.)))(10.(44.(42.R7.))(45.(42.R7.))))P,Pa,$6.P,(1;.$46.(47.$1.(48.R1.))$49.)P,(20.(10.=R2.)(21.R2.(23.+2.+40.)))(20.(10.(41.(42.R;.))R3.)(21.R3.(45.(42.R;.))))(4:.$1.R9.R8.$33.+<.+90.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG GROW AMS NEEDR HND DIMG ROIMG. unfold ecp_reducer_stmtA.
  intros until d. intros HH HK LFB MX NST XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H ->.
  destruct dX as [X sX nX pX xs0 padX ownX].
  pose proof (arl_need_ecp_rt R) as NER.
  assert (JC : JCA asegs R HIA h LB LF m (mkMPD X sX nX pX xs0 padX ownX) sp lo 40 (RFRAME ra s0 s1 s2 s3)).
  { constructor; try assumption; try reflexivity. clear; lia. clear - SLO NEEDR NER; lia. }
  eapply r_main; first [ exact JC | eassumption | eapply uwc_nonneg; exact UW | clear - SLO NEEDR NER; lia | idtac ].
  all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
