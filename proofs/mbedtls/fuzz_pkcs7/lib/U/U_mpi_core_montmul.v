(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_mla U_ct_memcpy_if.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001c6e664db1a0b5 1 1 4 1 0 1 3 52 1 65 1 80 1P00751bbb5fffc416 1 2 4 2 0 1 64 1 4 2 27 1 65 1 3 41 1 66 1 67 1P00ab70a0f146e0e8 1 1 4 2 0 1 78 1 4 11 1 51 4 79 1 80 4P010c5e4f8bdf21ba 1 1 4 4 1 1 55 4 81 1 84 1 6 3 1 38 4 54 4 82 1 83 1 85 4P02109a85618656f1 1 1 4 2 40 1 78 1 4 0 1 70 4 79 1 80 4P0238f23a8f9dfb05 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P025a93f27c55af9b 0 3 0 1 65 1 67 1P036209eedc5fab86 1 1 4 2 28 1 45 1 6 0 2 2 8 22 8 38 8 46 2 47 8P03a05b9a4e8f6ec9 1 1 8 1 0 1 2 7 1 45 1P03b23054aafe2020 0 2 0 1 64 1P03b37399746d8358 1 1 4 4 1 1 55 4 82 1 83 1 6 3 1 38 4 51 1 81 1 84 1 85 4P0441e04f144d667d 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P04d115b837928155 1 1 4 1 0 1 4 6 1 46 2 59 1 74 2P052e17f8de7847a1 1 1 4 2 0 1 78 1 4 11 1 51 4 79 1 80 4P05320584f3d74094 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P056f4cdbaccba1f6 1 1 4 2 44 1 78 1 5 0 2 27 8 62 8 79 2 80 8P05e097466b1fb8e9 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P05f228d63c556bef 0 2 0 1 7 1P0626ebf572f0d7a8 1 1 8 1 0 1 2 7 1 45 1P063dc21a089cf4ff 1 2 4 2 0 1 78 1 4 2 45 1 79 1 3 32 1 80 1 81 1P06502d075e86bb88 1 1 4 1 0 1 2 43 1 70 1P06f2a2759b4ee08d 1 1 4 1 0 1 2 51 1 78 1P0924d86b5e224fc6 0 5 0 4 11 4 51 16 78 4 79 4P09d2b552fdd25157 1 1 16 2 0 1 78 1 3 14 1 79 1 80 16P0a8155f54c9fe661 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P0a88c803cf220d29 0 3 0 1 28 1 69 1P0ad3b5fe174ea321 0 7 0 32 9 32 50 256 51 128 63 128 78 32 79 32P0b1e9c91507d7f40 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P0b4b195702252200 1 1 4 1 0 1 3 52 1 53 2 80 1P0b9dc7cf075f212f 1 1 4 3 0 1 82 1 83 1 6 3 1 30 4 53 4 81 1 84 1 85 4P0bfe6932b14a36d3 1 1 4 3 0 1 81 1 84 1 4 3 4 82 4 83 4 85 16P0d43911ad07c22a2 1 1 4 2 26 1 64 1 5 0 1 25 4 40 4 65 1 66 4P0e27d5966ccf6648 0 2 0 1 64 1P0e94296f00dcc5ef 1 1 4 4 1 1 71 4 82 1 83 1 5 3 1 51 1 81 1 84 1 85 4P0f2df874ac4f30b4 1 1 4 1 0 1 4 23 1 28 1 65 1 72 1P110081a4155dc2f0 0 5 0 1 2 1 72 4 82 1 83 1P1199bb580bd071db 0 2 0 1 41 1P119b6de837658fdc 1 1 4 4 1 1 73 4 81 1 84 1 5 3 1 54 4 82 1 83 1 85 4P1211aeb3e8ee77f0 0 3 0 1 32 8 63 4P1212cd93e9193704 0 6 0 4 9 4 32 16 63 16 78 4 79 4P1242fbc20fbdf657 1 1 4 3 0 1 81 1 84 1 4 3 4 82 4 83 4 85 16P136cc1056cb07019 1 1 4 2 44 1 80 1 3 1 1 79 1 81 4P14bf345c1b7cde55 1 1 4 1 0 1 4 22 1 42 1 65 1 70 1P15702a24d2ea6447 1 1 8 1 0 1 2 7 1 45 1P15edece30ee56d5e 1 1 4 2 0 1 65 1 4 5 1 49 4 64 1 66 4P162874baa399767b 1 1 4 1 0 1 2 41 1 64 1P16465f6dfbfac777 0 2 0 1 32 1P16521b9d9606915d 0 2 0 1 31 1P173ecf643e9107cb 1 1 4 3 1 1 48 1 49 1 4 2 4 47 4 50 4 51 16P17d30bd0125d2f43 1 1 4 4 0 1 72 4 80 1 83 1 4 2 1 81 1 82 1 84 4P18d1b8e4c534c313 0 2 0 1 33 1P19722f504e7bd2a9 0 2 0 1 32 4P1a447d004de6f651 0 2 0 1 7 1P1ab535687884940f 0 4 0 1 48 1 78 1 79 1P1b0850de40dc0cfc 1 1 4 1 0 1 4 16 1 38 1 53 1 62 1P1cc60a1b2d5b8b73 1 1 4 1 0 1 2 40 1 64 1P1dcd93195c917785 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P1dd89de2c3dcb000 2 56 1 1 4 3 1 1 67 1 68 1 7 0 1 27 4 40 1 42 4 66 1 69 1 70 4 1 1 4 3 2 1 66 1 69 1 5 0 1 43 4 67 1 68 1 70 4P1e76bebc3ded049d 1 1 4 1 0 1 2 32 1 78 1P2021ac230b0f6c0e 1 1 4 2 42 1 80 1 3 1 1 79 1 81 4P204fe693d3249225 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P212cf76384f3b9cd 1 1 4 4 1 1 71 4 81 1 84 1 5 3 1 54 4 82 1 83 1 85 4P221ff358e1d6b156 0 2 0 1 64 1P22e6b913e1e43861 0 4 0 8 10 16 50 32 63 16P22e7852a7ce6afee 1 1 4 3 0 1 81 1 84 1 4 3 4 82 4 83 4 85 16P2339a12458423cf5 1 1 4 4 1 1 75 4 81 1 84 1 5 3 1 54 4 82 1 83 1 85 4P2360b6ec23057755 1 1 4 2 26 1 64 1 4 0 1 25 4 65 1 66 4P23a2fab30a4e683a 2 67 1 1 4 3 2 1 67 1 70 1 6 0 1 28 4 43 4 68 1 69 1 71 4 1 1 4 3 3 1 68 1 69 1 7 0 1 20 4 44 4 47 4 67 1 70 1 71 4P245e16de8e3554dc 0 4 0 1 48 1 78 1 79 1P249e8d00ee6b8564 1 1 4 5 0 1 2 1 29 4 82 1 83 1 2 52 1 84 1P264c6111241204a1 2 63 1 1 4 4 3 1 57 4 67 1 70 1 5 0 1 44 4 68 1 69 1 71 4 1 1 4 3 2 1 68 1 69 1 6 0 1 28 4 43 4 67 1 70 1 71 4P26f9be602d135e1f 1 1 4 3 0 1 81 1 82 1 7 2 2 29 8 50 2 52 8 80 2 83 2 84 8P27c7f1d51642cc5a 1 1 4 3 0 1 82 1 83 1 6 3 1 30 4 53 4 81 1 84 1 85 4P27ef0d2aaf1ab257 0 2 0 1 34 1P29894eac5c0c0e1c 1 1 4 1 0 1 3 36 1 37 2 60 1P2a2f48810c09c587 1 2 4 2 0 1 64 1 4 2 27 1 65 1 3 41 1 66 1 67 1P2aa59d6e7e7d33d3 1 1 4 3 1 1 81 1 82 1 5 2 4 53 16 80 4 83 4 84 16P2afffed87b820750 1 1 4 1 0 1 2 50 1 78 1P2b2ba2dc5ee4a42e 0 2 0 1 32 1P2b45221d7c24feb0 1 1 4 5 0 1 2 1 29 4 82 1 83 1 2 64 1 84 1P2c3940f9e3f0a626 0 3 0 1 7 8 23 4P2c4c682226836205 1 1 4 3 1 1 47 1 50 1 4 2 4 48 4 49 4 51 16P2cd000028cb7e880 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P2cde86b48a98dc86 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P2d4662a1ff90f07e 1 1 4 1 0 1 2 40 1 64 1P2d65bbf15bbf0aaa 1 1 4 2 45 1 79 1 3 0 1 78 1 80 4P2d91adaccc1a8e52 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P2e12f196da880741 1 1 4 3 1 1 81 1 82 1 4 2 1 80 1 83 1 84 4P2e69fd91266f053a 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P2e77800c1cd51b26 1 1 4 3 0 1 81 1 84 1 4 3 4 82 4 83 4 85 16P2f49f108906e806f 1 1 4 1 0 1 2 51 1 78 1P2fdfa971442e9629 1 1 4 1 0 1 2 40 1 64 1P30213ca0276984bc 1 1 4 3 1 1 81 1 82 1 4 2 4 80 4 83 4 84 16P30a69d73f49e6206 1 1 4 4 1 1 75 4 82 1 83 1 5 3 1 51 1 81 1 84 1 85 4P321e521e643bf19a 1 1 4 2 0 1 64 1 4 7 1 22 4 65 1 66 4P3252c560982ad9c4 0 3 0 1 29 1 71 1P32ab80bdbb1963e6 1 1 16 2 46 1 78 1 3 0 1 79 1 80 16P32ced55851aed25b 1 1 4 1 0 1 2 50 1 78 1P32f4f0ec4eb6be63 0 5 0 1 2 1 70 4 82 1 83 1P345fc4d211e2a5da 0 2 0 1 31 1P348bf227c098dddc 1 1 4 1 0 1 2 39 1 62 1P34bd7639dafa1331 1 1 4 1 0 1 3 36 1 41 1 60 1P34f1d03c54d3a433 0 3 0 1 40 1 49 1P35c202e9f603d9ae 1 1 4 2 45 1 79 1 4 0 1 32 4 78 1 80 4P36ce08a6ad833c82 0 2 0 1 6 1P36ef8bf7db995000 1 1 4 3 1 1 81 1 82 1 6 2 2 29 8 64 8 80 2 83 2 84 8P3741e8e67d94162a 1 1 4 1 0 1 2 47 1 74 1P375f2708a077e87e 1 1 4 1 0 1 3 50 1 63 1 78 1P37b04a15637d9653 0 5 0 1 2 1 40 4 49 1 50 1P37fe4ddfa95ed25d 1 1 8 1 0 1 2 7 1 45 1P38fabb85b694474e 0 3 0 1 50 4 51 8P397714cada5500f1 1 1 4 3 1 1 80 1 83 1 5 2 4 53 16 81 4 82 4 84 16P39ce9a8206b3dd29 1 1 4 3 1 1 81 1 82 1 6 2 2 29 8 64 8 80 2 83 2 84 8P3aa34f57359b89b4 1 1 4 3 1 1 81 1 82 1 4 2 4 80 4 83 4 84 16P3ac6451792261115 2 27 1 1 4 3 3 1 49 1 50 1 7 0 2 25 8 30 2 41 8 48 2 51 2 52 8 1 1 4 3 2 1 48 1 51 1 4 0 1 49 1 50 1 52 4P3b6f5b9803cd536d 0 3 0 1 64 1 66 1P3b7d5786e6dabb05 1 1 4 2 33 1 46 1 3 0 1 45 1 47 4P3b7ff5cc6b2a512f 1 1 4 3 0 1 82 1 83 1 6 3 1 30 4 53 4 81 1 84 1 85 4P3b9458ab1da27815 1 1 4 2 27 1 65 1 4 0 1 41 4 64 1 66 4P3be82b6c2d00e5d8 1 1 4 1 0 1 2 50 1 78 1P3c19b36f292bdf45 1 1 4 3 0 1 82 1 83 1 6 3 1 30 4 53 4 81 1 84 1 85 4P3c29d4d2461ee0cf 1 1 4 3 0 1 48 1 49 1 6 2 2 29 2 40 8 47 2 50 2 51 8P3c390885a2b182a9 1 1 4 2 42 1 78 1 4 0 1 68 4 79 1 80 4P3ca7c82f07b57160 0 5 0 4 7 4 22 16 64 4 65 4P3cb479cd58db7270 1 1 4 2 0 1 65 1 5 5 1 40 4 49 4 64 1 66 4P3d49419caa41659c 1 1 4 2 0 1 79 1 6 9 8 50 64 51 32 63 32 78 8 80 32P3db631d72896ef85 1 1 4 4 1 1 73 4 82 1 83 1 5 3 1 51 1 81 1 84 1 85 4P3e4012ae949be60f 0 2 0 1 65 1P3f0025ffd4092a9e 1 1 4 1 0 1 2 23 1 45 1P3f9b8ac32e750e9e 1 1 4 4 0 1 70 4 80 1 83 1 4 2 1 81 1 82 1 84 4P3fc64880d231c5e8 1 2 4 2 0 1 79 1 4 2 44 1 78 1 4 27 1 32 1 80 1 81 1N005b3a8082292704N00e9d896f7766eb5N0135852b3231e2ecN017b8bd19384dfdeN01872a024743f151N01cbae7a948c13d9N0294b18cdc0e192eN02dbba16a2e53300N03cdf60e85498cc3N03f7610f2b6018d3N04b97d70874e76aeN0503255d31ef5986N05f23b1b992f9510N06813569732e9bb5N06d74b1034024ea4N0737fbb7c74dda70N07aa6780f9848fb8N09cc88ac902d8586N0a1167589ab42e51N0a612b2b95326192N0aa1e5624e3d5862N0aafc986d623385cN0b0aa02c2a0ad90bN0b8087707f5d48baN0c4712b9b4497655N0d18e4640d1a7335N0d1f4ba6d3b9422fN0df0f51dc2c0bb33N0e4d59e590a02772N0fba26e92c7e0945N107db94840e790edN114d537e1ec885fdN11834b945f27c6dbN1190e6fb4b740539N11c3ea57981c2c2fN11d9391f91efe07aN1238312f36302c6aN12797b6bd4aafe98N129847e722be4e43N133041b24c44f268N13cd9315eca97ae1N1468f42488744c63N148a9b5e15adaf51N149069f485f43c25N14efa4ad3ebb7549N14fe389a5bdbc028N15a25deb8aaf9289N15cc9858b053ea55N16acc4bed87fcce4N16d8ad8b205d9d83N176ef00b1ae5ec11N180137309e78297aN1849a67d364a92a9N194bd6a2b8a8489bN1966d2ae4f127d53N19b5980a2dd4b31cN1a361948310ab2c2N1a5487fc8c4b4e4dN1ab1b7a3f18eadf3N1aff7565bc89370cN1c1e90f3c1d91381N1c59cd592895015fN1c66182940aef93fN1d06f40ada1d9a17N1d184ff34e5f65f2N1d7c14fe59a09dbfN1dda923eecfabfafN1ddbde9b062e360bN1e2775339bc831b6N1e6ba0a4c5680c74N1ea1b518eabbd982N1eabaa520c10e294N1ec58bdb4b8d536fN1ec5ef290a54181cN1f162051416623b9N1f402002d7b9f7c6N1f5ae4b4e76d932fN1f7de45cfd526459N1fb8e67da75d7f61N1ff658cc7f4358e3N20199503078384b8N206f907d44574694N2071f1c59e5a918eN212f1b435cf2aed9N21460cc7f3745bc9N2194fe8ca6c9e2e6N21a2432206d50f40N224ac046fa256526N22a278779606ae8eN22f09fcbcc76ed15N232f1a72f09f3542N25157904f4a79494N25a8bbac400b9fe4N25b064d038ae98b3N264733d4cc0cb0f4N26a2755a70c76badN26c6f098030586d3N26fe7fa587f46e80N272bf9195f26d553N272de8c80935c601N27f93e99f541aba9N28089acbba343a29N280d03255d27b925N28de70754678e0b7N29a140c32cdc541bN2aa33ecb6a54a65aN2aaac8296f131374N2b18c03fcd91861eN2b5694b423c55f4eN2b7a4d7a1ba5d29fN2bb951a81ff38970N2bbbe66bc15c3d6fN2c5726f6cc2ba2aaN2c5f21968838a0f4N2c89abbd0cf78630N2d38ba964196161bN2d8f3e034f7e620aN2da155b05d6fac9cN2df5f976395682a5N2e0c91cacd14f578N2e0e6ff26f671e0eN2e7edc0a4e092b41N2f01c639ec3e6571N2f0ab02898c006c9N2f1e496f8a0a3d9bN2f4c25ddbcff4130N2fa318a22c1c4690N2fa4a4354598e2f0N2fe2b386705dd6b0N3178a2c96f44b41dN319a00beb8777deaN31a70ed6a42292a4N31a832b0e79223e3N31b589b6d5c93ec3N325c91a531a9d9a2N32737b0e7011da6eN32a09ca42b744c64N3431e28329a998a7N348cbdd080bce4d0N35543b503227c937N35b77599e21c8bc8N35d6a8e850ff6d57N363e413deb1a953fN37426f8686e2ab83N375f1b57d40afe8fN3797a4151f8aee4cN37f8b96895079871N3816b4aa9fa96680N38d23312a94fbf87N393c00b82823026cN39511bdb76a9eb81N39569f581ea99c28N399259a20d91081bN3a5599304f3ef737N3a9c718fb9f071beN3ab764a57a0bfc75N3ae5bb32d8a42e76N3d31f0e71e161b1aN3dcadd3ea7eedf6eN3dedc39e74be89ecN3e34f583b69d5379N3e894c06e9bec562N3f5bba68c1c58f4eN3fd1d4ab98442d18N3fe210197c3d9f42"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_montmul () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_MONTMUL_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_montmul_post"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].


Definition U_MPI_CORE_MONTMUL : Z := 0x23e8c.
Definition MPI_CORE_MONTMUL_STACK : Z := 192.

Definition mpi_core_montmul_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X an T : Z) (xs ts : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_montmul ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(1.(4.(2.&40.))Lts',(4.(2.&40.))(5.(6.$0.R13.(7.(8.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(9.O19.)O8.(:.(2.&40.))R3.(;.O1:.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O7.(11.O7.(12.+4.O6.)))(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.(11.(12.+2.O6.)+1.))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O18.)$15.)(14.&40.O18.))(16.(>.$?.$?.)))))O1.R3.)(5.(17.O1:.O1.R3.)(5.(18.O1:.R3.)(5.(19.O1:.R3.O7.R2.)(5.(6.$1:.(1;.(2.&40.)R2.)(1;.(2.&40.)O4.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O6.)R2.)(1<.(2.&40.)(1=.O6.)O4.))(5.(19.O1:.R3.O5.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.(11.(12.+2.O6.)+1.))R1.)(1<.(2.&40.)(1=.(11.(12.+2.O6.)+1.))O3.))(1>.O1:.R3.O2.(14.&40.O18.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_montmul_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_montmul ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.PA,$?.PB,$?.Pbn,$?.PN,$?.Pan,$?.PT,$?.Plo,$?.Pxs,(4.(2.&40.))Pys,(4.(2.&40.))Pzs,(4.(2.&40.))Pns,(4.(2.&40.))Pts,(4.(2.&40.))P,(19.O2.R>.R=.R5.)P,(20.O2.R?.R=.(21.R5.))P,(20.O2.R10.R=.(21.R5.))P,(20.O2.R11.R<.(21.R5.))P,(19.O2.R12.R;.R5.)P,(5.(22.+1.R=.)(22.R=.+1387.))P,(5.(22.+1.R10.)(22.R10.+2710.))P,(22.R?.(23.(1;.(2.&40.)R<.)))P,(22.R10.(23.(1;.(2.&40.)R<.)))P,(22.R13.(23.(1;.(2.&40.)R<.)))P,(22.R12.(23.(1;.(2.&40.)R<.)))P,(22.(11.(12.+2.R13.)+1.)(23.(1;.(2.&40.)R<.)))P,(24.(22.(11.R19.(12.+4.(23.(1;.(2.&40.)R11.))))R13.)(22.(11.R13.(12.+4.(23.(1;.(2.&40.)R=.))))R19.))P,(24.(22.(11.R19.(12.+4.(23.(1;.(2.&40.)R11.))))R14.)(22.(11.R14.(12.+4.(23.(1;.(2.&40.)R>.))))R19.))P,(24.(22.(11.R19.(12.+4.(23.(1;.(2.&40.)R11.))))R15.)(22.(11.R15.(12.+4.(23.(1;.(2.&40.)R?.))))R19.))P,(24.(22.(11.R18.(12.+4.(23.(1;.(2.&40.)R11.))))R16.)(22.(11.R16.(12.+4.(23.(1;.(2.&40.)R10.))))R18.))P,(24.(22.(11.R19.(12.+4.(23.(1;.(2.&40.)R12.))))R1=.)(22.(11.R1=.(12.+4.(23.(1;.(2.&40.)R15.))))R19.))P,(6.$?.(25.R1>.+4.)=)P,(6.$?.(25.R1>.+4.)=)P,(6.$?.(25.R1>.+4.)=)P,(6.$?.(25.R1=.+4.)=)P,(6.$?.(25.R1<.+4.)=)P,(26.=R23.)P,(26.=R23.)P,(26.=R23.)P,(26.=R22.)P,(26.=R21.)P,(26.(11.R28.(12.+4.(23.(1;.(2.&40.)R20.))))(27.+2.+40.))P,(26.(11.R28.(12.+4.(23.(1;.(2.&40.)R20.))))(27.+2.+40.))P,(26.(11.R28.(12.+4.(23.(1;.(2.&40.)R20.))))(27.+2.+40.))P,(26.(11.R27.(12.+4.(23.(1;.(2.&40.)R20.))))(27.+2.+40.))P,(26.(11.R26.(12.+4.(23.(1;.(2.&40.)R20.))))(27.+2.+40.))P,(1>.O2.R2>.R26.(14.&40.R4>.))P,(22.R27.(13.(14.&40.R4?.)$15.))P,(6.$?.(25.(14.&40.R50.)+10.)=)P,(24.(22.(11.R30.(12.+4.(23.(1;.(2.&40.)R28.))))R29.)(22.(14.&40.R51.)R30.))P,(24.(22.(11.R30.(12.+4.(23.(1;.(2.&40.)R28.))))R2:.)(22.(14.&40.R52.)R30.))P,(24.(22.(11.R30.(12.+4.(23.(1;.(2.&40.)R28.))))R2;.)(22.(14.&40.R53.)R30.))P,(24.(22.(11.R2?.(12.+4.(23.(1;.(2.&40.)R28.))))R2<.)(22.(14.&40.R54.)R2?.))P,(24.(22.(11.R2>.(12.+4.(23.(1;.(2.&40.)R28.))))R2=.)(22.(14.&40.R55.)R2>.))P,(18.O2.R36.)P,(6.$?.(25.(14.&40.R58.)+2.)=)P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R50.(28.&40.R37.))P,(6.(2.&40.)R4?.(28.&40.R37.))(29.O2.(2:.O2.R60.R5?.R5>.R5=.R59.R58.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R41.R40.R3>.R39.R38.R36.R32.R37.R3?.)(7.(8.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.)R41.(28.&40.O1.)R40.(:.(2.&40.))R3?.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L13976346308.4L25270283530.4000003004S1kS". (* [comment removed for export] *)
Lemma u32s_skipn : forall (ws : list word) k, skipn (4 * k) (u32s ws) = u32s (skipn k ws).
Proof.
  induction ws as [|w ws IH]; intros k.
  - cbn [u32s flat_map skipn]. rewrite !skipn_nil. reflexivity.
  - destruct k as [|k]; [reflexivity|]. replace (4 * S k)%nat with (4 * k + 4)%nat by lia. rewrite <- (skipn_skipn (4 * k) 4).
    cbn [u32s flat_map]. change (flat_map le4 ws) with (u32s ws).
    rewrite (skipn_app 4). rewrite (skipn_all2 (le4 w)) by (rewrite length_le4; lia).
    rewrite length_le4, Nat.sub_diag, skipn_O. cbn [app skipn]. apply IH.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L35705320628.4000003S1k". (* [comment removed for export] *)
Lemma u32s_firstn : forall (ws : list word) k, firstn (4 * k) (u32s ws) = u32s (firstn k ws).
Proof.
  induction ws as [|w ws IH]; intros k.
  - cbn [u32s flat_map]. rewrite !firstn_nil. reflexivity.
  - destruct k as [|k]; [reflexivity|]. replace (4 * S k)%nat with (length (le4 w) + 4 * k)%nat by (rewrite length_le4; lia).
    cbn [u32s flat_map firstn]. change (flat_map le4 ws) with (u32s ws). rewrite firstn_app_2, IH. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47604499300.6000004S2ws". (* [comment removed for export] *)
Lemma u32arr_of_u8arr_u32s : forall segs m A ws, u8arr segs m A (u32s ws) -> u32arr segs m A ws.
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length in Hw. replace (4 * Z.of_nat (length ws)) with (Z.of_nat (4 * length ws)) by lia. exact Hw. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L1089915561.10 L23967543801.1000000=00JS1k1n2Hk1q2HqS1k1n2Hk1q2Hq". (* [comment removed for export] *)
Lemma same_from_of_window : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_montmul ()) "Pk,$1:.Pn,$1:.Pl1,(4.(2.&40.))Pl,(4.(2.&40.))Pl0,(4.(2.&40.))P,(6.(4.(2.&40.))(1<.(2.&40.)R5.R3.)(1<.(2.&40.)R5.R2.))P,(2;.R6.R5.)P,(2<.(2.&40.)R6.R4.R3.)(2<.(2.&40.)R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros k n l1 l l0 SK Hk FS q Hq. rewrite <- (FS q Hq).
  transitivity (nth_error (skipn k l1) (q - k)). { rewrite nth_error_skipn. f_equal. lia. }
  rewrite SK, nth_error_skipn. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mm_tinv_tac T an m lo sp W :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx T ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
  lazymatch goal with Hi' : mem_inv _ mx |- _ =>
  lazymatch goal with Hs : stk _ mx lo _ |- _ =>
    assert (TI' : u32arr usegs mx T l /\ Z.of_nat (length l) = 2 * an + 1
                  /\ munch W m mx /\ wmono usegs m mx /\ mem_inv usegs mx /\ stk usegs mx lo (bv_unsigned sp + -144));
    [split; [exact Hu| split; [rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] | split; [first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | split; [exact Hw| split; [exact Hi'| exact Hs]]]]] |]
  end end end end end end.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A B bn N an T lx la lb ln lt lo : Z) (xs0 ys zs ns ts0 : list word) (junk : list byte) (wmm : word).
  Hypothesis Han : 1 <= an <= 4999.
  Hypothesis Hbn : 1 <= bn <= 10000.
  Hypothesis Ln : an <= lx /\ an <= la /\ bn <= lb /\ an <= ln /\ 2 * an + 1 <= lt.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LB : Z.of_nat (length zs) = lb.
  Hypothesis LN : Z.of_nat (length ns) = ln.
  Hypothesis LT0 : Z.of_nat (length ts0) = lt.
  Hypothesis DXT : X + 4 * lx <= T \/ T + 4 * lt <= X.
  Hypothesis DAT : A + 4 * la <= T \/ T + 4 * lt <= A.
  Hypothesis DBT : B + 4 * lb <= T \/ T + 4 * lt <= B.
  Hypothesis DNT : N + 4 * ln <= T \/ T + 4 * lt <= N.
  Hypothesis DNX : N + 4 * ln <= X \/ X + 4 * lx <= N.
  Hypothesis ALX : X mod 4 = 0. Hypothesis ALA : A mod 4 = 0. Hypothesis ALB : B mod 4 = 0.
  Hypothesis ALN : N mod 4 = 0. Hypothesis ALT : T mod 4 = 0.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la < 2^64.
  Hypothesis BB : 0 < B /\ B + 4 * lb < 2^64.
  Hypothesis NB : 0 < N /\ N + 4 * ln < 2^64.
  Hypothesis TB : 0 < T /\ T + 4 * lt < 2^64.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 192.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SBB : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis SN : N + 4 * ln <= lo \/ bv_unsigned sp <= N.
  Hypothesis STT : T + 4 * lt <= lo \/ bv_unsigned sp <= T.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis HA0 : bytes_at usegs m A (u32s ys).
  Hypothesis HB0 : bytes_at usegs m B (u32s zs).
  Hypothesis HN0 : bytes_at usegs m N (u32s ns).
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr usegs m (X + 4 * an) (skipn (Z.to_nat an) xs0).
  Hypothesis HThi : u32arr usegs m (T + 4 * (2 * an + 1)) (skipn (Z.to_nat (2 * an + 1)) ts0).
  (* [comment removed for export] *)
  Hypothesis HXlo : u32arr usegs m X (firstn (Z.to_nat an) xs0).

  Notation POST := (mpi_core_montmul_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X an T xs0 ts0 lo m).
  (* [comment removed for export] *)
  Notation W1 := [(T, T + 4 * (2 * an + 1)); (bv_unsigned sp - 192, bv_unsigned sp)].
  Notation W := [(X, X + 4 * an); (T, T + 4 * (2 * an + 1)); (bv_unsigned sp - 192, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -144)
     [C8 (Z_to_bv 64 X); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 bn); C8 wmm;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation TINV WW mm ts := (u32arr usegs mm T ts /\ Z.of_nat (length ts) = 2 * an + 1
                          /\ munch WW m mm /\ wmono usegs m mm /\ mem_inv usegs mm /\ stk usegs mm lo (bv_unsigned sp + -144)).

  Lemma sub_W1_W : sub_fp W1 W.
  Proof. intros x Hx. cbn [outside] in *. clear -Hx. tauto. Qed.

  Ltac mm_tinv1 := mm_tinv_tac T an m lo sp constr:(W1).
  Ltac mm_tinvW := mm_tinv_tac T an m lo sp constr:(W).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12085521688.3 L13367256336.18L13369352988.18L17751026768.12L19343677116.3 L35733287302.4 L36962904668.12L40582529269.3 L52956766754.3 L6155465678.4  00000;01301m02U02`02m03T03_03j047S2an3xs'2LXS2sp1X2bn2an1T2lx2la2lb2ln2lt2lo3xs03Han2Ln2L03DXT2LO2SXS2sp1X2bn2an1T2lx2la2lb2ln2lt2lo3ts03Han2Ln3LT03DXT2LO3STTS2bn2an2lx2la2lb2ln2lt3ts02Ln3LT03ts'2LTS2an3ts'2LTS2an1T3ts'2LTS2bn2an2lx2la2lb2ln2lt3xs02Ln2L03xs'2LXS2an3xs'2LXS2an3ts'2LTS1X2an3xs'2LX". (* [comment removed for export] *)
  Lemma fin_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_montmul ()) "Pm',P,(2.&40.)(3.(2.&8.))Pxs',(4.(2.&40.))Pts',(4.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.Van,)))(=.(>.$?.$?.)(10.$?.$?.VT,(11.VT,(12.+4.(11.(12.+2.Van,)+1.))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+<0.)(14.&40.Vsp,))(16.(>.$?.$?.)))))Vm,R12.)P,(17.$2=.Vm,R13.)P,(18.$2=.R14.)P,(1>.$2=.R15.Vlo,(14.&40.Vsp,))P,(19.$2=.R16.VX,R15.)P,(6.$?.(23.(1;.(2.&40.)R16.))Van,)P,(19.$2=.R18.VT,R16.)P,(6.$?.(23.(1;.(2.&40.)R17.))(11.(12.+2.Van,)+1.))(2:.$2=.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,Van,VT,Vxs0,Vts0,Vlo,Vm,(7.(8.Vra,Vsp,Vgp,Vtp,R17.R16.R15.Vs0,Vs1,R14.R13.R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(9.Vra,)Vfc,(:.(2.&40.))R1:.(;.$2=.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX HT LT.
    unfold mpi_core_montmul_post, MPI_CORE_MONTMUL_STACK.
    flexi 16%nat. exists (xs' ++ skipn (Z.to_nat an) xs0), (ts' ++ skipn (Z.to_nat (2 * an + 1)) ts0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * an) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Han Ln L0 DXT SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX. replace (Z.to_nat an - length xs')%nat with 0%nat by xlia LX. reflexivity. }
    split. { apply u32arr_app. split; [exact HT|]. replace (T + 4 * Z.of_nat (length ts')) with (T + 4 * (2 * an + 1)) by xlia LT.
             eapply u32arr_transport; [exact HThi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Han Ln LT0 DXT STT LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LT LT0 Ln. }
    split. { rewrite skipn_app, skipn_all2 by xlia LT. replace (Z.to_nat (2 * an + 1) - length ts')%nat with 0%nat by xlia LT. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L11091130492.1  L16347013912.3  L17307787420.5  L19150041346.2  L28573892092.6  L32879631684.4  L3871601228.20  L48475109505.4  L54058447839.16 L56428688875.2  L57626602949.9  L58983641412.2  L59308586377.4  L61872756415.3  L66894707720.2  L6768645335.5   L8893533347.3   M23323922861.142M23496508212.128M335504877.142  M37820296991.142M40010603807.142M40528863961.142M48042675648.142M50515372812.142M54052351740.142M5438809200.142 M7856579169.142 M9393718692.142 00000400>00L00Q00a01001f02002^02c03603<03H03P03V03h04304;04G06]08Q08i08l0;_0>60?>0?H0AJ0CGS2spS2an1T3HanS2an1k1j2Hk2HjS1X1jS2sp1X2an1T1x2HxS2an3Han3ws12L1S2sp1X2bn1N2an1T2lx2la2lb2ln2lt2lo2ns2Ln3DNT3DNX2LO2SNS2sp2lo2LOS2sp1X2bn2an1T2lx2la2lb2ln2lt2lo2Ln3DXT2LO3STTS1N1jS2sp1X2an1x3Hx13Hx3S1A2anS2an1j2Hk2HjS2an1T1jS1X2anS2an2xs2LX4dbs'2LDS2an2ts3LT'S2an3HanS2an1j2Hj2H4S2ra2sp1X1A1B2bn1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han2Ln2LN3LT03DXT3DNX2XB2AB2BB2NB2TB3SPR2LO2SX2SN3STT1k1j2xs2ts3xa12Hk2Hj2LX3lxv4lxv02H72LPS2ra2sp1X1A1B1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han2XB2AB2BB2NB2TB3SPR2LO1k1j2xs2ts3xa12Hk2Hj3lxv4lxv02H72LPS2an2xs2LX3Han2ts3LT'2LPS1XS2ra2sp1X1A1B2bn1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han3Hbn2Ln2L02LA2LB2LN3LT03DXT3DAT3DBT3DNT2XB2AB2BB2NB2TB3SPR2LO2SX2SA3SBB2SN3STT1k1j2xs2ts3xa12Hk2Hj3lxv4lxv02H73LT'2LPS2ra2sp1X1A1B2bn1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han2Ln2L03DXT3DNT3DNX2XB2AB2BB2NB2TB3SPR2LO2SX3STT1k1j2xs2ts3xa12Hk2Hj2LX3lxv4lxv02H73LT'2LPS2ra2sp1X1A1B1N2an1T2lx3xs02ys2zs2ns3ts02XB1k1j2xs2ts3xa12Hk3lxv4lxv02LPS2sp2lo2LOS2ra2sp1X1A1B2bn1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han2Ln3LT02XB2AB2BB2NB2TB3SPR2LO1k1j2xs2ts3xa12Hk2Hj3lxv4lxv02H73LT'2LPS2ra2sp1X1A1B2bn1N2an1T2lx2la2lb2ln2lt2lo3xs02ys2zs2ns3ts03Han2Ln2XB2AB2BB2NB2TB3SPR2LO1k1j2xs2ts3xa12Hk2Hj2LX3lxv4lxv02H72LP". (* [comment removed for export] *)
  Lemma sub_walk : forall (k : nat) (j : Z) (xs ts : list word) (mm : mem)
      (xra xt2 xa0 xa2 wa4 xs5 xt3 xt4 xt5 ws0 ws4 ws11 wa7 wj wj4 : word),
    Z.to_nat (an - j) = k -> 0 <= j < an ->
    ws0 = Z_to_bv 64 (T + 4 * an) -> ws4 = Z_to_bv 64 (A + 4 * an) -> ws11 = Z_to_bv 64 an ->
    wa7 = Z_to_bv 64 (2 ^ 64 - 1 - (T + 4 * an)) -> wj = Z_to_bv 64 j -> wj4 = Z_to_bv 64 (4 * j) -> wa4 = Z_to_bv 64 (4 * an) ->
    u32arr usegs mm X xs -> Z.of_nat (length xs) = an ->
    TINV W mm ts -> FRAME mm ->
    evt usegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) xt2 ws0 (Z_to_bv 64 0)
              xa0 (Z_to_bv 64 X) xa2 wj wa4 (Z_to_bv 64 1) (Z_to_bv 64 1) wa7 (Z_to_bv 64 an) (Z_to_bv 64 N) ws4 xs5
              (Z_to_bv 64 B) ws4 (Z_to_bv 64 (an + 2)) (Z_to_bv 64 A) ws0 ws11 xt3 xt4 xt5 wj4)
          F (Z_to_bv 64 0x24044) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j xs ts mm xra xt2 xa0 xa2 wa4 xs5 xt3 xt4 xt5 ws0 ws4 ws11 wa7 wj wj4 Hk Hj -> -> -> -> -> -> ->
      HX LX (HT & LT & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hj|].
    pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear -Han Ln LN DNX DNT SN LO; lia)) as HN.
    lx_run_tac (PLAN [0x24044; U_CT_MEMCPY_IF] [] 80%N); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24044) _ _ _ _) =>
             mm_tinvW;
             let mx := lx_cur_mem in
             lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
              eapply (IH (j + 1) l); [xlia Hk Hj | klia | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0
                                      | exact Hu | rewrite ?upd_length; exact LX | exact TI' | assumption] end
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x258b8) _ _ _ _) =>
             (* [comment removed for export] *)
             mm_tinvW; (flat constr:(TI') 6%nat; flclear TI'; intros HT' LT' MU' WM' MI' ST');
             try rewrite (Z_to_bv_bv_unsigned sp);
             let mx := lx_cur_mem in
             lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
            lazymatch goal with FR' : rw_cells _ mx (bv_unsigned sp + -144) _ |- _ =>
               pose proof (stk_release usegs mx lo _ _ ST' FR' ltac:(cbn; clear -LO SPR; lia)) as STR; cbn [cells_size csize Nat.add] in STR;
               lazymatch type of STR with stk _ _ _ ?h => replace h with (bv_unsigned sp) in STR by (clear; lia) end;
               pose proof (u8arr_of_u32arr _ _ _ _ Hu) as HX8;
               pose proof (firstn_skipn (Z.to_nat an) ts) as EY; symmetry in EY;
               assert (LP : length (firstn (Z.to_nat an) ts) = Z.to_nat an) by (rewrite firstn_length; xlia LT');
               pose proof HT' as HT2; rewrite EY in HT2; apply u32arr_app in HT2; (flat constr:(HT2) 2%nat; flclear HT2; intros _ HThi2); rewrite LP in HThi2;
               replace (T + 4 * Z.of_nat (Z.to_nat an)) with (T + 4 * an) in HThi2 by xlia Han; apply u32arr_ro in HThi2;
               pose proof U_ct_memcpy_if_spec as SP; unfold ct_memcpy_if_stmt, U_CT_MEMCPY_IF, CT_MEMCPY_IF_STACK in SP;
               eapply evt_mono;
               [ eapply SP with (D := X) (S1 := T + 4 * an) (S2 := 0) (n := 4 * an) (lo := lo) (dbs := u32s l) (sbs := u32s (skipn (Z.to_nat an) ts));
                 try reflexivity; try eassumption;
                 try (rewrite ?u32s_length, ?skipn_length, ?upd_length; clear IH SP; klia)
               | clear SP; intros ms' PO; unfold ct_memcpy_if_post, CT_MEMCPY_IF_STACK in PO;
                 (flat constr:(PO) 25%nat; flclear PO; intros yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m' dbs' -> MUc WMc MIc HD LD SK STc);
                 rewrite u32s_length, ?upd_length in LD;
                 destruct (bytes_as_u32s (Z.to_nat an) dbs') as (ws1 & E1 & L1); [clear -LD LX; lia|];
                 rewrite E1 in HD; apply u32arr_of_u8arr_u32s in HD;
                 eapply (fin_post m' ws1 ts);
                 [ eapply munch_trans; [exact MU'|]; eapply munch_weaken; [|exact MUc]; intros x Hx; cbn [outside] in *; (flat constr:(Hx) 4%nat; flclear Hx; intros Hx1 Hx2 Hx3 _); clear -Hx1 Hx2 Hx3 Han; lia
                 | eapply wmono_trans; [exact WM' | exact WMc]
                 | exact MIc | exact STc | exact HD | clear -L1 Han; lia
                 | eapply u32arr_transport; [exact HT' | exact MUc | exact WMc |]; cbn [disjoint_from]; rewrite LT'; clear -Han Ln DXT STT LO; lia
                 | exact LT' ] ]
             end end
         | |- _ => idtac
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L15146305847.19 L17307787293.5  L23983898556.1  L24965107837.2  L32908971933.11 L35518580213.1  L43954729113.18 L43980920595.18 L51431053239.18 L5743289867.2   L57628700040.5  L57628700040.6  L59308586248.4  L60295512454.1  M35464069560.175M42189887312.173M49197642965.173M62531888576.173M9798980755.173 00000a00o01201701[01_02O03G04704<04J04Z04f04i05505C05Q05Y05gS2sp1B2bn2an1T2lx2la2lb2ln2lt2lo2zs2Ln3DBT2LO3SBBS2an1k1i2Hk2HiS1NS1A1iS2bn2an2lx2la2lb2ln2lt3xs03Han2Ln2L0S2anS2sp1A2bn2an1T2lx2la2lb2ln2lt2lo2ys2Ln3DAT2LO2SAS2sp1X2bn2an1T2lx2la2lb2ln2lt2lo3xs03Han2Ln2L03DXT2LO2SXS2sp2bn1N2an1T2lx2la2lb2ln2lt2lo2ns2Ln3DNT2LO2SNS1T1iS2sp2an1T1x2HxS2sp1X2an1T1x2HxS2an1i2Hk2HiS1XS2an1i2Hi2H6S2an1T1i2H82H9S1A2an1i2H82H9S2an3HanS2an1T1i2H82H9". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (ts : list word) (mm : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 wpt wpa wi : word),
    Z.to_nat (an - i) = k -> 0 <= i < an ->
    wpt = Z_to_bv 64 (T + 4 * i) -> wpa = Z_to_bv 64 (A + 4 * i) -> wi = Z_to_bv 64 i ->
    TINV W1 mm ts -> FRAME mm ->
    evt usegs POST
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp xt0 xt1 xt2 wpt (Z_to_bv 64 0)
              xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 an) (Z_to_bv 64 N) wpa xs5
              (Z_to_bv 64 B) wpa (Z_to_bv 64 (an + 2)) (Z_to_bv 64 A) wpt wi xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x23f3c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ts mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xt3 xt4 xt5 xt6 wpt wpa wi Hk Hi -> -> ->
      (HT & LT & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hi|].
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; clear -Han Ln LA DAT SA LO; lia)) as HA.
    pose proof (u32ro_transport _ _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB; clear -Han Hbn Ln LB DBT SBB LO; lia)) as HB.
    pose proof (u32ro_transport _ _ _ _ _ _ HN0 MU ltac:(cbn [disjoint_from]; rewrite LN; clear -Han Ln LN DNT SN LO; lia)) as HN.
    pose proof (u32arr_transport _ _ _ _ _ _ HXlo MU WM ltac:(cbn [disjoint_from]; rewrite firstn_length; clear -Han Ln L0 DXT SX LO; lia)) as HXl.
    assert (LXl : Z.of_nat (length (firstn (Z.to_nat an) xs0)) = an) by (rewrite firstn_length; clear -Han Ln L0; lia).
    pose proof (sumsarr_ok [T]) as LXSUMS.
    lx_run_tac (PLANS [0x23f3c; 0x24044] [] 120%N SUMSARR); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23f3c) _ _ _ _) =>
             mm_tinv1; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | exact TI' | assumption]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x24044) _ _ _ _) =>
             mm_tinvW;
             let mx := lx_cur_mem in
             lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
              eapply (sub_walk (Z.to_nat an) 0 l); [xlia0 | klia | f_equal; first [xlia0 | lia] | f_equal; first [xlia0 | lia] | f_equal; first [xlia0 | lia]
                                                    | f_equal; first [xlia0 | lia] | f_equal; klia | f_equal; klia | f_equal; first [xlia0 | lia]
                                                    | exact Hu | rewrite firstn_length; xlia Han Ln L0 | exact TI' | assumption] end
         | |- _ => idtac
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L30498740165.4  L35733287302.5  L43061838352.94 L57628700040.5  L60330452198.96 L6155465678.5   M10415598215.146M1316410650.146 M15237932557.146M16597807539.146M1825667241.146 M27951947078.146M31127504446.146M3229177674.146 M35521550130.146M40215986979.146M42933808377.146M56527186650.146M58437446534.146M62531888576.146M63432124821.146M66267194107.146M6653585595.146 M68216110327.146M6886548471.146 00000>00N01;01I02002@02A02N02O02P02b02o03<03I03Q03R03U03b03c03k04P04Q04R04S04VS2an2ts3Han2LTS2an1T2ts3Han2LTS2ra2sp1X1A1B1N2an1T2lo2xs2ys2zs2ns2ts2LO3SPRS2sp2an1T1x2HxS2ra2sp1X1A1B1N2an1T2xs2ys2zs2ns2ts3SPRS1X2an2xs3Han2LXFS1T2ts3NZT2TTFFS2sp2lo2LO3SPR3LO0S1N2ns3NZN2NTS1B2zs3NZB2BTS1A2ys3NZA2ATS2an3HanFS1AS1X2xs3NZX2XTFS2an3HanS2bn2an2xs2ys2zs2ns2ts2LX2LA2LB2LN2LTFFFS1T". (* [comment removed for export] *)
Lemma U_mpi_core_montmul_spec : mpi_core_montmul_stmt usegs U_MPI_CORE_MONTMUL.
Proof.
  unfold mpi_core_montmul_stmt, U_MPI_CORE_MONTMUL.
  intros until ts. intros HX HA HB HN HT Han Hbn LX LA LB LN LT DXT DAT DBT DNT DNX ALX ALA ALB ALN ALT NZX NZA NZB NZN NZT XT AT BT NT TT
         ST LO SPA SX SA SB SN STT MI RA -> -> -> -> -> -> ->.
  unfold MPI_CORE_MONTMUL_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB0. pose proof (u32arr_bound _ _ _ _ HT) as TB0.
  pose proof (u32ro_bound _ _ _ _ HA) as AB0. pose proof (u32ro_bound _ _ _ _ HB) as BB0. pose proof (u32ro_bound _ _ _ _ HN) as NB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  pose proof (munch_refl [(T, T + 4 * (2 * an + 1)); (bv_unsigned sp - 192, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat an) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat an) (length xs))) with (X + 4 * an) in HXhi by xlia LX Han.
  rewrite <- (firstn_skipn (Z.to_nat (2 * an + 1)) ts) in HT. apply u32arr_app in HT. flat constr:(HT) 2%nat. flclear HT. intros HTlo HThi.
  rewrite firstn_length in HThi. replace (T + 4 * Z.of_nat (Nat.min (Z.to_nat (2 * an + 1)) (length ts))) with (T + 4 * (2 * an + 1)) in HThi by xlia LT Han.
  assert (LTlo : Z.of_nat (length (firstn (Z.to_nat (2 * an + 1)) ts)) = 2 * an + 1) by (rewrite firstn_length; xlia LT Han).
  pose proof (lock HXlo) as HXlo'. pose proof (lock HXhi) as HXhi'. pose proof (lock HThi) as HThi'.
  pose proof (lock HA) as HA'. pose proof (lock HB) as HB'. pose proof (lock HN) as HN'. clear HXlo HXhi HThi HA HB HN.
  carve_frame 144%nat ST. lxp_split_frame [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat.
  pose proof (sumsarr_ok [T]) as LXSUMS.
  lx_run_tac (PLANS [0x23f3c] [] 80%N SUMSARR); lx_tree.
  all: lxp_unjunk; mm_tinv_tac T an m lo sp constr:([(T, T + 4 * (2 * an + 1)); (bv_unsigned sp - 192, bv_unsigned sp)]).
  all: eapply (@loop_walk) with (k := Z.to_nat an) (i := 0) (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs))
      (ln := Z.of_nat (length ns)) (lt := Z.of_nat (length ts)) (ys := ys) (zs := zs) (ns := ns) (xs0 := xs) (ts0 := ts) (wmm := a6);
    try eassumption; try reflexivity; try klia; try (f_equal; klia).
  all: first [exact (unlock _ HA') | exact (unlock _ HB') | exact (unlock _ HN') | exact (unlock _ HXhi') | exact (unlock _ HThi')
             | exact (unlock _ HXlo') | idtac].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
