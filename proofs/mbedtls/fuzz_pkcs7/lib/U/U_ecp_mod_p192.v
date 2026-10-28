(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_core_mla U_mpi_core_add U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr LxU_SumsEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002d9ce52e6868cf 0 3 0 1 82 1 89 1P00e271080799e80a 1 1 4 1 0 1 2 78 1 110 1P00eb6e79dd583923 1 1 4 1 0 1 2 82 1 114 1P011a9ca1239374d2 1 1 4 1 0 1 3 28 1 35 1 60 1P013262830a2f2b00 0 3 0 1 2 1 6 1P02425649b7ec7242 0 2 0 1 74 1P029ae4bb6cfb91ab 0 2 0 1 76 1P0324086088d25a21 0 3 0 1 2 1 104 1P034772cbfc48dc59 0 2 0 1 98 1P036e3bd4c473b522 0 2 0 1 2 1P038692601d7bf21c 0 2 0 1 102 1P0386afd37a69de38 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P03dfa128fab799d6 0 2 0 1 86 1P041e004b4b0c1b64 1 1 16 3 0 1 112 1 113 1 8 79 4 81 1 102 1 103 1 104 1 111 1 114 1 115 16P042219e882512295 0 3 0 1 94 1 96 1P0433b7d00d4ba11b 0 3 0 1 82 1 89 1P04403dc71140b40a 0 2 0 1 68 1P0484c2e9e634f1e2 0 3 0 1 68 1 70 1P04bb92466d37b8dd 0 2 0 1 110 1P0546c3c0fc8c915d 0 3 0 1 74 1 76 1P0576ce45cc886842 0 2 0 1 2 1P059aa8b002faa7eb 0 2 0 1 74 1P059ad52186f100d7 0 2 0 1 4 1P05f1b445ff5d488d 0 2 0 1 68 1P06059da69ba5ce11 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P071d0a802643ca1f 0 2 0 1 108 1P07526bc5b108bb29 0 2 0 1 4 1P075ce2277fac41d1 0 2 0 1 68 1P077dc8f15f4097f4 0 2 0 1 90 1P079a2b2acf818101 0 2 0 1 2 1P07fec4d18d9d772a 1 1 16 3 0 1 112 1 113 1 8 79 4 81 1 102 1 103 1 104 1 111 1 114 1 115 16P0803a98ce5d6277f 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P081765c6f762b619 0 2 0 1 94 1P08603b3b3df3fe68 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P08bb3d2e6940cefa 0 3 0 1 78 1 80 1P0a4fb226ea70d34b 2 100 1 1 8 3 2 1 113 1 114 1 4 0 2 112 2 115 2 116 16 1 1 8 3 1 1 112 1 115 1 5 0 1 80 4 113 1 114 1 116 8P0a93aeefca4493b4 0 2 0 1 3 1P0af2a8fbfca84cf1 1 1 4 1 0 1 2 78 1 110 1P0b538bb409462e82 0 3 0 1 106 1 108 1P0b88aa566c7e69d6 0 2 0 1 72 1P0b9ee1707ee325ab 0 3 0 1 4 1 102 1P0bbc93b910d09fc7 1 1 4 1 0 1 2 82 1 114 1P0bce0b3deb475a2e 0 2 0 1 1 1P0c2f8ccbf0c1f649 0 2 0 1 101 1P0ca71cc4f8037335 0 2 0 1 112 1P0d9a4e124f90a5f0 0 3 0 1 6 1 68 1P0dbb2e750f72de07 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P0e3af377dff6c371 0 3 0 1 78 1 85 1P0ea985e61705968f 1 1 16 3 0 1 112 1 113 1 8 79 4 81 1 102 1 103 1 104 1 111 1 114 1 115 16P0f54e49a3df744e2 1 1 4 1 0 1 3 22 1 29 1 54 1P102448165314141b 1 1 4 1 0 1 3 16 1 23 1 48 1P10b811ccc413fd44 0 2 0 1 74 1P112b4fb8eeb859d4 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P11b767258ed6877e 0 3 0 1 8 1 74 1P129bfbc181554d96 1 1 4 1 0 1 3 30 1 37 1 62 1P1302d7de12ea6ff6 0 5 0 1 2 1 4 1 6 1 86 1P135409718bdb7054 0 2 0 1 102 1P13606089c2f17cdb 0 2 0 1 88 1P136c4c14a16e26a3 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P138a079d89428a98 1 1 4 1 0 1 3 26 1 33 1 58 1P13aa39d82fc13ddd 0 2 0 1 106 1P13aeaa81c8eabc66 0 3 0 1 111 1 113 1P1448b75954e8fdac 0 3 0 1 12 1 106 1P1548ef90d5cb8693 1 1 4 1 0 1 2 82 1 114 1P15d86af0fcda91e4 0 2 0 1 85 1P166b30deb09dd20a 0 2 0 1 100 1P168e9c179921cd8f 1 1 4 1 0 1 2 78 1 110 1P17a3a50549d8dd43 0 3 0 1 86 1 88 1P17f497757821cb5b 0 2 0 1 86 1P182e56e74be72d73 0 3 0 1 78 1 85 1P1928c27627d5b55f 0 2 0 1 1 1P194c1bebb0edf69b 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P1a6f54b2dc8d85c5 0 2 0 1 89 1P1b3ed680c20095e2 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P1b5367660ae2e4d5 0 5 0 1 106 1 107 1 114 1 115 1P1b7a9ba447748b54 0 2 0 1 98 1P1bc5d60509a96b34 0 2 0 1 76 1P1beed7704bf71a94 0 2 0 1 1 1P1bf19f26734c326f 0 2 0 1 103 1P1c77cab352c4363e 1 1 4 1 0 1 2 82 1 114 1P1ce96e48ca0f48ac 0 2 0 1 86 1P1cfb5683f5f14610 0 3 0 1 2 1 102 1P1d6049175dfe4c98 0 5 0 1 2 1 92 1 94 1 96 1P1e040d9fd5d67bcc 0 3 0 1 2 1 90 1P1e48093951c14da1 1 1 4 1 0 1 2 78 1 110 1P1e672ffc902f7874 1 1 4 1 0 1 3 14 1 21 1 46 1P1e90a57afb512ad6 0 2 0 1 68 1P1ebf90bf7b5b3b3e 0 2 0 1 80 1P1ec1b8925c8adafc 0 2 0 1 11 1P1f25e8cf728b0d36 0 2 0 1 72 1P1f3f7c956cf7fa0c 0 2 0 1 75 1P1f6e58bb3869a10f 0 3 0 1 108 1 110 1P1f83e5fa04be4249 0 2 0 1 4 1P1f8652d10c9ba08b 0 3 0 1 2 1 94 1P1f9f3be977cb6194 1 1 16 3 0 1 112 1 113 1 8 79 4 81 1 102 1 103 1 104 1 111 1 114 1 115 16P1fcc9cbe912535bc 0 2 0 1 86 1P200b1c569c270da8 0 2 0 1 74 1P204a86c4955c2155 0 3 0 1 71 1 73 1P20d142fd7774c5a1 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P20e6783bc5278126 0 2 0 1 84 1P21584a6056f09349 0 2 0 1 3 1P217d74a9f72668d7 0 3 0 1 110 1 112 1P21ad31113a6c82c3 0 2 0 1 74 1P21ea118ab7bbfba1 0 3 0 1 2 1 26 1P224fcbc5b1f35756 1 1 4 1 0 1 3 32 1 39 1 64 1P22e73c5d7d8d0303 0 3 0 1 78 1 85 1P23fa76f1f03baed9 0 2 0 1 82 1P241ae7c484d4c3cf 0 2 0 1 2 1P2437d25c37994cbc 0 2 0 1 4 1P253c6e7df89af338 0 2 0 1 80 1P25927bdbfac56ae8 2 100 1 1 8 3 2 1 113 1 114 1 4 0 2 112 2 115 2 116 16 1 1 8 3 1 1 112 1 115 1 5 0 1 80 4 113 1 114 1 116 8P25ccdc76a40eda51 0 3 0 1 82 1 89 1P260ad595332241ab 0 3 0 1 90 1 92 1P265e88ba110b1c98 0 2 0 1 4 1P26b6b5a1b4f46f44 0 4 0 1 2 1 4 1 6 1P26e49a6abb6a34e3 0 2 0 1 90 1P26f4e57da0927e7a 0 2 0 1 73 1P27543d607235c98b 0 2 0 1 3 1P275ea65237caa8cb 0 2 0 1 104 1P277844f0227191f6 0 2 0 1 106 1P27edde10df632075 0 2 0 1 2 1P2826433306ac92c3 0 3 0 1 2 1 6 1P298d55d51d0c7fa1 0 3 0 1 78 1 85 1P2ad975d11b3e42cf 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P2ae7a3c94a598714 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P2af38cf40017a534 0 2 0 1 12 1P2b20e67bc734ec3c 0 2 0 1 3 1P2ba75b1e744c51c1 0 3 0 1 2 1 110 1P2bf7ca951db9abb4 0 2 0 1 2 1P2c255cf1fc6ec58a 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P2c80978308840b07 0 3 0 1 40 1 86 1P2cbccf2468717b95 0 3 0 1 80 1 82 1P2cc69c779ab7dc9e 1 1 4 1 0 1 2 82 1 114 1P2cf374af4ad35d1d 1 1 4 1 0 1 2 82 1 114 1P2dde56c4db95aa3d 0 2 0 1 1 1P2df2bcf3b5f89864 0 3 0 1 82 1 89 1P2ebf4b802cc07532 2 100 1 1 8 3 2 1 113 1 114 1 4 0 2 112 2 115 2 116 16 1 1 8 3 1 1 112 1 115 1 5 0 1 80 4 113 1 114 1 116 8P2ed66972d8a2f80a 0 2 0 1 83 1P2eea560de380c5bc 0 2 0 1 2 1P2f79020bfe2ba5f1 0 3 0 1 91 1 93 1P2fa85c203467813a 0 3 0 1 2 1 110 1P2ff04fa6afd30b0e 0 3 0 1 2 1 112 1P3048491f0b7c8e66 0 2 0 1 86 1P30516befa80ef9ea 0 3 0 1 82 1 89 1P3060228e673519dc 0 5 0 1 2 1 4 1 6 1 10 1P309c0ab31d4395ea 0 3 0 1 4 1 102 1P3102db3e43326de7 0 2 0 1 1 1P3118d78b1581170d 1 1 4 1 0 1 3 34 1 41 1 66 1P317d561ac0e1d1fa 0 3 0 1 82 1 89 1P3190b84235bdf3ea 0 2 0 1 77 1P319d776a4258b250 0 5 0 1 4 1 6 1 80 1 82 1P319e536435779e5e 0 3 0 1 12 1 106 1P328efa31a3debd91 0 2 0 1 106 1P3340c00fdae53755 0 2 0 1 78 1P33591e6c19188c3c 0 2 0 1 102 1P33762180f85582a0 0 2 0 1 3 1P33888919a71f4207 0 4 0 1 2 1 102 1 104 1P33bc371214ce1b97 0 2 0 1 74 1P344d9190fac2fe92 1 1 4 1 0 1 3 18 1 25 1 50 1P347ca4082683892f 0 2 0 1 92 1P3526fda4df6d13c3 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P3564e84196b1278b 2 106 1 1 8 3 2 1 117 1 118 1 4 0 2 116 2 119 2 120 16 1 1 8 3 1 1 116 1 119 1 5 0 1 84 4 117 1 118 1 120 8P35d639fb725354bc 0 2 0 1 69 1P362c02cd53d661f9 0 3 0 1 96 1 98 1P364c3107e99e27df 1 1 4 1 0 1 3 20 1 27 1 52 1P36b9ff88b2c02735 0 2 0 1 68 1P37c60f46ef1a537d 2 100 1 1 8 3 2 1 113 1 114 1 4 0 2 112 2 115 2 116 16 1 1 8 3 1 1 112 1 115 1 5 0 1 80 4 113 1 114 1 116 8P384cc29dd7a2a47e 0 2 0 1 74 1P38a507220dc58675 0 3 0 1 104 1 106 1P399bcf6361a2e8de 1 1 4 1 0 1 2 82 1 114 1P39e524babea838af 0 2 0 1 68 1P3a1a63c459bf85eb 0 3 0 1 82 1 89 1P3a31ed48b6c338e7 0 2 0 1 2 1P3a6dbec1ff304e45 0 3 0 1 106 1 108 1P3a74a4e5f6660110 0 2 0 1 94 1P3af320418548cd56 0 3 0 1 98 1 100 1P3b278dd7f4f5fe03 0 2 0 1 104 1P3b2ab9833021ffdf 0 3 0 1 4 1 36 1P3b622ef232ada8ca 1 1 4 1 0 1 3 24 1 31 1 56 1P3c84523aa621202b 1 1 4 1 0 1 3 12 1 19 1 44 1P3c8de8f552b537e2 1 1 16 3 0 1 116 1 117 1 8 83 4 85 1 106 1 107 1 108 1 115 1 118 1 119 16P3d24351903dacf43 0 2 0 1 96 1P3e120be89166377f 1 1 4 1 0 1 2 82 1 114 1P3e4aadbe144c7708 0 5 0 1 2 1 4 1 6 1 86 1P3ea62c638a4cf7a7 0 2 0 1 1 1P3ebbd7704783f498 0 3 0 1 70 1 72 1P3f07faa4e60e32a3 0 2 0 1 1 1P3f088666a67cb437 0 2 0 1 84 1P3fb2f0d5c2802c96 0 2 0 1 1 1P3ff50571094a10a8 0 2 0 1 86 1P3ffce07757b99eb6 0 3 0 1 82 1 89 1N0182b21a307c65feN01efc2aa1e81add4N0299af2d11355e80N029db0decb95f3c5N02d0c6e4ed8b54f5N031be820af62f7e7N03be88c75d2eff89N03d81a521d7308fdN04b7e3d5e3cc835fN04d4c4f5f81af667N053d70e4371cc587N054f554bef5e03f8N059651247140f2f1N05e9248539b25f96N05fb261b0e0bc27eN066b1f6708ecbf1cN06f6405a348e3d50N0720482bb0b11744N075ee63af0ea5e7cN0770e32a79e3caf7N0793f89fe78b3c15N07d671401a14f39eN08483b40e0b67cadN085dbc514c6a96eeN087d74f628560b16N090488a1156885b6N0911bfa76c473354N091cf9cec79dff4bN0966d5dd1ba0856aN099174c97c529245N099a900bc5715446N09f4944ecacf77c6N0a1b75d4d0d53619N0a1c4350fb7a8884N0a2302e5fafc9ddcN0a754da4307e64b5N0a871db8a5a3abcaN0a8a5cd74b9301b3N0b22f1036be38b68N0c1405fd01a1580dN0c4c74c74d97901bN0c81810f678d0214N0cb6e2993e367481N0cd4a7fcc74e035fN0dc108608b95e836N0dfeca7b2d55a19aN0e05258a1dbb1fe2N0e0d59a53dfda587N0e16a3ed722d22f9N0e1d2f9cf18992acN0e3ab5bff428e81aN0e6f80850bca1418N0e788b96fd5c6d73N0eb05cc3cc8bf4a6N0ed78ed1c10d4fddN0efb8c42d2900cebN0f027daf2288452fN0f84704ddab8735dN0fb9449dc8bceb44N0fc226e56f90b25aN0fc62d4509631c80N1053ce217c98f2b7N107e9f297bf7e502N10e5517a5b66de0eN10ffd93f8c3c8723N1143291fc63e43adN114c0973cc22fb00N115d89ac7cf601a1N1199e2b204d0c298N11e6aedb8d0f52fbN125f7ba8ce7091efN1497b591790cf9c6N14a5e092ecc497e0N152b4a61ae018e37N154e7fe181c5c2d1N155ab3b0dbcded39N15d845116273fa06N165f1ccda250433eN16989d89571b5bcbN16e1445497cc61c0N172841f25ea919f3N17d4ae04d10a7fe9N180efcacaf45cf23N186f2aec4108715bN189e333181973716N18c0bddf56746d92N18c11f15215ec38cN194334f740f388b1N1986bf8c0ac28e40N1ab93df399e92e02N1b355b05d2d38085N1b3efdc99754d83eN1cd5090cfd08b6b4N1ce5e0100b4749cdN1d1899aeb6425727N1e2a080ee040a43bN1ed320a13d9770f3N1fac7bab401a1b34N1fc445212d52e1cfN202ee7b917685d93N2088e9e8fa9d42e9N21af9508aa3bb9fdN21ef3bb981e7fb3eN2213f94e18386cbdN2277db92f50e9215N227a5ca16f1f2146N2283f6a7c3a318c1N230b3856dd81cd6eN23175e0636bfe4baN23d72fbaa5ea3b21N23e83c62b57477adN2401bb716f41e70aN241242cef6e2c0e1N24e026c27784f4beN25fe1a551e669237N26824756a680fc4aN26b426ac4883a7eeN26fe159272325949N2716866532af8ec9N279bdad85ce2c3ccN27bff386d622ca4aN27c6d91bcdf1aa61N280c59c9206de54aN28131d64aa7aade4N2832ff6141d9efbfN28dac349434a7ad5N29036b280bb23e55N298760de68709f42N2989f5cbf1744823N29d48174d83daa30N2a4cee7e5e886cc3N2b299ab1052f367dN2b52e70343aea0dbN2b5b083bd0d93128N2b9cf5ef21359a2aN2c95c912d83e2ef9N2d053c06fb84a6a0N2d123259a6ab484fN2d22c53225d43878N2d52ef3247b23c97N2d7e1f274c2b6c46N2d80c39b6a4ec2ffN2e2cd5bf57836342N2e35cf400d4c2133N2e522b72df3b8cbfN2e61479ffc0e20bdN2ea0d448956f40a2N2ede112d8c89c093N2f5418af6d7ac9f1N308a476ccd9f2074N30c9d7982afa7dfcN3116bae7198b068eN31d07e1a7bd83ecaN31d8e508f8005057N32da6af904617612N331505d97d85f2ecN3325f79343abd8e7N333dbcdb8db241b9N3359caa795dbfb25N33cf86da81532817N33d6887e7c0a3c27N33e15397ce4f92e0N34991f2c3e41447eN350b4ee72c0d2bafN3553ea35d823c6c6N3598765b073a60faN36d7758eac8b6a06N36e40e96a90a5b6cN3793cf88d5fb8f0eN388f2705efcd88beN394ffe057ebf3680N3950a706cec973f5N39c954f52558db5bN3a7ecbe5221fc51dN3b03f972762acd65N3b787a071ff29c9fN3b926fce1f028e45N3bd83495d712a766N3bda9684c43dbfebN3bfe85e80052f744N3c7d49521fd60dbdN3c94f3980902331dN3cb3d160c091270dN3cd326deba31ed61N3d7107dcd313ffa9N3dae52ec87a008a8N3daf2d5ff1f37637N3db71f9ccc588b58N3dcb31407c594da2N3e0d4879a7a22cf6N3f8f9988dfbc93c2N3f9327900cc7af94"%lxh.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_ECP_MOD_P192 : Z := 0x3c478.

(* [comment removed for export] *)
Ltac ecp_leaf_gc :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | u32arr _ _ _ _ => fail | rw_cells _ _ _ _ => fail | bytes_at _ _ _ _ => fail
    | context [zlow _ _] => clear H | context [zswrap _ _] => clear H | context [Z.b2z _] => clear H
    end end;
  repeat match goal with
  | H : 0 <= ?v + 2147483648 |- _ => is_var v; clear H
  | H : 0 <= - ?v + 2147483647 |- _ => is_var v; clear H
  | H : 0 <= ?v, H' : 0 <= - ?v + 18446744073709551615 |- _ => is_var v; clear H H'
  end;
  repeat match goal with v : Z |- _ => clear v end.

Section RED.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01A0@L10311464405.81 L11803550370.82 L11805629605.85 L12836469452.83 L19026695374.123L21765854580.81 L21887662552.111L21887662552.80 L22000474640.111L2211492706.81  L23587552326.114L24167279349.81 L27775132660.81 L28689697126.147L28692136132.74 L29012665503.110L32453224331.81 L33510041944.111L33510041944.81 L34290115814.80 L35754698159.83 L35754698159.84 L38017522480.129L3818668784.81  L3820734411.147 L38443780964.81 L39945925021.111L41562522430.110L41930202676.112L41942718641.81 L43061838089.78 L44152525618.4  L44622288685.83 L44622288685.84 L45293014477.81 L4541941209.2   L45425587647.3  L4742244590.153 L4742244590.154 L4742244590.155 L4742244590.156 L47501154741.114L47759495350.153L47759495350.154L47759495350.155L47759495350.156L49698585326.83 L49698585326.84 L50807132385.110L52102261165.153L52102261165.154L52102261165.155L52102261165.156L52616107219.126L54052327864.111L54054590744.147L54391891673.84 L54392444536.154L54392444536.155L54392444923.155L54392444923.156L54398396379.154L54398396379.155L57628696595.14 L57628700040.8  L59314873579.156L59314873579.157L63559401084.114L65054579130.113L65502165646.74 L65502251305.123L65699637964.152L66083662040.111L66083662040.81 L68616792782.147L7024252226.153 L7024252226.154 L7190686615.102 L7190734735.81  L9144264913.81  L9716869748.80  00000@00i01N02002Y02c02m03703A03T04804B04L05=05[05\05f06006:06D06`07?08508H08k09A09_09i0:30:=0:[0:i0;a0<\0=F0=G0=H0=g0>a0?[0@P0@a0AH0B20B\0CC0Cc0DF0DP0E10EU0F90FZ0G30G=0GW0HD0I>0J80K30Kn0Lh0Mb0NN0Ng0P80QH0QZ0RC0RM0R[0S=0SG0SQ0Sk0TL0Tm0US0V90VC0VMS1L2sp2dX3DHI2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2I4S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22B0S2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L2sp2dX2lo3SLO2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB1HS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2ra2sp2dX2XB2HB5Ha_st5Hl_stS2sp2s02dX2XB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XBS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L2HI2sp1h2dX4HTOP2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2dX3dX22n22N2S1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XBFFS2sp2dX2XB3dX22n22P'5lxwsf1a2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2XB2xx3HxxS2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n0S2ra2sp2dX3SPB2XB2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB2HB5Ha_st5Hl_st2s1S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21nS1L2HI2sp1h2dX2XB3dX21a1CS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C12C21l2l02Rb1HS1L2sp2dX2XB2I32I4S1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS2sp2dX2XBS2sp2dX2XB3dX2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS2sp2dX2XBS2sp2dX2XB". (* [comment removed for export] *)
  Lemma U_ecp_mod_p192_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P192 U_MEMSET_FUNC 12 144.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P192. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(MA) 2%nat. intros FLt1 _. flat constr:(FLt1) 4%nat. flclear FLt1. intros CH XAL X0 _. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add mpi_cells length] in XB. clear CH.
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 80%nat ST.
    do 14 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (MA1 : mpd_at usegs m1 LB dX).
    { eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; lia|].
      intros O. flat constr:((mpdr_blk_facts usegs L m LB dX (proj1 MA) O HBR)) 5%nat. intros _ _ I3 I4 _. cbn. lia. }
    assert (PX1 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1) by (eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]).
    clear HH MA MU WM.
    (* [comment removed for export] *)
    pose proof (U_mpi_grow_spec L HI HFREE HCALLOC HLS SW DIMG HND) as SG. unfold mpi_grow_stmt, U_MPI_GROW in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 12); rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3c4b0)) with (Z_to_bv 64 0x3c4b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OLDL : md_own dX = LHeap -> 0 < md_p dX /\ md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros O. flat constr:((mpdr_blk_facts usegs L m1 LB dX (proj1 MA1) O HBR)) 5%nat. intros _ _ I3 I4 _. lia. }
    presx_stack usegs L PXg ltac:(unfold mpd_ivs; destruct (md_own dX) eqn:?; cbn;
                                 [ split; [lia| exact I] | split; [lia|]; split; [pose proof (OLDL eq_refl); lia| exact I] | exfalso; apply NST; reflexivity ]).
    assert (PX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply (heap_presx_weaken usegs L); [exact PXg| lia| intros x Hx; exact Hx]. }
    clear PX1 ST MI SOK MK HH1 MA1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 _.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & _)|[Er EdX]] FRr]; [exfalso; subst r; apply K; reflexivity|]. subst dX2.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 12 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
      flat constr:((grow_ok_facts _ _ _ _ _ _ _ MA2 OUT2 GR ltac:(lia))) 9%nat. intros O2 N2 S2 P2 EA2 LEN IN2 PAL2 U.
      flat constr:((proj1 (Forall_forall _ _) HBR2 _ IN2)) 5%nat. intros B0 _ _ B4 B5. cbn in B0, B4, B5.
      assert (APX : md_addr dX + 16 <= md_p dX2 \/ md_p dX2 + 4 * md_n dX2 <= md_addr dX).
      { eapply (new_limbs_apart_range usegs L HI) with (SP := bv_unsigned sp); [exact HH2| exact MA2| exact OUT2| exact FRr| lia| exact DI1| exact DI2| | lia| exact XP| exact O2].
        intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      flat constr:(MA2) 2%nat. intros (CH2 & _) _. rewrite EA2, S2, P2 in CH2. unfold mpi_cells in CH2.
      set (P' := md_p dX2) in *. set (n2 := md_n dX2) in *. set (ws0 := md_limbs dX2) in *.
      pose proof (u32arr_bound _ _ _ _ U) as UB. assert (PB : P' + 4 * n2 <= 2 ^ 64) by lia. clear UB.
      pose proof (same_from_refl (Z.to_nat n2) ws0) as FS.
      clear MU WM. pose proof (munch_refl [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH0. clear HH2. pose proof (conj MA2 I) as MA0. clear MA2.
      clearbody ws0.
      (* [comment removed for export] *)
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 12 <= n2) by (clear -N2; lia).
      clear MU. pose proof (munch_refl [(P', P' + 4 * n2); (lo, bv_unsigned sp)] m2) as MU.
      apply (lxp_aevtM_of_evt _ _ _ _ MK). lx_mkR.
      lx_run_tac (PLAN [] [] 400%N); lx_tree.
      (* [comment removed for export] *)
      all: try (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
             tryif lx_is_zlit e then fail else
             match goal with H1 : 0 <= e, H2 : 0 <= - e |- _ => replace e with 0 by (clear -H1 H2; lia) end end).
      all: lx_gen_regs; apply evt_done; try clear U; try clear LEN; try clear MU; try clear WM;
        let mx := lx_cur_mem in let xP := constr:(P') in let xm := constr:(m2) in let xlo := constr:(lo) in let xsp := constr:(sp) in
        lazymatch goal with Hu : u32arr _ mx xP ?l |- _ => rename Hu into U;
          assert (LEN : Z.of_nat (length l) = n2)
            by (first [ rewrite ?upd_length; exact (unlock _ LEN0)
                      | lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ => rewrite Hl end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption]
                      | rewrite ?upd_length;
                        lazymatch goal with |- Z.of_nat (length ?l2) = _ => lazymatch goal with Hl : Z.of_nat (length l2) = _ |- _ => rewrite Hl end end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption] ]);
          (* [comment removed for export] *)
          repeat match goal with Hl : Z.of_nat (length _) = Z.of_nat (length _) |- _ => clear Hl end;
          set (lxwsf := l) in U, LEN; clearbody lxwsf; ecp_leaf_gc
        end;
        lazymatch goal with Hm : munch _ xm mx |- _ =>
          assert (MU : munch [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2 mx)
            by (eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia);
          match goal with SO : statics_ok _ _ xm |- _ =>
            eapply (statics_ok_munch usegs L) in SO; [| exact Hm| intros aa Ha _; cbn; clear -Ha B5 DI1 DI2 ACL DHI LO0; lia] end;
          clear Hm end;
        lazymatch goal with Hw : wmono _ xm mx |- _ => rename Hw into WM end;
        try clear ST2; lx_release_frame; lazymatch goal with Hs : stk _ mx xlo ?h |- _ => (tryif constr_eq h (bv_unsigned sp) then idtac else replace h with (bv_unsigned sp) in Hs by (clear; lia)); rename Hs into ST2 end;
        let xa := constr:(md_addr dX) in
        try clear CH2; lazymatch goal with Hc : rw_cells _ mx xa _ |- _ => rename Hc into CH2 end;
        repeat match goal with H : lx_opq _ _ _ _ _ _ _ |- _ => clear H end.
      all: (flat constr:(HH0) 2%nat; flclear HH0; intros HH2 _). all: (flat constr:(MA0) 2%nat; flclear MA0; intros MA2 _).
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mfin end.
      apply aevtM_done. unfold mpi_binop_post.
      try match goal with Kz : bv_unsigned ?v = 0 |- _ => is_var v; replace v with (Z_to_bv 64 0) in * by (apply bv_eq; rewrite Kz; reflexivity) end.
      lazymatch type of U with u32arr _ _ _ ?wsf =>
        (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] => lazymatch xa0 with Z_to_bv 64 0 => flexi 17%nat; exists LB2, (relimb dX2 wsf), 0 | _ => flexi 17%nat; exists LB2, (relimb dX2 wsf), MBEDTLS_ERR_ECP_BAD_INPUT_DATA end end) end.
      split; [first [reflexivity| do 2 f_equal; apply bv_eq; vm_compute; reflexivity]|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split. { apply (@HEAP_munch usegs L HI h2 _ m2 mfin mo2 _ lo HH2 MU WM ACL).
               intros a Ha NO. cbn in NO. rewrite HT2.
               destruct (Z_le_dec P' a) as [C1|C1]; [destruct (Z_lt_dec a (P' + 4 * n2)) as [C2|C2]|].
               - right. right. exists (P', 4 * n2). split; [exact IN2| cbn; lia].
               - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                 + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                   exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                   unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
               - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                 + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                   exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                   unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..]. }
      split. { eapply relimb_at; [exact MA2| exact O2| rewrite EA2, S2, P2; unfold mpi_cells; exact CH2| exact U| rewrite LEN; reflexivity]. }
      split. { eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; rewrite O2; discriminate| reflexivity]. }
      split. { eapply (reducer_presx usegs L HI) with (lo' := lo); [exact HH2| exact MA2| exact OUT2| exact FRr| exact O2| exact EA2| exact PX2| | exact WM| lia| lia| exact DHI| exact DI1| exact DI2].
               rewrite EA2. exact MU. }
      split; [assumption|].
      eapply reducer_R_ok; [exact MA2| exact OUT2| exact GR| lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_ECP_BAD_INPUT_DATA; lia].
  all: match goal with |- ?gg => idtac "REDLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

