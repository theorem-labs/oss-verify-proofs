(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_x509_get_uid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P008edbd0b96ecf0a 0 4 0 1 37 1 49 1 50 1P0099b62e735a69fb 0 4 0 1 35 1 47 1 48 1P02e6e1854e2bdef2 1 1 8 3 1 1 41 1 44 1 4 2 2 42 2 43 2 45 16P02ee96adc034e353 0 2 0 1 34 1P0353ad7c30bcde03 1 1 8 3 1 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P03552f8e9454c336 1 1 8 2 0 1 34 1 3 14 1 35 1 36 8P03ac89e5f7a62c98 0 2 0 1 2 1P03b5fa650b94b5b2 0 4 0 1 28 1 29 1 30 1P03de8b31169115ef 1 1 8 3 1 1 42 1 43 1 4 2 2 41 2 44 2 45 16P045d16059cbe46c4 0 4 0 1 34 1 46 1 47 1P05d7a40f942c8a0f 0 2 0 1 3 1P0619d5fdf2fda724 0 4 0 1 1 1 29 1 30 1P0628251666cdb4a8 0 2 0 1 30 1P062f314b3ab8a0ae 0 3 0 1 3 1 32 1P06c69f0301abc4ad 0 2 0 1 34 1P07e56d2d3e5a2471 0 5 0 1 1 1 28 1 40 1 41 1P08c152921700d04d 0 4 0 8 18 8 39 8 40 8P090d3420f5160c37 1 1 8 2 0 1 49 1 3 29 1 50 1 51 8P090fa894c1519a12 0 4 0 8 28 8 49 8 50 8P09afccd043c0d0a2 0 4 0 1 35 1 47 1 48 1P0a06a5060f16c1b9 0 4 0 1 34 1 46 1 47 1P0a60de2450dbab64 0 4 0 1 27 1 30 1 31 1P0acc89d76526db1b 0 3 0 1 28 1 29 1P0ad6c60eafdfce0a 0 2 0 1 32 1P0b0224f0bbb31e8d 0 2 0 1 32 1P0b2396a5244e8487 0 4 0 1 24 1 34 1 35 1P0b4d96937af6faac 1 1 8 2 0 1 39 1 3 19 1 40 1 41 8P0b97eefa2e38d9d1 0 2 0 1 6 1P0c0a3f8ef9010cb4 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P0e0ff31901c2ac87 0 4 0 1 34 1 46 1 47 1P0e3491e6724665eb 0 4 0 1 4 1 33 1 35 1P0ec04b696051c6bf 0 2 0 1 34 1P0ee0da4406bb3f57 0 2 0 1 1 1P0f28b0381637ac01 1 1 8 3 1 1 42 1 43 1 4 2 2 41 2 44 2 45 16P0f79880aef3d0fde 0 2 0 1 1 1P1082c3d91d439197 0 4 0 1 2 1 43 1 44 1P10d020564e90a0fb 0 4 0 1 27 1 39 1 40 1P10e9634d37a15145 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P10eeb9887ac288f3 0 5 1 1 3 1 30 1 42 1 43 1P111b3e82e4fd1764 0 4 0 1 34 1 46 1 47 1P1138c5e70c6df594 0 4 0 1 37 1 49 1 50 1P115f07109b123bda 0 2 0 1 1 1P120f1e22110ca9c0 0 4 0 1 2 1 43 1 44 1P12297eced3c9c89f 0 4 0 1 1 1 40 1 41 1P12f80a3d41a04519 0 4 0 1 1 1 40 1 41 1P1356cf682d862c72 2 36 1 1 8 3 1 1 52 1 53 1 5 0 2 39 2 51 2 54 2 55 16 1 1 8 3 2 1 51 1 54 1 4 0 2 52 2 53 2 55 16P1358aec7f6e78396 0 4 0 1 37 1 49 1 50 1P13c586fe4f6805af 1 1 8 3 0 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P13d367ec138f5ef3 1 1 8 3 0 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P13d8fcce7a40c155 0 4 0 1 25 1 35 1 36 1P149382fa2ad003e8 0 4 0 1 25 1 35 1 36 1P149fc17c43ba9092 0 2 0 1 5 1P14f2fe6afef0d5e4 0 3 0 1 27 1 31 1P15275e16e6797e27 0 4 0 1 35 1 47 1 48 1P153a5f8d07455be6 0 3 0 1 1 1 30 1P153b950f5a0f323c 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P15aa00e500a37116 0 4 0 1 27 1 39 1 40 1P163d44f6bb096ff5 1 1 8 3 1 1 41 1 44 1 4 2 1 42 1 43 1 45 8P166ae0a711d03e7d 0 4 0 1 24 1 34 1 35 1P16a440975e29a682 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P16d66f034a2ae94e 0 4 0 1 35 1 47 1 48 1P17ca7f8f3f78e665 0 2 0 1 2 1P18994953cbe7a10f 0 4 0 1 27 1 30 1 31 1P189c96adf2df392e 0 4 0 8 19 8 39 8 40 8P1937e1a4e4c57e58 1 1 8 3 0 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P1952e2e9c1457c57 0 2 0 1 1 1P1a3ea0d3dd6b168a 1 1 8 3 0 1 42 1 43 1 4 2 1 41 1 44 1 45 8P1a5bf49f9a72e6c0 0 4 0 1 25 1 35 1 36 1P1aa00823e6077383 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P1ad54349a3c64f59 1 1 8 3 1 1 41 1 44 1 4 2 2 42 2 43 2 45 16P1b0041b3b9c236d8 0 4 0 8 13 8 34 8 35 8P1b563a2e873edab4 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P1b85b9ed73570624 0 3 0 1 28 1 32 1P1c6487da873de69f 0 4 0 1 34 1 46 1 47 1P1cc92dbdeaab9aa3 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P1cccb8b3e2b1efca 0 4 0 1 37 1 49 1 50 1P1ce0e654580bc91e 0 4 0 1 24 1 34 1 35 1P1d1679bf16bfb713 0 4 0 1 25 1 35 1 36 1P1d7b9c2c21d4171e 0 4 0 1 34 1 46 1 47 1P1dcf548c2ff75f23 1 1 8 3 0 1 41 1 44 1 4 2 2 42 2 43 2 45 16P1e335408cd3835ab 0 4 0 1 37 1 49 1 50 1P1e934553c0bac7e3 0 4 0 1 28 1 29 1 30 1P1ea90144317108d5 0 4 0 8 28 8 49 8 50 8P20aae44c84f7b895 0 2 0 1 5 1P20d3a593334fd1b2 0 2 0 1 5 1P227ef96e7942109f 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P22f04a7b3086e200 0 4 0 1 35 1 47 1 48 1P2394981f620ae96f 0 4 0 1 24 1 34 1 35 1P23b52788d97723c3 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P2492b7764dc1b0f1 0 4 0 1 24 1 34 1 35 1P24f397a2c4ed6b5b 0 2 0 1 6 1P260392c214cf3cda 0 2 0 1 30 1P268e9c59a19f8b4e 1 1 16 2 22 1 39 1 3 0 1 40 1 41 16P26a64a68ec96fd6b 0 2 0 1 1 1P26cd8711dd970104 0 4 0 1 34 1 46 1 47 1P275d3bf13c06ba88 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P27a46a3850b317d5 1 1 8 3 1 1 41 1 44 1 4 2 2 42 2 43 2 45 16P27bd0942aac62ec4 0 3 0 1 31 1 35 1P28a0dad4368bf236 0 4 0 1 25 1 35 1 36 1P28a81e3316c7827e 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P28d9e0b84d30311a 0 4 0 1 37 1 49 1 50 1P2a0af82529e27ff2 0 4 0 1 1 1 40 1 41 1P2ab74e75379d225d 0 3 0 1 28 1 29 1P2abfc4dbe56f56e8 1 1 8 2 0 1 49 1 3 29 1 50 1 51 8P2b1b40ed8a3dd1a3 0 3 0 1 27 1 31 1P2b6903cd8fc46365 0 3 0 1 1 1 30 1P2bca684a8e9cf2c1 0 2 0 1 31 1P2cc8e4f45523b04e 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P2cfa3cfe0013c3b9 0 4 0 1 1 1 40 1 41 1P2e788ea05e350b36 0 2 0 1 5 1P2f1dcab55c1eb914 1 1 16 2 0 1 39 1 3 9 1 40 1 41 16P303e7165cd2bb3ff 0 4 0 1 35 1 47 1 48 1P307ae59ce6881749 0 4 0 1 25 1 35 1 36 1P309c305a035bdd25 0 4 0 1 25 1 35 1 36 1P3153a1af0320894c 0 2 0 1 5 1P3198fad77b66bedd 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P31f2578398dabe10 0 4 0 1 1 1 40 1 41 1P32043c7d56949944 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P33121dd6915f6e86 0 3 0 1 3 1 32 1P335d6e1869717792 2 35 1 1 8 3 1 1 52 1 53 1 5 0 2 39 2 51 2 54 2 55 16 1 1 8 3 2 1 51 1 54 1 4 0 2 52 2 53 2 55 16P34ea31f7f87dc83d 0 2 0 1 1 1P35c06555c89cb028 0 4 0 1 37 1 49 1 50 1P35e5b32a8c9566fe 2 25 1 1 8 3 1 1 42 1 43 1 5 0 2 29 2 41 2 44 2 45 16 1 1 8 3 2 1 41 1 44 1 4 0 2 42 2 43 2 45 16P371984dab3804e20 0 2 0 1 7 1P38551f9707904975 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P3875510c50dc4b95 3 21 0 2 1 1 2 1 0 5 0 1 3 1 27 1 37 1 38 1 0 4 0 1 2 1 37 1 38 1P392fe18804e9b407 0 3 0 1 4 1 33 1P3931ce69b81b6458 0 2 0 1 2 1P39465672cb2067ab 0 2 0 1 32 1P3ac7f3467d64b08a 1 1 8 3 1 1 41 1 44 1 4 2 2 42 2 43 2 45 16P3ad577b1e4ff0f3f 0 4 0 1 3 1 32 1 34 1P3adf90fadc7a8b9b 2 22 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P3b54ad5f51114c18 0 4 0 1 27 1 39 1 40 1P3bf8fdb11a135f71 0 2 0 1 35 1P3c1634d1b5b6e522 1 1 8 3 0 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P3c9c64520f68a7f3 1 1 8 3 1 1 42 1 43 1 5 2 2 29 2 41 2 44 2 45 16P3d105ba1f1b47f84 0 4 0 1 24 1 34 1 35 1P3d243f6eac347079 1 1 8 2 29 1 40 1 3 0 1 39 1 41 8P3d7aaf9121c8d073 0 4 0 1 3 1 42 1 43 1P3e5cb79b8e519a32 0 4 0 1 35 1 47 1 48 1P3e5edfa488b0e943 0 2 0 1 30 1P3e9a321bdc3e2baf 2 23 1 1 8 3 2 1 37 1 38 1 5 0 2 26 2 36 2 39 2 40 16 1 1 8 3 1 1 36 1 39 1 4 0 2 37 2 38 2 40 16P3fcdee431ab2454d 1 1 8 3 0 1 41 1 44 1 4 2 2 42 2 43 2 45 16N014db80a6d4ebe20N0167aa0b3a96b6ebN01ae79bd286a7af5N01bd0ec2050c63dbN01c2099cec8a5eb3N03003dd170b60914N030a712171af1f5aN04123960f2cb9001N042967a0a7c7a695N04628f43ccb65a9cN04dc427b3071b078N04e43cad169258ddN05252f22e1b8e1d5N0536b0091c46b1ecN054ae1275cab9be5N057088ddb7aee964N0591c87e966129baN05ac0aa132dee814N05bf4f8e0a737c3fN05c9215798313bb4N05da2dc15d4f580fN062861049694ad9eN0629198f43c58d28N06b2ae982af73ad6N06eb64a48465b73dN071106e3c16e80a2N07148ae30ddff1feN071e04d640e5ca6eN07f66db376eb458bN07fe4362c8207703N080e7915a85b436dN084661447baaa697N08ea69353d703782N091b2cbd555b5b67N09870cf34b7abf0cN09956da72c10cce4N099e779cf48a51fbN09caeb6e2075b27dN0a6f6d1086bd252aN0af563fd572c6c97N0af88463f83509e7N0b04d3f89447474aN0bdb97d106b66fd8N0c590cf174275826N0c638f3a37daf964N0cdf2f80f6dfdd44N0cff258c538c634cN0d4801f93e8ab4a3N0d61cfdbcaf77ebfN0d6215a70abdc29dN0ed863dbb97198c7N0ed952296c5a8d01N0edf3663472d8095N0f02da9d1a572a59N1078d89a875044daN10851d28f0ff5cf8N112ee7746ea3ab15N11606d1278113712N1175e43aaff8c37bN1195a907aaa4d83bN124ef7c14899cee3N1259e52e5ed5f46bN127c25ab328461f3N12a18588a7d777bdN12cf5a3d0b856cc0N130a814d93991442N1398c2ef71908446N13e06c72ca50b192N141f68bc53fd3809N147a724b2984c9afN148e40193f098ce0N155b48d021cf5646N15d8abac2cea6ac9N161d137536874940N164baf01a4f8b9bfN168a4b2b8ece18e4N16eb7cb2b3ed01ebN1727602883463f69N173a970a601178c7N1771e912ddc12e00N17723de33d8b3b06N18477e188c29d5d3N18f85111c27bac93N19d936937a65fdbeN1a0689281a87cbe0N1a18f3bca3a06f44N1a5c354197edd3a4N1aef67e24c870866N1b1eef4be2b7d797N1b697d47942026a1N1cdbe729809830d0N1d053fb42911ebb8N1d293e9afcfd5766N1ec49eb4dfcb63f4N1f18bdf34a068c7fN1f93e36576741be0N1fea8fd5e25aa6f2N20311c3a5d7fc7f6N2045ddfbb61d467fN207e139c253aa6e1N20c417f408012984N217d2bd9bafe9093N224a014536a932fdN2254a8ae1b7201f1N230fc049f384b978N23124b3cf02a9772N24c94d1f7422bf89N24d33c37734e3f1bN24e2b88c78162b4bN251ecaacc9ac916aN255278b8f545d51dN255f0bebdc0c123eN256260805317f758N258363b45e56277cN25f02c02d612bcbbN2682149a5df328caN26d05ec5da9bc1a5N26eb6cbcc4ccceecN26f3336e95fb3790N27e393b7e91e9b53N280f2a99b808cae7N281b2e2757f7cd31N283e56447d9b66b4N2914a7118f7ae56cN297df1a0f4ee4817N29f59151fcace872N2a0be8a64eb04014N2be4f4389d679c46N2c1a91e06ef35442N2cb287a99c2da32dN2cd3155e447dddd7N2d5b8d46d0377827N2d7efafa7834f656N2d8add97eb63a077N2dd9e591b5dd23e9N2de4e1119145fd3bN2df4d786efe420c2N2e21fc602d05eba7N2e23fa9cff884721N2e4c11bbeba66c0dN2e657f3fe5c17781N2e667451924e09d0N2edb4e94566124c8N2f139d04827884efN2f6e71edfde53bb1N2fbb5cc7f048d9f2N2fd6f5b9538725afN2fe5151880814fadN305988f1fe99c853N3079e6fb5f734ecaN314ac0af28242259N3165642a6f40f068N31a960efa39f8de0N31b88011165e4054N323d1c0e70cce3d8N324f5fa0b3299531N32ca07642c013147N3329da106cd99799N3352cc0791584aa1N339de7c7b1b6c062N3467de7361fa80d7N350edd0e0b5c040dN35ce5ddbb5a4465fN36352bfec534eb61N366e3d43dc9a2f26N36da4b969de6ee0bN36f1bc1ba366f53fN36fc2c33d95f6c8dN371e05bfbb540823N37f50849aff7465eN38375a1ad5f68c1bN3851adba7a453827N3865b68abe03a8c2N3a3c598e5973bb98N3a4ed5612bc7391fN3aaa0919352a727aN3b658f9951b30c38N3b79e704cc5cce6fN3bb6e1b9840a5465N3c5291967af135ffN3c77a9a73a3016fcN3d5e0efc0e1eb199N3d7976a4d0b7e96aN3df5509ebe32a32dN3e2dcf5d0601b2c0N3e3d600a53c61bcbN3e529862939f3089N3e8f4ce33880d4dcN3eb5ee866a0abf7fN3f3a1b016501b7fd"%lxh.
Ltac2 gd_tbl_A_x509_get_uid () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "x509_get_uid_postA"].


Definition A_X509_GET_UID : Z := 0x0aa4b0.
Notation X509_GET_UID_STACK_A := 64 (only parsing).   (* [comment removed for export] *)

Definition x509_get_uid_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP UID P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_uid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.(2.&40.)Lln,(2.&40.)(1.(2.&40.)Lq,(2.&40.)(5.(6.$0.R16.(7.(8.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(9.O19.)O8.(:.(2.&40.))R6.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O18.)+40.)(12.&40.O18.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1:.O1.R6.)(5.(15.O1:.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-3000.R5.)(18.R5.=))(5.(19.O1:.R6.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1:.R6.O6.(=.$1:.(1<.R3.)(=.$1:.(1<.O2.)(=.$1:.(1;.R2.)(=.$1:.(1;.R1.)(13.$1:.))))))(5.(1=.O1:.R6.O3.(12.&40.O18.))(5.(18.O5.R4.)(18.R4.O4.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_uid_stmtA {L : heap_layout} (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP UID P END BUF lo n : Z) (bs : list byte) (tg0 pad ln0 q0 : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m UID [C4 tg0; C4 pad; C8 ln0; C8 q0] ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= UID \/ UID + 24 <= PP) ->
  (Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (Z.of_nat (length bs) = 0 \/ UID + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= UID) ->
  PP mod 8 = 0 -> UID mod 8 = 0 -> 0 < PP -> 0 < UID -> 0 < BUF -> 0 <= n < 16 ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_UID_STACK_A -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (UID + 24 <= lo \/ bv_unsigned sp <= UID) ->
  (Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  (* [comment removed for export] *)
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m PP 8 -> aobj segs AL CS m UID 24 -> aobj segs AL CS m BUF (Z.of_nat (length bs)) ->
  crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 UID -> a3 = Z_to_bv 64 n ->
  evtA segs AL CS (x509_get_uid_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP UID P END lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Context {L : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP UID P END BUF lo n : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= UID \/ UID + 24 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ UID + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= UID.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis UIB : 0 <= UID /\ UID + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : UID mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < UID.
  Hypothesis Hn : 0 <= n < 16.
  Hypothesis SPL : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : UID + 24 <= lo \/ bv_unsigned sp <= UID.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (UID, UID + 24); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (x509_get_uid_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP UID P END lo pad m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).

  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_uid ()) "Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ptg0,(2.&40.)Pln0,(2.&40.)Pq0,(2.&40.)P,(19.$1>.Vm,VPP,(=.$1:.(1;.(16.&40.VP,))(13.$1:.)))P,(19.$1>.Vm,VUID,(=.$1:.(1<.R4.)(=.$1:.(1<.Vpad,)(=.$1:.(1;.R3.)(=.$1:.(1;.R2.)(13.$1:.))))))P,(1?.$1>.Vm,VBUF,Vbs,)P,(15.$1>.Vm,)P,(20.$1>.VAL,Vm,)P,(21.$1>.VAL,VCS,Vm,VPP,+8.)P,(21.$1>.VAL,VCS,Vm,VUID,+18.)P,(21.$1>.VAL,VCS,Vm,VBUF,(22.(23.(2.&8.)Vbs,)))P,(1=.$1>.Vm,Vlo,(12.&40.Vsp,))(24.$1>.VAL,VCS,(25.$1>.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VUID,VP,VEND,Vlo,Vpad,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VUID,)(16.&40.Vn,)R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+::4;0.)Vfc,(:.(2.&40.))Vm,(;.$1>.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros a4 a5 a6 a7 tg0 ln0 q0 HPP HUID HBUF MI AB OPP OUID OBUF ST.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn [Z.pow Z.of_N Pos.pow] in SPR.
  assert (OUL : aobj asegs AL CS m (UID + 8) 8) by (eapply aobj_sub; [exact OUID| lia| lia]).
  carve_frame 48%nat ST.
  pose proof (sums_asn1_ok AL IMG) as LXSUMS.
  lx_pre. lx_run_tac (PLANS [] [(0xaa508, DJoin); (0xaa52c, DJoin)] 121%N [SUM_getlenA; SUM_gettagA]).
  lx_tree.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx END FORM main_walk: unexpected leaf left:" g end.
  Qed.
End Walk.

Lemma A_x509_get_uid_spec {L : heap_layout} : forall AL, asan_img_ok AL -> x509_get_uid_stmtA asegs AL A_X509_GET_UID.
Proof.
  intros AL IMG. unfold x509_get_uid_stmtA, A_X509_GET_UID.
  intros until q0. intros HPP HUID HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 Hn ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OUID OBUF SCS -> -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HUID) as UIB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, UIB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.
