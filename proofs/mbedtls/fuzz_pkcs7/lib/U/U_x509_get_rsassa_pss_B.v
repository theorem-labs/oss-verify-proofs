(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_int U_oid U_oid_md_alg U_asn1_get_mpi U_platform_zeroize U_asn1_get_alg_A U_asn1_get_alg U_asn1_get_alg_null U_x509_get_hash_alg U_x509_get_rsassa_pss_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007e9cef20932bba 1 1 4 3 1 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P00864c340d01949d 0 5 1 1 3 1 37 1 52 1 53 1P008aa3971e8a78d0 0 4 0 1 3 1 61 1 62 1P00d535532d684dbe 0 5 0 1 5 1 12 1 57 1 59 1P00d7fc501a637d5c 0 2 0 1 7 1P00fc74167fa2b76c 0 2 0 1 44 1P022203c7e1d1fafc 1 1 4 3 0 1 60 1 63 1 4 2 1 61 1 62 1 64 4P02ed43490129c193 0 2 0 1 5 1P0588ebd970448882 0 2 0 1 6 1P0596ed4e760e81d3 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P05987ec47dc1a7ec 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P05bca8960701234d 1 1 4 3 0 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P05cdb42e5b82693c 0 5 1 1 3 1 37 1 52 1 53 1P069784ac85f45f20 0 4 0 1 43 1 58 1 59 1P0838715dd09f8bd1 0 4 0 1 3 1 61 1 62 1P099f7a79ae38074b 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P09dc86f6efbcd0fc 1 1 4 3 1 1 60 1 63 1 4 2 1 61 1 62 1 64 4P0a0a713ccbe81234 1 2 16 2 0 1 49 1 16 2 5 1 50 1 2 51 1 52 1P0a325cd09be03526 1 1 4 3 1 1 61 1 62 1 4 2 1 60 1 63 1 64 4P0b5a192af4641d7a 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P0c93f6f21c1ea680 0 4 0 1 2 1 62 1 63 1P0da60e48a35b2407 0 2 0 1 35 1P0ddc5f42832b57bd 0 2 0 1 1 1P0e98cd4f0c0378ae 1 1 4 3 1 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P0eab1b69b1335e4f 0 2 0 1 5 1P0f0b14f6d4d5c683 0 2 0 1 44 1P0fa828f1423da30c 0 3 0 1 5 1 53 1P0fead46daa3b644b 0 2 0 1 5 1P0fede9eff532267b 0 4 0 1 2 1 51 1 52 1P101c40f090d9b65e 0 4 0 16 21 16 58 16 59 16P105b92ae0055e16a 0 3 0 1 4 1 51 1P10b2e6e99f56ca8e 0 5 0 1 4 1 13 1 52 1 61 1P10c22b0e9ab3e3d2 1 2 16 2 0 1 58 1 16 2 14 1 59 1 2 60 1 61 1P113ade138a3399ad 0 2 0 1 5 1P114474d4fd69e5b2 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P114532c3fc5b16d1 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P119b0e3af848bfe4 0 2 0 1 1 1P120de04e55d0b575 0 5 0 1 4 1 13 1 52 1 61 1P132ef2ddd0725981 0 2 0 1 42 1P1477a0dbe099fd21 0 3 0 1 34 1 43 1P1579bd4f2ebbeb63 0 2 0 1 5 1P16b617369687a8a2 0 1 1 1P16ba889af63671f5 0 4 0 1 43 1 58 1 59 1P16d537d0e1112be3 0 4 0 1 12 1 57 1 59 1P178f9f65f543762e 0 2 0 1 1 1P188a0b72268d3077 0 2 0 1 42 1P18e30a7a2d44e9ca 1 1 4 3 1 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P1adf4b23cd655c48 0 3 0 1 34 1 43 1P1b0a5101071ed063 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P1b1ca3bfde84e20d 1 1 4 3 0 1 60 1 63 1 4 2 1 61 1 62 1 64 4P1c12a35d1cf47529 0 2 0 1 5 1P1c283e2652b7ca1f 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P1c2b476b7e638cd6 0 2 0 1 40 1P1c5fa4e12ab86681 0 2 0 1 5 1P1d0302db75060b26 0 5 0 1 5 1 12 1 57 1 59 1P1d2b67565fdb5c1e 1 1 16 2 5 1 50 1 3 0 1 49 1 51 16P1dfaf04776f528db 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P1f4d4975cd7f6899 0 2 0 1 3 1P2018f00e2c1d8b37 0 4 1 1 2 1 60 1 61 1P20581eee5f5ccf07 0 2 0 1 7 1P2097f4d560113023 1 1 4 3 1 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P21aa45d52afb2539 0 2 0 1 1 1P21c269b5af380b4c 0 2 0 1 1 1P22e49fad457626f4 0 4 0 1 39 1 41 1 42 1P2432e6fb00238ac3 1 1 4 3 0 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P24f336140edf429f 0 2 0 1 2 1P25d4752d71d4960a 0 2 0 1 1 1P25e8e8b0719e1eba 1 1 4 3 0 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P25ee1a85a03ffee6 0 3 0 1 39 1 41 1P25f083d4f63154db 0 1 1 1P267e6bc3b6477601 0 4 0 1 12 1 57 1 59 1P283a01897a614a6a 1 1 4 3 0 1 60 1 63 1 4 2 1 61 1 62 1 64 4P29070c1d736b23b6 1 1 4 3 0 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P2b1034e04a726fab 0 2 0 1 5 1P2bdd7c5c02079ce0 0 5 1 1 2 1 36 1 51 1 52 1P2bfcedf614775e8b 0 4 0 1 2 1 51 1 52 1P2c561a55fd3a4cf4 0 3 0 1 39 1 41 1P2c767d489f6cb153 1 1 4 3 0 1 60 1 63 1 4 2 1 61 1 62 1 64 4P2cd9529251fde4d6 1 1 16 2 14 1 59 1 3 0 1 58 1 60 16P2e3c609d04e909a1 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P2e4571eeb170dba8 0 2 0 1 42 1P2e6917a15563858f 1 1 4 3 0 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P2e6f42474bc8ce49 1 1 4 3 1 1 52 1 53 1 5 2 1 36 1 51 1 54 1 55 4P2f574881565142c4 0 5 1 1 2 1 45 1 60 1 61 1P3022b558c47143f1 0 4 0 1 2 1 60 1 61 1P321eb194d79b8c15 1 1 4 3 1 1 60 1 63 1 4 2 1 61 1 62 1 64 4P326e0a090325423e 0 5 1 1 2 1 36 1 51 1 52 1P328563bbe3f805f6 1 1 4 3 1 1 60 1 63 1 4 2 1 61 1 62 1 64 4P329236f8b9857c26 1 1 4 3 1 1 61 1 62 1 5 2 1 45 1 60 1 63 1 64 4P3293a93c12d065ee 0 5 1 1 3 1 46 1 61 1 62 1P338c4dfd7a4df6b7 0 1 1 1P33a6a2c15d12db52 0 5 1 1 3 1 46 1 61 1 62 1P344bf3afaab164fb 1 1 4 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 4P3477989671516cee 1 1 4 2 45 1 59 1 3 0 1 58 1 60 4P35634f492a2a8e37 0 3 0 1 29 1 40 1P3644529b69c9b724 0 6 0 1 4 1 5 1 13 1 52 1 61 1P381073a2205b3562 0 3 0 1 29 1 40 1P38559033ce6e1391 0 4 0 1 39 1 41 1 42 1P390ae880114f42ff 0 4 0 1 3 1 52 1 53 1P3953aaecad31005d 0 6 0 1 4 1 5 1 13 1 52 1 61 1P398d88ccb7627ce9 0 2 0 1 7 1P3a0fda443f451190 0 2 0 1 6 1P3b2ffd2c925d66af 1 1 4 3 1 1 60 1 63 1 4 2 1 61 1 62 1 64 4P3b318e56010feac6 1 1 4 3 0 1 60 1 63 1 4 2 1 61 1 62 1 64 4P3b5ce5041ee30485 0 2 0 1 1 1P3cfb2b182b20b1c5 0 4 0 1 3 1 52 1 53 1P3d02d03e3d55f7ed 0 2 0 1 49 1P3e82541ee618b6ca 1 1 4 3 1 1 60 1 63 1 4 2 1 61 1 62 1 64 4P3f0e8b0ee2319e36 0 2 0 1 42 1N001ea7ad09d4a570N0057e87bd9285960N006cc4d1a0854afaN00b79f4f1aa5759dN00c14992a66bb502N00ebd292518f0902N01007363ed0f2cb1N01292aeef6a4892bN0137e9a013605d90N0140ed14b6982e6dN015da45f401edec9N0171f7382687758bN01b26445dc4081a7N01f44af608e79682N02115bdae4ac1aceN021a17d81eeba49fN026a9ed9f40c03a5N0285e732432a4463N03254cb274e56edaN0337669f27400be9N03641949a44b1069N0365953edeaad6c3N0372ad0593ae0431N03b32b7fdc8494ffN03e27767fcfb8d99N03fd406beb0cbeb2N04191ffd8a93d02eN0436b80b4af2a2f0N04435b131f8951edN0446222f6d03214dN0455f9333983cfd4N0481be3a39ff0af9N049cf62e226997f0N04c568602983fbf6N04ff2aee6269d47eN05201e04eabb4fe2N059beff9598e992dN05c7e370d0cd30ccN05d9d6b84a535accN05eb47534acfeb4eN060075fec55f1980N067688db5fdd385fN0685fe9dd546b731N068e741b218fd53cN069e27a39e290e0dN07076d9ecec192c2N07829b54cd21bebdN078c2fb0de3fc30dN0792c567babbac5bN07c4b1cb998610c2N0801c3313b10dc5bN08146fd472cef532N084818cc76b37244N08b43f64afc2c033N08de270d3a8e18e8N090ce1d91ccdd3d3N09139010c525d7cfN096be83367958dbdN09b7670a9ad09497N09fa45f521eb8dd7N0a548c038f689df6N0acdb59132868299N0ad52e919ae98d90N0b0334bdb28bfd8eN0b2f9fb11a737f0eN0b314026cc1ba2a3N0b38fda55403e00bN0ba1fd1e3a3e702dN0be0bfa09fbe4742N0bebe7b0ab3fef68N0bfee4e857ac5975N0c16aa4ccee773c1N0c3996b26fc60990N0c43281861456596N0c67d9edb2569cd3N0ca17659bd0424b0N0ca3136635c1fcd3N0cb5b13eb3d221dbN0ce3d89a27f41d8aN0d473d09c221ceceN0d646ed16bfe2a83N0d6c310ad5e34bacN0d8316ff2960d965N0da1cc86b5c6bb9aN0dedc9702d197057N0e0000142fbedcaeN0e547dc973b39152N0e75de1583a75236N0e96a31b254e4eccN0ef0d164a1f58f5fN0f080d3201b846fdN0f4e01bcc89b20e1N0f6c89818d3ad4daN0fdc65575ed4e10aN1045bdf343ab38c4N107119559a0907a5N10d466f506a56e55N10faac201137f979N112901075d565218N112fcfd1a3865f42N115fa33b3905ebe5N11a489373e382917N11c1b4869ab5a57dN121496fbaa9da312N121672eaba12290dN1263bab6b166e6ccN126f2594bc3c1ae6N1282c6e803dba85aN1284eae977efa500N12cd701e1b71d682N130dc5c7d49e4700N1331667cfbd273c6N1350fa59ff0534d4N13a08cb2d5a18216N13b0c62fb205314bN13ca6ab776f22bd8N13de38675625c7f1N145f54fac3ed8a95N14678453510e4a10N1468276a697a1e0eN1491ee7c38fcb62eN14a6af75f5830a41N14ba61b256a306e6N14bb05a420598c99N14be3e3dd543024fN14bf2d3347a566c4N14dad2b2113455aaN15170c7d6d0bc5b1N152273f9905bc3f8N1536d0ad1adfea69N153a32bd7e7cb279N153e23ccedd9b0daN15a7868a1a95bfc2N160c154021f84a94N161915ce2215d724N162c92b268a11f70N16c884484f3172f1N16d11047faa9017aN16fe652309d574d5N170ecc3cc5d50c9bN17301597ca83a9c4N173b3298ae605a05N1751ee19aa5a45c0N17a97e0793c952dfN17b92e48add7dfbbN17ed15e8fa0c0861N182a3f947c13ad66N184aa8dc8d31382bN184f30be579d70caN18521d8435c2c414N185851213dc72353N18735971cee77988N188161ecb0af329fN188b2774878ed850N18abd078434a0835N18b080cfc738c993N1903291ccbad26b0N1922842452592df5N194c7b7963a8838eN19a98f4f6640e5c4N19b0b02bfa97575cN19b5c0d66585f9c8N1a0ef15ba8641f47N1a0f40ab02f2259fN1a6747cbf22c004dN1a6be004c98402f8N1ab91220f8738951N1abbe67ea1935c07N1acb1c92b85c7cbfN1ae0e7886f7fd841N1b3c7a3c19587cc1N1b6533c6659ba314N1b856ffb42c5d477N1ba4553f43c01647N1bbd85dfe53a63a8N1bc3e31b72be2080N1bcaeba60bab21b5N1bcfa8185d0ebe01N1c516de08abd89efN1c8ad87225e066edN1c95eda377b2d478N1c99f17c7e3fa93fN1ca8ef75ab8e53deN1cff5e2bb7c40671N1d07e6e400e0e1a5N1d268fead57b07efN1d651cb8990592dfN1d6eaa769e2f7bb8N1db2f61c26cf7044N1ddcbeb8b1389babN1e0dd7e6b873a4b4N1e0e1b4123946d10N1e36366537d6365fN1e41b8492a9a2b0dN1e7d560612232b27N1ea46d1ee60ef676N1ebd13c01e62a767N1f017594ecce6541N1f05924a378c833dN1f2aee2b993b8fc2N1f579e016d048943N1f60693df147f572N1f9aed8273d7aef3N1faedfa31b2c3653N1fe758dfec1b8e21N200950ed6135713eN2013af4a8aca7b15N20412ef84912d39cN206d3e529b54c7caN2114669113cd7d65N211641571d4ea571N21579bd29235461bN216a5ad077876a7dN21705abd372f08d7N2198a50ccf8e00cdN220b881cf7841202N222467a8535c23bbN223bd2d1cb05cfa7N22618ec1d71d1884N226dd355ed78000dN228959b6ef5a800fN22d36707ab778a6bN22e6f5225808ce83N22f51e2c73d26eb0N22f79eee80b9c2d3N232025702e32ce22N236f64121354baa2N23730f931c1c64baN23d673551805a138N23f78cec460420acN243b739473ea1594N24bb8bfc7172f8daN24e22ac461245608N25074029b40db786N2526d93b675c53a3N2530db80244d71bbN255d95593c2f4d12N25799165d82f7f09N25b34fa07077fba1N25f4895771c4184fN2619d3bfd68c2e34N2623afcc7ad93c35N26cf52eec1acca46N26d8fc579d59c809N2742d5bc33080cecN274fdc9c2057cb78N275c185d23a178cfN27acd91ca6926c48N280c53d8695eb29fN28180db25cdcd6faN281af2db5352bac0N28329c9eb7d67c68N2839a148f6639cbcN2846d7eb82767109N284760b3c4eb6218N287d4f266e7958c1N28c4f98132ed7cc9N2938917eb3e7fc3aN2a499daa455d58ceN2a5283d54336a4d6N2a5fa1aeb5a8bbc9N2a6fdbcd880d739cN2a7014f13efc44fdN2a761a5a07374b92N2a951d3b5cd13cb1N2ac33fe9729ac123N2ac7517a5087c0d2N2aed7309d564157dN2b24d3fdeb13fb7cN2b4df272e69f717bN2b56deb55736a6e0N2b5ac7cfdba520aaN2b5b15a0d4462d1cN2bad1b1b9767830bN2bc5a6f929fb26d5N2bd1c6d12221fccaN2beb4c281dda72c5N2c39cbd01a4636dcN2c3fc12131d1a46cN2c5bfca6d2d67d89N2c64ecc1354e752fN2c73f2223815a940N2c8edd90f7eb52fcN2caacd288581d3c3N2cb10499929c5552N2cc9a09113dc4de6N2d00b7aac4cad40eN2d2d18ded10b82c2N2d4bbfaf78f65175N2d5d8af6ce6ac482N2dcf1753846993caN2dd61462a2518d6eN2e3ebf8188fc0e86N2e52592cf71370ecN2e75f6e83ef02e23N2e7b21dffd87b8f9N2e7f4722d2cb9a5bN2ed1a9209326d00fN2effb14c5d9b3e76N2f17e69ebcdfdc66N2f413e4bc39fce30N2f78899018f9daffN2f9a52179ec82706N2faf8eda16806bceN2fb3c920fc768860N2fc56bebdf0f6d7bN2fea33399e81ac02N3023a7dbafc72623N303a7b78ebe3b326N30b020e671c94595N30d2bb4884b79054N30f4969b4f04ebf6N30fa30abfd5c99b1N310a88dff5a0936aN31379347dce5182bN317b695ae1ce46a5N3210d43f6f497426N326c856900eb035eN326e4b02100232bcN327dbfc427d59143N32bfd93165a8db6aN32c59e68b3ef3c49N32d06a9a1a4c3953N33a7ae160c573424N33dbd8c912e9b186N33fd354cf46ebefaN34195bec79cf0087N34268df43ced9c0eN342a9bb4ea2df4feN3440b5b0dd9662f2N3447c9ec12f75eeaN347b7dc427588728N34a303a1ea904699N34fd3796415168f9N35a8c03729bc5ec2N35bfc9a63687f24bN35ed00a8015ef4a0N3609beeb5ee50e91N36408c3c815aac00N3649193943da2abcN3675f3acb139c11aN3681021da9564bfcN36c7ade6f881d1c5N36d9de28ff21f5cdN36e4c3febc4d3882N36f237241f8c3002N370860410a2540f8N3762d187d2ab440aN377315aa1ee05926N3789a678b6bd7866N3794140e9c9367d0N37a55c6a7819b0dfN37bee15f5df62983N37cda23e505e7c6dN37e91b10965d2891N37f205ebd8b72794N3825d4b1b486eff7N383d26fa9fa8323bN38852f2c1d6e0697N38c0e2678dc6aa3aN3918e09394936838N39220d064bab8dc3N393c63d91e16213dN394b9493a869ebd6N395c4a26fa791acdN39a5c6a48c2d804eN39b5c60b371a128aN39dac5585e8b9a28N3a10c3b937eb6aa2N3a410e568f179e6cN3a57ca346568d0aaN3a6396cd4578b975N3ad69e56b94807bfN3af61b6c7ca1b72dN3b17f85f0a4d3941N3b298ffb80309c4aN3b381e53000f1fd8N3b660b408911cb71N3b6f4c0c79175d5cN3b88f308427a18aaN3b9e3cb9f9307ce4N3bc5211e7bc86d60N3bd5767ad2a589f7N3be3670df83026f9N3c4a5d9afee5e73aN3c6df205ffcd9f54N3c7743403e5e24e7N3c8ed707d9b81c6dN3cb5829d29398dabN3cb692cff31e3ddaN3cc6aa8a93b5171bN3ce52254283410a0N3cfcce1080392a00N3d145121e10153e0N3d1780c7c44c862fN3d17b382bdd41015N3d18dd1dce762861N3d42aec60d70e1dcN3d5bc75318c5b2d0N3d712dc468e0b641N3d721bb895223a5bN3dcd98409f64d860N3dcf2de848c2c97dN3dd995c2fbb575caN3e0a92138d44ee8bN3e5699b77b0ce0d5N3eec3f9cfd45d910N3ef297fa2fd62946N3f0006ebbdd581f5N3f2a4947a38fc432N3f61c3427be51bf4N3f6691bcfe784fb1N3f6bc3a91b64468cN3f6feabdf37a7172N3f814f714f852377N3f8533e17427c32bN3f866c939feba78cN3fa0937330d5073cN3fa304f56f04aa00N3fd9f759d346fd8eN3ff9e306e512b2d0"%lxh.
Ltac2 gd_tbl_P_x509_get_rsassa_pss_B () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_rsassa_pss_A.x509_get_rsassa_pss_params_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variables (MSF MDTBL : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word).

  Notation CTX := (rsassa_ctx usegs L MSF MDTBL U_ASN1_GET_ALG_NULL U_ASN1_GET_ALG U_OID_GET_MD_ALG U_X509_GET_HASH_ALG sp PAR MD MGF SALT BUF pp lo bs plen).
  Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - 240, bv_unsigned sp)].
  Notation POST := (x509_get_rsassa_pss_params_post usegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation ENDv := (pp + bv_unsigned plen).
  Hypothesis HC : CTX.
  Let exit_walk' := exit_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let sel_walk' := sel_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.
  Let s4_walk' := s4_walk L MSF MDTBL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m PAR MD MGF SALT BUF pp lo bs plen HC.

  (* [comment removed for export] *)
  #[using="MSF MDTBL PAR HC exit_walk' s4_walk'"] Lemma s3_walk : forall (p : Z) (j4 : list byte) (tfw lw : word) (qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 p)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    BUF <= p -> p <= ENDv ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 p) (Z_to_bv 64 SALT) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2798c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros p j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 mm
    F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK Hp0 Hp1.
  open_ctx HC.
  pose proof (bv_unsigned_in_range 64 plen) as PLR.
  try (unfold bv_modulus in PLR).
  try (cbn in PLR).
  (* [comment removed for export] *)
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
  { lxp_apply exit_walk. }
  lxp_gc. try lxp_statics.
  lxp_frame_cut (bv_unsigned sp + -128) [64; 72; 80].
  pose proof U_asn1_get_tag_spec as SP.
  unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SP.
  callx_sp (bv_unsigned sp + -128)
    (eapply SP with (PP := bv_unsigned sp + -56) (LENP := bv_unsigned sp + -64) (P := p) (END := ENDv) (BUF := BUF) (bs := bs);
    rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
  try clear SP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64) [C8 ?lw] |- _ => rename H into FL; rename lw into Lw end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q end.
  match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
  match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
  match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST4 end.
  pose proof (bv_unsigned_in_range 64 Lw) as LR.
  unfold bv_modulus in LR.
  cbn in LR.
  lxp_gc.
  destruct (Z.eq_dec r 0) as [R0|R0].
  2: { assert (RN : r < 0) by lia. clear R0.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
    all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162228; lxp_apply s4_walk ]. }
  subst r.
  specialize (HL0 eq_refl).
  destruct HL0 as [Hq HqL].
  try clear Hr.
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
  lxp_gc. try lxp_statics.
  lxp_frame_cut (bv_unsigned sp + -128) [72; 80].
  pose proof U_asn1_get_int_spec as SPI.
  unfold asn1_get_int_stmt, U_ASN1_GET_INT in SPI.
  callx_sp (bv_unsigned sp + -128)
    (eapply SPI with (PP := bv_unsigned sp + -56) (VALP := SALT) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
    rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
  try clear SPI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q2 end.
  match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
  match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST5 end.
  lxp_gc.
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
  all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162228; lxp_apply s4_walk ].
Qed.
End Walk.
