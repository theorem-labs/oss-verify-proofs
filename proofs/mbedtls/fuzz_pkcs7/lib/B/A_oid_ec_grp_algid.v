(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX Image Statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums LxAOid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0050ac16fa4bb125 0 4 1 1 2 1 67 1 68 1P00bbe1a134d304c8 1 1 8 2 50 1 61 1 3 0 1 60 1 62 8P012088fdcc39c3a8 0 4 1 1 43 1 46 1 53 1P01297906f82001e0 0 5 0 1 50 1 57 1 66 1 67 1P01893fbecfc0e5dc 0 4 1 1 40 1 43 1 50 1P01b3aebc260f4e06 0 6 0 1 46 1 47 1 53 1 60 1 61 1P02b7cbc80b637663 0 2 0 1 1 1P02d377df92892acb 0 4 1 1 43 1 46 1 53 1P030b75db48e568f1 2 46 0 7 0 1 3 1 49 1 54 1 56 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P037d1890b6a51347 0 2 0 1 1 1P037fb703f51c9641 0 5 0 1 50 1 57 1 66 1 67 1P049bbcc328919bd7 0 2 0 1 1 1P049fd9a80d6145b2 0 4 0 1 50 1 65 1 66 1P04c02eb2cf1e1891 2 48 1 1 8 3 2 1 63 1 64 1 6 0 2 48 2 55 2 62 2 65 2 66 16 1 1 8 3 1 1 62 1 65 1 4 0 2 63 2 64 2 66 16P050ca4e37a8494b2 0 4 1 1 2 1 64 1 65 1P060985b04428acc8 1 1 4 2 0 1 65 1 3 10 1 66 1 67 4P0643fea604b61f57 2 47 1 1 4 3 2 1 63 1 64 1 6 0 4 48 4 55 4 62 4 65 4 66 16 1 1 4 3 1 1 62 1 65 1 4 0 4 63 4 64 4 66 16P064b4e3b41b08db0 0 5 0 1 44 1 48 1 51 1 52 1P069694c4a3bd3414 0 5 0 1 46 1 53 1 60 1 61 1P07073dc28ff510aa 0 5 0 1 48 1 55 1 62 1 63 1P077def49733d0238 1 1 4 3 0 1 67 1 70 1 4 2 4 68 4 69 4 71 16P096e5485495b4265 1 1 8 3 0 1 67 1 70 1 4 2 2 68 2 69 2 71 16P0a3db6cc1a641ad9 0 5 0 1 54 1 61 1 68 1 69 1P0a3efc7383464de7 1 1 4 3 0 1 64 1 67 1 4 2 4 65 4 66 4 68 16P0ab381d0be3d8a9e 0 2 0 1 52 1P0ad312e3f0457429 0 4 0 1 50 1 65 1 66 1P0b0bad8d636bb3d7 0 5 0 1 44 1 48 1 51 1 52 1P0b8f6d04b68804f5 0 6 0 1 46 1 47 1 53 1 60 1 61 1P0bd79e40fb7c5bf0 2 48 1 1 8 3 2 1 63 1 64 1 6 0 2 48 2 55 2 62 2 65 2 66 16 1 1 8 3 1 1 62 1 65 1 4 0 2 63 2 64 2 66 16P0bfd0ece244ef598 0 3 1 1 3 1 56 1P0c2d1d8e1544fa00 0 5 0 1 50 1 57 1 66 1 67 1P0c9f25739ffa9fc1 2 47 1 1 4 3 2 1 63 1 64 1 6 0 4 48 4 55 4 62 4 65 4 66 16 1 1 4 3 1 1 62 1 65 1 4 0 4 63 4 64 4 66 16P0d6b6857413e6440 0 2 0 1 2 1P0d713c66e735f1ea 0 4 1 1 40 1 43 1 50 1P0dc9e0f69c07813e 0 4 0 8 41 8 60 8 61 8P0eaae6dc4ac9337e 0 5 0 1 46 1 53 1 60 1 61 1P0f24f0a8305fa486 0 2 0 1 2 1P0f3442add38fa307 0 5 0 1 46 1 53 1 60 1 61 1P0f5d148ea5015512 0 4 0 1 45 1 60 1 61 1P0fd6f3f4d5ca2650 0 5 0 1 50 1 57 1 66 1 67 1P10d0396976a31101 0 4 0 4 51 4 68 4 69 4P115c795a4d82a968 0 4 0 1 45 1 60 1 61 1P11dbf8fd35b8910f 0 5 0 1 2 1 7 1 58 1 59 1P11ed469b0d890568 0 5 0 1 2 1 46 1 53 1 54 1P1260e9348d64f624 0 5 0 1 46 1 53 1 60 1 61 1P13f49b9d59a84341 0 5 0 1 46 1 53 1 60 1 61 1P1408d4ecbadc2da3 2 52 1 1 4 3 1 1 69 1 70 1 6 0 4 52 4 59 4 68 4 71 4 72 16 1 1 4 3 2 1 68 1 71 1 4 0 4 69 4 70 4 72 16P14c4b7b1c50b7171 0 5 0 1 2 1 4 1 55 1 56 1P150a7a179e59e204 0 5 0 1 50 1 57 1 66 1 67 1P153bbff725839707 0 4 0 1 3 1 65 1 66 1P153e48fc1d01505e 0 3 0 1 3 1 51 1P157d4768a370add2 0 4 1 1 2 1 64 1 65 1P1626ff5660a131c8 2 52 1 1 4 3 1 1 69 1 70 1 6 0 4 52 4 59 4 68 4 71 4 72 16 1 1 4 3 2 1 68 1 71 1 4 0 4 69 4 70 4 72 16P1643a6b0aada80b9 0 4 0 4 48 4 65 4 66 4P16489154c2f849da 0 5 0 1 51 1 58 1 65 1 66 1P16748fd43d87c55d 0 2 0 1 53 1P16b90da1c2cc7124 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P174bbc8e3d322fc5 1 1 8 3 0 1 64 1 67 1 4 2 2 65 2 66 2 68 16P178ab2d2a22e1645 0 2 0 1 2 1P180ab811f205311f 0 4 0 1 47 1 62 1 63 1P182a2d8d69e5d0c4 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P184dea080d0b937f 0 2 0 1 2 1P191f464f6bda2669 0 4 1 1 43 1 46 1 53 1P19579f6ed179d2da 0 4 0 1 48 1 62 1 63 1P195f25e1de182eb7 2 46 0 7 0 1 3 1 49 1 54 1 56 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P197e9c640b0d774e 0 4 0 8 43 8 62 8 63 8P1980ab6dc26c8f5a 0 2 0 1 2 1P19c2c40508e4fc92 1 1 16 2 1 1 61 1 7 38 1 41 1 47 1 48 1 54 1 62 1 63 16P1a77a9e102516ec4 0 4 0 16 12 16 65 16 66 16P1b1f3ae0b514cf3b 0 3 1 1 3 1 59 1P1b44585f6cac39ad 2 47 1 1 4 3 2 1 63 1 64 1 6 0 4 48 4 55 4 62 4 65 4 66 16 1 1 4 3 1 1 62 1 65 1 4 0 4 63 4 64 4 66 16P1bdc80d859939075 0 2 0 1 2 1P1c388f07be69fb79 0 5 0 1 51 1 58 1 65 1 66 1P1c60ae354415682e 0 5 0 1 46 1 53 1 60 1 61 1P1c63ed5fd7cbb921 0 2 0 1 49 1P1cb4ff7b806a86f0 0 3 0 1 1 1 57 1P1cd87222a1ceed75 0 2 0 1 2 1P1cf4d06490b58adf 0 5 0 1 46 1 53 1 60 1 61 1P1d5b85b22fed2925 2 46 0 7 0 1 3 1 49 1 54 1 56 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P1d66515f2099400f 1 1 8 2 0 1 60 1 3 1 1 61 1 62 8P1d93617556bcabfa 0 3 0 1 5 1 57 1P1ebab6b67fa87d90 0 2 0 1 2 1P1f90343e807daa5f 1 1 16 2 1 1 61 1 7 38 1 41 1 47 1 48 1 54 1 62 1 63 16P1fcb70b42a9dd295 0 6 0 1 46 1 47 1 53 1 60 1 61 1P2010d4cb2216b515 1 1 4 2 0 1 65 1 3 10 1 66 1 67 4P20c1193655c50d89 0 6 0 1 46 1 47 1 53 1 60 1 61 1P20f0228d253f2e91 2 48 1 1 8 3 2 1 63 1 64 1 6 0 2 48 2 55 2 62 2 65 2 66 16 1 1 8 3 1 1 62 1 65 1 4 0 2 63 2 64 2 66 16P21e2892ab0b3660b 0 4 0 1 1 1 66 1 67 1P236eac1b86ad8482 0 5 0 1 50 1 57 1 66 1 67 1P23c8e2d0ddb4c96c 0 5 0 1 5 1 49 1 56 1 57 1P23d88bb51fbaa1ab 0 5 0 1 46 1 53 1 60 1 61 1P240c65facc6c3ce5 1 1 8 2 0 1 60 1 3 1 1 61 1 62 8P24ae49b74f90becf 1 1 16 2 1 1 61 1 7 38 1 41 1 47 1 48 1 54 1 62 1 63 16P24b93d801c051f85 2 47 1 1 4 3 2 1 63 1 64 1 6 0 4 48 4 55 4 62 4 65 4 66 16 1 1 4 3 1 1 62 1 65 1 4 0 4 63 4 64 4 66 16P24d9cab38b63298f 0 4 1 1 40 1 43 1 50 1P260146a6d37aaa95 0 2 0 1 2 1P2608a0f6ca0521b6 0 5 0 1 50 1 57 1 66 1 67 1P261bbc6351c45592 0 5 0 1 46 1 53 1 60 1 61 1P261eee350e1cd8ac 0 4 0 1 47 1 62 1 63 1P2664022a17abd7a9 0 4 0 8 41 8 60 8 61 8P26923cc21e6aade3 2 48 1 1 8 3 2 1 63 1 64 1 6 0 2 48 2 55 2 62 2 65 2 66 16 1 1 8 3 1 1 62 1 65 1 4 0 2 63 2 64 2 66 16P28716060511a9e7e 0 4 0 1 51 1 65 1 66 1P2897707ec423ce1b 0 5 0 1 48 1 55 1 62 1 63 1P28c7e2e5eba127cd 0 4 1 1 43 1 46 1 53 1P299e663ccccab3f2 0 5 0 1 46 1 53 1 60 1 61 1P29ba773e672f8553 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P2a4fe32f1455e266 0 5 0 1 54 1 61 1 68 1 69 1P2a5947e7f2d397c4 1 2 16 2 0 1 62 1 16 2 1 1 61 1 2 63 1 64 1P2a806d4e5e161dfc 0 5 0 1 46 1 53 1 60 1 61 1P2b0780248f16c3e4 0 5 0 1 46 1 53 1 60 1 61 1P2cf20f6f79f631a3 2 46 0 7 0 1 3 1 49 1 54 1 56 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P2d4df8e907f9904e 0 2 0 1 1 1P2d6a695cafe331b5 0 2 0 1 2 1P2d84555e889b27ec 0 3 0 1 2 1 54 1P2df4c45364840b2c 1 1 16 2 1 1 61 1 7 38 1 41 1 47 1 48 1 54 1 62 1 63 16P2e30a6bdb629682d 0 4 1 1 2 1 67 1 68 1P2e9949e060296cc4 0 4 0 1 45 1 60 1 61 1P2f3e3482911309cf 0 5 0 1 46 1 53 1 60 1 61 1P2f613f00021ab461 0 5 0 1 54 1 61 1 68 1 69 1P2fb5fa1b0a0b1319 0 2 0 1 52 1P30938bd556ee0d17 0 2 0 1 49 1P31cce8378acb17f1 1 1 4 2 0 1 68 1 3 13 1 69 1 70 4P31f972b3b84fd83f 0 4 1 1 40 1 43 1 50 1P3208b94eba4f5124 2 63 0 4 0 1 2 1 69 1 70 1 0 5 0 1 3 1 58 1 69 1 70 1P32447467dcf25e55 0 4 0 1 1 1 63 1 64 1P324ec81a4643dff8 0 4 0 1 3 1 68 1 69 1P35368126eda9b2bc 0 4 1 1 2 1 64 1 65 1P35469cb398f04042 1 1 4 2 0 1 65 1 3 10 1 66 1 67 4P35987663c1b74b8c 0 5 0 1 54 1 61 1 68 1 69 1P35f7d1ab9ef8c27a 2 63 0 4 0 1 2 1 69 1 70 1 0 5 0 1 3 1 58 1 69 1 70 1P366f086ef0376bc3 0 2 0 1 1 1P367ae00a31167916 0 3 0 1 3 1 51 1P3734780b456b2614 0 2 0 1 2 1P3780fce68819a835 1 1 8 2 0 1 62 1 3 3 1 63 1 64 8P388d4d93f2a6379f 0 2 0 1 1 1P389c6db1ac01e9da 0 5 0 1 54 1 61 1 68 1 69 1P3909b95bf144728a 0 2 0 1 56 1P394ce1c25f58b0fa 1 1 16 2 0 1 65 1 3 13 1 66 1 67 16P3a35e3dab381166d 1 1 16 2 0 1 62 1 3 10 1 63 1 64 16P3bcee03fc3e4ca28 0 2 0 1 1 1P3bd4c099e10ddbef 0 5 0 1 50 1 57 1 66 1 67 1P3d471fe46049c200 0 5 0 1 50 1 57 1 66 1 67 1P3dd92b220bcc84e5 0 3 0 1 1 1 54 1P3de01eb7dd3cca92 0 5 0 1 50 1 57 1 66 1 67 1P3eb816c85c03162a 0 4 0 16 9 16 62 16 63 16P3f0996534dbbbc2d 0 2 0 1 1 1P3f4b3963c9a5ee55 0 4 0 1 45 1 60 1 61 1P3f79ec01fd9c4079 0 4 1 1 2 1 67 1 68 1P3f85f7f6e1a39cbf 0 2 0 1 2 1N000fc0f3b2f854dbN01115b332719bb6eN0154453a4f2fd08eN0188ec2f093d1baaN018c71980a4d09ccN01be6125efd4ab2bN01d7906e4bb5215aN01f6e139981df6b8N025fe459b3bfaae4N02c7d2c36db54a53N02e4b5fd505ad935N031d5596e7a8cc2dN035f407c02313facN0398b79531870ea7N03b776961d6b3019N03e129cbd41d1898N040c7e0df78462f9N045d17089f3f8bd1N0487a6052165c435N04bdc7d428bb25baN04c4c41ff347fbbcN050ebe8aa283ca93N0515fbcc184a94fdN051fe5f61db9a066N05479999dac31d97N0564767be8270a9aN05a29e64dc732726N05bbdf2f1231733eN05ea5c39a6844d26N0604a360bcfd1a83N062fb6c76eec87acN06430b59f767066dN0674c9ac04f039b9N06d104144c8db8d8N071940eec6ed0797N074b3253d618ab67N07816eaef43ef9adN07898e8d2c35032eN07b62d82fa6bf274N07dbce5bed3de51aN07e078e4ae33dca2N07fec90cf5c7c419N081c297a9eaf7f50N086b7c848d4e4fa4N092b2bdf430c3513N0935e58517711113N098db9787e82fdceN09c5e097c481508aN0a2383432eb234f9N0a6ca675aad7861eN0ab5163e8cb464efN0aee525de3f6e375N0c77bfeafef0546bN0c902709738343fcN0ccd99c3a6e7a188N0d2ee0feed5dcdaaN0d82641e9559acfcN0e549857562de2abN0e55ec463239ad21N0eeec1c85473e283N0f30ba85cf602b6bN0fe2785bca3ce089N0ffea3403c45f638N1021c1e7dc61ff8eN1055689b58638b98N106742280300b836N1072fdce7d72aba5N113f684bb8ac8db0N1163fd1bd5c5fcd1N11e06d2e543ffcbfN1202265c3ea53ca8N12115b5454962147N121d09c1c4aff029N121fe1e7acaa86b1N130cfc18de375297N1313cdc2b203552dN1353cd0994ac2194N1384372a8a71312bN13d03be56759088bN146db438632117d2N1477e7b0affb3a08N149d6c173fc80a5bN14f061c888bc4b3bN157a032f84bd6a03N15bbfcf9af8b2d38N161cb7bf47303e95N1642c052e7c85017N166ec0fbd71c9846N16d5f0aacdeaa184N1776690c0f98b45eN182c180529d03caaN184805ac6272ac1eN18c244753b5b2cd3N18e5fb33b5176220N192d5c1af62e9c69N19667b207d5d1e0dN199d751efc9d77f9N19bf3c464623099aN1a0dca57a03ecfe3N1c1c7a340a5074b3N1c31be8b825d6307N1d2e1fb16d37a4b3N1d6b1b83e6dae3a3N1d6fd830dd654496N1dc6a60d64402093N1dfdbc1624bbe198N1e1262be6cf7f1aeN1e2535ad467f21c6N1e42b1cd4fd3830bN1e75c3d2fdd98214N1e7a4ab3b6dc0022N1ee53667596c8577N1f2869680796054bN1f73adac53f652bbN20255f133948cb50N21476027b38f25fcN216749a4305b4056N222bcd8a4b824d23N2256d3bcd658580bN2304c144511b9859N231e0c7cc4639ad3N236b6e5142eeb75bN2514cffc98c01673N251c31cccbac8df5N257cd0e3e41412e4N257d3d7e85d2c2dbN265ffb3a67c4f4efN267ad75f64d32c6dN269fbb16fcbbdc76N273271c0fcff1e32N27ebfaf0672ad82bN27f7503642a8c1fcN2823a8779a08fe03N283179233184240aN2833d2f975494986N2850c62d83d1ccc1N286fdf16079f2d57N28dafadf96415dbdN28f712fa6af399beN28fb6c57e435832aN2910dee337d46861N2941258f6bcd2f11N29549bffc0c5a069N297d75e4caad1954N2a196aa3a249ad83N2a1ca59f3d95858cN2a6150e5fa79d502N2ab43144bc6ab6daN2b7864ae7aadbbd8N2bc276e9a20cc20aN2cb84f234413e4d5N2cf3a52d1a10e7faN2cfa13714cd3035fN2d381c8abd4ca8dfN2d41398cf84bf273N2d855e4510d175c0N2ea642740ae5bbb1N2ea7bf85bc518d9aN2ef06b919017d702N2f54a3104cd33b67N2f6218425041b88bN2f84c1cf8d05cf7dN2f86245f0974324bN300d3f0ab6097dc8N302589376b4dc453N302c5fb8ec4718beN304c2c48753b93e7N3064b22b12ef8270N30a6152ae0ac9f87N30e0e5bf04cb5879N30ec066d1664fcd8N315974e9459be19fN3199705235be7d8eN31aeb3577887d8f0N31f3e4198420cd36N32141cf7481943ddN3231dd6093fbb5f2N32dbf68299d7dbedN33b314c29f4bc4f2N33f08ff11471f4efN33fa782169eb6e7eN340b93a24a9a95e8N3485e186d9332f66N34e8741406c918cfN3517915130f624ebN353d0729145b4a1cN355d3a3778d8d5e4N35bd9b6af150ed56N35cf7b3f437cd280N3689824c5df11eb0N36a6a8eb806f1c21N36c598618ffc164aN37137f62ee40fe74N371d92640b1bc9daN3723029b68c52d28N3750d125aa4e5083N375670a18c441f15N376830b9868bdc47N37ba47fbb854ddaeN37f0457b60c02f5eN38b775975abfc612N38e19622844405b4N38e1d71819ac6286N39142023358e0ec6N391be5d428592458N39efe4ccc140f937N3a2fa558bba11e86N3a9fd8c4bf35065cN3aa22fc241fc28d6N3b3e1ed108285c08N3b536b21a7d98bb7N3b9c9b4074c65209N3bc10b25b57d5c5fN3c54ad740e374c16N3caf1c753b5c2009N3cb15713a30ea3c3N3cbf1e1765ff1a67N3ceb130ca3640f59N3cec952b5754ea0eN3e53218a161d3b63N3f7ea641a82b613cN3fad21ebe46804e4N3fb4b731ecd3a83d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_oid_ec_grp_algid () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "A_OID_GET_EC_GRP_ALGID"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_rt_hyps"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_lookup1_stmtA"].


Definition A_OID_GET_EC_GRP_ALGID : Z := 0x0a8b70.
Definition A_OID_EC_GRP_ALGID_TBL : Z := 0x0f1ce0.
Notation OID_EC_GRP_ALGID_STACK_A := 32 (only parsing).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GSB : al_gsb AL = AGSB.
  Hypothesis MCI : arl_memcmp_i R = A_WRAP_BCMP.
  Hypothesis RTC : forall m, arl_rtc R m -> asan_rtc m.
  Hypothesis NEEDB : 0 <= arl_need_bcmp R.
  Hypothesis ISH : forall h LB LF m, HM asegs R HIA h LB LF m -> img_shadow_ok asegs AL m.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (OID EXT P LEN lo : Z) (tg pd : word) (xs : list byte).
  Hypothesis HLEN : Z.of_nat (length xs) = LEN.
  Hypothesis D1 : EXT + 4 <= OID \/ OID + 24 <= EXT.
  Hypothesis D2 : EXT + 4 <= P \/ P + LEN <= EXT.
  Hypothesis AL1 : OID mod 8 = 0.
  Hypothesis AL2 : EXT mod 4 = 0.
  Hypothesis NZ1 : 0 < OID.
  Hypothesis NZ2 : 0 < EXT.
  Hypothesis NZ3 : 0 < P.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 32 - arl_need_bcmp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : OID + 24 <= lo \/ bv_unsigned sp <= OID.
  Hypothesis DS2 : EXT + 4 <= lo \/ bv_unsigned sp <= EXT.
  Hypothesis DS3 : P + LEN <= lo \/ bv_unsigned sp <= P.
  Hypothesis P47 : P + LEN + 8 <= 2^47.
  Hypothesis CW : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) EXT 4.
  Hypothesis EXTB : EXT + 4 <= 2^64.
  Hypothesis PB : P + LEN <= 2^64.
  Hypothesis OIDB : OID + 24 <= 2^64.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (hcs_img_cs R HIA h IMG GSB) as ICS;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  Notation W := [(EXT, EXT + 4); (lo, bv_unsigned sp)].
  Notation POST := (oid_lookup1_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc EXT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation TBLC := A_OID_EC_GRP_ALGID_TBL (only parsing).
  Notation SB := (Z_to_bv 64 (al_sb AL)).

  Definition offsets : list Z := [0; 40].



  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@D1321268744.108 D55386061505.108D563007111.109  D62022258533.109L13706168263.84 L13706168263.85 L13706168263.86 L13706168263.87 L13706178068.84 L13706178068.85 L13706178068.86 L13706178068.87 L13706178455.84 L13706178455.85 L13706178455.86 L13706178455.87 L14196763997.116L2063521819.115 L29428324939.5  L29786575724.115L31115876057.2  L34290115814.102L34882647402.128L34882647402.90 L35653441506.7  L39350774109.116L41272565821.113L41272565821.128L43061431611.100L44358090780.115L45067427193.2  L55299785966.133L55299785966.172L55299799889.128L55299799889.90 L57450540059.115L59314873579.2  L59314873579.3  L59314873579.4  L59743371566.115L60098763854.3  L61564298268.115L8717110295.115 00000?00N00e01601701801901:01Z01n02@02A02R02f03803903L03[03m04<04=04L04M04N04f05905H05W06^06m06n06o07007107207A07B07C07D07S07]07l08;S2sp3OID3EXT2xsS2sp3OID3EXT2xsS1R3HIA1h2sp3OID3EXT2xsS1R2sp3OID3EXT2xsFFFFS1R5NEEDB2sp1P2lo2xs3SLO1a2Ha2H1S2sp1P2lo2xs1a2Ha2H1S3EXT1P2xs1a2Ha2H1FS2sp1P2xs1a2Ha2H1S2sp1P2lo2xs1a2Ha2H1S3EXT1P2xs1a2Ha2H1FS1R2sp3OID3EXT2xs1HS2sp3OID3EXT2xsS1R2lo3LOS3ALO3ACPS2sp3OID3EXT2xsFS2sp3OID3EXT2xsFFS1R3HIA1h2sp2lo3TOP4HTOPS1R2sp3OID3EXT2xs1HS2sp3OID3EXT2xsS2sp3OID3EXT2xsS1R5NEEDB2sp3OID3EXT1P3LEN2lo2xs4HLEN2D12D23NZ13NZ23SLO3DS13DS23DS33SPRS2sp3OID3EXT2xsFFFFFS2sp3OID3EXT2xsFFFS2sp3OID3EXT2xsS1R2lo3LOSS2sp3OID3EXT2xsS2sp3OID3EXT2xs". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_oid_ec_grp_algid ()) "Pv0,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Px12,(0.&40.)Px13,(0.&40.)Px14,(0.&40.)Px15,(0.&40.)Px16,(0.&40.)Px17,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VOID,(4.Vtg,Vpd,VLEN,VP,))P,(5.$2.Vm,VP,Vxs,)P,(3.$2.Vm,VEXT,(6.$7.(8.R=.)(9.$7.)))P,(:.$2.Vm,Vlo,(;.&40.Vsp,))P,(<.$2.Vm,)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VOID,+18.)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VP,VLEN,)P,(=.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)Vm,VEXT,+4.)(10.$2.(>.VR,)(?.$2.VR,VHIA,Vh,)(11.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VEXT,Vlo,Vm,)(12.(13.Vra,Vsp,Vgp,Vtp,R12.R11.R10.Vs0,Vs1,(14.&40.VOID,)(14.&40.VEXT,)R?.R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(14.&40.$15.)Vfc,(16.(0.&40.))Vm,(17.$2.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros v0 x5 x6 x7 x12 x13 x14 x15 x16 x17 HH HOID HXS HEXT ST MI OOID OP OEXT.
  rt_facts.
  unfold A_OID_GET_EC_GRP_ALGID.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
  pose proof (artA_bcmp asegs R HIA) as SPB.
  rewrite MCI in SPB.
  unfold A_WRAP_BCMP in SPB.
  unfold buf_cells in HOID.
  carve_frame 32%nat ST.
  img_aobj A_OID_EC_GRP_ALGID_TBL 80 as OTBL. unfold A_OID_EC_GRP_ALGID_TBL in OTBL.   (* [comment removed for export] *)
  lx_tbl_attrs A_OID_EC_GRP_ALGID_TBL offsets 32.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lx_pre. lxr_pose. lxa_auto [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_bcmp0A 0x25f60 3 1 4 5 6; SUM_bcmp0A 0x25fa0 3 1 4 5 6] [P; Z.of_nat (length xs); arl_need_bcmp R].
  lx_pre. lx_run_tac (PLANS [] [(0xa8c54, DJoin); (0xa8c68, DJoin)] 116%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_bcmp0A 0x25f60 3 1 4 5 6; SUM_bcmp0A 0x25fa0 3 1 4 5 6]).
  lx_tree. all: lxa_unglob.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; try lx_rejoin; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx END FORM main_walk: unexpected leaf left:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13667526808.81L36071685254.81L58646921526.8100000I00]011S2sp3OID3EXT1P3LEN2xs3P47S2sp3OID3EXT2xs4OIDBS2sp3OID3EXT2xs4EXTB". (* [comment removed for export] *)
Lemma A_oid_get_ec_grp_algid_spec : ltac2:(CDefT.buildp (gd_tbl_A_oid_ec_grp_algid ()) "PR,$18.PHIA,(19.$2.R1.)P,(1:.R2.R1.)(1;.$2.R3.R2.$15.+20.)")
(* [comment removed for export] *).
Proof.
  intros R HIA (IMG & GSB & MCI & RTC & NEEDB & ISH).
  unfold oid_lookup1_stmtA. intros until xs.
  intros HH HOID HXS HLEN HEXT D1 D2 AL1 AL2 NZ1 NZ2 NZ3 ST LOS SLO TOP SPA DS1 DS2 DS3 P47 CW MI OOID OP OEXT -> ->.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 4) with 4 in EXTB.
  pose proof (rw_cells_bound _ _ _ _ HOID) as OIDB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in OIDB.
  change (Z.of_nat 24) with 24 in OIDB.
  pose proof (bytes_at_bound _ _ _ _ HXS) as PB. rewrite HLEN in PB.
  eapply main_walk; try eassumption; try lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
