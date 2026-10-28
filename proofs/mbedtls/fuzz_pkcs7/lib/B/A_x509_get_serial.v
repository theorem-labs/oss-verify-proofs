(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len P_x509_get_serial.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0010231368804bd6 0 4 0 1 38 1 50 1 51 1P004e8f3981d3b4c0 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P005d524f5237a9f9 0 4 0 1 25 1 37 1 38 1P00c1bb860f796386 1 1 16 2 0 1 41 1 3 13 1 42 1 43 16P01ac39b7db1a46ff 0 4 0 1 1 1 42 1 43 1P023441566affcdab 0 4 0 1 36 1 48 1 49 1P0246a9f6c2874f9c 0 4 0 1 38 1 50 1 51 1P02b11069fa6872da 0 4 0 1 29 1 41 1 42 1P02f0b26b22e1e603 0 2 0 1 1 1P032a85d03a614898 0 4 0 1 1 1 42 1 43 1P03b552029d92d161 0 3 0 1 1 1 38 1P042aa1829d368956 1 1 16 2 24 1 41 1 3 0 1 42 1 43 16P04524508713e0b46 0 3 0 1 33 1 37 1P0486e589332a895a 0 2 0 1 32 1P050fd64d7fafb4eb 0 4 0 1 23 1 33 1 34 1P05e931e823ce5caa 0 4 0 1 25 1 37 1 38 1P06c058a52e39aae5 0 4 0 1 38 1 50 1 51 1P07901dbc1278ad5e 0 4 0 1 22 1 32 1 33 1P0877a1fd466c9af0 0 4 0 1 22 1 32 1 33 1P0890938d6412a14c 1 1 8 3 1 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P09d6ce00b025954a 1 1 8 3 1 1 44 1 45 1 4 2 2 43 2 46 2 47 16P0a14d6da45bba391 0 4 0 1 23 1 33 1 34 1P0ae6195785d09714 0 2 0 1 5 1P0b4ad86065b4f12d 0 2 0 1 1 1P0ba2bda19cd9b4ce 0 4 0 1 1 1 28 1 30 1P0c08ea426c21a4dc 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P0c294670a57c8b52 0 4 0 1 25 1 37 1 38 1P0c4249dde184072a 0 2 0 1 2 1P0c4ffca755df0b24 0 4 0 1 38 1 50 1 51 1P0e484f0b576a34ff 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P0e4ba017bed45c62 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P0e67fee6b3a40639 0 3 0 1 5 1 32 1P0e8cf4067fffd7e3 0 2 0 1 1 1P0e9212a11359a513 0 2 0 1 6 1P0ee5879a24fb1129 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P0f04ace2a9c0caa3 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P0fa6c0cfa723ea7e 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P0fadd90ed0a2fe36 0 3 0 1 4 1 31 1P0fb01a082742fb81 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P114cdbc5a36cd9b8 2 37 1 1 8 3 1 1 53 1 54 1 5 0 2 40 2 52 2 55 2 56 16 1 1 8 3 2 1 52 1 55 1 4 0 2 53 2 54 2 56 16P118ee49dc6833b0d 0 3 0 1 29 1 33 1P1202260025da2518 0 4 0 1 23 1 33 1 34 1P123d801b227465c8 0 2 0 1 2 1P1293852c31a022b2 0 2 0 1 33 1P12fa4a76070d41d7 0 4 0 1 36 1 48 1 49 1P1410df60d691abd0 1 1 8 3 1 1 44 1 45 1 4 2 2 43 2 46 2 47 16P1535556d866e4b85 0 2 0 1 36 1P15b4016028c926d7 0 2 0 1 36 1P15f41f03c2420090 0 4 0 8 22 8 41 8 42 8P1627b4a064b37688 1 1 8 2 0 1 50 1 3 32 1 51 1 52 8P1667d0ed683323ed 0 4 0 1 2 1 45 1 46 1P16a4c7d350b2a1ec 0 4 0 1 36 1 48 1 49 1P173732ec464e0766 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P17bea7ecb7b99fe6 0 4 0 1 29 1 41 1 42 1P18271e1ba6fb7e91 0 5 0 1 25 1 26 1 27 1 29 1P18945d25e63e0308 1 1 8 3 1 1 43 1 46 1 4 2 2 44 2 45 2 47 16P18c551556d9ff7f1 0 4 0 1 1 1 42 1 43 1P19801c64cab44218 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P1a11c8b5ef81c031 0 2 0 1 34 1P1a178cdbfa30853b 1 1 8 3 0 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P1a57ee72d0be68f4 0 4 0 1 22 1 32 1 33 1P1aecda862f6adca2 0 4 0 1 23 1 33 1 34 1P1b5534e806c83885 0 2 0 1 1 1P1b6f60f34812caac 0 2 0 1 32 1P1ba374b7da5109a5 0 3 0 1 1 1 38 1P1bb02db692747657 0 4 0 1 23 1 33 1 34 1P1c39597f54a9524d 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P1cbc8dd46a5a6cd1 0 2 0 1 36 1P1cdb87948ed50bc8 0 4 0 8 23 8 41 8 42 8P1d8447c41e738977 0 4 0 1 25 1 37 1 38 1P1e99892b2c766d7d 0 2 0 1 1 1P1edc700c68fe3b87 0 4 0 8 13 8 32 8 33 8P1f038bc695a48b91 0 4 0 1 2 1 45 1 46 1P1f62520913843eca 0 4 0 1 22 1 32 1 33 1P202f9160de7878ee 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P205be9eecfaacf6a 0 4 0 1 25 1 37 1 38 1P2082e82546a35147 2 27 1 1 8 3 1 1 44 1 45 1 5 0 2 31 2 43 2 46 2 47 16 1 1 8 3 2 1 43 1 46 1 4 0 2 44 2 45 2 47 16P209a079681dca783 0 2 0 1 5 1P20be424af1f4053c 0 2 0 1 2 1P20dea90c64518687 0 4 0 1 25 1 37 1 38 1P214fe68f5e488201 0 2 0 1 37 1P21bdcbfdcd0a396e 1 1 8 3 1 1 43 1 46 1 4 2 2 44 2 45 2 47 16P221cc868122666cf 0 4 0 1 29 1 41 1 42 1P2222f4fb709c9bb0 0 3 0 1 8 1 35 1P232dc6aa1514b5b8 0 4 0 8 31 8 50 8 51 8P2365315ad57f5924 1 1 8 3 0 1 43 1 46 1 4 2 2 44 2 45 2 47 16P23ad2165d96aaca2 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P244da6abfe7df15b 0 3 0 1 7 1 34 1P252f5944e0c0bbcb 0 2 0 1 32 1P255b75291bec7272 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P256a30d765d84493 0 4 0 1 22 1 32 1 33 1P26965737bc6adb3b 0 5 1 1 3 1 32 1 44 1 45 1P269ec991e642b114 0 2 0 1 1 1P2711638d3aaedc63 1 1 8 3 0 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P27a70a42bdee983b 0 3 0 1 3 1 30 1P2844babd297315d4 0 4 0 1 36 1 48 1 49 1P292e3ba3afed1e4b 0 2 0 1 1 1P294c362b14fd8749 3 19 0 2 1 1 2 1 0 5 0 1 3 1 25 1 35 1 36 1 0 4 0 1 2 1 35 1 36 1P2a13a6d5ac28a5f0 0 3 0 1 3 1 30 1P2a78074347f7c7b6 1 1 8 3 0 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P2a8f2fbe69bb3dfd 0 2 0 1 33 1P2b0b6989f5fbd665 0 4 0 1 22 1 32 1 33 1P2bfc753ebd52c924 1 1 8 2 31 1 42 1 3 0 1 41 1 43 8P2cae48c563d66923 0 4 0 8 31 8 50 8 51 8P2cbeca6ed9e58e23 2 26 1 1 8 3 1 1 42 1 43 1 5 0 2 29 2 41 2 44 2 45 16 1 1 8 3 2 1 41 1 44 1 4 0 2 42 2 43 2 45 16P2d292aef1ec4a04c 0 3 0 1 7 1 34 1P2d68b9e1dd6c9103 1 1 8 2 0 1 50 1 3 32 1 51 1 52 8P2de0f29060bb4472 0 4 0 1 23 1 33 1 34 1P2de56b017de619e1 0 4 0 1 38 1 50 1 51 1P2e2cc605a6568459 0 2 0 1 1 1P2f92bb8b453ed140 0 4 0 1 36 1 48 1 49 1P30c53eb06475069a 0 2 0 1 2 1P3116ea1864638fd7 0 2 0 1 30 1P3191b1f8a97936b9 1 1 8 3 1 1 43 1 46 1 4 2 2 44 2 45 2 47 16P3293cac7cd95795f 1 1 8 3 1 1 43 1 46 1 4 2 1 44 1 45 1 47 8P32dcfd2359b2edd1 0 3 0 1 1 1 28 1P32f45f1d20dbd644 0 2 0 1 28 1P3369ef19c21357d2 1 1 8 3 1 1 43 1 46 1 4 2 2 44 2 45 2 47 16P3381561538ff6f6f 0 2 0 1 34 1P33c82c1cac1a0d66 2 21 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P33fc19bfdacec06b 0 3 0 1 2 1 37 1P33ffe7965808f476 0 2 0 1 7 1P34a9611c0574dcc4 0 4 0 1 1 1 42 1 43 1P352079a3349123bd 0 4 0 1 23 1 33 1 34 1P353aa43242c51796 0 3 0 1 1 1 28 1P357927f4a2027c8b 0 2 0 1 30 1P358aa18c3a81689f 1 1 8 3 0 1 44 1 45 1 4 2 1 43 1 46 1 47 8P36439a1bbbc77f41 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P3672bd82b172440d 0 2 0 1 2 1P36789e2e64537e4b 0 4 0 1 1 1 42 1 43 1P37a40044a694200e 2 20 1 1 8 3 2 1 35 1 36 1 5 0 2 24 2 34 2 37 2 38 16 1 1 8 3 1 1 34 1 37 1 4 0 2 35 2 36 2 38 16P37c6df188f70d399 0 3 0 1 26 1 30 1P37c9a095be47e4b4 0 2 0 1 7 1P3813432c9af277a1 0 2 0 1 5 1P38b75abdb1a3d4db 2 36 1 1 8 3 1 1 53 1 54 1 5 0 2 40 2 52 2 55 2 56 16 1 1 8 3 2 1 52 1 55 1 4 0 2 53 2 54 2 56 16P3905c5732d566213 0 3 0 1 5 1 32 1P392e7bded5c312e8 1 1 8 3 0 1 43 1 46 1 4 2 2 44 2 45 2 47 16P3a95003fe0a02a70 0 4 0 1 36 1 48 1 49 1P3b103d514562aa71 0 4 0 1 36 1 48 1 49 1P3b1082f60c88357e 0 4 0 1 1 1 27 1 28 1P3b2b3254c33daf82 0 5 0 1 1 1 30 1 42 1 43 1P3b60e839aac0768c 0 2 0 1 2 1P3c15505bfc514b44 1 1 8 2 0 1 41 1 3 23 1 42 1 43 8P3d61a9eccea738f2 0 4 0 1 25 1 37 1 38 1P3d7c41ab54e1f115 0 4 0 1 38 1 50 1 51 1P3db6e665edb3e607 1 1 8 2 0 1 32 1 3 14 1 33 1 34 8P3e0ee4e3204842c0 0 3 0 1 2 1 37 1P3e96a10461f08cbe 0 2 0 1 34 1P3eb3dd53ccfe1114 1 1 8 3 0 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P3f9c1e6a4cef696a 0 4 0 1 38 1 50 1 51 1P3fa0517ac2557c84 1 1 8 3 1 1 44 1 45 1 5 2 2 31 2 43 2 46 2 47 16P3fe30b71afeac7a9 0 4 0 1 3 1 44 1 45 1N01b81617b5b58b39N01bad61b1d261ceaN01ce35dba5a1ca4eN020b7e368d9c267dN020d192913a38b02N0225f24a1502a945N02284fc17a308e68N027954798f8bc50cN02942371108ad784N02ea70015f3d731fN0322a024f42af8eeN0368c3072b3369b9N03fb0fc59ec7af28N044f9a9b202afb74N0462ac7ebe9f5dc2N0529f6586a1fcdb7N05987c16eb1dcdfdN05c49c70cccea052N05e8f8eb32aa43dcN06509b291cdefcffN06640ce970c80a5bN06b479d737e4e6afN06fb95c8450e41e6N07432f3db7479729N075d20f7fadae2e2N07b682a3f7c7bfd5N07efcd4ee5eb9bbcN07fc7e38ef54369cN080da617d347d5e8N08345a24678393c5N084200df8e978501N085d1ba00d90c764N08e28e09b137ce55N08e51ad1ab7cf175N099de1df2365f5afN09a6be103e93eaf6N0a25cd2c65004477N0a520ba91e1cd33cN0aab7425be8a3138N0b03f03712809ac4N0b467d13751e7b4fN0b7ba8d30d0035f8N0ca9857f5e13addeN0cb794f2fe4faeefN0cd37e2c01dfca98N0d6467a702e61f2bN0d89bfa47def4cadN0e0432598b29340aN0f787856050a024dN0f90303cd48eb85fN1007e9bc48189cecN1119d006db443058N113da1b43919048fN11811cbced92b475N11b99c228f82aeefN11ce39677a72e328N11e8afaf8ccfd549N120fe28dc86eae7aN1221173c666cedc4N12803081aa57647cN132a706633545e54N132c1b9aa5a2e6ddN142e6a324a237c38N151a4c36cce0e621N1591cb0c573b0748N15ef5dc32833dde1N16148dd25652bcabN16415c4362e8b9b7N16b0600dd5ad7780N16c2f79c0ddb29efN16f121130ee31757N1705700f2d80978eN17eeade4ca2e7ea2N182746fd783aee15N186cffac21692430N18df1de244872871N196d58624fdfb262N19a2184d3739d206N19d226cfa2cab401N19d793b9b0f2babeN1a5334361458ffceN1a77e6b3747e0368N1acc42eaf85e26d7N1acd4120c04e84feN1add44703e7fcf64N1aef97b5b85276c9N1b1c6df5ddfde038N1b2fd1b044d042c1N1bad09702a39b864N1bb655700284ad5bN1bdfddb1661ba0f2N1c0d4e5f23cc7f93N1c1cb52119493eb6N1c23308e5148a3c8N1c74090173997ee3N1cb7cae9915c77b5N1cb9e48fd3786284N1cccd66734037682N1d58212a0136573bN1e55a4ef864da9d0N1eb435bef9f6c6b3N1ee572f6be8a1530N1ee6410412cbd305N1eea96f9df2e4f86N1f013388582ef565N1f840862622e3879N1f86ecac8f77be34N1fedd327155794acN1ff0cb26856e4b0bN1ff9da16e4427e57N2076ae30c3bde011N20a80ccc123aa0ddN20f5041da174d7dbN21953ef56349fe0bN21adb31a15bbc8e5N221098dd2eca694fN2212395fc48a774cN222839bf737e9646N228e78d5c9f97c91N22fe6f8f1116dbf7N2310e3d03801cb74N238dd1b475313cb7N23bc0b3f479596e3N23cbe3c4e588883cN241dcaadcc3cbc10N2422c2b311f55610N249edea7e2f277aeN24d03182f54d44e0N251db8f80f6d98e1N252a0368af69f189N258e7cdf3c8b86a0N260e8822cde87e5bN2671198a1caf25dbN267642d04255fdf5N269c79d3d3273cfbN26c326b4f6204e2aN26e5bece33bdfec1N272496aa0cb935f7N2729837dd8d20c40N27332243ea251d0bN2762cdc3df657d5eN2827f4619883aafcN2842224c30fc7b23N28721c8f7d16c444N28835313ba1bee5cN288410125e9e7e27N28e479a1ace18533N29471be735db8759N296ee48f66db4836N2992640ab420332bN29a9bc3c066cce40N29b284a20c7be631N2a55d01547e7a29dN2a6d50b91b4f8a97N2a79d86683b65f14N2aba028b2fbd2df9N2aca155f91e05af9N2b483d6bd52f9dffN2b844a35b5303913N2bbe577b10a677c1N2c0b883139a1e647N2c409a2de55de1f3N2c527b63ec2b5952N2c7ab8f8106ff8fbN2ce19f217ea89069N2d0a124e62a9b0efN2db2e1db45903dddN2edd0386dfceb7afN2f03ec7793fade4aN2f04df27eef7dcebN2f8f089398759aa5N30b1b4968e8af7f6N30e48e21065311b7N31189b6109b7dd7fN312404087f4438c2N31608338db964608N316b0bab72b52139N31b806eaa3fdfc39N32dc116da9dfe200N32dd4bb8b972653aN32fc84253d14edfeN3302dc4209a3c7f2N330ed4358bb31a8bN33344cdcc0cca70bN3351fc938d354660N33f889fb5f8589bcN3446b4d7e30eb312N348461ae4194580aN34ae5542cc8ebf2fN34d35b4854d707f7N34dcb805c14196feN34de1c9b893e9f1dN35030f73c193c3cbN356850c61f3b21d6N356fd9c0374ae68cN35dd530d9c2fc750N35ebb553ab1cb8ddN35ed9b1fdd7702d0N3615b97cfd1f3ddcN3623e1de2d956702N373141b75d1acbc5N373e54e557aebed1N373edeb6e8f8f218N3831ea451926dabeN383af4645310766eN38420e3ce8b6f879N38c02f7164308f2dN38f3ad35219e867fN390e24814c6f4668N394f8b03fbccfbd2N39609c8853a7307bN3964a4c2a5e884e3N3a62a1e0a6688de7N3a775cdecc61b900N3a954d106f5b7167N3afb9bf3f3382837N3b08938d6ca5a645N3c47b419185a4728N3dcb4cce689fd3f0N3f17109f0ab26452N3fad1b2273d06b2dN3fd87c6e5f287586N3fecc95442d79f4e"%lxh.
Ltac2 gd_tbl_A_x509_get_serial () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "x509_get_serial_postA"].


Definition A_X509_GET_SERIAL : Z := 0x0abf34.
Notation X509_GET_SERIAL_STACK_A := 64 (only parsing).   (* [comment removed for export] *)

Definition x509_get_serial_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SER P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_serial ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R16.(7.(8.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(9.O19.)O8.(:.(2.&40.))R6.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O18.)+40.)(12.&40.O18.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1:.O1.R6.)(5.(15.O1:.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-3000.R5.)(18.R5.=))(5.(19.O1:.R6.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1:.R6.O6.(1<.R3.O2.R2.R1.))(5.(1=.O1:.R6.O3.(12.&40.O18.))(5.(5.(18.O5.R4.)(18.R4.O4.))P,(6.$4.R5.=)(5.(18.(10.O5.+2.)R2.)(5.(18.=R3.)(6.$4.(10.R2.R3.)R5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_serial_stmtA {L : heap_layout} (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP SER P END BUF lo : Z) (bs : list byte) (tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m SER (buf_cells tg0 pad len0 q0) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= SER \/ SER + 24 <= PP) ->
  (Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (Z.of_nat (length bs) = 0 \/ SER + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SER) ->
  PP mod 8 = 0 -> SER mod 8 = 0 -> 0 < PP -> 0 < SER -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_SERIAL_STACK_A -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (SER + 24 <= lo \/ bv_unsigned sp <= SER) ->
  (Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  (* [comment removed for export] *)
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m PP 8 -> aobj segs AL CS m SER 24 -> aobj segs AL CS m BUF (Z.of_nat (length bs)) ->
  crange CS lo (bv_unsigned sp - lo) ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 SER ->
  evtA segs AL CS (x509_get_serial_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SER P END lo pad m)
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
            (PP SER P END BUF lo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SER \/ SER + 24 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ SER + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SER.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis SERB : 0 <= SER /\ SER + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SER mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < SER.
  Hypothesis SPL : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SER + 24 <= lo \/ bv_unsigned sp <= SER.
  Hypothesis DS3 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation W := [(PP, PP + 8); (SER, SER + 24); (bv_unsigned sp - 64, bv_unsigned sp)].
  Notation POST := (x509_get_serial_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SER P END lo pad m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).

  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_serial ()) "Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ptg0,(2.&40.)Plen0,$4.Pq0,$4.P,(19.$1>.Vm,VPP,(=.$1:.(1;.(16.&40.VP,))(13.$1:.)))P,(19.$1>.Vm,VSER,(=.$1:.(1?.R4.)(=.$1:.(1?.Vpad,)(=.$1:.(1;.(16.&40.R3.))(=.$1:.(1;.(16.&40.R2.))(13.$1:.))))))P,(20.$1>.Vm,VBUF,Vbs,)P,(15.$1>.Vm,)P,(21.$1>.VAL,Vm,)P,(22.$1>.VAL,VCS,Vm,VPP,+8.)P,(22.$1>.VAL,VCS,Vm,VSER,+18.)P,(22.$1>.VAL,VCS,Vm,VBUF,(23.(24.(2.&8.)Vbs,)))P,(1=.$1>.Vm,Vlo,(12.&40.Vsp,))(25.$1>.VAL,VCS,(26.$1>.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSER,VP,VEND,Vlo,Vpad,Vm,)(7.(8.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(16.&40.VPP,)(16.&40.VEND,)(16.&40.VSER,)R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(16.&40.+:;?34.)Vfc,(:.(2.&40.))Vm,(;.$1>.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros a3 a4 a5 a6 a7 tg0 len0 q0 HPP HSER HBUF MI AB OPP OSER OBUF ST.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn [Z.pow Z.of_N Pos.pow] in SPR.
  assert (OSL : aobj asegs AL CS m (SER + 8) 8) by (eapply aobj_sub; [exact OSER| lia| lia]).
  carve_frame 48%nat ST.
  pose proof (sums_asn1_ok AL IMG) as LXSUMS.
  lx_pre. lx_run_tac (PLANS [] [(0xabf94, DJoin); (0xabfd0, DJoin); (0xabfe4, DJoin)] 137%N [SUM_getlenA; SUM_gettagA]).
  lx_tree.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx END FORM main_walk: unexpected leaf left:" g end.
  Qed.
End Walk.

Lemma A_x509_get_serial_spec {L : heap_layout} : forall AL, asan_img_ok AL -> x509_get_serial_stmtA asegs AL A_X509_GET_SERIAL.
Proof.
  intros AL IMG. unfold x509_get_serial_stmtA, A_X509_GET_SERIAL.
  intros until q0. intros HPP HSER HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI ALWF CSOK AB OPP OSER OBUF SCS -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HSER) as SERB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add buf_cells] in PPB, SERB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  unfold buf_cells in HSER.
  eapply main_walk; try eassumption; try lia.
Qed.
