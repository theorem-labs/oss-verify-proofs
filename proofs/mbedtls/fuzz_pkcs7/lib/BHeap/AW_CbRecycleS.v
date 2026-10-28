(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_Poison AW_MallocA AW_AllocA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_CbRecycle AW_LargeFree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00a4836e17883d09 0 4 1 1 32 1 39 1 40 1P00eaca07e86edd7e 0 2 0 1 45 1P016a08467f417604 0 2 0 1 1 1P01c5e06386db44d7 0 2 0 1 61 1P028a7029b406d923 0 2 0 1 29 1P02d86829725816f8 0 2 0 1 30 1P032ae4055801d110 0 3 0 1 48 1 49 1P033826d907c0500b 0 2 0 1 53 1P03a97b47fbb5ffb1 0 2 0 1 44 1P03c4d413a6d4c100 0 2 0 1 24 1P040679d936e97f8f 0 3 0 4294967296 1 1 32 1P043717d1efe894b6 0 4 1 1 45 1 46 1 47 1P04a61dd3a046d400 0 2 0 1 44 1P04acf9d45fb86337 0 2 0 1 24 1P04fcf9cfa042cbd1 0 2 0 1 60 1P0501ab62c2d62c6a 0 2 0 1 24 1P057f385b2a2848d9 0 4 1 1 46 1 47 1 50 1P0593a314299a526c 0 5 2 1 37 8 40 1 41 1 52 1P06b8cc868b22af69 1 2 4096 2 0 1 65 1 4096 2 1 1 66 1 2 67 1 68 1P06cbfc08c94e338d 0 4 1 1 32 1 39 1 40 1P072398e76a89888a 0 2 0 1 24 1P077dd955e8c9abce 0 2 0 1 60 1P07cdefea4ca32046 0 2 0 1 36 1P07e3804963022a26 0 2 0 1 38 1P07e45446c8a6d4f9 0 4 1 1 46 1 47 1 51 1P0827327f6fce1b20 0 4 1 1 46 1 47 1 48 1P086f3b4fedab80d1 0 2 0 1 45 1P08a283c512d37b78 0 6 0 4096 40 4096 44 4096 45 4096 63 4096 64 4096P093fd5032f02a53c 0 2 0 1 58 1P094fe3d52ff4a948 0 2 0 1 68 1P095fe59c44a72d39 0 4 1 1 45 1 46 1 49 1P09cf12f5f91fb548 0 4 0 1 32 1 47 1 48 1P09f43f695621a0ef 0 4 0 1 48 1 60 1 61 1P0a0b2c4fa85275ba 0 4 1 1 32 1 39 1 40 1P0a24687b882a60d5 0 3 0 4294967296 2 1 33 1P0ac7675f92ced230 0 2 0 1 60 1P0bc7fb703c78a40a 0 2 0 1 45 1P0bdae6c7fb197637 0 2 0 1 56 1P0bfdb5ca861ea4ff 0 2 0 1 59 1P0c11e54c0ddc07f4 0 2 0 1 44 1P0c5ca58c1220c0a5 0 4 1 1 23 1 25 1 26 1P0c795812552d7292 0 2 0 1 47 1P0d3a82430058c64d 0 2 0 1 48 1P0d4f36ae39c4b15e 0 2 0 1 59 1P0d512e14162ad57d 0 4 1 1 46 1 47 1 48 1P0d5e2f09475f7c3a 0 2 0 1 7 1P0d9a6f9420fffb8b 0 4 0 1 45 1 46 1 49 1P0d9bf40eff8e6f0e 0 2 0 1 45 1P0da90f6047083444 1 1 4096 2 10 1 60 1 3 0 1 61 1 62 4096P0dead6ca6b559564 0 4 0 4096 50 4096 60 4096 61 4096P0e3fe6475fc95816 0 5 2 1 37 8 40 1 41 1 52 1P0e450efd45ce0686 0 4 1 1 43 1 45 1 46 1P0e53253862bac575 0 2 0 1 24 1P0e9fa41afca2e12c 0 4 0 1 46 1 47 1 50 1P0ed2cae6acd1c6f1 0 2 0 1 56 1P0f122a26e7c1bebb 0 3 0 4294967296 2 1 33 1P0f22d8b5c0140a7a 0 2 0 1 60 1P0f4f562876f3761e 0 2 0 1 35 1P0fdc760ae8f3a597 0 2 0 1 58 1P1006301c3b08566c 0 4 1 1 43 1 45 1 46 1P1006703a97d51e42 0 3 0 4294967296 4 1 35 1P1024b0e25b3e4f52 0 2 0 1 1 1P10270f36bf838081 0 2 0 1 2 1P105c52c6cc32c5af 0 5 0 1 40 1 41 1 57 1 58 1P10e910d929fb37b3 0 2 0 1 45 1P11046784691fce60 0 2 0 1 59 1P1121b59c299e912b 0 4 0 1 46 1 47 1 50 1P11386489524739d7 0 2 0 1 58 1P1170aa6a599fdd08 0 2 0 1 36 1P117bbe1a2bc815e9 0 4 1 1 45 1 46 1 49 1P118b01c018507640 0 4 1 1 46 1 47 1 51 1P119bdfa5b0e82c12 0 4 1 1 43 1 45 1 46 1P11c463ad716a6b20 0 2 0 1 56 1P121e0a33d2506b05 0 9 0 1 41 8 42 8 44 1 45 1 52 8 53 8 54 1 59 8P125bc1488a2c1a2b 0 2 0 1 58 1P128072316ae1f1ab 0 4 0 1 34 1 44 1 45 1P12bf960bc8930566 0 2 0 1 55 1P1333865c4a3fa10a 0 4 1 1 46 1 47 1 51 1P133abde942ca2e5c 0 2 0 1 45 1P1445e5d8146134eb 0 2 0 1 29 1P144d0907a1adb273 0 2 0 1 34 1P14a0c8a0ba6faa3a 0 3 0 4294967296 1 1 32 1P14ad2abde8234b68 0 2 0 1 24 1P154b45ee9c91741c 0 2 0 1 61 1P157a48ab6f366bb2 0 2 0 1 59 1P158029b1d37162e0 0 2 0 1 59 1P15a537b00d40c7d1 0 2 0 1 45 1P15a8d9f23408b659 0 4 1 1 44 1 46 1 47 1P16069360d839d46c 0 4 0 1 36 1 46 1 47 1P1615b0a905f83294 0 6 0 4096 40 4096 44 4096 45 4096 63 4096 64 4096P164039124d326758 0 4 1 1 43 1 45 1 46 1P1668dd906cf95070 0 2 0 1 44 1P167183dcb5c93f2f 0 2 0 1 51 1P169ddc7dbb9e9cc7 1 1 9223372036854775808 1 0 1 2 1 1 36 1P16c06ae9eda46318 0 2 0 1 38 1P16d3a7801f2823aa 0 4 0 1 46 1 47 1 50 1P16fa6bde7173e48a 0 4 1 1 32 1 39 1 40 1P171bc54318d41aa1 0 3 0 1 42 1 50 1P174ca46a64ea3049 1 1 4096 5 0 1 48 1 49 1 60 2 61 1 3 50 1 61 1 62 4096P17996da4110d17c9 0 2 0 1 38 1P17a1485f1d6f326f 0 2 0 1 59 1P18153a54c9392f14 0 2 0 1 68 1P1880318c6909cfe0 0 2 0 1 38 1P189cb493ae732caf 0 2 0 1 45 1P18c3a3d2344ab384 0 2 0 1 48 1P190b185c6380fcda 0 2 0 1 57 1P197c23b3f7803ec8 0 2 0 1 1 1P19fe1a330c05f4d4 0 2 0 1 44 1P1a49be02c580eb5a 0 3 0 4294967296 4 1 35 1P1aa1be464693bbe4 0 3 0 4294967296 3 1 34 1P1ad3bb22623f02e6 0 2 0 1 45 1P1b3a97a702805de0 0 3 0 4294967296 4 1 35 1P1b46a3c56cdd7da5 0 2 0 1 24 1P1b5533e490a3d259 0 2 0 1 24 1P1b7d5ca90c7b10de 0 2 1 1 58 1P1bbfe479768a3989 0 2 0 1 24 1P1bd6ee5ca79dfeb8 0 2 0 1 35 1P1bf4ffbd3ce98b49 0 2 0 1 24 1P1c9f1e3c24aefc7e 0 4 0 1 49 1 60 1 61 1P1e42fa7a344f2a6f 0 4 1 1 43 1 45 1 46 1P1ec636a9b6e0ec29 0 4 1 1 32 1 39 1 40 1P1ee1d2c490110d3b 0 2 0 1 26 1P1f0aafab1ec68e6a 0 2 0 1 59 1P1f34e335b53971c5 0 4 1 1 46 1 47 1 51 1P1f3a5c5ab3e2799b 0 2 0 1 38 1P1f48efd6555591a7 0 4 1 1 23 1 25 1 26 1P1f4920e178e28cc1 0 2 0 1 38 1P1f628be530742396 0 2 0 1 1 1P1f907898e4604cb2 0 5 2 1 37 8 40 1 41 1 52 1P1fb67abfc793d976 0 4 1 1 23 1 25 1 26 1P20595387f53e499f 0 5 2 1 37 8 40 1 41 1 52 1P206bb28817370f07 0 4 1 1 43 1 45 1 46 1P20aff26d39e19146 0 4 1 1 43 1 45 1 46 1P20e106482c6e379e 0 2 0 1 59 1P2129033019cdd439 0 3 0 2 1 1 35 1P2162495a431c9044 0 2 0 1 38 1P21f5e3561a1c24e1 0 2 0 1 1 1P2255bdde27446322 0 3 0 2 2 1 34 1P2263c06ac773b96b 0 2 0 1 57 1P227b5a430201f522 0 2 0 1 24 1P23214c653aab9f6a 0 2 0 1 27 1P248aaa6256e63be1 0 2 0 1 59 1P24bfc8370b71724c 0 2 0 1 44 1P25a6931db7f347ef 0 2 0 1 45 1P25c3d6a5389c5818 0 2 0 1 57 1P2633663656e7598e 0 4 1 1 44 1 46 1 47 1P26d90010d1ca386b 0 4 0 1 45 1 46 1 49 1P2733e8c887b76a34 0 2 0 1 24 1P2788ceee952f0d27 0 4 0 1 45 1 46 1 49 1P27d0349b96afa483 0 4 1 1 44 1 46 1 47 1P28079938d661dfc6 0 3 0 4294967296 1 1 32 1P2883a527456d0b45 0 6 0 4096 40 4096 44 4096 45 4096 63 4096 64 4096P28ceba38f2db074c 0 4 1 1 44 1 46 1 47 1P2988557306af6cb7 0 4 1 1 44 1 46 1 47 1P2a395918ae0d490f 0 2 0 1 58 1P2a46e74255fbbade 0 4 1 1 46 1 47 1 50 1P2ae5b5be9bc44170 0 4 1 1 44 1 46 1 47 1P2b65fd13e57d9eba 0 4 1 1 45 1 46 1 50 1P2bd8978ba36c856f 0 4 0 1 45 1 46 1 49 1P2c4b73ead134aa44 0 2 0 1 38 1P2cacd8b874319b3a 0 4 1 1 45 1 46 1 50 1P2caee1a69e84be72 0 2 0 1 24 1P2d02b958ab915b4d 0 2 0 1 28 1P2d065f258189bbca 0 2 0 1 51 1P2d22c6e124645056 0 2 0 1 27 1P2d4b253d0e2e9d8c 0 2 0 1 2 1P2d61bfacdb0fc180 0 2 0 1 45 1P2d65decfdfb48649 0 6 1 1 35 1 39 1 40 1 58 1 59 1P2daaf4399399b428 0 2 0 1 19 1P2dc295e254f8727e 1 1 8 1 0 1 2 57 1 68 1P2dde418e82c1d085 0 2 0 1 38 1P2e5e53a95ceab848 0 4 1 1 32 1 39 1 40 1P2ebeee796e9a065d 0 2 0 1 24 1P2ee03554bb4da77f 0 2 0 1 35 1P2fc7f1b44a7c606e 0 2 0 1 18 1P2feccba64d531b32 0 4 1 1 44 1 46 1 47 1P301a28dca20086b3 0 2 0 1 1 1P3033c7914abbc330 0 4 1 1 45 1 46 1 50 1P3043f04ed0fe416a 0 4 1 1 32 1 39 1 40 1P30eb78bbcc907c3f 0 4 1 1 45 1 46 1 50 1P30eba3625afb3db4 0 4 1 1 32 1 39 1 40 1P31315af2ca73a42b 0 3 0 1 2 1 60 1P318456289a6fa7ef 0 2 0 1 44 1P319f15e9439b80e3 0 3 0 1 49 1 50 1P31d68c56c504bf72 0 2 0 1 44 1P31e7be746c4aaa24 0 2 0 1 44 1P3279a635a9b2e4a9 0 2 0 1 57 1P32b78638682c5e70 0 4 1 1 32 1 39 1 40 1P331d7b10671697db 0 2 0 1 24 1P33414f7af6997d27 0 6 1 1 35 1 39 1 40 1 58 1 59 1P33433c55fac9914e 0 4 1 1 43 1 45 1 46 1P33ab6e466d50d706 0 6 1 1 35 1 39 1 40 1 58 1 59 1P33f1ee26a8769c4b 0 4 1 1 23 1 25 1 26 1P3419d4448c9e0aea 0 2 0 1 38 1P345669ac41ae3683 0 2 0 1 58 1P34619d087b30fac1 0 2 0 1 24 1P34b50643a7c50351 0 9 0 1 41 8 42 8 44 1 45 1 52 8 53 8 54 1 59 8P34d3eaf952967cd5 0 2 0 1 45 1P3551755ae99625b6 0 2 0 1 47 1P35e7c18a3fed857b 0 2 0 1 45 1P35f286254b0adaaf 0 4 1 1 44 1 46 1 47 1P362f7f1fbd4300b8 0 2 0 1 45 1P36ed762c098c4961 0 4 1 1 45 1 46 1 47 1P372731a724e32def 0 2 0 1 38 1P37589293ba03f5ed 0 4 1 1 32 1 39 1 40 1P382dd2f50c8532a0 0 6 1 1 35 1 39 1 40 1 58 1 59 1P383e29b5ed00e96f 0 2 0 1 9 1P384e6aad0451b0a7 0 5 0 1 32 1 47 1 60 1 61 1P38c41dff077278c4 0 4 1 1 44 1 46 1 47 1P39390f80139e9d4c 0 4 1 1 43 1 45 1 46 1P3a0ec51ff259efd7 0 2 0 1 45 1P3a203eac6325d0c4 0 4 0 1 46 1 47 1 50 1P3aa3bd14325577d2 0 2 0 1 8 1P3adce79b26b83c54 0 2 0 1 24 1P3ae7c0c53469303c 0 2 0 1 35 1P3b94e58d1b107d38 0 9 0 1 41 8 42 8 44 1 45 1 52 8 53 8 54 1 59 8P3bcbe240d54ce764 0 2 0 1 44 1P3c499d9d60bac113 1 1 4096 2 0 1 60 1 3 50 1 61 1 62 4096P3c682d8d003851fd 0 2 0 1 45 1P3c9a984b66df44b7 0 4 0 1 28 1 30 1 31 1P3cb98278402fd0bc 0 4 1 1 43 1 45 1 46 1P3d028c5b72e449af 0 2 0 1 1 1P3d13c0cc1f0ab3aa 0 2 0 1 1 1P3d5e6a02ea021c9f 0 4 1 1 23 1 25 1 26 1P3d7d96aaf783699a 0 2 0 1 44 1P3d8420acb7325b68 0 2 0 1 45 1P3ddf851ce6d5ba6c 0 2 0 1 24 1P3df60c49b04eb605 0 4 1 1 44 1 46 1 47 1P3e0b36f08b5856cf 0 2 0 1 44 1P3e0d429f2e3b238c 0 4 1 1 23 1 25 1 26 1P3ed757cf2b90369c 0 2 0 1 58 1P3f42bbd9d45bd318 0 4 1 1 32 1 39 1 40 1P3f48558b617a8d9f 0 2 0 1 38 1P3f5d094c155517e4 0 3 0 4294967296 1 1 32 1P3f68d59e8761c65a 0 2 0 1 60 1P3f9e7922cc48e751 0 2 0 1 28 1P3fe2855f9fdbb2f4 0 4 1 1 32 1 39 1 40 1N001f48dc005ec76dN00263606c739a815N00f3fc8ce24e3e0aN013db3adbbefc490N016b6e7ccb370dffN0258b7c144ea512cN03a6d5370151a4f1N03d504275bcc700aN041c8cb72369d968N045f02aac7c3b137N04c9ce791e01ae49N053e914b7520b330N055f9bf5fa7085aeN06d27f51680a30fbN07e9294e32cca570N083474ae00822927N098dc8f8b934806eN0a08f79b78c5b056N0aa54a1a86d6cd5dN0ab9dfd4a26b55b6N0b16b468cebd1b8dN0cca7207fd6e1dbdN0ddbd21de4f949bdN0e55526911ecb013N0f8648054a27ee30N0f8afbea11f3c8b2N0ff067050a7c8ca8N10550fda735f943bN10c0de008b4ece3fN113b4edefa356cf1N118a9981a026a4cdN11a4a59541a7c3edN11c515932c4645b7N11e6c91a5d19e7c4N1222ad160a1a5944N1297684dd52a4a82N12e4106b467934c3N133e880e05e9074fN1378824f7459f470N13a1a5550aa9b19eN13bb8be0252daaafN140573e7141e57faN14a7b45907e86713N153d6bba2cf815a8N15d0c2c6c6914658N172aef04633a7373N19148a2ccd3e1a84N1939b2cb30d9313eN19c2d847b97429d9N1ac62fb96bc6a17cN1b9d27d0b9756afdN1bdc5964b3c1b855N1c03372f9d2ba34dN1cc6cb3c7c162ec2N1d16d11e2827c460N1db57b0ea532b5abN212eaf67830c3f23N2196a0fa28825627N21aae0faf639fc52N21d9f4e299714900N2219f77a618854efN22324cc7b993e292N228bf56947d31c17N2292e7898e98c98dN22d4a7afd9083b76N22efee7684dd1ca2N23bed8f2166d658dN243c57f3cdbd140fN247e55f648541aa4N2560c1bf1b3e02e9N267dbb2c5c6b1c36N26f55deeebf55c2fN27ad1527602df090N2907dd515adecc41N2965987423678e88N297f199b6439a43dN298e08836c160b34N2c544004da349652N2dc4013dff44ef9aN2e25173dd9eeb21cN2f9502a5dd7b4226N2fc69ed7b312b858N307e99e6dbe32fa0N313cc9dd6235a591N318fe04e9c4e71c0N32d9327ddba28284N3337ed0962c5215cN33701b2b0022271aN3407c30d628837a4N349672ab5105643eN34a1e83e0d1f3e0cN3738aae4e48b788eN374575bbb347e1c1N389c8bcd8e7706c5N38e2d4db67774f1bN38e619364e55e96eN38f14e03f7944cc4N391ec85038e9d9f6N3a127a9955b841ccN3a4e2d535f9fb2e1N3ac9a6cb2d4ea046N3cab716c4cf5cc56N3cec8e62319a4b20N3d2bf56008831feaN3df65f59ccec9ceaN3eec4c8fbb4ceecbN3f54b97c65140f1a"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_CbRecycleS () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SEC_MUTEX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SECONDARY"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.CbRecycleS.gbb_regs"; "ARUN_1.A_GBB_POST"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_GBB_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.ZArith.BinInt.Z.modulo"; "ARUN_1.CbRecycleS.gbb_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_GBB"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.cbr_frame"; "ARUN_1.A_CBRS_B"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_GSTATS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.A_LARGE_DEALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.dealloc_statics"; "ARUN_1.CbRecycleS.cbrS_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_GBB : Z := 0x49e44.             (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_GBB_LOOP : Z := 0x49eb0.        (* [comment removed for export] *)
Definition A_GBB_POST : Z := 0x49edc.        (* [comment removed for export] *)
Definition A_CBRS_B : Z := 0x49c38.          (* [comment removed for export] *) (* [comment removed for export] *)

Section CbRecycleS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Ltac bytes_eq := vm_compute; repeat (first [reflexivity | apply f_equal2; [apply bv_eq; vm_compute; reflexivity|] ]).

  (* [comment removed for export] *)
  Definition gbb_regs (SP : Z) (ra gp tp t0 t1 t2 s1 s2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm PA i near n : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "(0.O1=.(1.&40.(2.O1>.-20.))O1<.O1;.O1:.O19.O18.(1.&40.$3.)O17.(1.&40.$4.)(1.&40.O5.)(1.&40.(2.O4.(5.+8.O3.)))(1.&40.O2.)(1.&40.(2.O4.(5.+8.O1.)))O15.O14.O13.O16.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L10351595562.3 L11540515147.2 L12381644380.76L14396835606.8 L14453872270.7 L15174512909.73L16583733025.7 L17297229833.8 L19020818174.8 L23852624400.68L27112196645.8 L34449353849.72L35343624383.72L36773129682.71L36773238500.74L41954763205.6 L43235924758.71L52052449389.73L52674177036.3 L56032132254.2 L57888288848.5 L58931556406.71L58931694336.74L59308628433.4 L59308628433.8 L62229578041.9 L65033765735.61L67574932281.8 L8740187061.2  00000800>00o01B01U02E02V02i03305A05P05n06L07207e08608a08b08j09109A09^0:>0:L0:d0;30<o0=G0=MS1i1n2HiS1h2H0S3hAR1k1i2PA1n5bases2Hk2Hi2NB3PA03PA13LMB3idx3IDXS1k1i2PA1n2Hk2Hi2KXS2mm1h2ms2HM2MH1b1XS3hAR1k1i2mm1n4near1h5bases2Hk2HM2MB2NR3LMB1b2BBS1i3idx2NE2LT3NE2S1k1i2PA1n2Hk2Hi2KXS1k1i1n2HkS3hAR2AL2CS1k1i2ra2gp2tp2t02t12t22s12s22a52a62a72s32s42s52s62s72s82s93s103s112t32t42t52t62SP2mm2PA1n4near1h3idx5bases1F2fc1m2Hk2NB3IDX3LMB3NTHS2mm2MB1b2BB2K2S3hAR1k1i2PA1n5bases2Hk2Hi3LMBS3hAR1k1i2PA1n5bases2Hk2NB3LMBS3hAR1k1i2mm1n1h5bases2Hk2H02HM2MB3LMBS3hAR1k1i2mm1n4near1h5bases2Hk2H02HM2MB2NR3LMB1b2K1S2mm4near1h2NR2K1S3hAR1k1i2mm1n4near1h5bases2Hk2HM2MB2NR3LMBFS1i1n2HiS1i3idxS1i1n3idx3IDX2ENS3hAR1k1i1n5bases2Hk3LMB1b2BBS3hAR1k1i2mm1n5bases2Hk3LMB1b2BBS2mm1h2HM2K21bS2mm1h2ms2MH1b3BD'2K12K2S2mm1h2H02HM2MBS3hAR2AL2CS1i2ra2gp2tp2t02t12t22s12s22a52a62a72s32s42s52s62s72s82s93s103s112t32t42t52t62SP2mm2PA1n4near1h5bases1F2fc1m2Hk2HiS2mm1h2ms2MH1b2BB3BD'2K2S1i2PA". (* [comment removed for export] *)
  Lemma gbb_loop : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "Pk,$6.Pi,$7.Pra,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps1,(8.&40.)Ps2,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PSP,$7.Pmm,$7.PPA,$7.Pn,$7.Pnear,$7.Ph,$7.Pms,$7.Pidx,$7.Pbases,(9.$7.)PF,(:.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(;.(8.&8.))P,(<.$7.(2.R25.(=.R26.))R9.)P,(>.(?.=R26.)(10.R26.R:.))P,(?.R;.(=.(11.$7.R6.)))P,(10.(=.(11.$7.R7.))(12.+2.+28.))P,(?.+65?000.R>.)P,(?.(2.R?.(5.+8.(=.(11.$7.R9.))))(13.VhAR,))P,(>.(?.=R;.)(10.R;.R?.))P,(<.(;.$7.)(14.$7.R;.(15.R<.))(16.$7.R>.))P,(10.=R?.)P,(?.R10.R14.)P,(10.R15.(2.R11.R10.))P,(10.R16.(12.+2.+3?.))P,Pj,$6.Pb,$7.P,(<.(;.$7.)(14.$7.R12.R2.)(16.$7.R1.))P,(17.R3.(15.R18.))(>.(>.(?.=R3.)(10.R3.(12.+2.+3?.)))P,(18.(<.$6.R4.(15.R15.)))(19.(?.(2.R4.+1000.)R18.)(?.(2.R18.R17.)R4.)))P,(>.(?.=R15.)(?.R15.R14.))P,P,(10.R13.R33.)(<.$7.R17.R16.)P,(1:.$1;.R10.R19.(1<.$7.(8.&40.)(1.&40.)R13.))P,(1=.VCS,R1:.(5.+8.(=.(11.$7.R14.))))P,(1>.$1;.R12.)(1?.$1;.VAL,VCS,Lms',$20.(21.(8.&40.)Lx15,(8.&40.)(21.(8.&40.)Lx16,(8.&40.)(21.(8.&40.)Lx17,(8.&40.)(21.(8.&40.)Lx5,(8.&40.)(<.$20.R5.(22.(23.R23.R3;.R3:.R39.R1.R37.R36.R35.R34.R4.R3.R2.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R22.R21.R20.R1>.R20.)R1:.(1.&40.$24.)R19.(25.(8.&40.))R18.(26.$1;.)))))))(22.(23.R1>.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1=.R1<.R37.R1:.R1;.)R15.(1.&40.$27.)R14.(25.(8.&40.))R13.(26.$1;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ra gp tp t0 t1 t2 s1 s2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP mm PA n near h ms idx bases F fc m
      Hk Hi NB LB PA0 PA1 IDX NI H0 HM MH MB DISJ NR NH HPA PACS MI; [lia|].
    facts. unfold gbb_regs, A_GBB_LOOP, A_GBB_POST, A_SEC_MUTEX, A_SECONDARY in *. unfold A_INSTANCE in *.
    assert (LMB : length (map (Z_to_bv 64) bases) = length bases) by apply map_length.
    destruct (nth_error bases (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    destruct (DISJ (Z.to_nat i) b NTH ltac:(clear -Hi; lia)) as [BB BD].
    pose proof (u64arr_read asegs m PA (map (Z_to_bv 64) bases) i (Z_to_bv 64 b) _ HPA ltac:(rewrite nth_error_map, NTH; reflexivity) ltac:(clear -Hi; lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. clear RD. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (NXT : forall (near' : Z) (x16 : word), 0 <= near' <= h -> (idx < i + 1 -> near' = h) ->
              evtA asegs AL CS
                (fun ms' => exists (x15 x16 x17 x5 : word),
                   ms' = MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp x5 t1 t2 (Z_to_bv 64 1074752) s1 (Z_to_bv 64 1074136) (Z_to_bv 64 mm)
                                (Z_to_bv 64 (PA + 8 * n)) (Z_to_bv 64 h) (Z_to_bv 64 (PA + 8 * n)) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 302812) fc None m (seg_rom asegs))
                (MS (mkR ra (Z_to_bv 64 (SP + -32)) gp tp (Z_to_bv 64 (mm - near)) t1 t2 (Z_to_bv 64 1074752) s1 (Z_to_bv 64 1074136) (Z_to_bv 64 mm)
                         (Z_to_bv 64 (PA + 8 * i)) (Z_to_bv 64 near') (Z_to_bv 64 (PA + 8 * n)) (Z_to_bv 64 b) x16 (Z_to_bv 64 (mm - b))
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x49ea8) fc None m (seg_rom asegs))).
    { intros near' x16 NR' NH'.
      (* [comment removed for export] *)
      zstep. replace (PA + 8 * i + 8) with (PA + 8 * (i + 1)) by (clear; lia).
      zstep. if_cases KX; zify_cond KX.
      - assert (EN : i + 1 = n) by (clear -KX Hi Hk PA0; lia).
        apply evtA_done. do 4 eexists. rewrite <- EN. rewrite (NH' ltac:(clear -IDX EN; lia)). reflexivity.
      - eapply (IH (i + 1)); try eassumption; try (clear -Hk Hi KX PA0; lia). }
    assert (II : Z.to_nat i = Z.to_nat idx \/ Z.to_nat i <> Z.to_nat idx) by (clear; lia).
    assert (BH : b = h \/ (b <> h /\ (b + 4096 <= h \/ h + ms <= b))).
    { destruct II as [E|NE]; [left; rewrite E, NI in NTH; congruence| right]. pose proof (BD NE) as X. split; [clear -X MH HM; lia| exact X]. }
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *) apply NXT; [exact NR|]. intros LT. apply NH. destruct BH as [->|[_ _]]; [exfalso; clear -K2 HM; lia|].
        destruct II as [E|NE]; [exfalso; rewrite E, NI in NTH; injection NTH; clear -K2 HM; intros ->; lia|]. clear -LT NE IDX Hi. lia.
      + (* [comment removed for export] *)
        zstep. zstep. apply NXT.
        * destruct BH as [->|[NE BD']]; [clear -H0; lia|]. clear -BD' K2 MH BB. lia.
        * intros LT. destruct BH as [->|[NE BD']]; [reflexivity| exfalso].
          destruct II as [E|NE2]; [rewrite E, NI in NTH; congruence|].
          pose proof (NH ltac:(clear -LT NE2 IDX Hi; lia)) as ->.
          rewrite ?Z.mod_small in K1 by (clear -K2 BB MB HM H0; lia). clear -K1 BD' K2 MH. lia.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K2; zify_cond K2.
      + apply NXT; [exact NR|]. intros LT. apply NH. destruct BH as [->|[_ _]]; [exfalso; clear -K2 HM; lia|].
        destruct II as [E|NE]; [exfalso; rewrite E, NI in NTH; injection NTH; clear -K2 HM; intros ->; lia|]. clear -LT NE IDX Hi. lia.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. apply NXT; [exact NR|]. intros LT. destruct II as [E|NE]; [| apply NH; clear -LT NE IDX Hi; lia].
        rewrite E, NI in NTH. injection NTH. intros <-.
        rewrite ?Z.mod_small in K1 by (clear -K2 BB MB HM H0 NR; lia). clear -K1 NR HM. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition gbb_cells (m : mem) (PA nres n : Z) (sorted : byte) (mw : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "(>.(28.$1;.O6.$4.(29.$2:.(2;.(1.&40.+1000.))(29.$2:.(2;.(1.&40.O5.))(2<.$2:.))))(>.(28.$1;.O6.(2.$2=.+70.)(29.$2:.(2;.(1.&40.O4.))(29.$2:.(2;.(1.&40.O3.))(29.$2:.(2>.O2.)(2<.$2:.)))))(28.$1;.O6.$3.(29.$2:.(2>.(1.&8.O1.))(29.$2:.(2>.(1.&8.=))(29.$2:.(2?.(1.&40.=))(2<.$2:.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac gbb_leaf HAL := match goal with
     | |- False => match goal with K : context [Z.land 4095 ?h] |- _ =>
          rewrite (Z.land_comm 4095 h) in K; change 4095 with (Z.ones 12) in K; rewrite Z.land_ones in K by (clear; lia);
          change (2 ^ 12) with 4096 in K; rewrite HAL in K; clear -K; lx_klin; lia end
     | |- _ => apply evtA_done; lx_exs; lx_ands; [> | | | lx_ands | | lx_mseq]; lx_close
     end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L11045386737.103L13398263039.1  L1702856238.101 L17835354460.16 L21005805564.16 L24524828174.16 L33021620580.101L35823568430.101L39082318472.104L39276134848.105L39396637589.0  L40717963570.101L41905953644.105L4311123308.105 L44016129579.16 L50352450190.16 L51967777081.101L53051764561.0  L53516992933.1  L53519997187.101L5560325164.105 L563960351.101  L57924723626.101L59310615780.1  L61677494953.129L61784595233.16 L65271643703.0  L7714179527.105 L8543861164.16  L9739880297.102 00000D00H00_01:01J01Z02102@02Z03A03B03Q04104Q04a05:05;05<05=05U06806906:06?06S06m06n07a08108ES3hAR1h5bases3LMB2HBS2PAS3hAR2AL5bases4IMG'3LMBS3hAR1n3idx5bases4IDXa4IDXbS3hAR1n5bases2N1S3hAR1h5bases2H0S3hAR2AL5bases4IMG'3LMBS3hAR5bases3LMBS3hAR1h5bases3LMB2HB5Ha_stS3hAR2PA1h5bases3PA03LMB2HB5Ha_st5Hl_stSS3hAR5bases3LMBS3hAR1h5bases3LMB2HB5Ha_st5Hl_stS3hAR1h5bases3LMB2HB5Ha_st5Hl_stS3hAR1h5bases2H0S3hAR1h3idx5bases4IDXa2H0FSSS3hAR2AL5bases5ALWF'3LMBS3hAR1h5bases2H03LMB2HB5Ha_st5Hl_stFFS3LXES3hAR2PA1h5bases3LMBS3hAR2mm1h2ms5bases2MH3HMSSS3hAR2SP1h2lo5bases2H05LOIMG3SPL3LMB2HB5Ha_st5Hl_stS3hAR1n5bases2N1S3hAR1h5bases2H03LMB". (* [comment removed for export] *)
  Lemma gbb_spec : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "Pra,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Ps2,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Psorted,(8.&8.)PSP,$7.Pmm,$7.PPA,$7.Pnres,$7.Pn,$7.Ph,$7.Pms,$7.Psz,$7.Pidx,$7.Plo,$7.Pbases,(9.$7.)PF,(:.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(;.(8.&8.))P,(?.+1.R:.)P,(?.R;.(=.(11.$7.R5.)))P,(10.(=.(11.$7.R6.))(12.+2.+28.))P,(>.(?.=R>.)(10.R>.(12.+2.+40.)))P,(?.+65?000.R10.)P,(?.(2.R11.(5.+8.(=.(11.$7.R9.))))(13.VhAR,))P,(>.(?.=R<.)(10.R<.R10.))P,(<.(;.$7.)(14.$7.R;.(15.R=.))(16.$7.R10.))P,(?.+65?000.R11.)P,(<.$7.(30.R12.+1000.)=)P,(?.R13.R17.)P,(10.R18.(2.R14.R13.))P,(?.(2.R15.R14.)(13.VhAR,))P,(>.(?.=R14.)(10.R14.(12.+2.+40.)))P,Pj,$6.Pb,$7.P,(<.(;.$7.)(14.$7.R14.R2.)(16.$7.R1.))P,(17.R3.(15.R1;.))(>.(>.(?.=R3.)(10.R3.(12.+2.+3?.)))P,(18.(<.$6.R4.(15.R18.)))(19.(?.(2.R4.+1000.)R1<.)(?.(2.R1<.R1;.)R4.)))P,(31.R10.R1;.R1:.R19.R1>.=)P,(1:.$1;.R11.R1<.(1<.$7.(8.&40.)(1.&40.)R14.))P,(1=.VCS,R1=.(5.+8.(=.(11.$7.R15.))))P,(28.$1;.R13.R1;.(29.$2:.(2;.(1.&40.R1;.))(29.$2:.(2;.(1.&40.R1:.))(29.$2:.(2;.(1.&40.R19.))(29.$2:.(2;.(1.&40.R18.))(2<.$2:.))))))P,(1=.VCS,R1<.+20.)P,(32.$1;.R15.R19.R22.)P,(?.(13.VhAR,)R1:.)P,(?.R1;.(33.R24.+20.))P,(?.R25.(12.+2.+3>.))P,(1=.VCS,R1=.(33.R26.R1=.))P,(1>.$1;.R1:.)(1?.$1;.VAL,VCS,Lms',$20.(21.P,(8.&40.)(;.(8.&8.))Lm',P,(8.&40.)(;.(8.&8.))(21.(8.&40.)Lx5,(8.&40.)(21.(8.&40.)Lx11,(8.&40.)(21.(8.&40.)Lx12,(8.&40.)(21.(8.&40.)Lx13,(8.&40.)(21.(8.&40.)Lx14,(8.&40.)(21.(8.&40.)Lx15,(8.&40.)(21.(8.&40.)Lx16,(8.&40.)(21.(8.&40.)Lx17,(8.&40.)(>.(34.(29.(35.$7.$7.)(36.$7.$7.R29.R32.)(29.(35.$7.$7.)(36.$7.$7.$3.(2.$3.+4.))(2<.(35.$7.$7.))))R25.R9.)(>.(37.$1;.R25.R9.)(>.(1>.$1;.R9.)(>.(31.R9.R30.R2?.R2>.R33.=)(>.(32.$1;.R9.R29.R32.)(<.$20.R:.(22.(0.R4?.(1.&40.R32.)R4>.R4=.R8.R4;.R4:.R49.R48.(1.&40.(2.R2=.+1000.))R7.R6.R5.R4.R3.R2.R1.R47.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R27.(38.R4?.)R26.(25.(8.&40.))R9.(26.$1;.)))))))))))))))))(22.(0.R45.(1.&40.R28.)R44.R43.R42.R41.R40.R3?.R3>.(1.&40.$4.)(1.&40.R27.)R3<.R3;.R3:.R39.R38.R37.R3=.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)R1=.(1.&40.$39.)R1<.(25.(8.&40.))R1;.(26.$1;.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sorted SP mm PA nres n h ms sz idx lo bases F fc m
      N1 NB LB NRB PA0 PA1 IDX NI H0 HAL HM MH HMS SZB DISJ (SEC & NCH & MUT) HPA PACS HH HCS ST LOIMG SPL SPH SCS MI.
    facts. unfold gbb_cells in *. unfold A_GBB, A_SECONDARY, A_SEC_MUTEX in *. unfold A_INSTANCE in *.
    change (1074072 + 64) with 1074136 in *. change (1074072 + 112) with 1074184 in *. change (1074072 + 680) with 1074752 in *. change (1074752 + 4) with 1074756 in *.
    pose proof (munch_refl [(lo, SP); (1074752, 1074756)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LMB : length (map (Z_to_bv 64) bases) = length bases) by apply map_length.
    assert (LMBz : Z.of_nat (length (map (Z_to_bv 64) bases)) = Z.of_nat (length bases)) by (rewrite LMB; reflexivity).
    assert (HA4 : h + 4096 <= ACEIL).
    { pose proof aceil_pg as AP. unfold ACEIL in *.
      pose proof (Z.div_mod h 4096 ltac:(clear; lia)) as E1. pose proof (Z.div_mod aceil 4096 ltac:(clear; lia)) as E2.
      rewrite HAL, Z.add_0_r in E1. rewrite AP, Z.add_0_r in E2. clear -E1 E2 HM MH HMS. nia. }
    destruct IDX as [IDXa IDXb]. destruct NRB as [NRa NRb]. destruct SZB as [SZa SZb]. lx_aceil. lx_c1_norm.
    (* [comment removed for export] *)
    lx_run (PLAN [0x49e68] [] 20%N).
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mx 1074752 _ |- _ => apply (rw_cells_reshape asegs mx 1074752 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end.
    zstep. rewrite (sx32_small 0) by (clear; lia).
    do 6 zstep.
    match goal with H : rw_cells _ ?mx 1074752 [C4 ?v] |- _ =>
      apply (rw_cells_reshape asegs mx 1074752 _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x49eb0] [] 20%N).
    replace (Z_to_bv 64 PA) with (Z_to_bv 64 (PA + 8 * 0)) by (f_equal; clear; lia).
    eapply evtA_cut.
    { eapply (gbb_loop (Z.to_nat n) 0) with (idx := idx) (ms := ms); try eassumption; try (clear -N1 IDXa IDXb H0 HM MH HMS LB NB; lia). }
    cbv beta. intros ms1 (x15 & x16 & x17 & x5 & ->). unfold gbb_regs, A_GBB_POST, A_SEC_MUTEX, A_SECONDARY, A_INSTANCE.
    change (1074072 + 64) with 1074136. change (1074072 + 680) with 1074752.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).
    all: gbb_leaf HAL.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac cbrS_A_leaf NP MBa MBb SB0 SB1 := match goal with
         | |- False => match goal with K1 : context [zlow 64 ?p <? zlow 64 ?sb], K2 : context [zlow 64 ?p <? zlow 64 (?sb + _)] |- _ =>
                         clear -K1 K2 NP MBa MBb SB0 SB1; lx_klin; lia end
         | |- _ => apply evtA_done; lx_exs; lx_ands; [> | | | | | lx_mseq]; lx_close
         end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L15613284277.9L36775322577.9L48195549377.9L59310615780.900000C00R00e018S2SB2mm3SB03SB13MBaS2SB2mm3MBa3MBbS2SB2mm3SB03SB13MBaS2SB2mm2NP4LXKF3LXE". (* [comment removed for export] *)
  Lemma cbrS_A : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "Pra,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PSP,$7.PCBP,$7.PSB,$7.Pmm,$7.Plo,$7.PF,(:.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(;.(8.&8.))P,(?.+10007???9000.R6.)P,(?.(2.R7.(12.+2.+25.))(12.+2.+2?.))P,(>.(?.=R7.)(10.R7.(12.+2.+3?.)))P,(19.(10.R8.R9.)(?.(2.R9.(12.+2.+25.))R8.))P,(3:.$1;.R5.$3;.(29.$2:.(2;.(1.&40.R:.))(2<.$2:.)))P,(32.$1;.R6.R9.R=.)P,(?.(13.VhAR,)R:.)P,(?.R;.(33.R?.+30.))P,(?.R10.(12.+2.+3>.))P,(1=.VCS,R=.(33.R11.R=.))P,(1>.$1;.R;.)(1?.$1;.VAL,VCS,Lms',$20.(21.P,(8.&40.)(;.(8.&8.))Lm',P,(8.&40.)(;.(8.&8.))(>.(34.(29.(35.$7.$7.)(36.$7.$7.R11.R15.)(2<.(35.$7.$7.)))R>.R1.)(>.(37.$1;.R>.R1.)(>.(1>.$1;.R1.)(>.(3<.R1.R15.R21.R22.R23.R2:.R2;.R31.)(>.(32.$1;.R1.R11.(2.R15.-30.))(<.$20.R2.(22.(0.(1.&40.$3=.)(1.&40.(2.R15.-30.))R30.R2?.R2>.R2=.R2<.(1.&40.R14.)(1.&40.R12.)(1.&40.$4.)(1.&40.R12.)R29.R28.R27.R26.R25.R24.R23.(1.&40.$2=.)(1.&40.+2000000000.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R10.(1.&40.$39.)R?.(25.(8.&40.))R1.(26.$1;.)))))))))(22.(0.R2?.(1.&40.R13.)R2>.R2=.R2<.R2;.R2:.R29.R28.(1.&40.R12.)(1.&40.R10.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R>.(1.&40.$3>.)R=.(25.(8.&40.))R<.(26.$1;.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP CBP SB mm lo F fc m
      SB0 SB1 MB NP SBC ST LOIMG SPL SPH SCS MI.
    facts. unfold cbr_frame, A_CB_RECYCLE, A_CBRS_B, A_GBB, A_SPACEBEG_CELL, A_SECONDARY in *. unfold A_INSTANCE in *.
    change (1074072 + 32) with 1074104 in SBC. change (1074072 + 64) with 1074136.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. destruct MB as [MBa MBb]. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x49e44] [] 40%N).
    all: cbrS_A_leaf NP MBa MBb SB0 SB1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition cbrS_post (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T p lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "Lms',$20.(21.P,(8.&40.)(;.(8.&8.))Lm',P,(8.&40.)(;.(8.&8.))(21.(8.&40.)Lx5,(8.&40.)(21.(8.&40.)Lx6,(8.&40.)(21.(8.&40.)Lx7,(8.&40.)(21.(8.&40.)Lx13,(8.&40.)(21.(8.&40.)Lx14,(8.&40.)(21.(8.&40.)Lx15,(8.&40.)(21.(8.&40.)Lx16,(8.&40.)(21.(8.&40.)Lx17,(8.&40.)(>.(34.(29.(35.$7.$7.)(36.$7.$7.O4.O19.)(29.(35.$7.$7.)(36.$7.$7.(2.O6.+;18.)(2.O6.+;28.))(2<.(35.$7.$7.))))O1.R9.)(>.(37.$1;.O1.R9.)(>.(1>.$1;.R9.)(>.(32.$1;.R9.O4.O19.)(<.$20.R:.(22.(0.O18.(1.&40.O19.)O17.(1.&40.$3?.)R8.R7.R6.O16.O15.(1.&40.$4.)(1.&40.$40.)(1.&40.O5.)R5.R4.R3.R2.R1.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O3.(1.&40.$41.)O2.(25.(8.&40.))R9.(26.$1;.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac cbrS_B_leaf lo NP PBa PBb SB0 SB1 := match goal with
         | |- False => match goal with K1 : context [zlow 64 ?p <? zlow 64 ?sb], K2 : context [zlow 64 ?p <? zlow 64 (?sb + _)] |- _ =>
                         clear -K1 K2 NP PBa PBb SB0 SB1; lx_klin; lia end
         | |- _ => lx_stk_grow lo; apply evtA_done; lx_exs; lx_ands; [> | | | | lx_mseq]; lx_close
         end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L11349971155.2 L13896181782.82L13896181911.79L15611183106.9 L18834821384.79L18834821513.82L221661884.2   L2573530350.1  L29501416508.2 L29919156958.1 L31161708658.9 L31848168474.2 L35859719815.2 L39654185788.2 L40545316878.1 L46493628694.82L46493628823.79L48189257590.9 L53797557639.2 L5860351834.2  L58756559770.2 L59321099091.9 L61122088602.2 L62542494298.2 L63787280654.1 L64519200211.2 L64889209966.1 L65141962503.2 L7870389527.79 L7870389654.82 00000100@00O00]00l01;01<01=01>01?01M01N01O01P01T01c02202@02A02B02C02U02V02W02[02\02`02a03003?FS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB1p3SB03SB1S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLFFFFS2SB1p3PBa3PBbFFFS2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS2SB1p3SB03SB1FFFS2SB1p2NP3LXE4LXE0FFS2SPFS2SPFS3hAR2SP2lo3SPLS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma cbrS_B : ltac2:(CDefT.buildp (gd_tbl_AW_CbRecycleS ()) "Pgp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)Ps4x,(8.&40.)Ps3x,(8.&40.)Ps2x,(8.&40.)Ps1x,(8.&40.)Ps0x,(8.&40.)Prax,(8.&40.)Prf,(8.&40.)Prfd,(8.&40.)PSP,$7.PCBP,$7.PSB,$7.Pmm,$7.Pp,$7.Pn,$7.Pctx,$7.Pb1,$7.Pst,$7.PT,$7.PCTX,$7.Plo,$7.PF,(:.&5.(8.&40.))Pfc,(8.&20.)Pm0,P,(8.&40.)(;.(8.&8.))Pm,P,(8.&40.)(;.(8.&8.))P,(?.+10007???9000.R>.)P,(?.(2.R?.(12.+2.+25.))(12.+2.+2?.))P,(>.(10.=R>.)(10.R>.(12.+2.+3?.)))P,(19.(10.R?.R11.)(?.(2.R11.(12.+2.+25.))R?.))P,(>.(?.=R?.)(10.R?.(12.+2.+20.)))P,(>.(?.=R=.)(10.R=.+100.))P,(>.(?.=R?.)(10.R?.+100.))P,(?.+65?000.R14.)P,(?.(2.R15.+10.)(13.VhAR,))P,(3:.$1;.R:.$3;.(29.$2:.(2;.(1.&40.R17.))(2<.$2:.)))P,(28.$1;.R;.R17.(42.R13.R12.))P,(28.$1;.R<.(2.R18.+4.)(43.R16.R15.))P,(1=.VCS,R19.+10.)P,(28.$1;.R>.(2.R14.+;18.)(29.$2:.(2;.R1?.)(29.$2:.(2;.R1>.)(2<.$2:.))))P,(44.R?.R15.R14.)P,(1=.VCS,R16.+1000.)P,(1=.VCS,R16.+10000.)P,(>.(?.+1000.R18.)(19.(?.(2.R18.+1000.)+10000.)(?.+65?000.R18.)))P,(?.(2.R19.+1000.)(13.VhAR,))P,(?.+65?000.R19.)P,(?.(2.R1:.+10000.)(13.VhAR,))P,(19.(?.(2.R1<.+1000.)R22.)(?.(2.R22.+10.)R1<.))P,(3<.R17.R26.R2>.R2=.R2<.R2;.R2:.R29.)P,(32.$1;.R18.R1<.(2.R27.-30.))P,(?.(13.VhAR,)R1=.)P,(?.R1>.(33.R29.+70.))P,(?.R2:.(12.+2.+3>.))P,(34.(29.(35.$7.$7.)(36.$7.$7.R20.R2;.)(29.(35.$7.$7.)(36.$7.$7.(2.R22.+;18.)(2.R22.+;28.))(2<.(35.$7.$7.))))R1=.R1<.)P,(37.$1;.R1>.R1=.)P,(1>.$1;.R1>.)P,(1=.VCS,R23.(33.R2>.R23.))(1?.$1;.VAL,VCS,(45.R2?.R32.R4>.R33.R34.R35.R36.R37.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R26.R2;.R24.R23.R22.R21.)(22.(0.(1.&40.$3=.)(1.&40.(2.R2?.-30.))R4>.(1.&40.$3?.)R4=.R4<.R4;.(1.&40.R2>.)(1.&40.R2<.)(1.&40.R2;.)R4:.R49.R48.R47.R46.R45.R44.R43.(1.&40.$2=.)(1.&40.+2000000000.)R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.)R23.(1.&40.$3=.)R22.(25.(8.&40.))R20.(26.$1;.)))")
(* [comment removed for export] *).
  Proof.
    intros gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s4x s3x s2x s1x s0x rax rf rfd
      SP CBP SB mm p n ctx b1 st T CTX lo F fc m0 m
      SB0 SB1 PB NP NB STB B1B M0 M1 SBC HW0 HW1 MCS TST DS TCS CTXCS TB1 TB2 CB1 CB2 APT FR ST LOIMG SPL SPH MU WM MI SCS.
    facts. unfold hdr_w0, hdr_rest, cbr_frame, cbrS_post in *.
    unfold A_CBRS_B, A_SPACEBEG_CELL, A_SECONDARY, A_GSTATS, A_LARGE_DEALLOC in *. unfold A_INSTANCE, A_TP in *.
    change (1074072 + 32) with 1074104 in *. change (1074072 + 64) with 1074136 in *. change (1074072 + 688) with 1074760 in *.
    destruct DS as (HK & TSD & TPC & TSA & CTH). unfold A_MFHOOKS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in HK, TSD, TPC, TSA. change (1684672 + 8) with 1684680 in HK.
    destruct PB as [PBa PBb]. destruct NB as [NBa NBb]. destruct STB as [STa STb]. destruct B1B as [B1a B1b]. lx_aceil.
    rewrite <- (Z_to_bv_bv_unsigned rf) in TST. rewrite <- (Z_to_bv_bv_unsigned rfd) in TST.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4a18c] [] 100%N).
    all: cbrS_B_leaf lo NP PBa PBb SB0 SB1.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CbRecycleS.

End ARUN_1.
