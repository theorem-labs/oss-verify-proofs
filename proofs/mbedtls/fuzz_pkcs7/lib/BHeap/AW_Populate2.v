(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00ca234574131e50 1 1 2048 6 1 16 15 16 16 16 19 16 21 16 22 16 2 8 1 23 1P010b59de1e8e92d0 0 4 0 1 10 1 12 1 13 1P0124fe38745ec218 0 6 1 16 27 16 28 16 29 16 41 16 42 16P0132b49adcd22544 0 4 0 1 26 1 40 1 41 1P01baa97c2ea13f20 0 2 0 1 27 1P0201a6ae94e722df 1 1 128 1 0 1 2 10 1 27 1P0271c1911e66a4f7 1 1 4 1 0 1 2 24 1 27 1P0301219020682e2e 1 1 4 2 0 1 17 1 2 10 1 20 1P03c943b259740ef8 0 4 0 16 16 16 27 16 28 16P03f550536a9c20ea 0 4 0 16 16 16 27 16 28 16P044be126cc83ce46 0 4 0 1 10 1 12 1 13 1P04c9bf44fb9390ec 0 4 0 1 26 1 40 1 41 1P0577d44bd3c7e603 0 2 0 1 22 1P05e45162d1b6bc91 0 4 0 1 10 1 12 1 13 1P065dfcd3182483cc 0 2 0 1 9 4P0705645a4e42bdcb 1 2 16 2 0 1 29 1 16 2 1 1 28 1 2 30 1 31 1P074f58fba7660f65 0 2 0 1 17 1P0814f489366bac95 1 1 2048 6 0 16 27 16 28 16 37 16 41 16 42 16 2 21 1 43 1P08d9c6b07a4c5a4e 0 2 0 1 27 1P09efecd252dd05c5 0 4 0 1 32 1 46 1 47 1P0a31b7e7db4f6573 0 4 0 16 14 16 20 16 21 16P0a666a581877fee9 0 4 0 1 32 1 46 1 47 1P0ab0e5a3d777b0b3 0 4 0 1 10 1 12 1 13 1P0adbceae69758aea 1 1 2048 6 1 16 15 16 16 16 19 16 21 16 22 16 2 8 1 23 1P0ade748328864fe0 0 4 0 16 14 16 20 16 21 16P0b118f2bbd952929 0 4 0 16 16 16 27 16 28 16P0b37e6598d7d8127 0 4 0 1 10 1 12 1 13 1P0b41bcdc7ffa6bbe 0 4 0 16 14 16 20 16 21 16P0b475c6bc353fe59 0 6 0 1 29 1 32 1 33 1 46 1 47 1P0b5fcd276d8484c8 0 2 0 1 28 1P0c500f08b19e8c81 0 6 0 1 30 1 33 1 34 1 47 1 48 1P0cb0155fe0a6da5f 0 4 0 1 26 1 40 1 41 1P0ef6a1d2c92818d9 0 4 0 16 14 16 20 16 21 16P0fdafeefbdcf9306 1 2 16 3 0 1 41 1 44 1 16 3 1 1 42 1 43 1 2 45 1 46 1P0fe72f3dfec0f216 1 2 16 2 0 1 29 1 16 2 1 1 28 1 2 30 1 31 1P1072569f843bd227 0 3 0 1 30 1 43 1P118749bf5e4f3716 0 2 0 1 15 1P1204002f3a619e14 0 4 0 1 26 1 40 1 41 1P1212d8dc13ec71bc 1 1 16 2 1 1 41 1 5 25 1 27 1 28 1 42 1 43 16P127a6f1a6c7ace99 0 2 0 1 22 1P12adb6db0f37c56a 0 2 0 4 12 4P12b9ddb022b2ef17 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P12bf413a364bf80b 0 4 0 1 26 1 40 1 41 1P12e0bb6b85bd9c49 0 4 0 1 32 1 46 1 47 1P12e8e52fe10c59be 1 1 128 2 1 1 38 1 2 22 1 41 1P13dec7a783bcf1d2 0 4 0 16 16 16 27 16 28 16P1426096ab0debc36 1 1 16 3 0 1 41 1 44 1 6 27 1 28 1 30 1 42 1 43 1 45 16P14457153e7936fc5 1 1 2048 6 1 16 27 16 28 16 37 16 41 16 42 16 2 21 1 43 1P14966bc2b8f2eff3 1 1 16 3 0 1 41 1 44 1 6 27 1 28 1 30 1 42 1 43 1 45 16P14d84091be13d7d9 0 6 1 16 15 16 17 16 18 16 28 16 29 16P151050b91f418e95 0 6 0 1 29 1 32 1 33 1 46 1 47 1P168f0df13b9b4912 0 6 0 1 29 1 32 1 33 1 46 1 47 1P16c8cfadb950ed6c 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P1710891d9e762e73 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P179599e3687f4dcb 0 4 0 16 16 16 27 16 28 16P17a213b773634b18 0 4 0 16 16 16 27 16 28 16P17e7be5a68622bd2 0 4 0 16 14 16 20 16 21 16P1803101328fdf7b8 0 4 0 1 26 1 40 1 41 1P189a4f2892270a74 1 1 128 4 0 1 30 1 32 1 33 1 2 21 1 40 1P18c1fc5ed9f38e8a 1 1 128 1 0 1 2 20 1 40 1P191fddef84bfd9d8 0 4 0 1 10 1 12 1 13 1P1a59871b44f7ff49 0 4 0 1 32 1 46 1 47 1P1b312cd1781f3833 0 2 0 1 16 1P1b6a491b6701f991 0 6 0 1 29 1 32 1 33 1 46 1 47 1P1bac29f1b9b758ad 0 6 1 16 15 16 17 16 18 16 28 16 29 16P1c1165ccd472345e 0 4 0 1 26 1 40 1 41 1P1c2a0f2ca5d01937 0 4 0 1 10 1 12 1 13 1P1c46a037f836750f 0 4 0 16 14 16 20 16 21 16P1cecf8b39145f79b 1 1 128 1 0 1 2 9 1 27 1P1d418427bd9595bd 0 6 0 1 29 1 32 1 33 1 46 1 47 1P1d4937dd32b0a899 0 4 0 1 32 1 46 1 47 1P1ef00acdf033b0fe 0 6 0 1 29 1 32 1 33 1 46 1 47 1P1f9b6d2a98764cf0 0 4 0 1 26 1 40 1 41 1P20564bf582f165d4 0 2 0 1 36 1P2076d3642b1dff40 1 1 2048 6 1 16 15 16 16 16 19 16 21 16 22 16 2 8 1 23 1P20a4f61d8afc7882 0 4 0 1 23 1 26 1 27 1P20e4a995a080f6e7 0 2 0 1 27 1P210270df8c612c51 1 1 2048 6 1 16 17 16 18 16 26 16 28 16 29 16 2 10 1 30 1P21b4f0817efbcded 0 4 0 16 14 16 20 16 21 16P21ba69dcc1bbe961 1 1 2048 6 1 16 27 16 28 16 37 16 41 16 42 16 2 21 1 43 1P2240beffbd28f288 1 1 16 3 1 1 41 1 44 1 6 27 1 28 1 30 1 42 1 43 1 45 16P2265d481eafe63d4 0 2 0 1 40 1P22b541ab685ed1f6 1 1 4 1 0 1 2 10 1 20 1P230afa115c8c2b46 0 4 0 16 16 16 27 16 28 16P236f13a2b68bb391 1 1 128 2 1 1 38 1 2 22 1 41 1P24a057202cb2cd76 0 4 0 1 32 1 46 1 47 1P24d721edd4c3f675 0 6 0 1 15 1 22 1 24 1 25 1 28 1P2521c123bd3f93ab 0 2 0 1 41 1P253cd731ceabfb3b 0 6 0 16 17 16 18 16 26 16 30 16 31 16P254fa3543be6e98e 0 4 0 16 14 16 20 16 21 16P26251c875bce3bf0 1 1 16 3 0 1 41 1 44 1 6 27 1 28 1 30 1 42 1 43 1 45 16P2642c846cc2ba26f 0 2 0 1 22 1P264e324ef972645b 1 1 2048 6 1 16 17 16 18 16 26 16 28 16 29 16 2 10 1 30 1P26b5d9062f5e9e63 1 1 128 1 0 1 2 21 1 40 1P26cb2c7b24ddadaf 0 4 0 16 14 16 20 16 21 16P27b720fc7c47bb93 0 4 0 16 14 16 20 16 21 16P27c4dd422dee91d3 0 4 0 1 30 1 41 1 43 1P2813b6189b1fa648 0 6 1 16 27 16 28 16 29 16 41 16 42 16P28899d3ed0b89bd0 1 1 2048 6 1 16 15 16 16 16 19 16 21 16 22 16 2 8 1 23 1P28b410d51f45e2d7 0 4 0 1 32 1 46 1 47 1P29b69f3f2fdc2eb6 0 4 0 1 32 1 46 1 47 1P29c649f2ce54bc71 0 3 0 1 40 1 41 1P2a20079623164f7b 2 34 1 1 128 5 0 1 2 1 34 1 42 1 43 1 2 23 1 44 1 1 1 524288 4 0 4096 1 4096 42 4096 43 4096 2 22 1 44 1P2b0cc293e36fd587 0 4 0 1 10 1 12 1 13 1P2b56f291ef221f9c 0 4 0 1 10 1 12 1 13 1P2befbe96c570b6c1 1 1 128 1 0 1 2 8 1 20 1P2cfbc3372b93b4de 2 34 1 1 128 5 0 1 1 1 34 1 42 1 43 1 2 23 1 44 1 1 1 524288 4 0 4096 2 4096 42 4096 43 4096 2 22 1 44 1P2d5bee63fd5a454c 0 4 0 16 14 16 20 16 21 16P2d6e30c5909eecf5 1 1 16 3 1 1 41 1 44 1 6 27 1 28 1 30 1 42 1 43 1 45 16P2db7aacf7380e949 0 4 0 16 16 16 27 16 28 16P2dc940bf5e88c4bf 0 4 0 1 26 1 40 1 41 1P2e837f3fd6b4251e 0 4 0 1 26 1 40 1 41 1P2ed0c4aff1ff62d4 1 1 2048 6 0 16 27 16 28 16 37 16 41 16 42 16 2 21 1 43 1P2f4e36f590e10dea 0 2 0 1 26 1P2f899ec51b43f153 0 6 0 16 17 16 18 16 26 16 30 16 31 16P2ffff517c979813b 0 6 0 1 29 1 32 1 33 1 46 1 47 1P306f5ee1e390d677 0 4 0 16 14 16 20 16 21 16P31673062dc2835ba 0 4 0 1 10 1 12 1 13 1P31c7f66472407e65 1 1 4096 2 0 1 40 1 3 19 1 41 1 42 4096P3209e77c832e1338 0 4 0 1 32 1 46 1 47 1P322897724c870270 1 1 128 2 1 1 38 1 2 22 1 41 1P3258a460a4f1e777 0 2 0 1 23 1P32bed94778b75f0d 1 1 4096 2 1 1 40 1 3 0 1 41 1 42 4096P333a1edfbf0ebe3c 0 4 0 16 16 16 27 16 28 16P33817b51cb98d017 0 4 0 16 16 16 27 16 28 16P33abd048dceb977d 0 6 0 1 30 1 33 1 34 1 47 1 48 1P33b1e2821807e55a 0 4 0 1 23 1 26 1 27 1P33b8e0788a5fc0ac 0 3 0 4 11 4 22 4P3439fc5d049f38d4 1 1 2048 6 1 16 17 16 18 16 26 16 28 16 29 16 2 10 1 30 1P345d80ceaec3bb41 0 5 0 16 25 16 45 16 52 16 53 16P355fc9c73e5eb9ca 1 1 128 1 0 1 2 7 1 20 1P35766e98a8f8a2f8 2 32 1 1 128 3 0 1 2 1 34 1 2 23 1 42 1 1 1 128 2 0 1 1 1 2 22 1 42 1P35d2eb6486c912dd 0 2 0 1 35 1P36bd78a84b8bd171 0 4 0 1 10 1 12 1 13 1P36ce195edd521ef6 0 4 0 1 10 1 12 1 13 1P37c23a13b317775c 1 1 2048 6 1 16 15 16 16 16 19 16 21 16 22 16 2 8 1 23 1P37e9f7fcd0c9add1 0 6 0 1 29 1 32 1 33 1 46 1 47 1P37ef448331c74fdf 0 4 0 16 14 16 20 16 21 16P3805931573aa9cf9 0 4 0 16 24 16 52 16 53 16P3865b04949dc35e1 0 4 0 1 26 1 40 1 41 1P3882426f941a88f1 0 4 0 16 16 16 27 16 28 16P38cba9abaf68d795 1 1 2048 6 1 16 17 16 18 16 26 16 28 16 29 16 2 10 1 30 1P393ca1fb2bf25db3 0 4 0 1 26 1 40 1 41 1P3a4e85547fcb815b 1 1 16 2 1 1 41 1 5 25 1 27 1 28 1 42 1 43 16P3a54e928ea71a040 0 4 0 16 16 16 27 16 28 16P3a58b1bd7c09bcad 2 34 1 1 128 5 0 1 1 1 34 1 42 1 43 1 2 23 1 44 1 1 1 524288 4 0 4096 2 4096 42 4096 43 4096 2 22 1 44 1P3b711127211f9b8c 0 4 0 16 16 16 27 16 28 16P3bef2dff1cfe66ee 0 4 0 1 10 1 12 1 13 1P3c42094c025840b8 0 4 0 16 16 16 27 16 28 16P3cbcca816f64e7a8 0 4 0 16 16 16 27 16 28 16P3cd33051b6db6eba 0 4 0 1 10 1 12 1 13 1P3ce6574c6973c19b 0 4 0 16 14 16 20 16 21 16P3cf06f3e58ccee2a 0 6 0 16 17 16 18 16 26 16 30 16 31 16P3de94eb55a2b0010 0 4 0 1 10 1 12 1 13 1P3e4c1405b6a97a3d 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P3e6694a9d5923e87 0 4 0 16 14 16 20 16 21 16P3e792615fb80ade2 1 1 2048 6 1 16 17 16 18 16 26 16 28 16 29 16 2 10 1 30 1P3eb07268afc487ec 0 6 0 1 30 1 33 1 34 1 47 1 48 1P3ecdaa9e42621022 1 1 16 2 0 1 30 1 5 15 1 17 1 18 1 31 1 32 16P3f02f5bf754e5335 1 2 16 2 0 1 29 1 16 2 1 1 28 1 2 30 1 31 1P3f1f97e9a32311d6 0 4 0 4096 19 4096 40 4096 41 4096N0181731eafb535aeN0284cb5a4d54af5dN028f4c7dee79680dN0432e5a3b0be9855N05848089715e4567N066737dae771b2d0N06d6c9e88b7ad07dN06f55e7dcb151d13N072eb1b3df94756aN0760bbd8d38d43e9N093666c81f0cea50N0979d7096fc508fdN0a6770a9938db309N0c0e2557aa4a6b73N0c765c5d335c0889N0d31999999ca0e4aN0da04cdaa549c0e9N0f1b41130fc12eacN0fa363dad2d4af22N0ff93051c10e1cebN10084829fca5b2ccN10df6684d97fdfa1N136aaf35e19078dcN1370bec44a09256bN14c475efd9930172N14d59635a39e614bN153cbe7543a94272N154907f7198c617bN16cac1e84f9b7aa5N1745a9aa91d65e2fN176aeec619f01106N18163add90f9731aN18b1c5e6f287c382N19db04ee7b58da7fN1a49362b2b0f910dN1a9c87ad07a81ca7N1ac953cd3fb68eddN1b153e312bcafa17N1b81098487f49883N1bf7b9e1396e5e10N1c1a76ee0349ff59N1c545e9c8c75b960N1e9c933962c60b9cN1ee7869929125b7cN1f0967563975f79fN1f52f9acc8b56d65N2026ab470553ec60N2043619f891898c9N22779ed0be66396fN230d495ca910430eN23f801519348137aN2506b7924c219e1aN258ba4daae9a5a00N25a1b83bd4625a47N26970595974eb071N26cc66c10cd3b244N292b75eac4ef6210N296a6f19d52588f9N2c8c5e1c3645d5b7N2cb8facb91bdc6eeN2d0824a89a00cea4N2dfe0be72949e868N2e128cbe1dc3574cN2e16007b2b84ec53N2f0349312f521e08N3027276a2033a34cN31360477fc0e4860N322097233676c3f0N346bd938a6cb858fN34799599b64cbff7N34f35b8cc8a2dc1bN34f5c696c0071f70N353d35113078988fN3807b09e75f0837bN39b3714e69b9e52cN39d79790496cdab8N3a47690f4ee02ff5N3a697de87d0766e5N3b9c78cadd06f011N3bb1f115e8b18da3N3c0959a0742166deN3d59b06bcb05102cN3dd992dc1293b34eN3df549e125d3510bN3e7fc5aa6901f76bN3e83a808b6df66a7N3f3557c5f12345d7N3f83c0460550e513N3fa0c7172e50c255"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Populate2 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Sem.mul_div"; "LinuxProcessSemantics.Riscv.Instr.M_DIVU"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.land"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "ARUN_1.carve_list"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Stdlib.ZArith.BinInt.Z.lxor"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EFS"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_NAME_EFS"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_PREMAPPED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Init.Datatypes.list"; "ARUN_1.Populate2.efs_mwc_regs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_RAR_MAP"; "ARUN_1.Populate2.efs_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.Populate2.efsB_post"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.pop_frame"; "ARUN_1.Populate2.popD_post"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L11319346946.5L19201695968.5L26983617675.5L56759370246.6L58931716944.5L58938013242.6L61883801886.5L7217548742.6 00000600<00B00J00P00X00^00eS1a2HaS1b2HbS1a2HaS1a1b2HaS1b2HbS1a1b2HbS1b2HbS1a1b1H". (* [comment removed for export] *)
#[using="Type"] Lemma mul_divu_lit : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pa,$0.Pb,$0.P,(1.(2.=R2.)(3.R2.(4.+2.+40.)))P,(1.(3.=R2.)(3.R2.(4.+2.+40.)))(5.(6.&40.)(7.&40.$8.(9.&40.R4.)(9.&40.R3.))(9.&40.(:.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros a b Ha Hb. unfold mul_div. rewrite unsigned_lit by lia.
  replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (0 <= a / b < 2^64).
  { split. { apply Z.div_pos; lia. } apply Z.le_lt_trans with a; [| lia]. apply Z.div_le_upper_bound; [lia|]. nia. }
  apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L10421833.9   L12506604108.9L18926754524.7L46992133059.7L56397866170.9L58761269238.700000<00M00U00]00i01:S1x3mfa2H01qS1x3mfa2H02HX1q1ES3mfa2H0S3mfa2H0S3mfa2H01q1ES1x3mfa2H03HUB2HX". (* [comment removed for export] *)
#[using="Type"] Lemma roundup_unit : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Px,$0.Pmfa,$0.P,(2.=R1.)P,(3.(;.R2.(4.+2.+12.))(4.+2.+3>.))P,(5.$0.(<.R3.(4.+2.+12.))=)P,(1.(3.R4.R5.)(2.R5.(;.R4.(4.+2.+12.))))(5.$0.(=.(;.R6.+3????.)+???????????<0000.)(;.R5.+40000.))")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros x mfa H0 HUB HAL HX.
  change 18446744073709289472 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 18))). rewrite land_clear_low by lia.
  change (2^18) with 262144 in *.
  pose proof (Z.div_mod mfa 262144 ltac:(lia)) as E. rewrite HAL, Z.add_0_r in E.
  set (q := mfa / 262144) in *.
  replace ((x + 262143) / 262144) with (q + 1); [lia|].
  apply (Z.div_unique_pos _ _ _ (x + 262143 - (q + 1) * 262144)); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition carve_list (au cs : Z) (nw : nat) : list word :=
  map (fun j => Z_to_bv 64 ((au + (Z.of_nat nw - 1 - Z.of_nat j) * cs) / 16)) (seq 0 nw).
#[using="Type"] Lemma carve_list_length : forall au cs nw, length (carve_list au cs nw) = nw.
Proof. intros. unfold carve_list. rewrite map_length, seq_length. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47221021981.6000008S2nw1j1H". (* [comment removed for export] *)
#[using="Type"] Lemma carve_list_nth : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pau,$0.Pcs,$0.Pnw,$>.Pj,$>.P,(?.R1.R2.)(5.(10.(6.&40.))(11.(6.&40.)(12.R5.R4.R3.)R2.)(13.(6.&40.)(9.&40.(:.(;.R5.(14.(15.(15.(16.R3.)+1.)(16.R2.))R4.))+10.))))")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros. unfold carve_list. rewrite nth_error_map, nth_error_seq.
  replace (Nat.ltb j nw) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [option_map]. rewrite Nat.add_0_l. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L16022306721.14L17397470920.10L22576782243.10L39125621115.9 L53041397756.14L59788054353.14L60813231345.10L9672920628.9  00000M00a01501F01c02@02T02eS1X2l12l21k2Hk2Hl2L13pre4HlenS1X2l12l21k2Hk2Hl2L1S1X2l12l21k2Hk2Hl2L1S1X2l12l21k2Hk2HlS1X2l12l21k2Hk2Hl2L13pre4HlenS1X2l12l21k2Hk2Hl2L13pre4HlenS1X2l12l21k2Hk2Hl2L1S1X2l12l21k2Hk2Hl". (* [comment removed for export] *)
#[using="Type"] Lemma cv_step : forall {X} (l1 l2 : list X) k x, (k < length l1)%nat -> length l1 = length l2 ->
  nth_error l2 k = Some x ->
  upd (firstn (S k) l1 ++ skipn (S k) l2) k x = firstn k l1 ++ skipn k l2.
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros X l1 l2 k x Hk Hl Hn.
  rewrite upd_firstn_skipn.
  2:{ rewrite app_length, firstn_length, skipn_length. lia. }
  assert (L1 : length (firstn (S k) l1) = S k) by (rewrite firstn_length; lia).
  rewrite firstn_app, firstn_firstn, L1 by lia. replace (Nat.min k (S k)) with k by lia. replace (k - S k)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r.
  rewrite skipn_app, L1, Nat.sub_diag, skipn_O, (skipn_all2 (firstn (S k) l1)) by lia. cbn [app].
  f_equal.
  destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen).
  rewrite E. rewrite !skipn_app, Hlen, Nat.sub_diag, skipn_O. replace (S k - k)%nat with 1%nat by lia.
  rewrite (skipn_all2 (n:=k) pre), (skipn_all2 (n:=S k) pre) by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma Z_to_bv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). exact H.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L15680320461.5L41415989753.5L66253724681.500000500600<S1E1iSS1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma carve_addr : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "PE,$0.Pi,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+3>.)))P,(1.(2.(14.+4.(;.R2.+1.))R3.)(3.R3.(4.+2.+3?.)))(5.(6.&40.)(9.&40.(;.R4.(17.(18.R3.+????????????????.)+2.)))(9.&40.(15.(15.R4.+4.)(14.+4.R3.))))")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros E i Hi HE. apply Z_to_bv_eqm. rewrite zb_lxor_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
  replace (E + (18446744073709551615 - i) * 4) with ((E - 4 - 4 * i) + 4 * 2^64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Populate2.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L10301937019.56L15471112047.56L17718797976.56L19325175391.55L21629997241.55L22026656983.56L31475289507.57L3437579167.56 L37957749663.5600000I00^01901D01S01n02>02W030S3hAR1c2au2mu3HAU3HMU3CS1S3hAR1c2au2mu3CS13CS2S3hAR2RI1c2au2mu2HC3HAU3CS1S3hAR1c3CS1S3hAR2au2mu3HAUS3hAR2RI1c2au2mu2HC3HAU3CS1S3hAR2RI1c2au2muS3hAR1c2au2mu3HAU3HMU3CS1S3hAR1c2au2mu3HAU3HMU3CS1". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_C : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pra,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps1,(6.&40.)Ps3,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PRB,$0.Pc,$0.Pau,$0.Pmu,$0.Pnf,$0.P,(2.+65?000.R7.)P,(2.(;.R8.+1000.)(1:.VhAR,))P,(5.$0.R8.(;.R9.(14.+80.R6.)))P,(1;.VCS,R:.+1000.)P,(1.(2.+1.R8.)(2.R8.+1?.))P,(1.(2.=R8.)(2.R8.R7.))P,(2.R8.+>0000000.)P,(1.(2.=R8.)(3.R8.(4.+2.+28.)))P,(1<.$1=.R10.(;.R>.+10.)(1>.$1?.(20.(9.&40.R9.))(21.$1?.)))P,(22.$1=.R11.)(23.$1=.VAL,VCS,Lms',$24.Znw,$0.(:.(15.R=.R>.)(25.R?.))(5.$24.R2.(26.(27.(9.&40.+4<<?4.)(9.&40.(;.R17.-40.))R2>.R2=.R2<.R2;.R2:.(9.&40.R12.)(9.&40.(;.R=.R1.))(9.&40.$28.)(9.&40.R12.)(9.&40.R11.)(9.&40.(;.R=.R1.))R25.R24.R23.R22.(9.&40.R11.)(9.&40.R1.)(9.&40.(15.R>.R?.))(9.&40.(25.R10.))R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R16.(9.&40.$29.)R15.(2:.(6.&40.))R14.(2;.$1=.)))(26.(27.R2=.(9.&40.(;.R15.-40.))R2<.R2;.R2:.R29.R28.(9.&40.R10.)R27.(9.&40.$28.)R25.R24.(9.&40.R=.)R23.R22.R21.R20.(9.&40.R?.)R26.(9.&40.R<.)(9.&40.(25.R>.))R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R14.(9.&40.+4<<=4.)R13.(2:.(6.&40.))R12.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s1 s3 a1 a2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m RI R RB c au mu nf
      R0 R1 HR RICS HC HAU HMU HNF NF MI.
    facts. unfold A_INSTANCE, A_EFS in *. subst R.
    pose proof (class_size_range c HC) as [CS1 CS2].
    assert (NW : 0 <= (mu - au) / class_size c <= mu - au).
    { split. { apply Z.div_pos; lia. } apply Z.div_le_upper_bound; [lia|]. nia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (mul_divu_lit (mu - au) (class_size c)) by lia.
    zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition efs_frame (m : mem) (SP : Z) (j0 : list byte) (q3 q2 q1 q0 qra : word) : Prop :=
    rw_cells asegs m (SP + -48) [CB 8 j0; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma efs_A_enough : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pra,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PRB,$0.Ptot,$0.Pmfa,$0.Plo,$0.Pc,$0.P,(2.+65?000.R7.)P,(2.(;.R8.+1000.)(1:.VhAR,))P,(5.$0.R8.(;.R9.(14.+80.R3.)))P,(1;.VCS,R:.+1000.)P,(1.(2.+1.R5.)(2.R5.+1?.))P,(1.(2.=R9.)(3.R9.(4.+2.+28.)))P,(2.(14.+4.R:.)R9.)P,(3.R:.(4.+2.+3?.))P,(1<.$1=.R10.(;.R>.+18.)(1>.$1?.(20.(9.&40.R;.))(21.$1?.)))P,(2<.$1=.R11.R;.R14.)P,(2.(1:.VhAR,)R<.)P,(2.R=.(15.R16.+30.))P,(2.R17.(4.+2.+3?.))P,(5.$0.(<.R18.+10.)=)P,(1;.VCS,R10.(15.R19.R10.))P,(22.$1=.R17.)(23.$1=.VAL,VCS,Lms',$24.(2=.(6.&40.)Lx13,(6.&40.)(2=.(6.&40.)Lx14,(6.&40.)(2=.(6.&40.)Lx15,(6.&40.)(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(1.(5.$24.R5.(26.(27.R3:.(9.&40.R20.)R39.R38.R37.R36.R35.R34.R33.(9.&40.+1.)(9.&40.R1;.)(9.&40.R1:.)R4.R3.R2.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1?.(2>.R3:.)R1>.(2:.(6.&40.))R1.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.R17.R20.)(21.(30.$0.$0.)))R1=.R1.)(1.(32.$1=.R1=.R1.)(1.(22.$1=.R1.)(2<.$1=.R1.R17.R20.)))))))))(26.(27.R35.(9.&40.R1;.)R34.R33.R32.R31.R30.R2?.R2>.(9.&40.$28.)(9.&40.R16.)(9.&40.R15.)(9.&40.R14.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1:.(9.&40.$29.)R19.(2:.(6.&40.))R18.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m RI R RB tot mfa lo c
      R0 R1 HR RICS HC HT HM HM2 MFA ST LOIMG SPL SPH SPA SCS MI.
    unfold A_INSTANCE, A_EFS in *. subst R.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_post.
  Qed.

  (* [comment removed for export] *)
  Definition efs_mwc_regs (SP : Z) (gp tp t0 t1 t2 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (R FA mfa : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "(27.(9.&40.+4:8<4.)(9.&40.(;.O17.-30.))O16.O15.O14.O13.O12.(9.&40.(;.O1.(4.+2.+12.)))(9.&40.(;.O2.O1.))(9.&40.$28.)(9.&40.(;.O2.O1.))(9.&40.(4.+2.+12.))(9.&40.$33.)(9.&40.O1.)(9.&40.+>0000000.)O11.O10.(9.&40.(4.+2.+12.))(9.&40.O3.)O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L15225004763.6 L23341822318.1 L25121556945.6 L34505064344.1 L44449330788.61L46083836741.77L5014790389.77 L56382327668.6 L59308579152.62L60587552073.78L66255686392.6 00000900=00K00O00f01M01]01j02X02h038S3mfa3HM0S2SPS3mfa3HM04HMALS2SPS3hAR2SP3mfa2lo3HM03SPLS3hAR2SP2RB2FA3mfa2lo3HM03HFA5LOIMG3SPLS3hAR2SP3mfa3HM0S3mfa3HM03HM2S3hAR2SP3mfa2lo3HM04HMAL3HM25LOIMG3SPL3SPA3LXES3hAR2SP3mfa3HM0S3tot3mfa3HM02HM". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma efs_A_map : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pra,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PRB,$0.PFA,$0.Ptot,$0.Pmfa,$0.Plo,$0.Pc,$0.P,(2.+65?000.R8.)P,(2.(;.R9.+1000.)(1:.VhAR,))P,(5.$0.R9.(;.R:.(14.+80.R3.)))P,(1;.VCS,R;.+1000.)P,(1.(2.+1.R5.)(2.R5.+1?.))P,(2.=R9.)P,(2.=R9.)P,(5.$0.(<.R:.(4.+2.+12.))=)P,(1.(3.R;.(14.+4.R<.))(2.(14.+4.R<.)(;.R;.(4.+2.+12.))))P,(2.(;.R<.(4.+2.+12.))(4.+2.+1=.))P,(5.$0.R?.(;.R10.+>0000000.))P,(2.=R11.)P,(2.(;.R12.(4.+2.+20.))(4.+2.+2?.))P,(1<.$1=.R16.(;.R14.+18.)(1>.$1?.(20.(9.&40.R10.))(21.$1?.)))P,(34.$1=.R17.$35.(1>.$1?.(36.(9.&8.=))(21.$1?.)))P,(2<.$1=.R18.R11.R1;.)P,(2.(1:.VhAR,)R12.)P,(2.R13.(15.R1=.+30.))P,(2.R1>.(4.+2.+3?.))P,(5.$0.(<.R1?.+10.)=)P,(1;.VCS,R16.(15.R20.R16.))P,(22.$1=.R1>.)(23.$1=.VAL,VCS,Lms',$24.(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(2=.(37.(6.&8.))Lj0,(37.(6.&8.))(1.(5.$24.R3.(26.(38.R25.R3>.R3=.R3<.R3;.R3:.R35.R34.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R20.R1>.R1<.)R24.(9.&40.$39.)R23.(2:.(6.&40.))R2.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.R1;.R25.)(21.(30.$0.$0.)))R22.R2.)(1.(32.$1=.R22.R2.)(1.(22.$1=.R2.)(1.(3:.R2.R25.R1.R32.R33.R38.R39.R3?.)(2<.$1=.R2.R1;.(;.R25.-30.)))))))))(26.(27.R3<.(9.&40.R22.)R3;.R3:.R39.R38.R37.R36.R35.(9.&40.$28.)(9.&40.R1=.)(9.&40.R1<.)(9.&40.R1:.)R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R21.(9.&40.$29.)R20.(2:.(6.&40.))R1?.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m RI R RB FA tot mfa lo c
      R0 R1 HR RICS HC HT HM0 HMAL HM HM2 HFA RB0 RB1 MFA PRE ST LOIMG SPL SPH SPA SCS MI.
    unfold A_PREMAPPED in *. unfold A_INSTANCE, A_EFS, A_RAR_MAP, A_NAME_EFS, efs_mwc_regs, efs_frame in *. change (1074072 + 56) with 1074128 in *. subst R.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x851a8] [] 60%N).
    all: rewrite (roundup_unit (4 * tot) mfa) in * by (clear - HM0 HM2 HMAL HM; lia).
    all: lx_deads.
    unfold A_INSTANCE, A_NAME_EFS. change (2^18) with 262144.
    lx_junk_under lo (SP + -40) 8%nat j0 FRa.
    lx_postw. exact FRa.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma efs_B_no : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq3,(6.&40.)Pq2,(6.&40.)Pq1,(6.&40.)Pq0,(6.&40.)Pqra,(6.&40.)Pj0,(37.(6.&8.))PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))Plo,$0.PW,(37.(30.$0.$0.))P,(3:.R3.R7.R8.R=.R<.R;.R:.R9.)P,(2<.$1=.R4.R3.(;.R8.-30.))P,(2.(1:.VhAR,)R4.)P,(2.R5.(15.R:.+30.))P,(2.R;.(4.+2.+3?.))P,(5.$0.(<.R<.+10.)=)P,(1;.VCS,R8.(15.R=.R8.))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R9.R>.)R8.)R;.R:.)P,(22.$1=.R;.)(23.$1=.VAL,VCS,Lms',$24.(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(1.(5.$24.R2.(26.(27.R14.(9.&40.R12.)R34.R33.R32.R31.R30.R15.R16.(9.&40.=)R2=.R2<.(9.&40.=)R2:.R29.R28.R27.R17.R18.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R11.(2>.R14.)R10.(2:.(6.&40.))R1.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.R=.R12.)R<.)R?.R1.)(1.(22.$1=.R1.)(1.(2<.$1=.R1.R=.R12.)(2?.(21.$3;.)R>.R1.))))))(26.(27.(9.&40.+4:8<4.)(9.&40.(;.R10.-30.))R32.R31.R30.R2?.R2>.R2=.R2<.(9.&40.=)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R?.(9.&40.+4:8<4.)R>.(2:.(6.&40.))R<.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q3 q2 q1 q0 qra j0 SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU MI.
    unfold efs_frame in FR. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). subst lxm. lx_post.
  Qed.

  (* [comment removed for export] *)
  Definition efsB_post (SP : Z) (gp tp s4 s5 s6 s7 s8 s9 s10 s11 q3 q2 q1 q0 qra : word) (F : bvmap 5 word) (fc : bv 32)
      (R FA T CTX mfa lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Lms',$24.(2=.(6.&40.)Lx5,(6.&40.)(2=.(6.&40.)Lx6,(6.&40.)(2=.(6.&40.)Lx7,(6.&40.)(2=.(6.&40.)Lx11,(6.&40.)(2=.(6.&40.)Lx12,(6.&40.)(2=.(6.&40.)Lx13,(6.&40.)(2=.(6.&40.)Lx14,(6.&40.)(2=.(6.&40.)Lx15,(6.&40.)(2=.(6.&40.)Lx16,(6.&40.)(2=.(6.&40.)Lx17,(6.&40.)(2=.(6.&40.)Lx28,(6.&40.)(2=.(6.&40.)Lx29,(6.&40.)(2=.(6.&40.)Lx30,(6.&40.)(2=.(6.&40.)Lx31,(6.&40.)(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(2=.(6.&40.)Lj1,(6.&40.)(2=.(6.&40.)Lj2,(6.&40.)(1.(5.$24.R12.(26.(27.O;.(9.&40.O1:.)O19.O18.R11.R10.R?.O<.O=.(9.&40.+1.)R>.R=.R<.R;.R:.R9.R8.O>.O?.O17.O16.O15.O14.O13.O12.O11.O10.R7.R6.R5.R4.)O:.(2>.O;.)O9.(2:.(6.&40.))R3.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.O3.O1:.)(1>.(30.$0.$0.)(31.$0.$0.(;.+7???8000.(:.(;.O7.O4.)+8.))(;.(;.+7???8000.(:.(;.O7.O4.)+8.))+8000.))(1>.(30.$0.$0.)(31.$0.$0.(;.O6.+;38.)(;.O6.+;48.))(1>.(30.$0.$0.)(31.$0.$0.(;.O8.+18.)(;.O8.+20.))O2.))))O1.R3.)(1.(32.$1=.O1.R3.)(1.(22.$1=.R3.)(1.(1<.$1=.R3.(;.+7???8000.(:.(;.O7.O4.)+8.))(1>.$1?.(3<.(3=.+8000.)(3>.(6.&8.)(9.&8.+?:.)(3=.+8000.)))(21.$1?.)))(1.(1<.$1=.R3.(;.O6.+;38.)(1>.$1?.(20.R2.)(1>.$1?.(20.R1.)(21.$1?.))))(1.(1<.$1=.R3.(;.O8.+18.)(1>.$1?.(20.(9.&40.(;.O4.(4.+2.+12.))))(21.$1?.)))(1.(3?.R3.)(1.(40.R3.O5.O6.)(2<.$1=.R3.O3.O1:.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L13922587162.22 L15488928053.22 L18720890185.22 L18926384029.22 L19806023472.24 L21061785948.22 L21943567510.22 L23535432052.84 L26682560688.91 L26682560690.89 L27846297964.3  L33066364120.22 L38237949960.3  L41015213144.22 L41122898750.24 L44637234084.18 L46256863012.18 L46595273239.109L49509889741.22 L50198383746.109L51489811881.89 L51489811883.91 L54939278768.24 L55588686165.0  L57628690880.110L57731194532.18 L58807237918.18 L58817773446.109L58817773446.111L58856313392.24 L63505931041.0  L68046851233.2  L68630208887.22 L8377867289.2   L9289892317.22  00000X01@02902L03N03h04i06:06_07@07G07Z07^08:09I0:00:W0:X0:k0:l0;O0<40=60=70>J0?10@00@k0BQ0CS0CT0C\0DU0D[0E2S3hAR2SP2RB3mfa2lo3RB03HM05LOIMG3SPL3SPAS3hAR2SP2RB3mfa2lo3RB03HM05LOIMG3SPL3SPAS3hAR2SP2RB2FA3mfa2lo3RB03HFA4RBAL3HM04HMAL5LOIMG3SPL3SPAS3hAR2SP2RB3mfa3HM0S3hAR2SP2RI2RB2FA1T3CTX1c3mfa2lo2HC3RB03HFA3RB13HM02T02C02CT5LOIMGS3hAR2SP2RB3mfa2lo3HM03SPLS3hAR2SP2RI2RB2FA1T1c3mfa2lo2HC3RB03HFA3RB13HM02T05LOIMG2A'2n'2H'S3hAR2SP2RI2RB2FA1T1c3mfa2lo2R12HC3RB03HFA3RB14RBAL3HM04HMAL3HM22T05LOIMG3SPL3SPAS3hAR2SP2RI2RB2FA1T1c3mfa2lo3HM01y2HyS3hAR2SP2RB2FA1T3mfa2lo3HM01y3H11S2SP2loS3hAR2SP2RB3mfa3HM0S2loS3hAR2SP2RB3mfa2lo3HM05LOIMGS3hAR2SP2RI2RB2FA1T3CTX1c3mfa2lo2R12HC3RB03HFA3RB13HM03HM22T02C02C12CT2CR5LOIMGS3hAR2SP2RB2FA3mfa2lo3RB03HFA3HM05LOIMGS3hAR2SP2RB2FA3mfa2lo3RB03HFA3HM05LOIMGFS3hAR2SP2RB3mfa3HM0FS3hAR2SP2RI2RB2FA1T1c3mfa3HM01y3H14S3hAR2SP2RI2RB2FA1T1c3mfa2lo3HM01y2HyS3hAR2SP2RI2RB2FA1T3CTX1c3mfa2lo2HC3RB03HFA3RB13HM02T02C02CT5LOIMGSS3hAR2SP2RI2RB2FA1T3mfa2lo2R13RB03HFA3RB14RBAL3HM04HMAL3HM22T05LOIMG3SPL3SPA3x152H0S3hAR2SP2RB2FA3mfa2lo3RB03HFA3HM05LOIMGS3hAR2SP2RI2RB2FA3CTX3mfa2lo2R13RB03HFA3RB13HM03HM22C02C15LOIMGS3hAR2SP2RI2RB2FA1T3mfa2lo2R13RB03HFA3RB13HM03HM25LOIMG3SPLS3hAR2SP2RI2RB2FA1T1c3mfa2lo2R12HC3RB03HFA3RB14RBAL3HM04HMAL3HM25LOIMG3SPL3SPA3CTX2T02T12C02C14TSEP2CTS3hAR2SP2RI2RB2FA1T3CTX1c3mfa2lo2HC3RB03HFA3RB13HM02T02C02CT5LOIMGSS2FA3mfaS3hAR2SP2RI2RB2FA3mfa2lo2R13RB03HFA3RB13HM03HM25LOIMG3SPLS2RI1cS3hAR2SP2RB3mfa3HM03SPH". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma efs_B_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq3,(6.&40.)Pq2,(6.&40.)Pq1,(6.&40.)Pq0,(6.&40.)Pqra,(6.&40.)Pj1,(6.&40.)Pj2,(6.&40.)Pj0,(37.(6.&8.))Pjunk,(37.(6.&8.))PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PRB,$0.PFA,$0.PT,$0.PCTX,$0.Pc,$0.Pmfa,$0.Plo,$0.PW,(37.(30.$0.$0.))Zbeg,$0.(;.R7.R3.)P,(2.+65?000.R;.)P,(2.(;.R<.+1000.)(1:.VhAR,))P,(5.$0.R<.(;.R=.(14.+80.R7.)))P,(1;.VCS,R>.+1000.)P,(1.(2.+1.R9.)(2.R9.+1?.))P,(2.+10007???9000.R>.)P,(5.$0.R>.(;.R?.+>0000000.))P,(2.(;.R10.(4.+2.+20.))R12.)P,(5.$0.(<.R11.+1000.)=)P,(2.=R=.)P,(5.$0.(<.R>.(4.+2.+12.))=)P,(2.(;.R?.(4.+2.+12.))(4.+2.+1=.))P,(1;.VCS,R=.(4.+2.+12.))P,(1.(1.(2.+1000.R14.)(41.(2.(;.R14.+1000.)+10000.)(2.+65?000.R14.)))(41.(2.(;.R14.+1000.)+7???7000.)(2.+10007???8000.R14.)))P,(2.(;.R15.+1000.)(1:.VhAR,))P,(5.$0.(<.R16.+1000.)=)P,(1;.VCS,R17.+1000.)P,(1.(2.+65?000.R17.)(41.(2.(;.R17.+10000.)+7???7000.)(2.+10007???8000.R17.)))P,(2.(;.R18.+10000.)(1:.VhAR,))P,(1;.VCS,R19.+10000.)P,(41.(2.(;.R1;.+1000.)R1=.)(2.(;.R1?.+1000.)R1;.))P,(41.(2.(;.R1;.+10000.)R1<.)(2.(;.R1<.+1000.)R1;.))P,(41.(2.(;.R1<.+10000.)R1?.)(2.(;.R21.+1000.)R1<.))P,(1<.$1=.R23.(;.+7???8000.(:.R18.+8.))(1>.$1?.(3<.(3=.+8000.)R28.)(21.$1?.)))P,(3?.R24.)P,(40.R25.R1?.R20.)P,(1<.$1=.R26.(;.R21.+;38.)(1>.$1?.(20.R2>.)(1>.$1?.(20.R2=.)(21.$1?.))))P,(1<.$1=.R27.(;.R25.+18.)(1>.$1?.(20.(9.&40.R1?.))(21.$1?.)))P,(3:.R28.R2<.R2>.R35.R34.R33.R32.R31.)P,(2<.$1=.R29.R20.(;.R2=.-30.))P,(2.(1:.VhAR,)R21.)P,(2.R22.(15.(15.R2?.+30.)+40.))P,(2.R30.(4.+2.+3?.))P,(5.$0.(<.R31.+10.)=)P,(1;.VCS,R25.(15.R32.R25.))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R26.R33.)(1>.(30.$0.$0.)(31.$0.$0.(;.+7???8000.(:.R24.+8.))(;.(;.+7???8000.(:.R24.+8.))+8000.))(1>.(30.$0.$0.)(31.$0.$0.(;.R2:.+;38.)(;.R2:.+;48.))(1>.(30.$0.$0.)(31.$0.$0.(;.R2=.+18.)(;.R2=.+20.))R25.))))R30.R2?.)P,(32.$1=.R31.R30.)P,(22.$1=.R31.)P,(5.(6.&40.)R56.(9.&40.$42.))(23.$1=.VAL,VCS,(43.R37.R58.R57.R4<.R4;.R4:.R49.R48.R47.R46.R45.R40.R3?.R3>.R3=.R3<.R36.R35.R31.R2?.R2>.R2=.R2;.R2:.R29.R34.)(26.(27.(9.&40.+4:8<4.)(9.&40.(;.R37.-30.))R58.R57.R56.R55.R54.(9.&40.(;.R2;.(4.+2.+12.)))(9.&40.R28.)(9.&40.R28.)R53.R52.R51.R50.R4?.R4>.R4=.(9.&40.(4.+2.+12.))(9.&40.R31.)R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)R36.(9.&40.+4:8<4.)R35.(2:.(6.&40.))R33.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q3 q2 q1 q0 qra j1 j2 j0 junk SP F fc m0 m RI R RB FA T CTX c mfa lo W beg
      R0 R1 HR RICS HC RB0 HFA RB1 RBAL HM0 HMAL HM2 BCS T0 T1 TAL TCS C0 C1 CCS TSEP CT CR SH PS TS TJ MFA FR ST LOIMG SPL SPH SPA SCS MU WM MI TP.
    unfold efs_frame in *. subst R beg. change (2^18) with 262144 in *.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. lx_hide SH. lx_aceil.
    lx_run (PLAN [A_POISON] [] 20%N).
    subst lxm. repeat match goal with H : ?T, K : ?U |- _ => constr_eq T U; clear K end.
    repeat match goal with K : munch [] m m |- _ => clear K | K : wmono _ m m |- _ => clear K end.
    replace (mfa + FA) with (FA + mfa) by (clear; lia).
    lx_unhide1 SH.
    pose proof (munch_refl [(lo, SP + -48); (2147450880 + (FA + mfa) / 8, 2147450880 + (FA + mfa) / 8 + 32768)] m) as MUm.
    pose proof (wmono_refl asegs m) as WMm.
    callxA (eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (lo := lo) (m0 := m) (junk := junk);
      [ lazymatch goal with
           | |- rw_cells _ _ _ [CB _ _] => exact SH
           | |- poison_statics _ => exact PS
           | |- stk _ _ _ _ => exact ST
           | |- crange _ _ _ => first [exact BCS | eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]]
           | |- munch _ _ _ => apply munch_refl
           | |- wmono _ _ _ => apply wmono_refl
           | |- mem_inv _ _ => exact MI
           | |- _ => clear - R0 R1 HC RB0 RB1 RBAL HFA HM0 HMAL HM2 LOIMG SPL SPH SPA; lia end .. ]).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TS' : thr_statics mc CTX T) by (eapply thr_statics_transport; [exact TS| exact MUm| | | |]; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; cbn;
                                                clear - LOIMG SPL RB0 RB1 R1 HFA HM0 C0 C1 HM2; lia);
      destruct TS' as (TS1 & TS2 & TS3 & TS4); unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in TS1, TS2, TS3;
      (* [comment removed for export] *)
      lx_hide MUm; lx_hide WMm;
      match goal with PC : rw_cells _ mc _ [CB _ (repeat _ _)] |- _ => lx_hide PC end;
      pose proof (munch_refl [(lo, SP); (T + 2872, T + 2888); (RI + 128 * c + 24, RI + 128 * c + 32)] mc) as MU2;
      pose proof (wmono_refl asegs mc) as WM2 end.
    subst tp. unfold A_TP.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N). lx_unhide.
    apply evtA_done. unfold efsB_post.
    lazymatch goal with MUl : munch _ ?mc lxm, WMl : wmono _ ?mc' lxm, PC : rw_cells _ ?mc'' _ [CB _ (repeat _ _)] |- _ =>
      change (262144 / 8) with 32768 in PC;
      set (Wme := [(lo, SP); (0x7fff8000 + (FA + mfa) / 8, 0x7fff8000 + (FA + mfa) / 8 + 32768); (T + 2872, T + 2888); (RI + 128 * c + 24, RI + 128 * c + 32)]);
      assert (MUme : munch Wme m lxm) by (subst Wme; lx_munch MUm MUl); subst Wme;
      lx_exs; lx_ands;
      [ lx_mseq
      | lx_munch3 MU MUm MUl
      | lx_wmono3 WM WMm WMl
      | assumption
      | lx_tr_rw PC MUl WMl
      | eassumption
      | match goal with |- rw_cells _ _ ?a _ => replace a with (RI + (128 * c + 24)) by (clear; lia); change (2^18) with 262144; assumption end
      | eapply poison_statics_transport; [exact PS| exact MUme |]; intros A' n' H'; cbn; clear - H' LOIMG SPL RB0 RB1 R1 HFA HM0 T0 HC HM2; lia
      | eapply thr_statics_transport; [exact TS| exact MUme | | | |]; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; cbn;
          clear - LOIMG SPL RB0 RB1 R1 HFA HM0 C0 C1 T0 HC HM2 CT CR; lia
      | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0?L16942402016.68L16942402016.69L17308520637.66L18628295885.67L2157271584.65 L2233853817.67 L23906008979.67L25648106397.67L28193507746.66L28922882432.65L314175014.68  L3256083756.65 L33829987662.65L39637404430.67L39639646470.66L3978485264.68 L3978485526.70 L40823184503.66L42941798008.59L44101127392.5 L48779389527.67L5331070982.66 L55323243545.66L58215863136.68L58555651851.66L58746523046.66L65395000123.65L66253725324.65L66859398586.71L760568750.65  L8755307029.66 L9801842029.66 00000]01J02302]03G04604g05Q06>06X07G08<08V09F0:60:b0;N0<10>70>B0?:0?j0@Z0AM0B00B]0CG0D<0D=0Do0EN0F>S3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2cs2nw2js2Hr3Hcs3LJS2F02HB1KS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2HB2LCS3hAR1r1i3FAN2cs2nw2js2Hr2Hi3Hcs3LJS2F02HBS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2F02HB2LC1KS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hnw3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2nw2js2Hr3LJSS3hAR1r1i3FAN2au2cs2nw2js1W2Hr3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hau3Hub3Hcs3LJS2F02HBS3hAR1r1i3FAN2nw2js2Hr3LJSS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3LJS2F02F12LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3LJS2F02F12LCS3hAR1r1i3FAN2au2cs2nw2js2Hr3LJS2LCS3hAR2AL2CS1i2ra2sp2gp2tp2t02t12t22s02s12s22a32a42a52a62a72s42s62s72s82s93s103s112t32t42t52t61F2fc2m01m3FAN2au2cs2nw2js1W2Hr2Hi3LJS2F0S1i2nw2Hi1KS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hau3Hub3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LC2ENS3hAR1r1i3FAN2au2cs2nw2js2Hr3LJS2LCS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hcs3LJS2F02HB2LCS3hAR1r1i3FAN2cs2nw2js2Hr3Hcs3LJS2F02F12HBS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hau3Hub3Hcs3LJS2F02HBFS3hAR1r1i3FAN2au2cs2nw2js2Hr3Hau3Hub3Hcs3LJS2F02HBS3hAR1r1i3FAN2nw2js2Hr2Hi3LJS1KS3hAR1r1i3FAN2au2cs2nw2js2Hr2Hi3Hcs3LJS2F02HB2LC". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_carve : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pr,$>.Pi,$0.Pra,(6.&40.)Psp,(6.&40.)Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Ps2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps4,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))PFAN,$0.Pau,$0.Pcs,$0.Pnw,$0.Pjs,(37.(6.&40.))PW,(37.(30.$0.$0.))P,(5.$0.(;.R25.(16.R26.))R3.)P,(1.(2.=R26.)(3.R26.R4.))P,(2.R5.(4.+2.+>.))P,(2.=R8.)P,(2.(;.R9.(14.R7.R8.))+>0000000.)P,(1.(2.+20.R9.)(2.R9.+10000.))P,(5.$>.(44.(6.&40.)R8.)(3=.R9.))P,(2.+65?000.R=.)P,(2.(;.R>.(14.+4.R;.))(1:.VhAR,))P,(5.$0.(<.R?.+4.)=)P,(1;.VCS,R10.(14.+4.R=.))P,(45.$1=.R12.R11.(46.(6.&40.)(47.(6.&40.)(3=.(15.R>.R30.))R=.)(48.(6.&40.)(3=.(15.R>.R30.))(12.R10.R?.(3=.R>.)))))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R12.(;.R12.(14.+4.R?.)))R=.)R14.R13.)P,(32.$1=.R15.R14.)P,(22.$1=.R15.)(23.$1=.VAL,VCS,Lms',$24.(2=.(6.&40.)Lx14,(6.&40.)(2=.(6.&40.)Lx15,(6.&40.)(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(1.(5.$24.R4.(26.(27.R37.R36.R35.R34.R33.R32.R31.R30.R2?.(9.&40.R16.)(9.&40.(;.R19.(14.+4.R16.)))(9.&40.(;.R18.(14.R16.R17.)))R2=.R3.R2.R2:.R29.R2>.(9.&40.R16.)R28.(9.&40.R17.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(9.&40.+4<=3<.)R1<.(2:.(6.&40.))R1.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.R19.(;.R19.(14.+4.R16.)))R14.)R1;.R1.)(1.(32.$1=.R1;.R1.)(1.(22.$1=.R1.)(45.$1=.R1.R19.(12.R18.R17.(3=.R16.))))))))))(26.(27.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.(9.&40.R34.)(9.&40.(;.R15.(14.+4.R12.)))(9.&40.(;.R14.(14.R34.R13.)))R29.R28.R27.R26.R25.R2:.(9.&40.R12.)R24.(9.&40.R13.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(9.&40.+4<=1<.)R18.(2:.(6.&40.))R16.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    induction r as [|r IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 s2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m FAN au cs nw js W
      Hr Hi Hnw Hau Hub Hcs LJS F0 F1 FAL FCS HA MU WM MI; [lia|].
    facts.
    assert (HB : 0 <= i * cs /\ i * cs + cs <= nw * cs) by (clear - Hi Hcs; nia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    rewrite (carve_addr (FAN + 4 * nw) i) by lia.
    replace (FAN + 4 * nw - 4 - 4 * i) with (FAN + 4 * (nw - 1 - i)) by lia.
    assert (LC : length (firstn (Z.to_nat (nw - i)) js ++ skipn (Z.to_nat (nw - i)) (carve_list au cs (Z.to_nat nw))) = Z.to_nat nw).
    { rewrite app_length, firstn_length, skipn_length, carve_list_length. lia. }
    pose proof (u32arr_store_ok asegs m FAN _ (nw - 1 - i) _ HA ltac:(rewrite LC; lia) eq_refl) as SOK.
    pose proof (u32arr_write asegs m FAN _ (nw - 1 - i) (Z_to_bv 64 ((au + i * cs) ≫ 4)) HA ltac:(rewrite LC; lia)) as HA'.
    (* [comment removed for export] *)
    zstep. store_done. try clear HA.
    replace (Z.to_nat (nw - i)) with (S (Z.to_nat (nw - 1 - i))) in HA' by lia.
    rewrite (cv_step js (carve_list au cs (Z.to_nat nw)) (Z.to_nat (nw - 1 - i)) (Z_to_bv 64 ((au + i * cs) ≫ 4))) in HA'.
    2:{ lia. } 2:{ rewrite carve_list_length. lia. }
    2:{ rewrite carve_list_nth by lia. f_equal. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. f_equal. lia. }
    (* [comment removed for export] *)
    zstep. replace (au + i * cs + cs) with (au + (i + 1) * cs) by lia.
    zstep. if_cases K; zify_cond K.
    - replace (Z.to_nat (nw - 1 - i)) with (Z.to_nat (nw - (i + 1))) in HA' by lia.
      clear LC. eapply (IH (i + 1)) with (js := js); try eassumption; try lia.
    - assert (EN : i + 1 = nw) by (clear - K Hi Hnw; lia).
      rewrite EN in *. replace (Z.to_nat (nw - 1 - i)) with 0%nat in HA' by lia. cbn [firstn skipn app] in HA'.
      apply evtA_done. do 3 eexists.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact HA'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_D_no : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps3,(6.&40.)Ps4,(6.&40.)Ps5,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq6,(6.&40.)Pq5,(6.&40.)Pq4,(6.&40.)Pq3,(6.&40.)Pq2,(6.&40.)Pq1,(6.&40.)Pq0,(6.&40.)Pqra,(6.&40.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))Plo,$0.PW,(37.(30.$0.$0.))P,(49.R3.R7.R?.R>.R=.R<.R;.R:.R9.R8.)P,(2<.$1=.R4.R3.(;.R8.-40.))P,(2.(1:.VhAR,)R4.)P,(2.R5.(15.R:.+40.))P,(2.R;.(4.+2.+3?.))P,(5.$0.(<.R<.+10.)=)P,(1;.VCS,R8.(15.R=.R8.))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R9.R>.)R8.)R;.R:.)P,(22.$1=.R;.)(23.$1=.VAL,VCS,Lms',$24.(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(1.(5.$24.R2.(26.(27.R13.(9.&40.R12.)R36.R35.R34.R33.R32.R14.R15.(9.&40.=)(9.&40.=)R2>.R2=.R2<.R2;.R2:.R29.R16.R17.R18.R19.R1:.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R11.(2>.R13.)R10.(2:.(6.&40.))R1.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.R=.R12.)R<.)R?.R1.)(1.(22.$1=.R1.)(1.(2<.$1=.R1.R=.R12.)(2?.(21.$3;.)R>.R1.))))))(26.(27.(9.&40.+4<<?4.)(9.&40.(;.R10.-40.))R34.R33.R32.R31.R30.R2?.R2>.(9.&40.=)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R?.(9.&40.+4<<?4.)R>.(2:.(6.&40.))R<.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU MI.
    unfold pop_frame in FR. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). subst lxm. lx_post.
  Qed.

  Definition popD_post (SP : Z) (gp tp a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra : word) (F : bvmap 5 word) (fc : bv 32)
      (R FAN au cs nw nf mu lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Lms',$24.(2=.(6.&40.)Lx5,(6.&40.)(2=.(6.&40.)Lx6,(6.&40.)(2=.(6.&40.)Lx7,(6.&40.)(2=.(6.&40.)Lx12,(6.&40.)(2=.(6.&40.)Lx15,(6.&40.)(2=.P,(6.&40.)(10.(6.&8.))Lm',P,(6.&40.)(10.(6.&8.))(1.(5.$24.R7.(26.(27.O=.(9.&40.O22.)O21.O20.R6.R5.R4.O>.O?.(9.&40.+1.)(9.&40.+1.)R3.(9.&40.=)(9.&40.=)R2.O1?.O1>.O10.O11.O12.O13.O14.O1=.O1<.O1;.O1:.O19.O18.O17.O16.O15.)O<.(2>.O=.)O;.(2:.(6.&40.))R1.(2;.$1=.)))(1.(2?.(1>.(30.$0.$0.)(31.$0.$0.O3.O22.)(1>.(30.$0.$0.)(31.$0.$0.O9.(;.O9.(14.+4.O6.)))(1>.(30.$0.$0.)(31.$0.$0.(;.O:.+10.)(;.O:.+18.))(1>.(30.$0.$0.)(31.$0.$0.(;.O:.+20.)(;.O:.+28.))(1>.(30.$0.$0.)(31.$0.$0.(;.O:.+44.)(;.O:.+45.))O2.)))))O1.R1.)(1.(32.$1=.O1.R1.)(1.(22.$1=.R1.)(1.(45.$1=.R1.O9.(12.O8.O7.(3=.O6.)))(1.(1<.$1=.R1.(;.O:.+10.)(1>.$1?.(20.(9.&40.(;.O5.O6.)))(21.$1?.)))(1.(1<.$1=.R1.(;.O:.+20.)(1>.$1?.(20.(9.&40.(;.O8.(14.O6.O7.))))(21.$1?.)))(1.(1<.$1=.R1.(;.O:.+28.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))(1.(1<.$1=.R1.(;.O:.+30.)(1>.$1?.(20.(9.&40.O4.))(21.$1?.)))(1.(1<.$1=.R1.(;.O:.+38.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))(1.(1<.$1=.R1.(;.O:.+44.)(1>.$1?.(36.(9.&8.=))(21.$1?.)))(2<.$1=.R1.O3.O22.))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L10362820699.1 L18486181741.17L23489667164.5 L23977171292.7 L35285469927.2 L68112162384.5 00000300b01001E01L01ZS1RS3hAR2SP2RI1R3FAN1c2nw2lo2R12HR2HC3HNW2F15LOIMGS2RI1R1c2HR2HCS3hAR2RI1R1c2R12HR2HCS2nf2nwS2RI1R1c2HR2HC". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_D_tail : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Ps1,(6.&40.)Pa0,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps2,(6.&40.)Ps4,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq6,(6.&40.)Pq5,(6.&40.)Pq4,(6.&40.)Pq3,(6.&40.)Pq2,(6.&40.)Pq1,(6.&40.)Pq0,(6.&40.)Pqra,(6.&40.)Pexb,(6.&8.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PFAN,$0.Pc,$0.Pcs,$0.Pau,$0.Pmu,$0.Pnf,$0.Pnw,$0.Plo,$0.PW,(37.(30.$0.$0.))P,(2.+65?000.R;.)P,(2.(;.R<.+1000.)(1:.VhAR,))P,(5.$0.R<.(;.R=.(14.+80.R:.)))P,(1;.VCS,R>.+1000.)P,(1.(2.+1.R<.)(2.R<.+1?.))P,(2.=R;.)P,(2.=R9.)P,(1.(2.+20.R>.)(2.R>.+10000.))P,(2.(;.R>.(14.R;.R?.))R=.)P,(2.R>.+>0000000.)P,(2.=R>.)P,(3.(;.R?.R>.)(4.+2.+28.))P,(2.=R15.)P,(2.(;.R16.(14.+4.R10.))R18.)P,(45.$1=.R1:.R17.(12.R14.R15.(3=.R11.)))P,(1<.$1=.R1;.(;.R19.+10.)(1>.$1?.(20.(9.&40.R13.))(21.$1?.)))P,(1<.$1=.R1<.(;.R1:.+20.)(1>.$1?.(20.(9.&40.R16.))(21.$1?.)))P,(1<.$1=.R1=.(;.R1;.+28.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))P,(1<.$1=.R1>.(;.R1<.+30.)(1>.$1?.(20.(9.&40.R17.))(21.$1?.)))P,(1<.$1=.R1?.(;.R1=.+38.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))P,(1<.$1=.R20.(;.R1>.+44.)(1>.$1?.(36.R25.)(21.$1?.)))P,(49.R21.R25.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)P,(2<.$1=.R22.R18.(;.R26.-40.))P,(2.(1:.VhAR,)R19.)P,(2.R1:.(15.R28.+40.))P,(2.R29.(4.+2.+3?.))P,(5.$0.(<.R2:.+10.)=)P,(1;.VCS,R1=.(15.R2;.R1=.))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R1>.R2<.)(1>.(30.$0.$0.)(31.$0.$0.R25.(;.R25.(14.+4.R1?.)))(1>.(30.$0.$0.)(31.$0.$0.(;.R26.+10.)(;.R26.+18.))(1>.(30.$0.$0.)(31.$0.$0.(;.R26.+20.)(;.R26.+28.))(1>.(30.$0.$0.)(31.$0.$0.(;.R26.+44.)(;.R26.+45.))R1=.)))))R29.R28.)P,(32.$1=.R2:.R29.)P,(22.$1=.R2:.)(23.$1=.VAL,VCS,(4:.R2?.R51.R50.R46.R45.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R2>.R2=.R29.R28.R25.R26.R22.R23.R24.R21.R20.R2<.)(26.(27.(9.&40.+4<<?4.)(9.&40.(;.R2?.-40.))R51.R50.R4?.R4>.R4=.(9.&40.R29.)R4<.R4;.R4:.R49.(9.&40.R25.)R48.R47.R46.R45.R44.(9.&40.R22.)R43.(9.&40.R26.)R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R2>.(9.&40.+4<=3<.)R2=.(2:.(6.&40.))R2;.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 s1 a0 a1 a2 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra exb SP F fc m0 m RI R FAN c cs au mu nf nw lo W
      R0 R1 HR RICS HC HAU HNW HCS HUB HMU HNF HT F0 F1 HA NF AU M40 MUC M56 EX FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    unfold pop_frame in FR.
    assert (HB : 0 <= nw * cs) by (clear - HNW HCS; nia).
    pose proof (carve_list_length au cs (Z.to_nat nw)) as LCL.
    (* [comment removed for export] *)
    assert (RB1 : R + 72 <= ACEIL) by (clear - R1 HR HC; lia).
    assert (RCS : crange CS R 72) by (eapply crange_sub; [exact RICS| clear - HR HC; lia| clear - HR HC; lia]).
    lx_hide MU. lx_hide WM. lx_hide HR. lx_c1_norm. lx_aceil.
    pose proof (munch_refl [(lo, SP); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69)] m) as MU1.
    pose proof (wmono_refl asegs m) as WM1.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).
    all: lx_deads.
    lx_unhide. apply evtA_done. unfold popD_post.
    (* [comment removed for export] *)
    match goal with K : rw_cells _ lxm (R + 32) [_; _] |- _ => chunk_split K 1%nat Ka Kb; replace (R + 32 + 8) with (R + 40) in Kb by (clear; lia) end.
    lazymatch goal with MUl : munch _ m lxm, WMl : wmono _ m lxm |- _ =>
      lx_exs; lx_ands;
      [ lx_mseq
      | lx_munch MU MUl
      | lx_wmono WM WMl
      | assumption
      | eapply (u32arr_transport asegs); [exact HA| exact MUl| exact WMl| rewrite LCL; cbn [disjoint_from]; clear - F0 F1 HNW HC SPL LOIMG RB1 HR R1; lia]
      | idtac ..] end.
    all: match goal with
         | |- rw_cells _ _ ?a ?cs => first [assumption | match goal with K : rw_cells _ _ a ?cs' |- _ => replace cs with cs'; [exact K| f_equal; f_equal; f_equal; clear; lia] end]
         | |- _ => assumption end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L13569652243.9  L17258022150.106L18139731904.106L21629997241.94 L22706564033.112L23489667164.5  L23599836716.28 L23977171292.7  L2905512986.107 L2915637780.106 L3015685436.110 L34223327394.9  L34223327408.9  L34567880432.107L408049835.2    L41872035009.9  L43581236023.104L43581265463.95 L43581313077.94 L44814644544.104L4485125793.106 L4485125803.27  L4491186351.107 L4597240079.104 L4927544362.9   L4927544376.9   L50272546125.28 L51483618296.9  L5315018327.111 L53710939925.27 L53710939935.106L53713068305.107L58995408528.27 L5980454812.107 L5982255506.106 L60415935267.107L60430845229.106L60707749535.111L63090555466.27 L63728029463.28 L64964002835.27 L66175771626.106L66178098660.107L67134276377.107L68112162384.5  L68334511137.111L8917493803.104 00000A01D01E02002g03504404I05`07708Q08_0930::0:A0:]0;H0<30<^0=H0>:0>_0?Q0@;0@O0@g0B10BF0BG0Bh0CV0DD0De0ES0FA0GM0HY0J;0Jh0Kl0La0N00O?0Oi0P70P80PbS1c2au2mu2cs4LXKFS3hAR2SP2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HAU3LJS5LOIMG3SPL3CS1FS3hAR2SP2RB2FA1c2au2mu2nf2js2cs3FAN3HAU3LJSS3hAR2SP1R2RB2FA1c2au2mu2nf2lo2js1W2cs2nw3FAN3LJS2x22H0S2RI1R1c2HR2HCS3hAR2RB2FA1c2au2mu2nf2js2cs2nw3FAN3RB03HFA3HAU3HNF3LJS3CS13NWPS3hAR2RI1R1c2R12HR2HCS3hAR2SP2RI2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HFA3RB13HAU4HTOT3LJS5LOIMG3SPL3CS13NWPS3hAR2SP2RI2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HFA3RB13HAU4HTOT3LJS5LOIMG3SPL3CS13NWZS3hAR2SP2RI2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN2R13RB03HFA3RB13HAU4HTOT3LJS5LOIMG3SPL3CS13NWPS1c2cs3CS13CS2S1c2au2mu2cs3CS13CS2S3hAR2SP1m2RB2FA1c2au2mu2nf2lo1b2js2cs2nw3FAN3RB03HAU3LJS5LOIMG3SPL3CS1S2au2muS2RB2FA1c2au2mu2nf2cs2nw3HFAS3hAR2SP2RB2FA1c2au2mu2nf2js2cs3FAN3LJS3CS1S3hAR2SP2RB2FA1c2au2mu2nf2js2cs3FAN3LJS3CS1S3hAR2SP2RB2FA1c2au2mu2nf2js2cs3FAN3LJS3CS1S3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJSS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJS3CS13CS2S3hAR2RB1c2au2mu2js2cs2nw3LJS3CS13CS2S3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJS3CS13CS2S3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJSS1c2au2mu2cs3HAU3HMUS1c2au2mu2cs3HAU3HMU3CS1S3hAR2RI2RB2FA1c2au2mu2nf2js2cs2nw3FAN2R13RB03HFA3RB13HAU4HTOT3LJS3CS13NWPS1c2au2mu2cs3HAU4LXKTFS3hAR2RB1c2au2mu2js2cs2nw3HAU3LJSS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3HAU3LJSS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3HAU3LJSS3hAR2RB1c2au2mu2js2cs2nw3LJS3NWPS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJS3NW1S3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJS3NW1S3hAR2SP2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HAU4HTOT3LJS5LOIMG3SPL3CS13NWPS3hAR2SP2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HAU4HTOT3LJS5LOIMG3SPL3CS13NWZS3hAR2SP2RI2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN2R13RB03HFA3RB13HAU4HTOT3LJS5LOIMG3SPL3CS13NWP1R2HR2HCS3hAR2RB1c2au2mu2js2cs2nw3RB03HAU3LJS3CS13NWPS3hAR2RB2FA1c2au2mu2nf2js2cs2nw3FAN3RB03HFA4RBAL3HAU3HNF3LJS3CS13NWPS3hAR2RB1c2au2mu2js2cs2nw3RB03HAU3HMU3LJS3CS13NW13NWPS3hAR2SP2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HFA3HAU3HNF3LJS5LOIMG3SPL3CS13NWZS3hAR2SP2RB2FA1c2au2mu2nf2lo2js2cs2nw3FAN3RB03HFA3HAU3HNF3LJS5LOIMG3SPL3CS13NWPS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJSS2RI1R1c2HR2HCFS3hAR2SP2RB2FA1c2au2mu2nf2js2cs2nw3FAN3LJS". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_D_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Populate2 ()) "Pgp,(6.&40.)Ptp,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Ps6,(6.&40.)Ps7,(6.&40.)Ps8,(6.&40.)Ps9,(6.&40.)Ps10,(6.&40.)Ps11,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pq6,(6.&40.)Pq5,(6.&40.)Pq4,(6.&40.)Pq3,(6.&40.)Pq2,(6.&40.)Pq1,(6.&40.)Pq0,(6.&40.)Pqra,(6.&40.)Pexb,(6.&8.)PSP,$0.PF,(19.&5.(6.&40.))Pfc,(6.&20.)Pm0,P,(6.&40.)(10.(6.&8.))Pm,P,(6.&40.)(10.(6.&8.))PRI,$0.PR,$0.PRB,$0.PFA,$0.Pc,$0.Pau,$0.Pmu,$0.Pnf,$0.Pr,$0.Plo,$0.Pjs,(37.(6.&40.))PW,(37.(30.$0.$0.))Zcs,$0.(25.R8.)Znw,$0.(:.(15.R7.R8.)R1.)ZFAN,$0.(;.R;.(14.+4.R7.))P,(2.+65?000.R?.)P,(2.(;.R10.+1000.)(1:.VhAR,))P,(5.$0.R10.(;.R11.(14.+80.R=.)))P,(1;.VCS,R12.+1000.)P,(1.(2.+1.R?.)(2.R?.+1?.))P,(2.+10007???9000.R12.)P,(5.$0.R12.(;.R13.+>0000000.))P,(2.(;.R14.(4.+2.+20.))R16.)P,(5.$0.(<.R15.+1000.)=)P,(1.(2.=R13.)(2.R13.R12.))P,(2.R13.+>0000000.)P,(5.$0.(<.R15.+10.)=)P,(2.=R14.)P,(2.R?.(4.+2.+>.))P,(2.(14.+4.(;.R16.R10.))(4.+2.+1=.))P,(1.(3.=R16.)(3.R16.(4.+2.+40.)))P,(5.$>.(44.(6.&40.)R15.)(3=.R12.))P,(1;.VCS,R12.(14.+4.R13.))P,(45.$1=.R22.R13.R17.)P,(1<.$1=.R23.(;.R21.+10.)(1>.$1?.(20.(9.&40.R1;.))(21.$1?.)))P,(1<.$1=.R24.(;.R22.+20.)(1>.$1?.(20.(9.&40.R1>.))(21.$1?.)))P,(1<.$1=.R25.(;.R23.+28.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))P,(1<.$1=.R26.(;.R24.+30.)(1>.$1?.(20.(9.&40.R1?.))(21.$1?.)))P,(1<.$1=.R27.(;.R25.+38.)(1>.$1?.(20.(9.&40.=))(21.$1?.)))P,(1<.$1=.R28.(;.R26.+44.)(1>.$1?.(36.R2=.)(21.$1?.)))P,(49.R29.R2=.R36.R35.R34.R33.R32.R31.R30.R2?.)P,(2<.$1=.R2:.R20.(;.R2>.-40.))P,(2.(1:.VhAR,)R21.)P,(2.R22.(15.R30.+40.))P,(2.R31.(4.+2.+3?.))P,(5.$0.(<.R32.+10.)=)P,(1;.VCS,R25.(15.R33.R25.))P,(2?.(1>.(30.$0.$0.)(31.$0.$0.R26.R34.)(1>.(30.$0.$0.)(31.$0.$0.R21.(;.R21.(14.+4.R22.)))(1>.(30.$0.$0.)(31.$0.$0.(;.R2>.+10.)(;.R2>.+18.))(1>.(30.$0.$0.)(31.$0.$0.(;.R2>.+20.)(;.R2>.+28.))(1>.(30.$0.$0.)(31.$0.$0.(;.R2>.+44.)(;.R2>.+45.))R24.)))))R31.R30.)P,(32.$1=.R32.R31.)P,(22.$1=.R32.)(23.$1=.VAL,VCS,(4:.R37.R56.R55.R4<.R4;.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R36.R35.R31.R24.R2=.R26.R25.R2;.R2<.R29.R27.R34.)(26.(27.(9.&40.+4<<?4.)(9.&40.(;.R37.-40.))R56.R55.R54.R53.R52.(9.&40.R31.)(9.&40.(;.R2;.R25.))(9.&40.R2:.)R51.R50.R4?.R4>.R4=.R4<.R4;.(9.&40.R30.)(9.&40.R25.)(9.&40.(15.R2<.R2=.))(9.&40.R26.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)R36.(9.&40.+4<<?4.)R35.(2:.(6.&40.))R33.(2;.$1=.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra exb SP F fc m0 m RI R RB FA c au mu nf r lo js W cs nw FAN
      R0 R1 HR RICS HC RB0 HFA RB1 RBAL HAU HMU AUAL HNF HNW HTOT HRR LJS FCS HA NF AU M40 MUC M56 EX FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    unfold A_INSTANCE, pop_frame in *.
    pose proof (class_size_range c HC) as [CS1 CS2]. fold cs in CS1, CS2.
    assert (NW0 : 0 <= nw) by (subst nw; apply Z.div_pos; lia).
    assert (NW1 : nw * cs <= mu - au) by (subst nw; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (RB2 : R + 72 <= ACEIL) by (clear - R1 HR HC; lia).
    assert (RCS : crange CS R 72) by (eapply crange_sub; [exact RICS| clear - HR HC; lia| clear - HR HC; lia]).
    lx_hide MU. lx_hide WM. lx_hide HR. lx_c1_norm. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4cd3c; 0x4cd1c] [] 20%N).
    all: subst lxm; repeat match goal with H : ?T, K : ?U |- _ => constr_eq T U; clear K end; lx_unhide.
    - (* [comment removed for export] *)
      clear H9 H10.
      assert (NWZ : nw = 0) by (subst nw; apply Z.div_small; lx_bool_norm; revert LXKT; clear - HAU HMU CS1 CS2; unfold zlow; intros; rewrite !Z.mod_small in LXKT by lia; lia).
      eapply pop_D_tail; try eassumption; try lia.
      rewrite NWZ in *. replace (Z.to_nat 0) with (length js) by lia. cbn. destruct js; [exact HA| cbn in LJS; lia].
    - assert (NWP : 1 <= nw) by (subst nw; apply Z.div_le_lower_bound; [lia|]; lx_bool_norm; revert LXKF; clear - HAU HMU CS1 CS2; unfold zlow; intros; rewrite !Z.mod_small in LXKF by lia; lia).
      clear H9 H10.
      replace (4 * nf + (4 * nw + (RB + 3758096384))) with (FAN + 4 * nw) by (subst FAN; clear -HFA; lia).
      replace (Z_to_bv 64 au) with (Z_to_bv 64 (au + 0 * cs)) at 1 by (f_equal; lia).
      assert (HA0 : u32arr asegs m FAN (firstn (Z.to_nat (nw - 0)) js ++ skipn (Z.to_nat (nw - 0)) (carve_list au cs (Z.to_nat nw)))).
      { rewrite Z.sub_0_r, firstn_all2, skipn_all2, app_nil_r by (rewrite ?carve_list_length; lia). exact HA. }
      clear HA.
      callxA (eapply (pop_carve (Z.to_nat nw) 0) with (W := []) (js := js); try apply munch_refl; try apply wmono_refl; try eassumption;
              clear - NW0 NW1 NWP HNW HAU HMU CS1 CS2 LJS RB0 RB1 RBAL HFA HNF HTOT R1; lia).
      replace (au + 0 * cs) with au by lia. replace (mu + - au) with (mu - au) by (clear; lia).
      eapply pop_D_tail; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Populate2.

End ARUN_1.
