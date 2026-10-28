(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_len LxConv_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0044132ea70917dc 0 3 0 1 4 1 27 1P0056fc0cfb11e021 0 4 0 1 26 1 42 1 43 1P0069063d3b23ecc8 0 2 0 1 26 1P00cf2fe35c8d36de 0 2 0 1 2 1P01060305cb28ce9f 0 4 0 1 1 1 19 1 21 1P0188810c43bf9fe8 0 2 0 1 2 1P025f707949027749 0 3 0 1 17 1 24 1P02f1fb31f840288a 0 3 0 1 16 1 17 1P032c70b8ba3fc268 0 3 0 1 7 1 30 1P0410e0450ee1e889 0 4 0 1 15 1 16 1 22 1P04a863dff814f2ba 0 2 0 1 26 1P05819f3a12650b97 0 2 0 1 1 1P05a0dbfae1775bbe 0 2 0 1 39 1P05c0847943551956 0 3 0 1 15 1 22 1P05e42fb1f50811ec 0 2 0 1 21 1P05f35a7ae6b6d789 0 2 0 1 1 1P05ffd76860c43b2d 0 2 0 1 29 1P06f096c8ad890a34 0 3 0 1 22 1 26 1P07b4f3200960a530 0 2 0 1 23 1P0892e1fc3dda90a4 0 4 0 1 13 1 14 1 20 1P08a254247af22d00 0 4 0 1 18 1 21 1 25 1P08c98e342dbc6164 0 4 0 1 16 1 24 1 25 1P08fc90a6d26f7804 0 4 0 1 25 1 39 1 40 1P0906a2baa42b6668 0 3 0 1 17 1 21 1P093948e4127ae3e5 0 4 0 1 26 1 42 1 43 1P09778ad205323377 0 3 0 1 20 1 24 1P09c5fa8c5cdb9f34 0 2 0 1 31 1P0a71e395ad40b7c4 0 6 0 1 15 1 16 1 17 1 22 1 24 1P0ac4faa6c2802b66 0 4 0 1 21 1 33 1 34 1P0b36def7a34aeb95 0 2 0 1 29 1P0b47b3230b4e25d1 0 2 0 1 14 1P0b69fb343917a41b 0 5 0 1 27 1 28 1 29 1 31 1P0bcecf86c78ce781 0 4 0 1 15 1 23 1 24 1P0c1af095490e2b5c 0 2 0 1 1 1P0c779d1258c828be 0 4 0 1 18 1 28 1 29 1P0cf5a47e4ff5c5bd 0 2 0 1 2 1P0d33ab54d14e9ad8 0 2 0 1 31 1P0d400d121a5c4565 0 2 0 1 2 1P0d520938bfdfeeb6 0 2 0 1 2 1P0dbc1f5efbe60f8a 0 2 0 1 1 1P0dea94018627d294 0 2 0 1 15 1P0dfcc9c3fc904ef0 0 2 0 1 15 1P0e59ffbc08af1f03 0 3 0 1 15 1 22 1P0ebf2dee776e7365 0 3 0 1 25 1 29 1P0ef81c9332d7cff2 0 4 0 8 13 8 30 8 31 8P0fc84d075c0d1032 0 3 0 1 1 1 24 1P0fd09cc48ad1b538 0 4 0 8 23 8 40 8 41 8P10ab622182591882 0 2 0 1 2 1P11d9076dee840e9a 0 3 0 1 6 1 29 1P11db33cfdb3fd3a3 0 4 0 1 16 1 24 1 25 1P124daa274d37e235 0 2 0 1 36 1P12682212eb1e01d7 0 4 0 1 15 1 23 1 24 1P12a632b69c68a0cb 0 4 0 1 1 1 18 1 19 1P140fddfe7d8c3b3d 0 2 0 1 15 1P14eb260c624b4da5 0 2 0 1 1 1P15ef612330f15784 0 2 0 1 2 1P164721f38aff37d5 0 3 0 1 18 1 25 1P16c3abef2cad19b7 0 2 0 1 1 1P180b876622997444 0 4 0 1 21 1 33 1 34 1P18a41b668f4284ff 0 6 0 1 18 1 21 1 22 1 23 1 25 1P197a5492a1934da0 0 2 0 1 21 1P1a000bb48829db74 0 2 0 1 15 1P1a16e0b55e5b5427 0 4 0 1 27 1 41 1 42 1P1b2467fb9f04963a 0 2 0 1 24 1P1c212f702e5984a7 0 4 0 8 10 8 23 8 24 8P1c9da0be1099cf86 0 4 0 1 27 1 41 1 42 1P1ce82c3d51fba330 1 1 8 2 0 1 42 1 3 24 1 43 1 44 8P1d35e11764cf908c 0 2 0 1 19 1P1e90dcba000b8782 0 4 0 1 18 1 28 1 29 1P1f33407e978ca604 1 1 8 2 0 1 30 1 3 14 1 31 1 32 8P1f789590acb70339 0 2 0 1 2 1P209082d875cbda70 0 5 0 1 21 1 22 1 23 1 25 1P2270e0df6f296e12 1 1 8 2 0 1 40 1 3 24 1 41 1 42 8P22c632a001ee99bb 0 3 0 1 1 1 19 1P2363ce89f8bea98a 0 4 0 1 16 1 17 1 23 1P2364b7fb9c2f2c7c 0 5 0 1 26 1 27 1 28 1 30 1P23e1c5d941c9475e 0 2 0 1 2 1P2405ed14bf1552de 0 2 0 1 23 1P241f60e00c19980c 0 2 0 1 32 1P250026ef22a1f293 0 2 0 1 5 1P25235ada00371b14 0 3 0 1 3 1 26 1P252c0ef6d0a6c3ca 0 4 0 1 27 1 41 1 42 1P257f2473be21bc8f 0 2 0 1 1 1P2597c296d17fb9c4 1 1 8 2 0 1 23 1 3 11 1 24 1 25 8P25b3a945db6c5c9a 0 2 0 1 6 1P261c922126992212 0 3 0 1 1 1 24 1P26492a52ba0b3abc 0 3 0 1 4 1 27 1P279fc7bc33406c37 0 2 0 1 14 1P27cb5370f5ecb39d 0 4 0 1 27 1 41 1 42 1P281b0587a739bb81 0 4 0 1 21 1 33 1 34 1P28a65695f01dd240 0 3 0 1 1 1 19 1P28bea6a916c4929a 0 5 0 1 16 1 17 1 18 1 20 1P293935711de7e83f 0 2 0 1 2 1P29cfaa34d11abcba 0 3 0 1 4 1 27 1P2a74b0a11f1c19a6 0 4 0 1 15 1 18 1 22 1P2b19769ce71030bc 0 2 0 1 1 1P2b5821f235f8b845 1 1 8 2 0 1 40 1 3 24 1 41 1 42 8P2b60f5fca736db4c 0 2 0 1 5 1P2bbdf215061ee547 0 4 0 1 21 1 33 1 34 1P2bbf6f2252d60169 0 6 0 1 16 1 17 1 18 1 23 1 25 1P2c1c4e2625e2a461 0 4 0 1 25 1 39 1 40 1P2c4625a00b851e4d 0 2 0 1 29 1P2d579c4f188039a1 0 3 0 1 3 1 21 1P2d62e1aafda75310 0 3 0 1 3 1 26 1P2dd4eb6813032d5d 0 3 0 1 28 1 32 1P2de8763d8096f4ba 0 4 0 1 21 1 33 1 34 1P2e8a5023b52bd43a 0 3 0 1 6 1 29 1P2e8f241e024656a0 0 4 0 1 21 1 33 1 34 1P30134c606af777fe 0 2 0 1 2 1P30dcaafb8d7e5a97 0 3 0 1 4 1 22 1P30e8d3b0a2ec25d8 0 2 0 1 28 1P310d08b13e0982e3 0 2 0 1 1 1P315cd77fc5695e47 0 2 0 1 1 1P31af7f060d38f01d 0 2 0 1 2 1P31e2a6a62892fd5e 0 4 0 1 15 1 16 1 22 1P32965c381a55d46a 0 2 0 1 40 1P330e7168db8193a2 0 2 0 1 14 1P34efbb6e6966b7f6 0 3 0 1 17 1 24 1P35b6b719af37a3e0 0 2 0 1 1 1P3631a7d98afb7762 0 4 0 1 1 1 23 1 24 1P36853dbbe86fe112 0 2 0 1 1 1P36a8095afdcc3006 0 2 0 1 2 1P375c186f3165a901 0 4 0 8 23 8 42 8 43 8P3a79b5bd254e46f4 0 2 0 1 28 1P3ba2ec25684831cd 0 5 0 1 13 1 14 1 19 1 20 1P3bc8877792b754b5 0 2 0 1 1 1P3bca55a8d51d58be 0 2 0 1 1 1P3bd2e17ac79eed0d 0 2 0 1 1 1P3bf21dbdc342938a 0 3 0 1 3 1 21 1P3c6993abfc2466b4 0 2 0 1 2 1P3e27a78ca1128bcd 0 4 0 8 23 8 40 8 41 8P3ebc450fb8128e8b 0 2 0 1 2 1P3f7c747151c230f8 0 4 0 1 13 1 14 1 20 1N000d8af9b2e1dbd4N002af242d6795416N00d8108251879f41N00de08bc37f072b5N0196f45ee3f35bb1N01ceb3faedf8d2cfN01f16523edaf2192N01f8409acba4a7feN0211cb47a7c0d3e8N02803d67aad65dffN02b30e7d388f94afN03041427920cd975N0322b9c76f34d45eN0337156eb0976a1bN034f936b3e3a6cbaN036ac9016f71d8ceN0405fb1e556ce775N04304e950200b86bN04351252a57e5b48N044567534efb05dfN04472a110c3c9d43N045b53ed39198c89N046226aea3100064N04a79e9e5f32e6adN04e2f1262d3686bfN04fb452471ca32a8N051a4312a641c037N052ce2a4a30521c3N060f0c0fef26a420N0633046dbd3a48c9N0670763413888437N06a04059aa657fd9N06c0dcf84fc71101N07185a0dadad169eN07419592195c72c7N076f22e35c8c8726N0788adc763c65c4eN07bfd6b07480967dN0851be913b870564N08717bf6412ac755N08dcbac0df37745aN09227674fdeedac4N094c6b2d34a70434N094ee4ea8c42fdf9N09a729838db3856bN09d281a0143c6107N0a1ef31a0fdda69fN0a3111bf1e70341cN0a48850fa3a16aa6N0a675d15494355e5N0aaf762587fe20e6N0ab081b4fc9a38d8N0acd45452d9f1415N0aef55fb42d3bf5fN0af6efd43b8cbff3N0b0a106756d33b1cN0b0dc640e578b71fN0b2543e8a79d4f84N0bbf791918ff0773N0bc55436c77dfaa3N0bd1edd76909aaaaN0c375897fb5c422dN0c3aabd314a61d4aN0c6453c81edf325cN0cb4bd76e30e553eN0d46cc1b0dc9b23eN0d5efedc025589abN0d63beecdd724e7bN0d95e9a907859fe7N0e042f827cffa216N0e41de3a6add5742N0e59ec114134d285N0ea7be9b7abf528dN0ee03e269aea6844N0f795f1f809b8ddfN0f9cb556b2a1fb4aN0fbd5f8797272010N0fcea55844c64c5dN0fd11ea3a74eaa3dN1003e3a5db8d9930N101307f9ce0d823bN1042f5a63e6e1439N10621576122e5c20N10667e046a4dffa9N10c14aefe7ace405N10e240d18074d34aN110157e059c72b92N1127cd41897c21a3N113857ca1a8b29edN114d53802cddb455N11572c099b205c40N115fb00623bc9cd9N118890f75f093060N11de837ca2c4ebfcN11eddb9bd1d07c06N11f0b951901adf92N12279232a04a2310N1251e9de8b3ba753N125c4269f785e613N12606d7a98eefd4dN1284b7906a4dce52N12bde8d024eca635N136687c2545cb6ebN1389dce163d10f5eN138e7f50ac09f15aN13f6a0ee2fe631c8N143df8440b72dadfN14e2329823886e3eN1505100c8a7f47d7N1655d5a6d941eb26N16ccda0454541619N1721428e6dcb8fa2N17260e6a96c19558N172e96a275b46d82N1738f752adf69444N175545bc5a32309cN17623ee35e2e08daN17a168601329e12bN17a6e30ced05f33eN17cdbbaa32862c42N18a83d230bdab2b2N18aee4d329825740N18cc9b640bb6fefaN1920ae37b9d76e12N194aab228e4db52dN196c8ef6541fea36N196d68f6f8e3690fN198a8193da3e09ecN19a286153edfff76N19b96f70babd99a7N19cc3dea258e4d50N19cf32c9dfd498d8N19d395791eabf27dN19dc1cf71098f34bN1a5fbaccc9fdfa3cN1a9b7f663bde3d1bN1ab4b44ebe4946e7N1b1d160b9d7a8d15N1b2aff4ec2034b94N1b68900faff624d7N1b9b1722a72c53afN1c1e44309b0f0ff1N1c2a07d3f9f395b7N1c4a8e01722eaa40N1c89872a0db26987N1cce005a6f960237N1cda19a84673ec9fN1cffd675cd2a6bcfN1d3b2c7da5ecfef5N1d87616ea5e6ae62N1dbe6038c46a705cN1dbe77717996e5aeN1dc3491543e072b3N1df875c9406629d1N1e808f1362ebfa4bN1e991dec7001e5c9N1eb319691e5222bcN1eb5bfe5fe2331c2N1eba6829319910baN1f32d98a29d19d52N1f6f0e803b32c37aN203ec9968d456b40N20618b20c7a8ac52N209b7a6b07f70132N213e97542c80b653N214898dea036950aN214e76fea19aa63aN21abf123d1a97954N21e94a1adaa0f2f8N21f04118608769e6N224ed23976d0a66fN229918c0846f55d0N22a94347378f5175N22bb6977447d0a67N22d56ca0fc5bf252N22dd172f7380fa88N233d3e3e5a73352fN2378425ed1f35492N23fa06eadd56ca72N241adf12c0bb3d3aN242a0cca355293e1N24706b9163813259N2483c1408654f55cN24a65434424d9963N24a9360c742ba896N24b43ee204bafdbcN24d9b026ee96c56fN2510dd680c3f7627N253ad29f3fb7fcbbN256e9ef4d3b97c94N258753961579eeaeN25f1bd1f9ffa71e8N264176eb503202e1N264fb6e5431d55c0N267742754acfc933N2685423252ce30d1N269e7964ed863e83N2771e85dc97bf908N277e3942123b5917N278b91f5f2ca7b5fN2795433c058d730eN27b96bf84cd585e3N27ed99155d593a85N27efb8b0c4d3136dN27f70d63a470a190N2802ffbf3752d6afN281ea9c6904cea22N28503d38513daa87N288d57bf99f162c5N288f5eedefd050f7N289b228e3b7bd0bdN28afd039492de684N28f3f29ebf388ffeN290a5ec2a2e03822N295d31340ccd25deN297d171ac0a2386eN29881eb81852dc4fN29b016b9ddcab8f6N29d0221c5f2a47e2N2a3d30b95cdd8462N2ad5b26ec485fe57N2b3e67df6f95b694N2b6a0b5846bf412bN2b6f6f04443e83c2N2b7c28ebf7106904N2bcc2c958cec6860N2bce81d9b1a4484dN2bec8e67927df5c6N2c0220fc0cd152ccN2c023cb26986f6a4N2c22b18a9e7d6c3dN2c314da39eb4ec31N2c5564ba9c2dee3eN2c8c8759aa514a4fN2cfe28eb6138a841N2d0e9b72d7e40e7cN2d313fdd1d34bb30N2d40a4a280d71443N2d94b4b139e3a493N2da9a948b4adc5c9N2e302402126bccffN2e9803f0bb7823a2N2ea5b20103202e28N2eea8190e9e02ac0N2f170eb4541a5827N2f17a9a6072c1914N2f532e652be12ac8N2f645fe4c40d5ccdN2fcb5313c387fc45N2fe7cc767d627c90N2ff398617a068fe5N305c07019fd1a8b4N309c605bb4a8c918N30f3e3c6c5530b8fN3123ccee0ddd3f5fN31268ccbdc15ce0dN3148d34dd5bf0db3N3199d2613313cc68N319baaa7d8036bfdN321b450088fff8dcN323f5c522c78a13fN325154f4a7c97300N326f1e5b91546a5cN32c2b42a884829ddN32c45e40ce61543eN32e6a1b1060e2e84N32e70a4340933d3bN332d3fd17ce7913fN33b68db7ff82ce56N340e00ae6158d8b2N34205de5e6fc44abN345171745c8a75ebN34517f12960d363fN3461643a64c9b674N34641a5544826cdcN346a5d4deb03dd19N347c9258c90ccb82N349018a43cb33db0N349dae4363ccc0ddN34b492cdaab616f9N34c83ebffdc43b9aN35505f7295ca53b3N35538dc0708d62abN35665438adfbfc85N3567f8d8a6e1541cN358768d8f05f95f6N35902ec3a0d76be5N359a3e74cf58439eN35a1096041fba587N35ce5420dc772b5eN35da9c4d5ee44a52N361942cd53b455c5N361a1decb6d60ceeN3634322ca5cef912N36987b2d2f2fafd9N36aa060a8e031179N36e70b3a9d247d25N371423ac57cc12bcN377b30a5952fce18N37c3b601de8d6e1eN37fdbcae3faa2d2fN38641d61db7c13b6N387814d69cb5a782N38781b7b2b508de4N38c50e85e87684faN38fc904e52d07087N39012031d738b437N390eb97cbf7799c1N3947782b022a4d8bN396d8b76c0854e19N3987c2487daa899eN39a07f10c2389261N39b481b97acde37eN39fe9552be03181cN3a73804d6683beefN3a90fdc608959303N3a932d443a1a06b8N3ac85c01a621fca4N3ae9e281079a6c67N3b0c0e4f7b5802ccN3b0ca5ccb928aff2N3b265027824176baN3c0640f6199302c0N3c0f28e70d63980dN3c21afb2ab39b71eN3c4bb4f7e86316b4N3c75d3f894a50b22N3cd2742f689569f5N3ce64c8feddd133aN3d2faaaf15cb9395N3d3433cb16c10b6aN3d41079b66599d21N3d709cce6b0b7692N3da4a13fee08f6e8N3debd082af54fd6fN3e3072214c551891N3e407dba30b5ac5eN3e5c809ad5a531a9N3eb620d1551bc688N3ec2e94bc004b644N3f0c90e4615b7bcfN3f891fc00d5dd200N3fd7238925be9897N3fd7d0b710b95cb2N3fd9e8ac34ba827bN3ff78334a466ca57"%lxh.
Ltac2 gd_tbl_A_asn1_get_tag () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Peano.le"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.asn1_get_tag_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"].


Notation GETTAG_STACK := 16 (only parsing).

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP LENP P END BUF lo : Z) (bs : list byte) (tag : Z).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= LENP \/ LENP + 8 <= PP.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : Z.of_nat (length bs) = 0 \/ LENP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= LENP.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis LENB : 0 <= LENP /\ LENP + 8 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : LENP mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < LENP.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SPL : lo <= bv_unsigned sp - 16.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis DS1 : PP + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : LENP + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= LENP.
  Hypothesis DS3 : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_tag ()) "(0.(1.$2.(3.(4.(5.&8.)Vbs,))=)(0.(6.(7.VBUF,(3.(4.(5.&8.)Vbs,)))(8.(9.&40.Vsp,)+10.))(6.(9.&40.Vsp,)VBUF,)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Notation POST := (asn1_get_tag_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP LENP P END lo m).


  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.

  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_tag ()) "Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Plenv,(5.&40.)P,(11.$12.Vm,VPP,(13.$14.(15.(>.&40.VP,))(16.$14.)))P,(11.$12.Vm,VLENP,(13.$14.(15.R2.)(16.$14.)))P,(17.$12.Vm,VBUF,Vbs,)P,(1>.$12.Vm,)P,(25.$12.VAL,Vm,)P,(19.$12.VAL,VCS,Vm,VPP,+8.)P,(19.$12.VAL,VCS,Vm,VLENP,+8.)P,(19.$12.VAL,VCS,Vm,VBUF,(3.(4.(5.&8.)Vbs,)))P,(18.$12.Vm,Vlo,(9.&40.Vsp,))(1?.$12.VAL,VCS,(20.$12.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VLENP,VP,VEND,Vlo,Vm,)(21.(22.Vra,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,(>.&40.VPP,)(>.&40.VEND,)(>.&40.VLENP,)(>.&40.Vtag,)R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)VF,(>.&40.+9990<.)Vfc,(23.(5.&40.))Vm,(24.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros a4 a5 a6 a7 lenv HPP HLEN HBUF MI AB OPP OLEN OBUF ST.
    pose proof (munch_refl [(PP, PP + 8); (LENP, LENP + 8); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof AB as AB0. lx_hide1 AB0.
    lx_run_tac (PLAN [A_ASN1_GET_LEN] [(0x99958, DJoin)] 200%N).
    lx_tree.
    - (* [comment removed for export] *) lx_leaf.
    - (* [comment removed for export] *) lx_leaf.
    - (* [comment removed for export] *)
      lx_unhide. lx_call_prep.
      pose proof (A_asn1_get_len_spec AL IMG) as SP. unfold asn1_get_len_stmtA, A_ASN1_GET_LEN in SP.
      eapply evtA_mono;
        [ lxc_apply (SP CS ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc lxm
                       PP LENP (P + 1) END BUF lo bs lenv);
          try lxc_cells_conv; try lx_arith
        | ].
      clear SP. intros ms' HQ. unfold asn1_get_len_postA in HQ.
      destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & p' & L
                      & -> & MU' & WM' & MI' & -> & Hr & HPP' & HLENP' & Hp' & HL0 & ST').
      unfold asn1_get_tag_postA; cbv beta.
      exists t0', t1', t2', (Z_to_bv 64 r), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', r, p', L.
      split; [reflexivity|].
      split; [replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; lx_munch_join|].
      split; [lx_wmono_join|].
      split; [exact MI'|].
      split; [reflexivity|].
      split; [exact Hr|].
      split; [exact HPP'|].
      split; [exact HLENP'|].
      split; [lia|].
      split; [intros HR0; specialize (HL0 HR0); lia|].
      exact ST'.
  Qed.
End Walk.

Lemma A_asn1_get_tag_spec : forall AL, asan_img_ok AL -> asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
Proof.
  intros AL IMG. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG.
  intros until tag. intros HPP HLEN HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 MI ALWF CSOK AB OPP OLEN OBUF ST SPL SPA SCS DS1 DS2 DS3 -> -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HLEN) as LENB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB, LENB.
  pose proof (proj1 HBUF) as BUF0. pose proof (proj1 ST) as LO0.
  eapply main_walk; try eassumption; try lia.
Qed.
