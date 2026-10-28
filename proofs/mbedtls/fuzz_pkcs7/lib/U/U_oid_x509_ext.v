(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsOid.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0069906be5a38780 0 2 0 1 2 1P017e62515e9d32b4 0 2 0 1 66 1P01e8a2365a438ffd 0 2 0 1 1 1P033ce8adc0f21554 0 3 0 1 6 1 64 1P0358471bd17c4450 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P036d9702caf4d7bf 0 3 0 1 6 1 72 1P03d288205771f655 0 2 0 1 70 1P0535dae4a7778595 0 3 0 1 4 1 70 1P062d1c92e0d47031 0 2 0 1 49 1P072b5d4671536ad4 0 2 0 1 65 1P0781ca1df070ecfb 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P0795750449f8d65b 0 2 0 1 63 1P08a390075abebacf 1 1 8 2 0 1 68 1 3 36 1 69 1 70 8P08e6d55c721e2bfd 0 4 0 1 8 1 67 1 68 1P0902e8dab075ff96 0 2 0 1 2 1P0a3eec5a6c0de197 0 3 0 1 6 1 64 1P0a828fbb97c2e1a5 0 4 0 1 10 1 69 1 70 1P0ab920a42c851a7c 0 3 0 1 6 1 64 1P0c1ca54d15165f24 0 2 0 1 1 1P0c3c9a89747af8c5 0 2 0 1 1 1P0caaaf8abff9878e 0 2 0 1 68 1P0dc9bd56db998d59 0 3 0 1 10 1 76 1P0e0746b1d656e94e 0 2 0 1 1 1P0fe110b31c8eb956 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P109a01eea3ba6054 0 2 0 1 74 1P11cb1155951f231d 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P12ce4dfd9bf82d22 0 4 0 8 35 8 68 8 69 8P12e55efb0055c254 0 4 0 1 12 1 71 1 72 1P13546d36d7f3b25c 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P145263142fd56a1e 0 3 0 1 2 1 68 1P1478b698879c6a64 0 2 0 1 59 1P152024cd6c9044a9 0 2 0 1 72 1P15e711fb5c5dce03 0 2 0 1 46 1P15e73d149ba832ab 0 4 0 1 20 1 79 1 80 1P1709aad35c069f92 0 2 0 1 1 1P19e46bbc975b5a77 0 2 0 1 2 1P1b53155e2562c983 0 3 0 1 6 1 64 1P1c44609b6c1429b1 0 2 0 1 59 1P1c59851bc2b02975 0 2 0 1 1 1P1e4bf4dbaed2aadf 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P20e07bba9f1078df 0 3 0 1 2 1 67 1P21f1e32aef3acb29 0 2 0 1 2 1P22179ca2c1f63791 0 4 0 1 14 1 73 1 74 1P22b81e43d8a24015 0 2 0 1 1 1P23bb209dff4583ad 0 4 0 1 5 1 61 1 65 1P23fb442546350e5c 0 3 0 1 12 1 78 1P2429ec9d11e55462 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P24915115f803acc1 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P2523fbb4bf1c248e 0 2 0 1 51 1P25bf4615eb30bf7b 0 4 0 1 18 1 77 1 78 1P268094e65925b72e 0 2 0 1 2 1P27c5e4a8cab0945d 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P282c7f4d56a82daa 0 3 0 1 14 1 80 1P28ed52522d2e0f27 0 4 0 1 5 1 61 1 65 1P29012a4a72feedfa 0 2 0 1 55 1P2c2286bbbd52c9c6 0 2 0 1 47 1P2d67dfea971cc20b 0 2 0 1 58 1P2edf973c78ed2e5c 0 2 0 1 50 1P2eed336f32aa684f 0 2 0 1 76 1P30000b08300c41f4 2 20 1 1 8 3 2 1 30 1 31 1 5 0 2 21 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P30529e1d96ad330d 0 2 0 1 2 1P338e106842fdab09 0 2 0 1 2 1P33e2c05a161a0a57 0 3 0 1 8 1 74 1P34375f2ac7b178d6 0 4 0 1 7 1 66 1 67 1P35b2418bf9e4a05d 0 2 0 1 64 1P3611a1923fd880cd 0 2 0 1 55 1P3645cb5eda6dd2ca 0 2 0 1 58 1P36ae6758b5babb90 0 2 0 1 2 1P373e9b20e2ec469b 0 2 0 1 54 1P3793025f737d866d 2 18 0 6 0 1 3 1 22 1 26 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P389884fce54c97eb 0 2 0 1 1 1P39dc92789c4b36bd 1 1 8 2 63 1 69 1 3 0 1 68 1 70 8P3b8716ed56e146bb 0 2 0 1 1 1P3d4f298db13d6f93 0 2 0 1 64 1P3da26a83f0e11cf0 0 2 0 1 54 1P3e5c355853e15218 0 4 0 1 16 1 75 1 76 1P3ef03bc657f8c29b 0 2 0 1 50 1P3f0d034c35067bf2 2 19 1 1 4 3 2 1 30 1 31 1 5 0 4 21 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16N004efc8049dbdd16N008b9dd4ac44e1fcN00b41d2a3ae6ed70N00d007fa6f648545N00ddaeec66e78c9fN010efdc55776845cN012a79092f4b4d86N0144a84838ac37afN015e1adf0f0af93fN017a494927d1e0d7N01a7929c3fa2aa91N01b117b01bfcabe9N01bb3734910058f4N01c4812310f771c2N0213d44e6b718eddN0223c44e6c7d42f8N024555f61d677413N0291b0c4054add65N02a22a389cceeeb6N02adc49c101c6ce7N02c0417572e961c6N02c89084e796d946N02e9ff5fc34cb427N02ef6ad45dd41d90N0328285d329c4772N033a21001c64ec21N034a79ec39e244c4N042811d136ab6323N04324d2297f27d2aN047d28cb9c814f1bN04d32016402bed3dN04ea7cb1d027d201N0524f3d2ec02f000N0562e8526e8eb1abN059a4d3dc771b90bN059e7032c3eb9be4N05f6d3cd2cff675cN065c2ab71af47670N0691798212f5d239N069890c5b7df1dbfN0698f7a7f3c9d8abN06f23348b7d0d88cN06f67cf65df96480N0700d0da836df8a0N0712ff7b2c420283N0716b335495b2138N07185e594bd7d3a5N079996074e931511N079b5d01e31d1409N07a44805788b677dN080b9efc797538cfN080dbc69e85cbbddN08279037a75f54c6N08771368f4fe0383N08c33d7583d7591aN08c586bf41b20d17N08de1b50b04883d5N08f6d366e4987aecN0905b8c15c6704f7N098c69e4f0f2a18eN09b01c374da789ceN09c113941436809bN0a3af841fe04a379N0a72bfa0d21ab741N0ab64e6b35187725N0ac5b00788f6a9b1N0adfd7d853353fc4N0afea6ea174f76c6N0aff506dec0bb161N0b249c4944901989N0b4c195dde57335aN0b5e4300fac262bbN0b882ea901f8b020N0b898ff8b4682a4cN0bd8c1e73490dfd5N0c2640f4274399ebN0c274a1c3cf4c923N0c40a20eeb381b71N0c451f1d1c99e49fN0c850530dcca6584N0c873df78fba88ddN0c8b5dcd3d21f326N0c91e3f9c0e3dea3N0c94fc8dab2b2a25N0c9c5ff6b0388deeN0d0c47d8bf084f9aN0d26429dede48336N0d2e7f0c62e8f19aN0d39bac7691a4ab4N0d5426943c498ca9N0da489e55cd1d1d9N0dc69ec33f92451dN0dcdb86697809902N0e2290ac58728b7eN0e76594b0709e431N0eed627419f54b59N0ef433e347f1e43fN0f0f3d4196519693N0f158816d2e5417fN0f4b5d333a9ae856N0f56a9b1216a1bf6N0f86317792fc5a8dN0f8f4aa4662a361bN0f9d146c27b9e01fN0fba9d061ce8ab44N0fd00bbe136fa674N101083f7d9a8fc12N10437162f7ec1523N1053e5b34331344fN108cbaef025441f6N10ab0520e2794740N10b5e3f9eb83c76cN10ee751784626eacN110cfacfda98b7b6N112bf8a4c64d3f05N112f95099d2371f8N113b7bf1b71f11c7N1169f96746158c87N11c286e1c10c7fe7N1219cf38e2c53257N1245c37f7e3b6e4dN1249026afec059e4N125b2ffeaff9151cN1268b816b24f99acN12a7569506896666N12a79c0101df57d3N12c80f774bcc69a4N12caa6968c0f50feN12cc178795b362f9N12f4876a71c4ef2dN130b6a010d12420dN133ac6d093a5c10bN139ce347eadd8ea3N139e1ffb90163e54N13c05035382fc73dN13d2284ce8bb9cf0N13f8032aff16e241N147f13cc3f76f62eN153660ab7b1e793dN158a24077e439eccN15a61c8812dd098eN15f34f57fa2d1da3N1604cb343a91928dN163e8ea828347b3dN164f2055140da990N1656aa6b89242b7fN1657bdd6918bf2cdN168b744bc9bc78a0N16e69c9808f3ffdbN170aefba18337ad0N171586ad0abbf059N171794ad116177edN172aaaf4afa384a2N172b30dbbd88a217N17359daff7f5e60dN175dff6f0c325cb5N177cceb5d3b22eaaN17a5daaddfa31409N17acf1770acdc0b8N17ae872f90e5310eN17c52f5c06e517dfN17c99a961f1cd567N17d7ccb7c1d2c0a2N17e9493d4bd128b5N17ec1bee416b74c0N180686f333ab9ec6N181c22404ce97f20N1823f05796f9a050N1828b5ae8b138bc9N183aeb280b441bf7N185b274d152dd132N18636a9795bcf4daN187270d7e0cf3c40N18828f195eacd2edN188cc39e093dacd9N18bad01cf6da7ab0N18f538c2343f407aN1915f360be6a2e59N191ba71a59db9d02N1953517ec22a22e0N195fa09a13b5cb9fN1971f4f71220fe25N1972425f5d27f7b8N198a0f550265e58aN19c609aae370d0a9N19cabbd251c04479N19cb3b5293e21692N19d3d5c696282dc6N19d6687a7022b988N1a0326b52233b8a4N1a170de7cd3937c1N1a187832ff18e962N1a455c822a59af67N1a728f5b2546fb18N1a7c776b2cfc47cbN1a96d2f6950e4434N1ac89449678ef16dN1aeb270cf5e90784N1b12ead7d1eb3083N1b2847184f852ca9N1b2870ad2ffcdb19N1b2a1eecb13599dcN1b9d6c06598e3d12N1b9f203ac0024a27N1bc0a8fdb15b289aN1bed51455d0e2f16N1c62d5c913061d62N1d22876a56c57036N1d31a035cc35056cN1d476b908c0232c6N1d47bcfe94db74e6N1d4c33d6a6c73560N1d67b6b916a66894N1d6e42ee4d83e623N1dc26f041a477ec8N1dda8e56f0199f22N1de4808b29a4857fN1e1ab3f761710f3dN1e26975192cd52faN1e454243d19f0836N1e4a4d2ae365b1e1N1e5c656f541cbbe8N1eb953f33ddebdbeN1ec3c6463c52f948N1ed5df8e03af8791N1efda0d19a93d8b8N1f2e2f570d154c0bN1f416dfd5d8e3657N1fad00794c68bbbaN1fb0e9ac37268d77N1fbb58ca0c4885aeN1fccdb0c75d0ad79N1fe7143042ab2607N200afe73bc6bf748N204255718784dd54N204c707127b5f73eN2100ba13999e9284N213cbeb28ab4227bN213ce3e3a4110242N2155643ed195c508N2165a439f1c953f0N21664ed193a9d9b7N21a1b66085637c8bN21b73755e364e981N21cb5dcd9aad6468N21d8dc7564e15fd8N2246774ed2802c24N224df300f4cc2178N22d300fcabfbbf6fN2306bbc6bda2acfeN231a5259de806de9N233aa664bf02c741N236c246bf143c88aN23793f1789ffa398N23d1bd39a7b07e98N245310a75259919aN24630d3470d81e44N24882d0e86b6be38N24d43a5f676250b1N25022acae4344f17N2508a25cd43e8c57N2522dadd6d9573ffN25293a8b1f6e6677N254cdaaa50f7bc66N25520fdcce039350N2557905c595650daN2590561707db83c3N2598e2a7e278da52N25b45237f98b5cf1N25ca92216be97a46N25df0556670b8abdN25f0fb14049decadN25f37bbc96cb7f55N262ef27fc1553d0dN263af1aee2016531N264635ae8f39393bN2662742c03a2863dN267e430284bf9d9eN267f73e0ef18230dN268615fd597847d6N26a70258325278cdN27154f217fdf6e6bN2717b55f4c82da70N27c4c21065a660dbN27d99853ebed5a88N2834aa65b4be1fb0N2843d52fd74bea46N28b78e0c2c264f42N28f29df06b0fd36aN2905d3f77e8d3992N292457fb15ee602cN2997100ad95951e4N29b5438a79c7a259N29cf06eb74e555c4N2a23d76c5a5c63adN2a316481af1e3342N2a328da7ab5632c6N2a343e332b08d147N2a38fc82da59bef2N2a3e29fe5d5a1c52N2a4cffdbf2193314N2ab4263923b4e1eaN2ac3828280f5a9feN2ae44edd5a64b669N2aee09ca965af479N2b01a9a1ca0cf175N2b16c81e7aca1166N2b1c3e37698cdff9N2b2285e575ba6c10N2b3dad372bc874beN2b671f3859d0d75fN2b7b261d07113b85N2b7deb68aaf61ab7N2b922feb8c13d752N2ba23b779c6a217cN2bac1bb7f0bf78c7N2badd34fa4df72a8N2bd601290bdc76c6N2c0a339c5f8e044cN2c0e516c23ccd782N2c237c9926115bf1N2c259d8b9f9b2498N2c64f66b9e3b652fN2cbd2ea2f7adb64aN2d387cabaeeb07deN2d7a56b70763fbfdN2d9e5d72b89f245cN2daa4866029bad3eN2e1dc794f4bfa976N2e1f24b9d730d003N2e312984edc88724N2e5fe640f936f260N2e6f1d68f9a7af88N2ed50dde7aa15f60N2ee01bca346592e5N2ee1f5c0d42c5f40N2ef7ba052242d596N2f74d4e67b1312a5N2fec0aec3af37fb7N3012589a72edb34eN3025c34c314e27beN30470a630b53523dN3049635fb823fd07N30542daf6191de70N30626292bfd757daN308669c32f1efec7N308d61b6761041cfN30977da9672baa53N30b3d9da1e5147e1N30b4e2847d114057N30c4d0abed840bf3N30c693d2e4a46c67N3103419bfa48845eN312d1f2b5b254a76N31369c20a03cb587N318459b6f8ff458bN3195771b2a2ebdd7N31ded4f8578486e3N320012b07dc12786N320ca9bc5ab4c8aeN32143129ba76cf4eN3217bd276e30aa4bN321a137658f20a25N32234a5f5e261f6fN322c3286e8e70c9dN325bee7c42c6286cN3263dcb13c8744d1N326ceb7093469771N3281acf848a21d70N328c10bec71ad79fN32cc181cdc265c98N32d8ddf4e6a3a76cN32e087f2e3bc6feaN32f186fad9d6117bN32f45020672bd0e5N33233c27e71044a8N3327605a5e8815a3N3365d5362837186dN336ddc6e158cc533N338d9a586b94ba13N33a6b087e5b38336N33b341e2ab99a408N33febd58486493f7N3407d1b6c8616973N342bbc5e1c7d60b3N34336056b2697845N34c238a67e6862aaN34df784eff092de8N35091bfa59c6ed52N35136f6b211bba7eN362272c5c8922f2fN36784fa987fe2d5cN3692dd257475e877N36eb361c1c27687cN36ed699e02776a5bN3705b13490562d37N3720dbf377998a9bN374c90d08dc7cebbN374fe6af8e356425N376798479b1586eaN37a87e1e2ddeb74eN380adde43a394ca8N38691ea54b3ba069N3872b76b862484b3N3894182481fc648fN389d20d9e0320ff5N38b7f782be12f4d0N38d2f8966e98ba95N38e5dcbb79f0b2f0N390f8182bd5a3bd4N3948c5114bbf9bf1N395e363204a9409eN396b17b7be07f916N3990108a554943a0N3991e63d702f9fa4N39e9598cb0caf762N3a2201b1991913ceN3a886a064a984afeN3a8d40ba72c49e16N3aaedfd0dbe0ea01N3af0bcedbb95d270N3b172a7ecdb6327eN3b22dbf065ea54ceN3b2e6a2cf00f4821N3b9c7c6e04a7d7ecN3ba769fd110d3a5eN3bcf8e20f28de8c1N3c180e56d4c2d31eN3c308037ebc3960dN3c708fc20544744dN3ca667c6c7d54627N3ca75b928dda1f05N3cc648d5aea6c271N3cef77cf9fbdee45N3d0673a0d38329d1N3d4da66b258a7e92N3d4fa2caad7d961bN3d61ec954cddfb21N3d887004c030d156N3dcd8c2ff5a32ec0N3e11bc1e1d9d2681N3e290446a6e9e5a4N3e349272e3d0ced7N3e3a7735b0e74edbN3e3ddc8c55e4958fN3e593b71a94b787eN3e80a816662f57c1N3e87430bc5f228faN3eb28df5423bf153N3f2a31a6294cdce9N3f66d695475546feN3f73fc269007420fN3f74809495770224N3f7d57ba7cb237adN3fe5480edcd8a60c"%lxh.
Ltac2 gd_tbl_P_oid_x509_ext () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.U.U_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.U_oid.oid_lookup1_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Walk.tbl_offsets"; "U_OID_X509_EXT_TBL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.U.U_oid.oid_lookup1_stmt"; "U_OID_GET_X509_EXT_TYPE"].


Definition U_OID_GET_X509_EXT_TYPE : Z := 0x25a4c.
Definition U_OID_X509_EXT_TBL : Z := 0x485a8.
Notation OID_X509_EXT_TBLN := 320 (only parsing).
Notation OID_X509_EXT_STACK := 48 (only parsing).

Definition U_oid_x509_ext_tbl_bytes : list byte :=
  Eval vm_compute in match image_bytes usegs 0x485a8 320 with Some bs => bs | None => [] end.

(* [comment removed for export] *)
Definition oidc (A : Z) (n : nat) : list byte :=
  match image_bytes usegs A n with Some bs => bs | None => [] end.

Lemma const_at_sub : forall L A n a k, const_at L A n -> A <= a -> a + k <= A + n -> const_at L a k.
Proof. intros L A n a k (H1 & H2 & H3) Ha Hk. split; [lia|]. split; [lia|]. intros x Hx. apply H3. lia. Qed.

Definition tbl_offsets : list Z := [0; 40; 80; 120; 160; 200; 240; 280].

Ltac subst_w := repeat match goal with H : ?x = Z_to_bv 64 _ |- _ => is_var x; subst x end.

(* [comment removed for export] *)
Ltac pclean :=
  repeat match goal with
         | H : _ mod 18446744073709551616 <> 0 |- _ => clear H
         | H : _ mod 18446744073709551616 = 0 |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : -255 <= _ <= 255 |- _ => clear H
         end.

Ltac solve_in := lazymatch goal with |- In _ _ => cbn; repeat (first [ left; reflexivity | right ]) end.

Ltac ro_const A n RO :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    let bs := eval vm_compute in (match image_bytes sg A n with Some bs => bs | None => [] end) in
    match goal with MI : mem_inv sg mx |- _ =>
      pose proof (ro_image_bytes_at sg mx A bs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
  end.


Ltac flia := first [clear_disj; lia | lia].
Ltac kdead :=
  exfalso;
  repeat match goal with H : context [Z.eqb ?a ?b] |- _ => revert H end;
  repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
  cbn; intros; first [ discriminate | lia ].
Ltac oid_tbl_facts L EXT sp m SOK CA ACL SLO DHI OD STK tbl n :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
  lazymatch goal with Hm : munch ?W1 ?mq mx |- _ =>
    let MUW := fresh "MUW" in
    assert (MUW : munch [(EXT, EXT + 4); (bv_unsigned sp - STK, bv_unsigned sp)] m mx)
      by (eapply munch_weaken; [| exact Hm]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia);
    let SO := fresh "SOKx" in
    pose proof (statics_ok_munch usegs L _ _ _ SOK MUW ltac:(intros a Ha NW; clear -Ha ACL SLO DHI OD; cbn; lia)) as SO;
    let rec go i :=
      lazymatch eval vm_compute in (i <? n) with
      | true =>
          let a := eval vm_compute in (tbl + 40 * i + 32) in
          let bs := eval vm_compute in (oidc a 4) in
          let H := fresh "TB" in
          pose proof (statics_ok_cells usegs L mx a bs SO
                        ltac:(eapply const_at_sub; [exact CA | vm_compute; intro; discriminate | vm_compute; intro; discriminate])
                        ltac:(vm_compute; reflexivity)) as H;
          cbn [length] in H;
          let i' := eval vm_compute in (i + 1) in go i'
      | false => idtac
      end in
    go 0
  end end.
(* [comment removed for export] *)
Ltac ro_const' A0 n0 RO :=
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
    let cbs := eval vm_compute in (match image_bytes sg A0 n0 with Some cbs => cbs | None => [] end) in
    match goal with MI : mem_inv sg mx |- _ =>
      pose proof (ro_image_bytes_at sg mx A0 cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO;
      let nz := eval vm_compute in (Z.of_nat n0) in let ROL := fresh "ROL" in assert (ROL : Z.of_nat (length cbs) = nz) by reflexivity end
  end.

Lemma U_oid_get_x509_ext_type_spec : ltac2:(CDefT.buildp (gd_tbl_P_oid_x509_ext ()) "PL,$21.(22.$7.R1.$23.$20.+140.+30.)")
(* [comment removed for export] *).
Proof.
  intros L. unfold oid_lookup1_stmt, U_OID_GET_X509_EXT_TYPE.
  intros until xs. intros HOID HXS HLEN HEXT D1 D2 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI SOK CA DHI OD -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HEXT) as EXTB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in EXTB.
  change (Z.of_nat 4) with 4 in EXTB.
  pose proof (rw_cells_bound _ _ _ _ HOID) as OIDB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in OIDB.
  change (Z.of_nat 24) with 24 in OIDB.
  pose proof (bytes_at_bound _ _ _ _ HXS) as PB. rewrite HLEN in PB.
  unfold buf_cells in HOID.
  assert (LEN0 : 0 <= LEN) by lia.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  assert (LXSUMS : forall AL, Forall (summary_ok usegs AL) [SUM_bcmpCP 0x46940])
    by (intros AL; repeat constructor; apply sum_bcmpCP_ok; exact U_bcmp_spec).
  lx_run_tac (PLANS [0x25a78] [] 40%N (@nil summary)); lx_tree.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  lazymatch goal with Hi : mem_inv _ m1 |- _ => rename Hi into MI1 end. clear MI.
  ro_const' 0x10519 3%nat RO1. ro_const' 0x106d8 3%nat RO2. ro_const' 0x106dc 3%nat RO3. ro_const' 0x106ff 9%nat RO4. ro_const' 0x10709 3%nat RO5. ro_const' 0x1070d 3%nat RO6. ro_const' 0x10783 3%nat RO7. ro_const' 0x10865 3%nat RO8.
  oid_tbl_facts L EXT sp m SOK CA ACL SLO DHI OD 48 U_OID_X509_EXT_TBL 8.
  lx_run_tac (PLANS [0x25c2c] [] 400%N [SUM_bcmpCP 0x46940]); lx_tree.
  all: first [ lxp_at 154668; kdead | lxp_ret ].
Qed.
