(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_platform_zeroize A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_asn1_get_alg_A A_asn1_get_len LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0054f16ca2d7c97c 0 2 0 1 2 1P013081e30af5af60 1 1 8 2 42 1 101 1 3 0 1 100 1 102 8P014173f600678eee 0 5 0 1 72 1 89 1 100 1 101 1P01c527ec91ca510a 0 2 0 1 19 1P01cba6db554d664b 1 1 32 3 0 1 102 1 103 1 5 48 1 62 1 101 1 104 1 105 32P02059a956050176e 0 2 0 1 91 1P025134c176d55f1d 1 1 8 3 1 1 102 1 105 1 5 2 1 47 1 103 1 104 1 106 8P0258a065eb14448e 0 4 1 1 2 1 100 1 101 1P02bd0db575da7834 0 2 0 1 93 1P0347ad80daeee705 0 2 0 1 93 1P03616f3719a7c3ec 0 4 0 1 3 1 103 1 104 1P039e910fb19c8b77 0 2 0 1 95 1P040012783cee61e8 0 5 0 1 72 1 89 1 100 1 101 1P04125e38e1142694 0 5 0 1 44 1 72 1 99 1 100 1P043028d3ca885bb0 1 1 32 2 5 1 98 1 3 0 1 99 1 100 32P047a64f7ff45e9b1 0 2 0 1 93 1P04b8699826d7ead3 1 1 32 3 0 1 100 1 101 1 5 46 1 60 1 99 1 102 1 103 32P04e898a4e6586e46 1 1 16 3 0 1 102 1 103 1 4 72 1 101 1 104 1 105 16P0534c958a90d874d 0 4 1 1 3 1 101 1 102 1P06a7986df1cca817 0 5 0 1 43 1 71 1 98 1 99 1P0705dfe5a7d0fb6b 0 2 0 1 1 1P0708367092abe559 0 2 0 1 19 1P072c9dd6b5418180 0 2 0 1 95 1P078bf62d6520ac9c 0 5 0 1 2 1 92 1 102 1 103 1P08590aec41f343a0 0 3 0 1 85 1 86 1P0873892dade54c34 0 4 0 1 3 1 103 1 104 1P0889fdb583adc13b 0 3 0 1 87 1 88 1P08e3751522fd9fd7 0 2 1 1 2 1P08e4d2ff9a6c130e 0 2 0 1 70 1P08f92a7108fe53d2 0 2 0 1 88 1P0914f86cb78e37b5 0 4 1 1 3 1 103 1 104 1P09790436c4b9c5ec 0 3 0 1 7 1 69 1P09e33762148006a0 0 6 0 1 3 1 48 1 74 1 103 1 104 1P09fb0e1e933bb1f9 1 1 8 3 0 1 102 1 105 1 4 2 1 103 1 104 1 106 8P0a593281f609210e 0 6 0 1 2 1 89 1 90 1 104 1 105 1P0aaa698aef9d9d5c 1 1 8 3 0 1 102 1 105 1 4 2 1 103 1 104 1 106 8P0beea62e4f9d0806 1 1 16 3 0 1 102 1 103 1 4 72 1 101 1 104 1 105 16P0c69d294d4c63234 0 2 2 1 4 1P0c88e0d237cbbf8d 1 1 32 3 0 1 99 1 100 1 5 45 1 59 1 98 1 101 1 102 32P0ca388481f89caae 0 3 0 1 85 1 86 1P0cb2a37910c53efe 0 2 2 1 4 1P0cc35ef47b11372f 0 5 0 1 45 1 93 1 100 1 101 1P0cf7fcf80043b6ba 1 1 32 3 0 1 102 1 103 1 5 48 1 62 1 101 1 104 1 105 32P0d855fd307b0d580 0 2 2 1 4 1P0da3b57fd1d82de2 0 5 0 1 44 1 72 1 99 1 100 1P0dee41c29d4dcf6b 0 5 0 1 44 1 92 1 99 1 100 1P0e398fe9524157eb 0 2 0 1 95 1P0f239ad894e9fee6 1 1 32 2 74 1 101 1 3 0 1 100 1 102 32P0ff5e0213e34c884 1 1 32 3 0 1 100 1 101 1 5 46 1 60 1 99 1 102 1 103 32P101bd04ff632b312 1 1 32 3 0 1 101 1 102 1 5 47 1 61 1 100 1 103 1 104 32P109adcc0dbb57c1f 0 4 0 1 1 1 101 1 102 1P10c88e4ea06bde3a 0 4 0 1 70 1 98 1 99 1P115e8f7b315359f5 0 2 0 1 95 1P119dd8a0b8f51e87 0 4 0 1 44 1 100 1 101 1P11b0430a19b0b561 0 5 0 1 72 1 89 1 100 1 101 1P1200f12360e5c31b 0 2 0 1 9 1P128a9ed48bd49029 0 6 1 1 2 1 87 1 88 1 100 1 101 1P1352f2d5d1f3c3c3 0 5 0 1 44 1 88 1 98 1 99 1P135952303da31585 0 5 0 1 2 1 92 1 102 1 103 1P136ca7d17972f51f 0 2 0 1 93 1P136e7b56a03b681f 0 2 0 1 88 1P13dea3a89abe8fd1 1 1 8 3 0 1 100 1 103 1 6 2 2 45 2 71 2 101 2 102 2 104 16P142818a5cb07eca1 1 1 16 2 0 1 100 1 5 14 1 72 1 89 1 101 1 102 16P14c3a3584cec2dea 0 4 0 1 2 1 104 1 105 1P14c7b07c8512f7eb 0 5 0 1 44 1 72 1 99 1 100 1P154e957c8abd3f38 0 5 0 1 43 1 71 1 98 1 99 1P15c0da8aff31e11c 0 2 0 1 11 1P16180c0c1abf0746 1 1 8 3 1 1 103 1 104 1 4 2 1 102 1 105 1 106 8P169c2deea21b6dfb 0 5 0 1 70 1 87 1 98 1 99 1P172a93fdfe163327 0 5 0 1 70 1 87 1 98 1 99 1P17e0f6adbba08847 0 2 0 1 2 1P181a9b67afda3a4d 0 5 0 1 44 1 72 1 99 1 100 1P181f5f064e96f54a 0 2 0 1 123 1P1943bf1d1e75b418 0 2 0 1 70 1P1954b68a6ac5626b 0 5 0 1 45 1 73 1 100 1 101 1P1a318a08619d9de9 1 1 16 3 0 1 100 1 101 1 4 70 1 99 1 102 1 103 16P1aa4d8eaf5029581 0 2 0 1 1 1P1acb5cd772cba9cd 0 2 2 1 4 1P1cd6cb6b8beb12aa 0 3 0 1 87 1 88 1P1cfeeda48fe9d2e0 0 2 0 1 9 1P1e32c29034484feb 0 7 0 1 43 1 69 1 82 1 84 1 98 1 99 1P1e36b38041be7943 1 1 32 3 0 1 100 1 101 1 5 46 1 60 1 99 1 102 1 103 32P1ec99525b1179650 1 1 32 2 0 1 98 1 3 2 1 99 1 100 32P1ee02804877b807f 0 2 0 1 2 1P1ee4c4cd008e5b36 0 4 0 1 44 1 100 1 101 1P1ef72dc678b93107 0 6 0 1 3 1 46 1 72 1 101 1 102 1P1f9bdbd189ed54a8 0 9 0 1 43 1 57 1 69 1 81 1 82 1 84 1 98 1 99 1P200c35f66c78ce21 0 2 0 1 93 1P2091f95c41149a4b 0 2 2 1 4 1P20dc2662e3b54f55 0 4 0 1 1 1 101 1 102 1P20e31fd351052e82 0 2 0 1 95 1P2169fea76b978f37 0 5 0 16 43 16 69 16 98 16 99 16P2228de3795c1fa56 0 2 0 1 19 1P223b23e23b967f80 1 1 8 3 0 1 103 1 104 1 6 2 1 48 1 92 1 102 1 105 1 106 8P2258f5854d2c9ee2 0 7 0 1 45 1 71 1 84 1 86 1 100 1 101 1P225ebde6cdb79bb1 1 1 8 2 44 1 101 1 3 0 1 100 1 102 8P22e9e266bda45c02 0 2 0 1 92 1P2319dfe359452a58 1 1 8 3 0 1 103 1 104 1 6 2 32 48 32 92 32 102 32 105 32 106 256P236595712ed859cf 0 6 0 1 1 1 46 1 72 1 101 1 102 1P236be581a25f0a4f 0 9 0 1 45 1 59 1 71 1 83 1 84 1 86 1 100 1 101 1P243fec05b2be1d2e 0 6 0 1 2 1 87 1 88 1 102 1 103 1P249492aaf26f9808 0 4 0 1 3 1 103 1 104 1P2512bc78a01d94dd 0 2 0 1 10 1P25508106e4e868df 0 6 1 1 2 1 87 1 88 1 100 1 101 1P256ad8b8e3e69a91 1 1 8 3 1 1 103 1 104 1 6 2 1 47 1 73 1 102 1 105 1 106 8P25a3aaaa62711087 0 2 0 1 94 1P25c1d57bc142d7f0 0 5 0 1 44 1 76 1 100 1 101 1P25d35f514003f76e 0 2 0 1 95 1P25f4774db9f00881 0 5 0 1 39 1 95 1 102 1 103 1P268a1fd67ab159d9 0 5 0 1 45 1 93 1 100 1 101 1P26f589c69a8081fb 0 2 0 1 93 1P272a1bfb6f45e695 0 6 0 1 43 1 45 1 64 1 69 1 87 1P2735d40c357a663c 0 7 0 1 43 1 69 1 82 1 84 1 98 1 99 1P28676e65c633b7fb 0 5 0 16 45 16 71 16 100 16 101 16P29adc54bf5a88405 0 5 0 1 46 1 74 1 101 1 102 1P2a2aee041552a6d4 0 2 2 1 4 1P2a373db8ed450ac5 1 1 8 3 1 1 103 1 104 1 6 2 1 47 1 73 1 102 1 105 1 106 8P2a38fa94b14cde6b 0 4 0 1 43 1 98 1 99 1P2a63443461c55b81 0 2 0 1 90 1P2baa660490ea454c 0 5 0 16 46 16 72 16 101 16 102 16P2c85e7741fa005bc 1 1 8 3 0 1 100 1 103 1 6 2 2 45 2 71 2 101 2 102 2 104 16P2c960eef6d04937e 1 1 8 3 0 1 103 1 104 1 6 2 1 48 1 92 1 102 1 105 1 106 8P2cb5c89a61d66d8b 0 2 0 1 20 1P2d52fdff39ded83f 0 2 0 1 123 1P2d88984791166a7f 0 5 0 16 15 16 69 16 98 16 99 16P2e3c647b450d2512 0 4 0 1 3 1 101 1 102 1P2e7b6fcded262b10 0 2 0 1 92 1P2f1160386d4194a1 1 1 32 3 0 1 100 1 101 1 5 46 1 60 1 99 1 102 1 103 32P2f78ba081f57c857 0 2 0 1 93 1P2fc30f9ab10b7a27 0 4 1 1 3 1 103 1 104 1P2fc69ff3c78d1ebb 1 1 32 3 0 1 100 1 103 1 5 46 1 65 1 101 1 102 1 104 32P2fe6af19b7c6f302 0 2 0 1 123 1P300150e9c32cc43c 0 2 0 1 95 1P305f121cf4b0fd4d 0 2 0 1 90 1P3109cf17f5b6fbed 0 2 0 1 70 1P313b9314780d83b0 0 2 1 1 3 1P31c9cf77f9921d15 0 4 1 1 2 1 100 1 101 1P3241bdaacf250ee6 1 1 8 3 0 1 103 1 104 1 6 2 32 48 32 92 32 102 32 105 32 106 256P339827a7e83057a1 0 2 0 1 124 1P33c29e0dd5e0c706 0 2 0 1 95 1P33cbfb77760cabee 0 2 0 1 93 1P33e67bc60bf18e46 0 5 0 1 44 1 88 1 98 1 99 1P3405d35bf077d245 0 5 0 1 70 1 87 1 98 1 99 1P34bcf78dc85ff0f5 0 5 0 1 46 1 90 1 100 1 101 1P3514e6c28403a31a 0 2 0 1 95 1P35570603054fb808 0 4 1 1 2 1 102 1 103 1P3563cf652cf5ae85 0 2 0 1 95 1P35b6c95bc8148fe6 0 4 1 1 3 1 103 1 104 1P35e45075ecd714ab 0 2 0 1 2 1P361aa9ab973898b1 0 6 1 1 2 1 89 1 90 1 102 1 103 1P364029659f92b78e 1 2 16 2 0 1 98 1 16 3 61 1 72 1 99 1 2 100 1 101 1P364ac6f8603ff4b4 0 7 0 1 45 1 71 1 84 1 86 1 100 1 101 1P366df73d3a6f6154 0 4 0 1 44 1 100 1 101 1P3679a986ad9fc397 0 2 0 1 88 1P37576b78a6137dd0 0 5 0 16 44 16 70 16 99 16 100 16P37d37bfe75cedd98 0 2 1 1 3 1P38596d735f0bbc6e 1 1 8 3 1 1 103 1 104 1 4 2 1 102 1 105 1 106 8P38958c1b7ed2b4bb 0 4 1 1 2 1 102 1 103 1P38d36621995c7cb3 0 2 0 1 93 1P38dada97b2c05022 0 2 1 1 2 1P38e6a2d0cfc8bf4f 0 2 0 1 8 1P38fa4d0b98da3ddd 0 2 0 1 95 1P38fa92c5489af4eb 1 1 8 3 1 1 102 1 105 1 5 2 1 47 1 103 1 104 1 106 8P38fd04e7d1c94178 0 2 0 1 93 1P394fdfc04496525a 0 4 0 1 72 1 100 1 101 1P3a61bfba9b27c9f6 0 6 1 1 2 1 89 1 90 1 102 1 103 1P3b601c081f0d69b9 0 4 0 1 2 1 104 1 105 1P3c04231d847c3692 0 4 0 1 43 1 99 1 100 1P3c1a8c47db63a6f1 0 2 0 1 1 1P3c23c9cea7b145dd 1 1 32 3 0 1 100 1 101 1 5 46 1 60 1 99 1 102 1 103 32P3c75277effe67ead 0 2 0 1 93 1P3c7f31009d98fbf3 0 4 0 1 38 1 102 1 103 1P3c857ec417665f7f 0 2 0 1 93 1P3cbab70445f1d5d4 0 5 0 16 17 16 71 16 100 16 101 16P3d06205f66529099 0 5 0 1 45 1 73 1 100 1 101 1P3d2bfea23cb425fd 1 1 16 3 0 1 100 1 101 1 4 70 1 99 1 102 1 103 16P3d6ffd6b4b44d0c6 0 4 1 8 2 8 102 8 103 8P3e960ada19ee9e1c 0 4 1 8 2 8 102 8 103 8P3e991ed249d18f73 0 2 0 1 95 1P3e9fd7403e7d5c4e 0 2 0 1 2 1P3ec94d0e4a4d4df9 0 2 0 1 1 1P3ffbfebe602e4894 0 2 0 1 124 1N000139a9e0f1a40eN001112d998634b88N001672de12441d6cN0019a6cbb86d40e3N001cd59d937e6b48N003e8e9304c993c6N0044a0abd840b379N00d045de9199c14aN012c7c23748fbd92N0134da46d6bd8090N01365d38e4180383N01532686b120805bN01b14a01cabe0ed8N01b29c9f1741ab02N01c71ddc649ca903N01e3b9e6f082640fN01f2f165c4f4d309N02011ae5ed2e7fd1N020fa90639b466dbN021e1f0ec9655e4eN021f72494e418c1aN0267d47b9a38cc01N0280e2d56b7f786bN028f408356e98e6cN02a9aac0b81f3b63N02e7cc590788cea6N03322e86fc2446f0N03426a1181573ba3N03532320d460e861N0354406430126a2bN03849e33ebcff88eN038ef99cb71f3f49N03a5de912c214cc6N04124e00ad686094N044cd1bbbf557e57N047d0d27c8323bd2N04a6aa3816e645b3N04dc3e7cd18722eeN04f3b1a692295616N04fb1a716c2461c1N050b53f78dbb224dN05102571aa6589feN05826b8b58bc46c2N05c2cd6db75310a2N0608f358e8134a73N06392b277c7b5bbeN06501db655f1af8eN06575f45dc879516N06b0283c31ea4edeN06b7c660e8f74bf8N06e65c03afacb8c2N06fb14140aee2e6bN0726bd29ba39d935N0746b81b09f940e8N075fb458bfc5644eN076294f805282a27N077aaa3ef0eff70aN079021e76457e7d8N07a054b3daca5676N07b2f32fd456ae60N07dc6875c27c7d1dN07f5cbe71892d3d3N08337fe6a6854522N0841b75984f5c609N085fe654321bde82N089cb06426e69509N08dd7b30065d0043N08e76967fa71a31cN08fe77baa188d00cN0901221cce9ee3f4N09119c32e8af71c5N0942fc3da7d581a4N0943dec4b066b913N096c64bb5e8b7d43N096d3876259bd234N09706a6d8503fae7N0979576f5fb2ece6N09a4124e69aaafb7N09a8fb5b2f07a80bN09c66ae8449a6aa3N09c851affd0b9b01N09cbeac91d9f93afN0a0985fdaf96446aN0a116c4075c4ab2cN0a568387ed1fbb8eN0a6bc32a16c48483N0a6c51500cf9a92bN0a9b4a694d295096N0ad356e1b2ade92eN0b543e30e1604a01N0b70b1ad2dd5bfdcN0bb19611cce0a99dN0bb46cfd206cbd06N0c215054bce6d94cN0c3a0c07d8a3b123N0c5df5f7e6f7b048N0c6b7b7b2f1d0e3bN0c8b14db2ac36120N0c96e55132b4d4aeN0cc552ebd86059b3N0cc8de42720d82e7N0cdb7d4aea764c7fN0ced34c3b183282bN0d1663cf7d901579N0d291efcfeddc661N0d47caac328800b2N0d667c5e3eccf3efN0db3e682f14423e7N0dca4aefa6e5ab6fN0dfc4f38e511d0c8N0e136aa5531abd7bN0e4754662552e3ccN0e8c367bd6e07a28N0f12619ef11c315fN0f3d89edda3c9335N0f637de406468cbdN0f699d2480de5465N0f6b2d06dd263481N0f8487960a26eb13N0fbb1417e2158704N0fd32c6cce8ac998N0fdb0531b86ffce6N0fedf87acd571c67N101c1efc123ab666N102dbed2630b2d8bN104bb23ff84bb9b3N1058d9dfbfd43272N107e7c8e500796a6N10999fcece9f3442N1127441f6452a68dN113ff4de6154145aN11a7187f4e5e6a07N11c7154c338fb7c1N11db0c4d155409d0N1203694f3411436dN123c1c52be25cf02N12555205d5311a6cN126589123b5e9020N12b02a6f4d37a06bN12b30be9cccfe66aN130c48b7cd87896cN13168d108d01be08N1325e217b40c1325N1370729efe76ba55N13a88ac42338def4N13c13a74b6db5b8eN13de54e554f474b6N13f239458af37dd4N142c242610297536N142d71807b490c25N1437c04d3a1aff17N143bd85dacd37ddcN14b87753e191cb05N14fdb42f237623e7N1515c10f5d9563eaN1527064ad9a4aa8fN152e8b49567af4a2N1533ffaf2d6ecf21N154f4c339a8cada2N158c9b3139b943adN15f9df1152095aeeN164e4e3c6b3a13a0N1689a454819c9ab5N16ae1e861da4f6b2N16b670b54fa0d159N16e0efa5ef7e2c1dN16f83a4a336ef2fbN1706a8e4eaadc4a0N170710a4091865c8N170b875d9e5f4819N171ec3f2dd51bfd3N1752dc8bd7cb0dc0N1755be0d8bc0a9e2N1767a160fd57e7faN17970f7e60f12b87N17a47d27d0af873bN17bf45583b06e60fN180fc7e62e55ac2aN181c5c6e4cc839f4N1821d0d1bff7cb7fN184e56dce7860b17N1851ad68a75ec113N185276a93c19f15eN186164cbff4f65f5N188497765d1213a3N1894a6326efaede1N19127d3ac56b4f8fN193c4f6346db01acN1952e9890137cb17N197cff2d90db661dN19879638287ed65eN19a77af9cdfc9662N19bd5e2262f46761N19c57dad94c3f6fcN1a452c70dd913c17N1a82cd1dee199d6aN1a9e5fdb46806f60N1aa74bf141bd6f27N1ab9da1a9368aeabN1b1710e7fac4992fN1b2bfc7d2b8dd9e0N1ba06ca6b254a09bN1bd40e396ae59c48N1c10e797627cb4c0N1c3dddd506dc52acN1c4bf83d11ae7ea0N1c7c27fde7a8cf64N1c7dd506fe01862aN1cdb60e3f4597067N1ceffcf6526d3703N1d0976e8f6bde672N1d0ecd421eb91cdeN1d2054d1c873fed4N1d5ae72a9cb86afcN1da9b8fdc9d2af45N1dcef5750853ccf9N1e1ebf9a808079d4N1e643ec740cb72baN1e801a964bfeabb5N1e8e48e5519d58a7N1ec0a787266de362N1f03d521b37866afN1fba55d1cf2028cfN1fce0c017360cb7fN1ff21adc5e976da6N202cf0a2ab6cdb3eN210ceb6a6aeb075dN21320fbaf80273cfN21409f6e3683d16bN2141bdbd00aef6e9N217f873612e91efcN21d166c7d6b1cd5dN21e8e3cf144d5f44N220f782bc4e3ea9aN22422943710f720bN225a95c5aaff7020N2264a816b816c8b6N22724aa481e4116eN22b675ea8440909bN230bcacea23a2ca1N2362e15aa8ba07ebN23dd2fbac20feea7N23e701eba1467851N2409ec6e0ec54322N24271d564939f480N245316e36a39b5b6N248e29585d68c451N24a3af4f7850d427N24d29d30a84e22eaN24d9ca541030c8beN24ed1d7dafb30b74N2523aeb49f0f912bN252b7842889bea5cN261f50919e5ec30cN2676220857bab696N267beec4bf9e44b0N269cfa359f110353N26c582f18929a38bN26d65af65a721660N26e3eb22da603ff0N2727e91c461fb363N272ffb30e89222c7N273af724159b98fdN275bd3f1e5f332c6N2764a78803963f66N27653069e79ad7a2N2783aa4f2c5de694N278fe5dfacb65573N27c6dbc999b687fdN27cc1829f83666faN2831b54481bbe30aN2834b6ddc930f54bN28687a32386476b4N28afef6bfb5025a2N28ba8333b20df845N28f61495719d8a58N29462931032f68fcN294ae0ede66a06bbN29547cd0100c247dN2976b661e3b61db8N298eb5426b195ac5N29bf8efecf8c3e8aN29dc3ab9598010bcN2a1f4f3201f4d1d0N2a3cf522567a3879N2a4b885e7fd44f02N2a57a7952dde41cbN2a64e881ccca0cf4N2a762c91186b6e48N2a92847bc3cc292aN2b3bb110cb3d804bN2b5a6ec8f66fc8abN2b5f28d53eaff19aN2b60249a0618b39eN2b6e189494596faeN2b714698c383dde2N2b7f4808470e2632N2bc3eb6523c2b6b5N2bc66976a35a151aN2be1039a785fdabaN2bfb07b065a8d7fbN2c01f7f6b700a00cN2c1fe03883e144a2N2c2c0e6d3497373cN2c8d4ec3c7d6991bN2c8eaf66925d3841N2cbce47bd8759ebeN2cd233d8ae7b767fN2d17bfb28b3f8618N2d5dda477bcc5939N2d8161b392ace1a7N2d88ff4f7e5596d6N2dcaca4a4eaa7f21N2e96dd95d9d28c0cN2ea3ee23dc75e58eN2ec0880dc29d5b89N2ecf34ad53242984N2f16e130805f5bb1N2f1a23f877e943a6N2f1b30f8a9f8c6d8N2f307a9a81388042N2f387ff9f8e65b46N2f5db5a596ebfa5dN2fc9355795fe1a3bN300ca18a19e8a826N30177618173b7183N3031b262c1a55ddeN30458e7407bff3d1N30570fe36c199276N306515817e24fe82N309ac961f3630306N30ee044f3468b84eN30fb789fb4ca34d7N31274f7bfbaa22b6N314f90a1635f5fceN31863bc6eb1c9096N3197e6bd8dd0e8d5N31a0b44efc15a291N31b2be75dc29c015N31c8c7900aef73e1N3237c8d500b9db92N324c551e9406e0caN32501ab447c28c31N328610881d2f4619N32c92dbd05c7fb92N3308d07358571916N331def96f0c992ecN335b1c9b293c6045N33837e8dbf619deeN338812631ba1ac41N33ae0a13196e6d87N33c61c6be8b3d484N33d891432679b1d8N33de32aa99140630N33e17fb8ec164cc4N3419a8511e648bd6N342a2e0a6f44060aN347a07b29659c3a7N34a2b818198107b4N34c3828a56046aabN34f82583ef98797aN35219a20db7325d4N35369cf7b809bd88N3536b5a5bcf9732fN354bc1df8894a729N3577a82330da8670N358154733155763eN3581f44bcd642304N35ae846ace0fad78N35b1456f766dcad2N35b836665dcb4a1aN35fefaf30420ce0bN3607ac1061f9df23N36555bb96b5d2ba4N3672d7d8c5e2504dN367bd4c215e0f1c5N3680f637057d9697N3687843eebf046aaN36a283e1f874b21cN3710cae2ef70da2dN372e2afb4250f158N375935d4e457b468N376c6bc5265ce072N377442ecc19b17f1N37c76a74b0357d67N37d75af6b3bb1c0aN3835b57a5815d135N386f24316a177da0N389eb990f0cb5cb2N38a31f2f50cfd45aN38a62649c1ded3bfN38cd250c5ab5d465N38e4cd0f77d42836N38fddae9e90586b8N395c658517259d2aN396a8d2c1f79e08eN398642cbabfded59N39d8b4a1dc4a097dN39fcb1c7cfb1ceb8N39fecfdc2d3f7bd2N3a3130000af0979bN3a3b4561ddaec09bN3a844a0299bf904aN3ac0ce986e07f0a9N3ad6a0493531fa04N3ad72281d41a30daN3adc90174057153fN3af884d98fda5e77N3b06616dce231130N3b0a4142d975a1baN3b49a802f174688cN3b671489780bfd94N3bce50ea5ba17e26N3bd9366f4ecb4b89N3bfb488ee1eaa685N3bfeaf68fe9dacf7N3c03d712100e664dN3c044789dc2d193fN3c674434244b65dcN3c676009107cf3ccN3c7e5ea1514bf41fN3c80188631b8fed6N3c8bd88399400df8N3c8d69130f6d2969N3cb644d40fcb6d3eN3d29464e1c6b81ccN3d3c73b697093123N3d46c22267f7ca04N3d5b4ef3c3f71726N3d7373c474c910e6N3da88339f5848e83N3db7771cfb8cae30N3dbb7fb53df79768N3e1b4588c63fae56N3e2a44c7cbbaac0cN3e3b5de09d9cd40bN3e405ea3718d71c2N3e8cd82d1fb0674fN3ee7121fd4d648a9N3ef9e7b976c95e81N3f032ef8b61eb90dN3f0435ef74f50789N3f05b8440f86caabN3f5a6e35986bab2bN3f72cf2b28da7db3N3f9d1ff3b4b3c611N3fab4c1515b52d8fN3fc9100c87a5ef98"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_asn1_get_alg_null_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "ASN1_GET_ALG_NULL_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "asn1_get_alg_null_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wlow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "Walk.PATH"].


Definition A_ASN1_GET_ALG_NULL : Z := 0x09ad70.   (* [comment removed for export] *)
Definition A_SMALLOC_1 : Z := 0x5306c.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_AMEMSET : Z := 0x68258.              (* [comment removed for export] *) (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_GET_ALG_NULL_STACK_A : Z := 4208.

Definition asn1_get_alg_null_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP ALG P END BUF lo slo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null_A ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.O20.O1?.O1>.)Lh',(4.O20.O1?.O1>.)(1.$5.Lr,$5.(1.$5.Lp',$5.(1.(2.&40.)Latag,(2.&40.)(1.(2.&40.)Lapad,(2.&40.)(1.(2.&40.)Lalen,(2.&40.)(1.(2.&40.)Lapw,(2.&40.)(6.(7.$0.R18.(8.(9.O1:.O19.O18.O17.R17.R16.R15.O16.O15.R14.R13.R12.R11.R10.R?.R>.R=.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R<.R;.R:.R9.)O:.(:.O1:.)O9.(;.(2.&40.))R8.(<.O20.)))(6.(=.O20.O1?.O1>.R7.O1<.O1;.R8.)(6.(7.P,$5.Sp(>.O20.O1?.O1>.R7.)(>.O20.O1?.O1>.O1=.))(6.(7.$5.(?.O20.O1?.O1>.R7.)(?.O20.O1?.O1>.O1=.))(6.(7.$5.(10.O20.O1?.O1>.R7.)(10.O20.O1?.O1>.O1=.))(6.(7.$5.(11.O20.O1?.O1>.R7.)(11.O20.O1?.O1>.O1=.))(6.(7.$5.(12.O20.O1?.O1>.R7.)(12.O20.O1?.O1>.O1=.))(6.(7.$5.(13.O20.O1?.O1>.R7.)(13.O20.O1?.O1>.O1=.))(6.Pmo,$14.(15.(16.O20.O1?.O1>.R8.R1.)(16.O20.O1?.O1>.O1=.R1.))(6.(17.O20.O1?.O1<.O1;.(18.&40.O19.)(18.&40.O19.)(10.O20.O1?.O1>.O1=.)(19.(1:.$5.$5.)(1;.$5.$5.O8.(1<.O8.+8.))(19.(1:.$5.$5.)(1;.$5.$5.O7.(1<.O7.+18.))(1=.(1:.$5.$5.))))O1.R8.)(6.(1>.O20.R8.)(6.(1?.O20.R8.O3.(18.&40.O19.))(6.(20.O20.(21.O1?.)R8.O2.(18.&40.O19.))(6.(7.(2.&40.)R14.(22.&40.R6.))(6.(6.(23.-7?.R6.)(24.R6.=))(6.(25.O20.R8.O8.(19.$26.(27.(22.&40.R5.))(1=.$26.)))(6.(25.O20.R8.O7.(19.$26.(28.R4.)(19.$26.(28.R3.)(19.$26.(27.R2.)(19.$26.(27.R1.)(1=.$26.))))))(6.(6.(24.O6.R5.)(24.R5.O5.))P,(7.$5.R6.=)(1.$5.Lap,$5.(6.(7.(2.&40.)R3.(22.&40.R1.))(6.(24.O4.R1.)(24.(1<.R1.(18.&40.R4.))R7.)))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition asn1_get_alg_null_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null_A ()) "Ph,(4.O4.O3.O2.)PLB,(29.$2:.)PLF,(29.$2:.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(2;.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$5.PALG,$5.PP,$5.PEND,$5.PBUF,$5.Plo,$5.Pslo,$5.Pbs,(29.(2.&8.))Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)P,(=.O4.O3.O2.R31.R30.R2?.R=.)P,(2<.(2=.$2:.R30.)#200.)P,(25.O4.R?.R>.(19.$26.(27.(22.&40.R<.))(1=.$26.)))P,(25.O4.R10.R>.(19.$26.(28.R7.)(19.$26.(28.R6.)(19.$26.(27.R5.)(19.$26.(27.R4.)(1=.$26.))))))P,(2>.O4.R11.R<.R9.)P,(24.R=.R?.)P,(24.R10.R?.)P,(24.R10.(1<.R?.(2?.(2=.(2.&8.)R<.))))P,(23.(1<.R10.(2?.(2=.(2.&8.)R=.)))(30.+2.+3?.))P,(31.(24.(1<.R15.+8.)R14.)(24.(1<.R14.+18.)R15.))P,(31.(7.$5.(2?.(2=.(2.&8.)R?.))=)(31.(24.(1<.R16.+8.)R12.)(24.(1<.R12.(2?.(2=.(2.&8.)R?.)))R16.)))P,(31.(7.$5.(2?.(2=.(2.&8.)R10.))=)(31.(24.(1<.R16.+18.)R13.)(24.(1<.R13.(2?.(2=.(2.&8.)R10.)))R16.)))P,(7.$5.(32.R18.+8.)=)P,(7.$5.(32.R18.+8.)=)P,(6.(23.=R1:.)(24.(1<.R1:.+8.)(30.+2.+40.)))P,(6.(23.=R1:.)(24.(1<.R1:.+18.)(30.+2.+40.)))P,(23.=R18.)P,(1?.O4.R1>.R18.(18.&40.R3>.))P,(20.O4.(21.O3.)R1?.R18.(18.&40.R3?.))P,(24.R1:.(33.(18.&40.R40.)$34.))P,(24.R1;.(33.(33.(18.&40.R41.)+130.)(35.O3.)))P,(24.R1<.(33.(33.(18.&40.R42.)+70.)(36.O3.)))P,(24.=(35.O3.))P,(24.=(36.O3.))P,(24.(37.O3.)R1>.)P,(24.R1?.R20.)P,(7.$5.(32.(18.&40.R47.)+10.)=)P,(24.(18.&40.R48.)(?.O4.O3.O2.R4<.))P,(24.(18.&40.R49.)(30.+2.+2?.))P,(31.(24.(1<.R29.+8.)R24.)(24.(18.&40.R4:.)R29.))P,(31.(24.(1<.R29.+18.)R25.)(24.(18.&40.R4;.)R29.))P,(31.(7.$5.(2?.(2=.(2.&8.)R24.))=)(31.(24.(1<.R27.(2?.(2=.(2.&8.)R24.)))R26.)(24.(18.&40.R4<.)R27.)))P,(38.(39.O3.)(3:.$2:.R50.(3;.R4?.))R27.R2<.+8.)P,(38.(39.O3.)(3:.$2:.R51.(3;.R50.))R28.R2<.+18.)P,(38.(39.O3.)(3:.$2:.R52.(3;.R51.))R29.R2:.(2?.(2=.(2.&8.)R27.)))P,(3<.(39.O3.)(3:.$2:.R53.(3;.R52.))R2:.(?.O4.O3.O2.R54.)R2?.+8.)P,(3<.(39.O3.)(3:.$2:.R54.(3;.R53.))R2;.(?.O4.O3.O2.R55.)R2?.+18.)P,(1>.O4.R32.)P,(7.(2.&40.)R51.(22.&40.(3=.O3.)))P,(3>.O4.(21.O3.)(>.O4.O3.O2.R58.)R34.R33.+8.)P,(3>.O4.(21.O3.)(>.O4.O3.O2.R59.)R35.R33.+18.)P,(3>.O4.(21.O3.)(>.O4.O3.O2.R5:.)R36.R31.(2?.(2=.(2.&8.)R2>.)))P,(7.(2.&40.)R4?.(22.&40.R36.))P,(7.(2.&40.)R4?.(22.&40.R34.))P,(7.(2.&40.)R4?.(22.&40.R37.))(3?.O4.(21.O3.)(>.O4.O3.O2.R5>.)(40.O4.O3.O2.R5>.R5=.R5<.R5;.R5:.R59.R58.R54.R53.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R3<.R3;.R39.R38.R37.R36.R35.R34.R33.R3:.)(8.(9.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.)R3<.(22.&40.O1.)R3;.(;.(2.&40.))R3:.(<.O4.)))")
(* [comment removed for export] *).

Lemma zcells_cell_at : forall n i, (i < n)%nat -> cell_at (zcells n) i = Some (C1 (Z_to_bv 8 0)).
Proof.
  induction n as [|n IH]; intros i Hi; [lia|]. cbn [zcells cell_at csize].
  destruct i as [|i]; cbn [Nat.eqb Nat.ltb Nat.leb Nat.sub]; [reflexivity|]. apply IH. lia.
Qed.

Lemma aobj_of_sshad0 : forall (AL : asan_layout) (CS : Z -> Prop) mX slo' shi B (k : nat),
  cs_ok AL CS -> sshad asegs AL mX slo' shi -> slo' <= B -> B + 8 * Z.of_nat (S k) <= shi -> B mod 8 = 0 -> 0 <= B ->
  crange CS B (8 * Z.of_nat (S k)) -> aobj asegs AL CS mX B (8 * Z.of_nat (S k)).
Proof.
  intros AL CS mX slo' shi B k OK SS H1 H2 HB H0 HC.
  pose proof (sshad_chunk asegs AL mX slo' shi k B SS H1 H2 HB) as SH.
  replace (shadow_of AL B) with (Z.shiftr B 3 + al_sb AL) in SH
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  eapply (aobj_of_zero_shadow_sh asegs AL CS mX B (zcells (S k)) B 0 (S k) OK SH HC HB H0 ltac:(lia)).
  intros i Hi. apply zcells_cell_at. exact Hi.
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis AMS : arl_amemset R = A_AMEMSET.
  Hypothesis GA : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : ALG mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 < ALG /\ ALG + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - ASN1_GET_ALG_NULL_STACK_A.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 304 - arl_need_amem R.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo ALG 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) ALG 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold ASN1_GET_ALG_NULL_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (asn1_get_alg_null_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG P END BUF lo slo).
  Local Notation W := [(PP, PP + 8); (ALG, ALG + 24)].

  (* [comment removed for export] *)
  Definition PATH (FB spv s2v sp1 sh2 : Z) (LF' : list blk) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null_A ()) "(31.(6.(7.$5.O4.=)(6.(7.(29.$2:.)O1.VLF,)(6.(7.$5.O5.O6.)(6.(7.$5.O3.(1<.O6.+60.))(7.$5.O2.(1<.O6.+80.))))))(6.(7.$5.O4.O6.)(6.(7.(29.$2:.)O1.(19.(1:.$5.$5.)(1;.$5.$5.O6.+80.)VLF,))(6.(7.$5.O5.O3.)(6.(7.$5.O2.O3.)(6.(41.VR,VLB,VLF,O6.+80.)(7.$5.(32.O6.+40.)=)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac fin_postA PRES :=
    apply evtA_done; unfold asn1_get_alg_null_postA;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    [ lazymatch goal with |- HM _ _ _ _ _ _ _ => eassumption end | ..];
    (lazymatch goal with
     | |- rw_cells _ ?m ?A _ => match goal with H : rw_cells _ m A _ |- _ => exact H end
     | _ => idtac end);
    (lazymatch goal with
     | |- presA _ _ _ _ _ _ _ _ _ _ => eapply presW_presA; exact PRES
     | |- rw_cells _ _ _ _ => idtac
     | |- forall mo, HK _ _ _ _ mo <-> _ =>
         first [ assumption
               | let mo' := fresh "mo" in intros mo';
                 repeat (eapply iff_trans; [ match goal with H : forall mo, HK _ _ _ _ mo <-> _ |- _ => apply H end | ]);
                 apply iff_refl ]
     | |- _ = 0 -> _ => first [ assumption | intros _ ]
     | |- _ => first [ assumption | reflexivity | congruence | (clear_disj; clear_mods; lia) | idtac ] end).

  (* [comment removed for export] *)
  Definition epi_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_A_asn1_get_alg_null_A ()) "PFB,$5.Pspv,$5.Ps2v,$5.Psp1,$5.Psh2,$5.PLF',(29.$2:.)Ph1,(4.$42.VR,VHIA,)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px9,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pj3,(29.(2.&8.))Pjrz,(29.(2.&8.))Pjsp,(2.&40.)Pr,$5.Pp',$5.Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pplen,(2.&40.)Pppw,(2.&40.)P,(=.$42.VR,VHIA,R27.VLB,R28.R25.)P,(7.P,$5.Sp(>.$42.VR,VHIA,R28.)(>.$42.VR,VHIA,Vh,))P,(7.$5.(?.$42.VR,VHIA,R29.)(?.$42.VR,VHIA,Vh,))P,(7.$5.(10.$42.VR,VHIA,R2:.)(10.$42.VR,VHIA,Vh,))P,Pmo,$14.(15.(16.$42.VR,VHIA,R2<.R1.)(16.$42.VR,VHIA,Vh,R1.))P,(7.$5.(11.$42.VR,VHIA,R2<.)(11.$42.VR,VHIA,Vh,))P,(7.$5.(12.$42.VR,VHIA,R2=.)(12.$42.VR,VHIA,Vh,))P,(7.$5.(13.$42.VR,VHIA,R2>.)(13.$42.VR,VHIA,Vh,))P,(6.(24.(33.(18.&40.Vsp,)+70.)R32.)(24.R32.(33.(18.&40.Vsp,)+60.)))P,(7.$5.(32.R33.+20.)=)P,(25.$42.R2?.R37.(19.$26.(27.R1:.)(19.$26.(27.R19.)(19.$26.(27.R18.)(1=.$26.)))))P,(25.$42.R30.(1<.R38.+18.)(19.$26.(43.#8.R18.)(1=.$26.)))P,(25.$42.R31.(1<.R39.+20.)(19.$26.(28.R10.)(19.$26.(28.R?.)(19.$26.(27.R>.)(19.$26.(27.R=.)(1=.$26.))))))P,(25.$42.R32.(1<.R3:.+38.)(19.$26.(43.#28.R19.)(1=.$26.)))P,(25.$42.R33.(1<.(44.R3;.+3.)(45.(21.VR,)))(19.$26.(46.(22.&8.+?1.))(19.$26.(46.(22.&8.+?1.))(19.$26.(46.(22.&8.+?1.))(19.$26.(46.(22.&8.+?1.))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.+?3.))(19.$26.(46.(22.&8.+?3.))(19.$26.(46.(22.&8.+?3.))(19.$26.(46.(22.&8.+?3.))(19.$26.(46.(22.&8.+?3.))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.=))(19.$26.(46.(22.&8.=))(1=.$26.))))))))))))))))))P,(47.(>.$42.VR,VHIA,Vh,)R3<.+80.)P,(7.$5.(32.R3=.+20.)=)P,(23.=R3>.)P,(24.(1<.R3?.+60.)R3<.)P,(3<.(39.VR,)(3:.$2:.VLB,(3;.R3;.))(37.VR,)(?.$42.VR,VHIA,Vh,)R40.+18.)P,(3<.(39.VR,)(3:.$2:.VLB,(3;.R3<.))(37.VR,)(?.$42.VR,VHIA,Vh,)(1<.R41.+20.)+40.)P,Px,$5.P,(6.(24.R43.R1.)(23.R1.(1<.R43.+80.)))(31.(6.(24.(37.VR,)R2.)(23.R2.(?.$42.VR,VHIA,Vh,)))(48.R3?.R2.))P,(31.(24.(1<.R43.+80.)VPP,)(24.(1<.VPP,+8.)R43.))P,(31.(24.(1<.R44.+80.)VALG,)(24.(1<.VALG,+18.)R44.))P,(31.(7.$5.(2?.(2=.(2.&8.)Vbs,))=)(31.(24.(1<.R45.+80.)VBUF,)(24.(1<.VBUF,(2?.(2=.(2.&8.)Vbs,)))R45.)))P,(1?.$42.R3>.Vlo,R45.)P,(24.Vlo,(33.(33.R46.+20.)(35.VR,)))P,(24.R47.R45.)P,(31.(24.(1<.R49.+80.)(37.VR,))(7.$5.R48.R49.))P,(6.(24.R47.R46.)(24.R46.(1<.R47.+20.)))P,(1?.$42.R43.R48.(1<.(18.&40.Vsp,)-50.))P,(25.$42.R44.(1<.R49.+8.)(19.$26.(27.R2:.)(1=.$26.)))P,(25.$42.R45.(1<.(18.&40.Vsp,)-50.)(19.$26.(27.Vs8,)(19.$26.(27.Vs7,)(19.$26.(27.Vs6,)(19.$26.(27.Vs5,)(19.$26.(27.Vs4,)(19.$26.(27.Vs3,)(19.$26.(27.Vs2,)(19.$26.(27.Vs1,)(19.$26.(27.Vs0,)(19.$26.(27.Vra,)(1=.$26.))))))))))))P,(25.$42.R46.VPP,(19.$26.(27.(22.&40.R2:.))(1=.$26.)))P,(25.$42.R47.VALG,(19.$26.(28.R2:.)(19.$26.(28.R29.)(19.$26.(27.R28.)(19.$26.(27.R27.)(1=.$26.))))))P,(2>.$42.R48.VBUF,Vbs,)P,(6.(24.VP,R2=.)(24.R2=.VEND,))P,P,(7.$5.R2?.=)(1.$5.Lap,$5.(6.(7.(2.&40.)R2<.(22.&40.R1.))(6.(24.VBUF,R1.)(24.(1<.R1.(18.&40.R2=.))R30.))))P,(6.(23.-7?.R30.)(24.R30.=))P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R4<.VPP,+8.)P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R4=.VALG,+18.)P,(3>.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)R4>.VBUF,(2?.(2=.(2.&8.)Vbs,)))P,(49.$42.(21.VR,)R4?.)P,(1>.$42.R50.)P,(4:.$42.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VALG,(1<.VALG,+18.))(1=.(1:.$5.$5.))))R52.R51.)P,(4;.VR,VLB,VLF,)P,(4<.VR,VLB,VLF,(18.&40.Vsp,)(19.(1:.$5.$5.)(1;.$5.$5.VPP,(1<.VPP,+8.))(19.(1:.$5.$5.)(1;.$5.$5.VALG,(1<.VALG,+18.))(1=.(1:.$5.$5.))))R5;.+60.)P,(4=.VR,VLB,VLF,(18.&40.Vsp,)(10.$42.VR,VHIA,Vh,)R5<.+80.)P,(20.$42.(21.VR,)R55.Vslo,R5<.)P,(20.$42.(21.VR,)R56.R5:.(18.&40.Vsp,))P,(4>.R5?.R5>.R5=.R5<.R5;.R5:.)(3?.$42.(21.VR,)(>.$42.VR,VHIA,Vh,)(40.$42.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VALG,VP,VEND,VBUF,Vlo,Vslo,R59.)(8.(9.R57.(22.&40.R5?.)Vgp,Vtp,R56.R55.R54.Vsp,(22.&40.R5=.)(22.&40.R3=.)R52.R51.R50.R4?.R4>.R4=.R4<.(22.&40.R5>.)R4;.R4:.R49.R48.(22.&40.(1<.(44.R60.+3.)(45.(21.VR,))))(22.&40.R60.)Vs9,Vs10,Vs11,R47.R46.R45.R44.)VF,(22.&40.+9:>=0.)Vfc,(;.(2.&40.))R58.(<.$42.)))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 CW2; try lx_pin1 CW1; try lx_pin1 SPA; try lx_pin1 RTS0; try lx_pin1 SLO3; try lx_pin1 SLO2; try lx_pin1 BUF0; try lx_pin1 AL2; try lx_pin1 AL1; try lx_pin1 bs; try lx_pin1 slo; try lx_pin1 lo; try lx_pin1 BUF; try lx_pin1 END; try lx_pin1 P; try lx_pin1 ALG; try lx_pin1 PP; try lx_pin1 m; try lx_pin1 fc; try lx_pin1 F; try lx_pin1 t6; try lx_pin1 t5; try lx_pin1 t4; try lx_pin1 t3; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 t2; try lx_pin1 t1; try lx_pin1 t0; try lx_pin1 tp; try lx_pin1 gp; try lx_pin1 sp; try lx_pin1 ra; try lx_pin1 LF; try lx_pin1 LB; try lx_pin1 h; try lx_pin1 GA; try lx_pin1 AMS; try lx_pin1 HIA; try lx_pin1 R.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02Z0@D10598676144.178D2459793318.178 D32452690557.178D32604263319.179D3386269609.177 D45702641176.177D47635295210.178D53304480533.178D62011770188.179D62022258533.178D62022316105.177D6897506287.177 K5152549648.224 L10773421954.141L13312155929.199L13424450161.144L13950455336.173L13950455460.207L15032546978.137L1685717371.0   L16975402087.144L17932209487.146L19135723283.2  L19546883924.144L19546999407.2  L20630677035.207L20630677159.173L2114001099.194 L22372406141.173L22372406257.207L24131365018.142L24387678245.236L26205700811.196L26965254398.146L27116614917.137L27386516966.1  L27650596369.143L28641830579.2  L32454903270.1  L32925469529.4  L33899371498.145L33901469287.144L33903568471.145L33903568471.146L34254091815.2  L34363428505.193L36187989568.2  L36301107185.143L36567293259.1  L39076636629.0  L39269760500.1  L39332637397.0  L39540652971.1  L39972639317.0  L4022468828.144 L4024567121.145 L4103369558.140 L4103370332.143 L4109651564.141 L4109651564.144 L41729115028.155L42411609006.0  L4406210294.147 L4410397510.148 L44321658622.141L45053222038.197L45826636441.194L47632025508.145L47634122531.141L47636232729.142L47636232729.146L48117620905.143L50790731766.8  L50876585809.7  L5162232212.2   L51767926.196   L51878069071.2  L52511154273.3  L53278386422.143L53574471957.137L53886235149.140L54009221249.139L54163769447.144L54510159614.8  L55259603906.147L55263796851.146L55348915583.2  L55685844716.146L55690048337.145L56602807449.195L57525278576.4  L58748461073.142L59308636694.1  L59308636694.8  L59504824377.235L60544121036.8  L61490559858.207L61490559998.173L62018535662.1  L62022572136.1  L6203796532.145 L6203796533.144 L64186535346.139L64824766027.195L66232301891.3  L66696405579.1  L66730930849.10 L67052002286.150L68040139772.2  L6899380056.1   L6899602147.140 L6899603304.141 L6912107245.142 L8285449844.142 L8285450231.141 L8287545981.143 L9165944844.152 L9168013737.154 L9631865130.139 L9631865646.138 L9631865646.139 L9633866540.2   L9877309020.10  P36561248207.223P5152549648.224 P66702450895.222Q10523111609.184Q10592386204.183Q10651763882.187Q12660624650.189Q23925414036.191Q23927511184.184Q24131365014.190Q24131365018.185Q24137657765.182Q26030354684.221Q30223088057.183Q30886270280.222Q32681887701.184Q33196749135.189Q34964698202.221Q35653441506.181Q36613016454.196Q38250992823.192Q38738229973.188Q4110986150.221 Q42439443119.221Q42441479407.196Q4279611329.221 Q43878048875.192Q46805771343.187Q47230721788.184Q47293410233.183Q52735241561.222Q55231354789.182Q55839915782.194Q56491743155.194Q5935758158.221 Q59865321072.221Q59867617328.196Q60109315147.181Q62009673036.191Q62011770184.184Q64133651577.222Q68708161853.188Q6897428434.182 Q6912107233.190 Q6912107245.185 Q7917062810.184 Q8699115497.221 00000;00<00G00[00\00g01201301@01M01Z01e01f01m02@03503>03G03K03L03S03^03_04T04]04n05?06N06_07007707O08^08i09009409;09<09@09K09L09M09j0:G0:H0:V0:W0:b0:c0:d0:h0:i0:m0:n0;50;<0;=0;>0;[0<80<X0<Y0<Z0<[0<b0>10>?0>@0>A0>^0?;0?S0?d0@@0@A0@O0@P0@Q0@\0@c0@n0A50A<0AW0B=0B>0B?0B\0B]0Bk0C:0CA0CE0Cd0D50DF0DO0DX0D[0D_0Dg0Do0E60FE0FF0FG0F`0G20G30G70G>0GE0GL0G\0Gl0H<0H=0HV0Ha0Hl0I70I?0I[0I\0I]0I^0Ig0In0J50J=0JI0Ja0Jh0Jo0K60KI0KP0K\0K]0Ke0L@0L[0MF0MM0MU0M^0N20NA0NJ0NT0N[0Ne0Nl0O80O?0O]0Ok0P40P50P60PC0PI0PO0PX0P`0Pg0Pn0Q50Q60Q_S2bs2FB3sp1FS2bs2FB3sp1S1R3HIA2bs2FB3sp12h1FS2bs2FB3sp1S2bs2FB3sp1FS1R2bs2FB3sp1S1R2bs2FB3sp1S1R2bs2FB3sp1S2bs2FB3sp1FS2bs2FBS2bs2FB3sp12H21p2PBS1R2sp2lo2bs3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACVS2bs1r2RRS2bs1r2RRS2bsSS2bs2FBS2bs2FB3sp1FS1R2sp2lo2bs3SLO3LOS2FB3sp13SP14SP1M4FBAL3FB03ALO3ACVS2FB4FBALS1P3END2bs2p'3PPES1P3END2bs2p'3PPES2sp2PP3ALG1P3END3BUF2lo2bs2B12B22B32D12D42D53SLO3DS13DS23DS42FB3s2v3SP13FB02H2S1P3END2bs2p'3PPES1P3END2bs2p'3PPES2bs2FBS2sp2lo2bs3SLO2FB3sp12H2S2sp2PP3ALG1P3END3BUF2lo2bs2B12B22B32D12D42D53SLO3DS13DS23DS42FB3s2v3SP13FB02H2S2bs2FB3sp1S2bs2FBS2FBS2bs2FBFS2FBS2sp2FB3SP1FFS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HFS2bs2FB3s2v2H2FS2bs2FB3sp1FSS2FBSS2FBSS2bs2FBS2bs2FBFFS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HS2sp2lo2bs3SLO2FB3s2v3SP13FB02H2SFFS2bs2FBS2sp2PP3ALG1P3END3BUF2lo2bs2B12B22B32D12D42D53SLO3DS13DS23DS42FB3s2v3SP13FB02H2S2bs2FB3s2v2H2FFS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS2FB3SP11HS1R2sp2lo2bs3SLO3LOS3ALOS1R2sp2lo3SLO3LOSS1R2sp2lo4RTA03sp13SP15SLO16FS2bs2FB3s2v2H2FFS2bs2FB3sp1S2bs2FBS2bs2FB3FB0S2bs2FBS2bs2FBS2sp2lo3slo3SLO4SLOL2FB3SP1S1R2sp2lo2bs3SLO3LOS2FB3sp13SP11H4FBS1FFS1R2sp2lo2bs3SLO3LOS2FB3SP11HFS2bs2FB3s2v2H2S1R2FB3spv4SEPFS2bs2FBS2KsS2sp2FB3sp13SP13FB04FBS13SPR2KsS2sp2bs2FB3sp12H2S1R2sp2lo3SLO3LOSS2bs1r2RRS2bs1r2RRS1RS2FBS2bs3sp1S2bs3sp1S2bs2FBS2sp2PP3ALG1P3END3BUF2lo2bs2B12B22B32D12D42D53SLO3DS13DS23DS42FB3s2v3SP13FB02H2FFS1R2sp2lo3SLO3LOS3sp13SP1S2sp2bs2FB3sh23H13FS2FBS2bs2FBS2bs2FBS2bs2FBS2bs2FB3sp14FBS1S2bs2FB3sp14FBS1S2bs2FB3sp14FBS1FS3slo2bs2FB3spv2H01R4SLOSS2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S2FB3FB0S2sp2lo3slo3SLO4SLOL3sp13SP1FFFS1R2sp2bsS2bs2FBS2PP2bsS3BUF2bsS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2bs2FBS2bs2FBS2bs2FBS2sp2lo2bs3sp11p2PBS2bs2FBS2bs2FB1p2PBFS3BUF2bsS2sp2lo2bs3SLO3sp13SP11p2PBS1R3HIA1h2sp2lo2bs3TOP4HTOPS1R3HIA1h2sp3slo2bs3TOP3spv3sp13SP14HTOP2H9S2lo2bsS3ALG2bsS2bs1p2PBS1R3slo2bs4SLOS1p2PBS1R3slo2bs4SLOSS2bs1p2PBS2sp2lo2bsS2PP2bsS1R2bs3ALOS2bs2FBS2bs2FB1p2PBS2bs2FBS2sp2lo2bs3SLO3sp13sh23SP13SH2S2sp2lo2bs3sh2S2bs1p2PBFFS1R2lo2bs3LOSS1R2bsS1R2bsS2bs1p2PBS3ALG2bsS2bs2FBS2bs2FBS2bs2FBFS1R3HIA1h2sp3slo2bs3TOP3sp13SP14HTOP1p2PB". (* [comment removed for export] *)
  #[using="CR4 CR2 CR1 DS4 DS2 DS1 SPH TOP LOS SLOL SLOS RTA0 SLO ALGB PPB D5 D4 D1 B4 B3 B2 B1 IMG"]
  Lemma epi_walk : epi_stmt.
  Proof.
  unfold epi_stmt.
  intros until ppw.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 HPAR RZ FSH CFB FBAL FB0 FBS1 FWH FWD FWS AP1 AP2 AP4
  ST1 SLO16 SPV1 SEPF SH2 STK2 SLOT SPILL HPP HALG HBUF PPE HR0 RR OPP OALG OBUF AB MI PRES WL WCF SFF SS1 SS2 HPATH.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB LF' _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  (* [comment removed for export] *)
  try unfold PATH in *. lxr_path. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x9af34] [(0x9aeec, DSplit)] 161%N). lx_tree.
  { (* [comment removed for export] *)
    lxr_leaf. lx_carry. lx_cond Ks.
    (* [comment removed for export] *)
    destruct HPATH as [(Es2 & ELF & Espv & Esp1 & Esh2)|(Es2 & _)]; [| exfalso; rewrite Es2 in Ks; clear - Ks FB0 FBS1 SP1 SPR; lia].
    subst LF' spv sp1 sh2.
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHZ end).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    try (match goal with H : rw_cells _ mf FB _ |- _ => release_frame H ST1 (FB + 24) end).
    try (match goal with H : rw_cells _ mf (FB + 24) _ |- _ => release_frame H ST1 (FB + 32) end).
    try (match goal with H : rw_cells _ mf (FB + 32) _ |- _ => release_frame H ST1 (FB + 56) end).
    try (match goal with H : rw_cells _ mf (FB + 56) _ |- _ => release_frame H ST1 (FB + 96) end).
    try (match goal with H : stk _ mf (FB + 96) (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge asegs mf lo (FB + 96) _ ST1 H ltac:(clear - SP1 FB0 SLO16 RTA0; lia)) as ST3; clear ST1 H end).
    try (match goal with H : rw_cells _ mf (bv_unsigned sp + -80) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
    assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)).
    { eapply sshad_merge; [exact SS1| | clear - SP1 FB0 SLOL SLO; lia]. eapply sshad_merge; [| exact SS2| clear - SP1 FB0; lia]. eapply (sshad_of_chunk_sh asegs AL mf 16 FB); [exact FSHZ| reflexivity| clear - FBAL; lia| clear - FB0; lia]. }
    lxr_stk_join. fin_postA PRES.
  }
  { (* [comment removed for export] *)
    lxr_leaf. lx_carry. lx_cond Ks.
    (* [comment removed for export] *)
    destruct HPATH as [(Es2 & _)|(Es2 & ELF & Espv & Esh2 & FRSH & F64)]; [exfalso; rewrite Es2 in Ks; clear - Ks; lia|].
    subst LF' spv s2v sh2.
    try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH5 end).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h1 LB _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h1 LB ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
    as (p & h2 & ROp & [old Hold] & CRp & NCp & NSp & HM2 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKiff2).
    replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
    clear G1 RZ.
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
    clear Hold.
    assert (SUB' : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata ((FB, 128) :: LF))) by (intros b Hb; apply fdata_cons_sub; exact Hb).
    pose proof (nc_apart _ _ _ _ _ p PP 8 NCp CR1 SUB' LOS ltac:(clear; lia)) as NP1.
    pose proof (nc_apart _ _ _ _ _ p ALG 24 NCp CR2 SUB' LOS ltac:(clear; lia)) as NP2.
    pose proof (nc_apart0 _ _ _ _ _ p BUF _ NCp CR4 SUB' LOS) as NP4.
    assert (NP5 : bv_unsigned sp + -80 + 80 <= p \/ p + 1 <= bv_unsigned sp + -80).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 8 + 8 <= p \/ p + 1 <= sp1 + 8).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1; lia| intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (INH : In (FB, 24) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    assert (IND : In (FB + 32, 88) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    assert (NP7 : FB + 24 <= p \/ p + 1 <= FB).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| eapply client_range_block; [exact INH| clear; lia| clear; lia] | intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP8 : FB + 32 + 24 <= p \/ p + 1 <= FB + 32).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| eapply client_range_block; [exact IND| clear; lia| clear; lia] | intros b Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp : wcover R LB LF (bv_unsigned sp) W p 1)
    by (eapply wcover_nc; [exact NCp| exact SUB'| clear - LOS SLO; lia]).
    rewrite ECS in CRp.
    clear HHe NCp NSp.
    (* [comment removed for export] *)
    zstep.
    zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. subst lxm.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    cbn [lb_remove fst Z.eqb] in HM2.
    rewrite Z.eqb_refl in HM2.
    try (match goal with H : stk _ mf sp1 (bv_unsigned sp + -80) |- _ =>
    pose proof (stk_merge asegs mf lo sp1 _ ST1 H ltac:(clear - SP1 SLO16 RTA0; lia)) as ST3; clear ST1 H end).
    try (match goal with H : rw_cells _ mf (bv_unsigned sp + -80) _ |- _ => release_frame H ST3 (bv_unsigned sp) end).
    assert (SSF : sshad asegs AL mf slo (bv_unsigned sp)) by (eapply sshad_merge; [exact SS1| exact SS2| clear - SP1 SLOL SLO SLO16 RTA0; lia]).
    lxr_stk_join. fin_postA PRES.
  }
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac apply_epi := eapply epi_walk; try eassumption; try reflexivity.

  (* [comment removed for export] *)
  Tactic Notation "callxA_sp_cs" constr(e) constr(E) tactic3(apptac) :=
    lazymatch goal with
    | |- evtA ?segs _ _ _ (MS _ _ _ _ _ ?m _) =>
        eapply evtA_cut_mono;
        [ apptac
        | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          first [ rewrite <- E; exact Hx | rewrite E in Hx; exact Hx | rewrite <- E in Hx; exact Hx ]
        | lazymatch goal with |- forall x, ?P x -> _ => let hd := head_of P in try unfold hd end;
          rewrite ?(unsigned_lit e) by qlia; post_callA segs m ]
    end.

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 RTS0; try lx_pin1 SLO3; try lx_pin1 SLO2; try lx_pin1 t6; try lx_pin1 t5; try lx_pin1 t4; try lx_pin1 t3; try lx_pin1 t2; try lx_pin1 t1; try lx_pin1 t0.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02T0@D10592385689.198D10592386202.177D10637084554.198D10651759757.174D14207190849.174D17714208912.198D2457697676.177 D32458983511.177D32458985044.198D32604263317.178D3375868588.176 D35112690362.175D38723547381.175D43966946138.198D45717324573.176D46805718120.174D47641584064.177D50480159773.198D53314967871.177D60098777666.175D60098833772.174D60109265000.177D60109265003.176D60109266539.198D62011769676.198D62011770188.176D62011770190.178D62011770191.177D62022258533.175D62022316107.174D6533180034.198 D68708163380.198D68714451741.175D6912107242.176 L10773421188.119L13424450173.144L15043033658.115L16977498607.122L17932209473.124L19546883928.144L20596825551.229L20596944330.228L20596944330.231L20596944330.232L24131365014.139L24715830035.223L24715830035.224L26965254384.124L27127101853.115L27196018929.228L27652692889.121L33805656935.223L33805656935.224L33899371496.123L33899371503.122L33901468271.123L33901468271.124L34866092019.286L34866092019.290L34866092019.291L34866092019.293L36301107191.121L4024567123.123 L4024567124.122 L4103368784.118 L4103369300.119 L4103369300.122 L4105466836.121 L4404113278.126 L4406210174.125 L44321658360.119L47632025510.123L47634121765.119L47634122273.120L47634122273.124L48119718063.140L53278386420.121L53429767039.228L53584960909.115L53886234891.118L53955276900.232L53955276900.233L54009221507.117L54161673711.122L55018117522.232L55018117522.233L55261700090.125L55263796849.124L55687951060.124L55690048339.123L57525278576.4  L58746365337.120L59311123024.220L59314873579.10 L59314873579.2  L59314873579.3  L59314873579.4  L59314873579.5  L59314873579.8  L59314988138.1  L59314988138.2  L60191618956.228L60191618956.231L60191618956.232L60191786889.229L6203796534.123 L6203796535.122 L64186534588.117L67052002282.147L6899602401.118 L6899602542.119 L6912107233.139 L8287545979.121 L8287545980.120 L8287545983.119 L9165944844.149 L9168013354.151 L962203802.229  L962388127.231  L962388127.232  L9631864872.116 L9631864872.117 L9631866404.117 Q10523111605.185Q10592386192.184Q10651763882.188Q10651763890.181Q12658527488.190Q1551931667.182 Q23925414032.192Q23927511196.185Q24131365014.186Q24131365019.183Q24133462168.191Q30223088053.184Q32681887705.185Q33194651973.190Q35509981082.182Q35653441506.168Q36117321936.181Q36613016458.197Q38250992819.193Q38736132831.189Q38738229979.182Q42441479395.197Q43878048879.193Q46805771343.188Q46805771351.181Q47230721776.185Q47293410229.184Q55246033563.183Q55839915786.195Q56491743167.195Q59867617340.197Q60109315147.168Q60740903729.181Q62009673032.192Q62011770180.185Q68708161843.182Q68710258999.189Q6910010095.191 Q6912107233.186 Q6912107244.183 Q7917062806.185 00000F00\01201H01I01_01`02602L02k02l02m03C03Y03o04E04[04\04]05<05[06:06Y07807P07h08@08X09009H09^0:40:J0:`0:g0<>0<B0<I0<T0=k0>M0>o0?Q0@30@:0@Z0A:0AE0AL0Al0B30BS0C30C40C50CS0D10DG0D]0E30EI0ET0E[0Eb0Ec0FA0F_0F`0Fa0Fb0Fi0Fj0Fk0GI0Gg0H?0HJ0Hj0I10I<0Ih0JT0J[0Jb0KF0Kj0LQ0LR0M00M10M@0MG0MH0MI0MJ0MK0ML0MM0MN0MQ0MR0N60NZ0O>0Ob0Oj0P20P90PK0PR0PY0P`0Q00Q@0QP0QQ0Qj0R@0RV0Rl0S70SB0SM0SV0S]0Sd0Sk0T30T>0TJ0Tb0Ti0U00U70U>0U?0UG0UH0Uc0Ud0VP0VW0V_0Vg0W60W@0WG0WN0WX0W_0Wf0XD0XR0XS0X`0Xk0Y10Y70Y?0YG0YN0YU0Y\0Y]S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1FS2PP3ALG2bs2FB3spv3sp1FS2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S1R3HIA2PP3ALG2bs2FB3spv3sp12h1FFS2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1FFS1R2PP3ALG2lo2bs3LOS2FB3spv3sp1S1R2PP3ALG2lo2bs3LOS2FB3spv3sp1S1R2PP3ALG2lo2bs3LOS2FB3spv3sp1S1R2PP3ALG2lo2bs3LOS2FB3spv3sp1S1R2PP3ALG2lo2bs3LOS2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S1R2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2bs2FBS1R2sp2PP3ALG2lo2bs3PPB4ALGB3SLO4RTA03LOS2FB3spv3sp13SP14SP1M4FBAL3FB05SLO164SPVA3ALO1HS2bsS2bs2FBS2bs2FB3sp1S1R2sp2PP3ALG2lo2bs3PPB4ALGB3SLO4RTA03LOS2FB3spv3sp13SP14SP1M4FBAL3FB05SLO164SPVA3ALO1HS2PP3ALG1P2bs2FB3spv3sp15lxv153H63S2PP3ALG1P2bs2FB3spv3sp15lxv153H61S2PP3ALG1P2bs2FB3spv3sp15lxv153H64S2PP3ALG1P2bs2FB3spv3sp15lxv153H65S2bs2FBS2PP3ALG2bs2FB3spv3sp15lxv183H57S2PP3ALG2bs2FB3spv3sp15lxv183H58S2bs2FB3sp1S2bs2FBS2PP3ALG2bs2FB3spv3sp15lxv143H36S2bs2FBS2PP3ALG2bs2FB3spv3sp15lxv183H58S2PP3ALG2bs2FB3spv3sp15lxv183H59FFS1R2sp2lo2bs3SLO3LOS2FB3SP12H0S1R2sp2lo2bs3SLO3LOS2FB3SP12H0S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2bs2FB3sp1S2bs2FBS2bs2FBFS1R2sp2lo2bs3SLO3LOS2FB3SP12H0S1R2sp2lo2bs3SLO3LOS2FB3SP12H0FFFS2bs2FBFFS1R2sp2lo2bs3SLO3LOS2FB3SP12H0S1R2sp2lo2bs3SLO3LOS2FB3SP12H0S1R2sp2lo2bs3SLO3LOS3ALOS2bs2FB3sp1S2PP3ALG2bs2FB3spv3sp15lxv143H63S2bs2FBS2bs2FB3FB0S2PP3ALG2bs2FB3spv3sp15lxv155lxv185lxv193H45S2PP3ALG2bs2FB3spv3sp15lxv155lxv185lxv193H46S2bs2FBS2bs2FBS2PP3ALG3BUF2bs2FB3spv3sp15lxv193H46S2PP3ALG3BUF2bs2FB3spv3sp15lxv193H47S1R2sp2lo2bs3SLO3LOS2FB3sp13SP12H04FBS1FS1R2sp2lo2bs3SLO3LOS2FB3SP12H0FS1R2FB3spv4SEPFS2bs2FBFFFFFFFS1GFS2PP3ALG3END2bs2FB3spv3sp15lxv153H60S2PP3ALG3END2bs2FB3spv3sp15lxv153H63S2PP3ALG3END2bs2FB3spv3sp15lxv153H64S2PP3ALG3END2bs2FB3spv3sp15lxv153H62S2bs3sp1S2bs3sp1S2bs2FBS2sp2bs2FB3sh23H15S2bs2FBS2bs2FBS2bs2FBS2bs2FB3sp14FBS1S2bs2FB3sp14FBS1S2bs2FB3sp14FBS1FS3slo2bs2FB3spv2H11R4SLOSS2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2PP3ALG2bs2FB3spv3sp1S2bs2FB3FB0S2bs2FB3FB0S2bs2FB3FB0S1R2sp2bsS2bs2FBS2PP2bsS2PP2bsS3BUF2bsS2PP3ALG2bsS1R3HIA1h2bsS1R3HIA1h2sp2bs3TOP4HTOPS2bs2FBS2bs2FBS2bs2FBS2bs2FBFS3BUF2bsFS1R3HIA1h2sp2lo2bs3TOP4HTOPFS1R3HIA1h2sp3slo2bs3TOP3spv3sp13SP14HTOP3H11S2lo2bsS3ALG2bsS3ALG2bsS1R3slo2bs4SLOSS2sp2lo2bsS2PP2bsS2PP2bsS1R2bs3ALOS2bs2FBS2bs2FBS2sp2lo2bs3SLO3sp13sh23SP13SH2S2sp2lo2bs3sh2FS1R2lo2bs3LOSS2PP3ALG2bsS1R2bsS1R2bsS3ALG2bsS3ALG2bsS2bs2FBS2bs2FBS2bs2FBF". (* [comment removed for export] *)
  #[using="CW2 CW1 CR4 CR2 CR1 DS4 DS2 DS1 SPH TOP LOS SLOL SLOS RTA0 SLO BUF0 ALGB PPB AL2 AL1 D5 D4 D1 B4 B3 B2 B1 GA AMS IMG"]
  Lemma body_walk : forall (FB spv s2v sp1 sh2 : Z) (LF' : list blk) (h1 : HST asegs R HIA) (m0 m : mem)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 s6v : word)
      (junk1 junk2 j3 jrz : list byte) (atag apad alen apw : word),
    HM asegs R HIA h1 LB LF' m -> hcs asegs R HIA h1 = CS -> htop asegs R HIA h1 = htop asegs R HIA h ->
    hstkhi asegs R HIA h1 = hstkhi asegs R HIA h -> (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) ->
    hflag asegs R HIA h1 = hflag asegs R HIA h -> havol asegs R HIA h1 = havol asegs R HIA h -> hfr asegs R HIA h1 = hfr asegs R HIA h ->
    bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 -> sp1 mod 32 = 0 ->
    rw_cells asegs m FB [CB 24 junk1] -> rw_cells asegs m (FB + 24) [CB 8 j3] ->
    rw_cells asegs m (FB + 32) [CB 24 junk2] -> rw_cells asegs m (FB + 56) [CB 40 jrz] ->
    rw_cells asegs m (Z.shiftr FB 3 + al_sb AL) (zcells 16) ->
    crange CS FB 128 -> FB mod 32 = 0 -> 0 < FB -> FB + 96 <= sp1 ->
    client_wrange L (LB ++ fdata LF') (arl_stklo R) (htop asegs R HIA h) FB 24 ->
    client_wrange L (LB ++ fdata LF') (arl_stklo R) (htop asegs R HIA h) (FB + 32) 64 ->
    (forall x, FB <= x < FB + 128 -> (arl_stklo R <= x < htop asegs R HIA h) \/ in_block LF' x) ->
    (forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata LF')) ->
    (FB + 128 <= PP \/ PP + 8 <= FB) -> (FB + 128 <= ALG \/ ALG + 24 <= FB) ->
    (Z.of_nat (length bs) = 0 \/ FB + 128 <= BUF \/ BUF + Z.of_nat (length bs) <= FB) ->
    stk asegs m lo spv -> lo <= spv - 96 - arl_need_amem R -> spv mod 16 = 0 -> spv <= sp1 -> (FB + 128 <= arl_stklo R \/ spv = FB) ->
    sp1 <= sh2 <= sp1 + 32 ->
    stk asegs m sp1 (bv_unsigned sp + -80) -> rw_cells asegs m (sp1 + 8) [C8 (Z_to_bv 64 FB)] ->
    rw_cells asegs m (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m PP [C8 (Z_to_bv 64 P)] -> rw_cells asegs m ALG [C4 atag; C4 apad; C8 alen; C8 apw] -> bytes_at asegs m BUF bs ->
    aobj asegs AL CS m PP 8 -> aobj asegs AL CS m ALG 24 -> aobj asegs AL CS m BUF (Z.of_nat (length bs)) ->
    abase asegs AL m -> mem_inv asegs m ->
    presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m0 m ->
    wlow R LB LF -> wcover R LB LF (bv_unsigned sp) W FB 96 ->
    shadow_free R LB LF (bv_unsigned sp) (hstkhi asegs R HIA h) FB 128 ->
    sshad asegs AL m slo spv -> sshad asegs AL m sh2 (bv_unsigned sp) ->
    PATH FB spv s2v sp1 sh2 LF' ->
    evtA asegs AL CS (POSTA m0)
      (MS (mkR (Z_to_bv 64 0x09addc) (Z_to_bv 64 spv) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1)
              x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 s2v) (Z_to_bv 64 ALG) (Z_to_bv 64 END) (Z_to_bv 64 PP) s6v (Z_to_bv 64 (al_sb AL)) (Z_to_bv 64 FB) s9 s10 s11
              x28 x29 x30 x31)
          F (Z_to_bv 64 0x09ae18) fc None m (seg_rom asegs)).
  Proof.
  intros until apw.
  intros HH ECS ETOP ESTK HKI EFLAG EVOL EFR SP1 SP1M FH G1 FD RZ FSH CFB FBAL FB0 FBS1 FWH FWD FWS SUBLF AP1 AP2 AP4
  ST1 SLO16 SPVA SPV1 SEPF SH2 STK2 SLOT SPILL HPP HALG HBUF OPP OALG OBUF AB MI PRES WL WCF SFF SS1 SS2 HPATH.
  rt_facts.
  pose proof (hm_top asegs R HIA h1 LB LF' _ HH) as HTOP.
  rewrite ETOP, ESTK in HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  cbn [zcells] in FSH.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mm _) =>
    assert (OSL : aobj asegs AL CS mm (spv - 72) 8) by
      (apply (aobj_of_sshad0 AL CS mm slo spv (spv - 72) 0 CSOK SS1);
       [ clear - SLO16 SLOL RTA0; lia | clear; lia | clear - SPVA; lia | clear - SLO16 SLOL SLOS RTA0 ALO ACP; lia
       | eapply crange_sub; [exact SCS | clear - SLO16 RTA0; lia | clear - SPV1 SP1; lia] ]) end.
  (* [comment removed for export] *)
  try unfold PATH in *. lx_pre. lxr_path. lxr_abase. lxr_pose.
  (* [comment removed for export] *)
  lxa_auto [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_amemset0A 24 [lxz4; lxz4; lxz8; lxz8] 4; SUM_getalgA 5 6 4] [FB + 32; PP; ALG].
  lx_pre. lx_run_tac (PLANS [0x09aed0] [(0x9aebc, DSplit)] 161%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_amemset0A 24 [lxz4; lxz4; lxz8; lxz8] 4; SUM_getalgA 5 6 4]). lx_tree. all: lxa_unglob.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x9aed0) _ _ _ (seg_rom _)] => lxr_leaf; lx_apply epi_walk | |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx BODY: unexpected leaf left:" g end.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
