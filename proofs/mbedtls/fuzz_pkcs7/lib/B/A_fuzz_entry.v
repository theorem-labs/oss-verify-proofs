(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_alloc_lib ATopContract A_pkcs7_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0124b54926d453df 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P01a0cfeac6084ae6 0 6 0 1 46 1 50 1 53 1 67 1 68 1P0210907c5754f9df 1 2 64 2 0 1 85 1 64 2 61 1 86 1 2 87 1 88 1P0256b69176a6e127 0 6 0 1 72 1 73 1 74 1 76 1 79 1P02a04e076dd67643 0 5 0 1 32 1 45 1 67 1 68 1P03c0e6b721649fe4 0 5 0 1 32 1 45 1 67 1 68 1P03d5b737993bf29b 0 4 0 1 45 1 67 1 68 1P048433a0146a3555 1 2 32 3 0 1 104 1 107 1 32 3 1 1 105 1 106 1 2 108 2 109 2P04e087be16aa7e80 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P06b10c6e5746e807 1 1 16 3 0 1 104 1 105 1 10 56 1 75 1 82 1 83 1 84 1 85 1 88 1 103 1 106 1 107 16P07048122fd9e357b 1 1 16 2 1 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P0748a1be187843da 0 3 0 1 37 1 71 1P07d9dd0fb1022576 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P07e9ab8ebff95d80 0 5 0 1 32 1 45 1 67 1 68 1P07f2553068d6df92 0 4 0 1 45 1 67 1 68 1P08be8c5ea6b08163 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P0958c49b86ef2773 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P0a9137bae142477c 0 3 0 1 37 1 71 1P0ab60b6d2ab58086 0 6 0 1 46 1 50 1 53 1 67 1 68 1P0ac499a3d27e19fc 0 6 0 1 46 1 50 1 53 1 67 1 68 1P0b16e756faadcfa2 1 1 16 3 0 1 105 1 106 1 10 57 1 76 1 83 1 84 1 85 1 86 1 89 1 104 1 107 1 108 16P0b860e3d6b6ce102 0 6 0 1 72 1 73 1 74 1 76 1 79 1P0b940b2d1676bcf9 1 1 64 2 1 1 85 1 3 0 1 86 1 87 64P0d9481ac55956eec 1 2 32 3 0 1 103 1 106 1 32 10 41 1 56 1 75 1 82 1 83 1 84 1 86 1 89 1 104 1 105 1 2 107 2 108 2P0dccc4f3705259b3 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P0df47193cef9de7b 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P0df494144ed7c546 0 4 0 1 45 1 67 1 68 1P0e0630d0a6429758 0 7 0 1 26 1 72 1 76 1 79 1 87 1 88 1P0e7c205bf0145ec5 0 5 0 1 32 1 45 1 67 1 68 1P0f161d63662dfcd0 0 3 0 1 37 1 71 1P0f41cc4d68cec127 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P0f9abf604321859f 0 4 0 1 45 1 67 1 68 1P0fb677c60415e733 1 1 16 3 0 1 105 1 106 1 10 57 1 76 1 83 1 84 1 85 1 86 1 89 1 104 1 107 1 108 16P0fc9f15ed19acfb2 0 3 0 1 29 1 38 1P10e480ba4ca4d9f5 0 6 0 1 82 1 85 1 88 1 103 1 104 1P10f759a2337dcee1 0 4 0 1 45 1 67 1 68 1P11475109f6bb7641 0 3 0 1 37 1 71 1P1175041d0b0c8283 0 4 0 1 45 1 67 1 68 1P11c4c9e8247b9349 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P120af1ca1ab1ce2e 0 3 0 1 37 1 71 1P121a75fbf95129c4 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P12ffdd64dd1f147b 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P134e55eb0651edc7 0 6 0 1 46 1 50 1 53 1 67 1 68 1P136bc96d2ae7e528 0 5 0 1 32 1 45 1 67 1 68 1P13edbe296a9d7e5e 0 5 0 1 32 1 45 1 67 1 68 1P144abbfcd1b262b9 1 1 16 3 1 1 24 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P152fa8ce6c25d0bf 1 1 64 2 61 1 86 1 3 0 1 85 1 87 64P155d7bc135c31107 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P1585cc6db63f4601 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P15bc371b8a99060a 0 6 0 1 67 1 70 1 81 1 103 1 104 1P15d0d39ee2a23de8 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P16ce915ad3eb5f4f 1 1 16 3 1 1 24 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P174fc40467f66bd1 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P18430990d69564c5 0 7 0 1 26 1 72 1 76 1 79 1 87 1 88 1P18d6c42c92da4981 1 1 16 3 0 1 104 1 105 1 4 70 1 103 1 106 1 107 16P1a866c8a41e27c42 0 4 0 1 45 1 67 1 68 1P1b1f961261207d3a 0 3 0 1 37 1 71 1P1b98c67d7b750d86 1 2 32 3 1 1 104 1 107 1 32 10 42 1 57 1 76 1 83 1 84 1 85 1 87 1 90 1 105 1 106 1 2 108 2 109 2P1bab11e7aee71643 0 3 0 1 37 1 71 1P1c158fe584f99d5e 0 6 0 1 72 1 73 1 74 1 76 1 79 1P1c388b00f7db68a7 0 4 0 1 45 1 67 1 68 1P1caab3e0878f50bb 0 4 0 1 45 1 67 1 68 1P1cbbb141403e421f 0 9 0 1 41 1 82 1 83 1 84 1 86 1 89 1 103 1 104 1P1d6dc4b37825221c 1 1 16 3 1 1 24 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P1de961a3e57c00f1 0 4 0 16 44 16 67 16 68 16P1e1495230f32d5ac 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P1e15d47d58e7c257 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P1e46da8491c062f8 0 6 0 1 72 1 73 1 74 1 76 1 79 1P1eaa5fe4f92308bd 0 5 0 1 32 1 45 1 67 1 68 1P1f736de18cf1e205 0 4 0 1 45 1 67 1 68 1P1f9a527cda8c3173 0 3 0 1 37 1 71 1P2020191292f67b35 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P202c4c5fc1708952 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P21a8ca9c7cfd234d 0 6 0 1 46 1 50 1 53 1 67 1 68 1P2249a184090018fe 0 4 0 1 25 1 87 1 88 1P2267b170e7c54b19 0 4 0 1 72 1 76 1 79 1P238fb8c62a883b45 0 6 0 1 72 1 73 1 74 1 76 1 79 1P23f66305895b8b78 1 1 16 3 0 1 104 1 105 1 4 70 1 103 1 106 1 107 16P245bb06a3544f78c 1 2 32 3 0 1 86 1 89 1 32 3 1 1 87 1 88 1 2 90 2 91 2P245ccf8ca28c66f7 0 6 0 1 46 1 50 1 53 1 67 1 68 1P247c8744a3a016a5 0 5 0 1 32 1 45 1 67 1 68 1P253209f410cb0068 0 3 0 1 37 1 71 1P25583c8c3e698209 0 6 0 1 72 1 73 1 74 1 76 1 79 1P255e341746e66416 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P26049b543c62f4dc 1 1 16 2 1 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P26dfe801a1d6effb 0 7 0 1 41 1 82 1 85 1 88 1 103 1 104 1P2701d6b44db50691 0 4 0 1 25 1 87 1 88 1P279efb16c79c7837 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P28260452c90e265f 0 6 0 1 72 1 73 1 74 1 76 1 79 1P287d583d6f5b3804 1 2 32 3 0 1 103 1 106 1 32 10 41 1 56 1 75 1 82 1 83 1 84 1 86 1 89 1 104 1 105 1 2 107 2 108 2P289e01d4151e9bdb 0 4 0 64 7 64 103 64 104 64P2981468924eb3f08 0 6 0 1 46 1 50 1 53 1 67 1 68 1P29d7784b71f48ae5 1 2 32 3 1 1 104 1 107 1 32 10 42 1 57 1 76 1 83 1 84 1 85 1 87 1 90 1 105 1 106 1 2 108 2 109 2P2a57f62ef23cf20c 1 2 32 3 0 1 103 1 106 1 32 10 41 1 56 1 75 1 82 1 83 1 84 1 86 1 89 1 104 1 105 1 2 107 2 108 2P2acc304e19ff3a1e 0 7 0 1 41 1 82 1 85 1 88 1 103 1 104 1P2adf2e6ecf98f52e 0 7 0 1 26 1 72 1 76 1 79 1 87 1 88 1P2aeb82694776e5ad 1 1 16 3 1 1 24 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P2cbc852b2b4692f8 1 1 16 3 0 1 105 1 106 1 10 57 1 76 1 83 1 84 1 85 1 86 1 89 1 104 1 107 1 108 16P2cd6850b95902274 0 5 0 1 32 1 45 1 67 1 68 1P2d178aa61895c32e 0 6 0 1 72 1 73 1 74 1 76 1 79 1P2ea1ff46b46b01fb 0 3 0 1 37 1 71 1P2eae1ba6392eb666 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P2ec9ceadb1e63fa0 0 6 0 1 46 1 50 1 53 1 67 1 68 1P2ee819577d67333b 1 1 16 2 1 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P2ef0f605f85aed03 0 6 0 1 46 1 50 1 53 1 67 1 68 1P2f14cfefc31b875d 0 4 0 1 45 1 67 1 68 1P2f6d4fcf9fe7a129 1 1 16 3 0 1 104 1 105 1 10 56 1 75 1 82 1 83 1 84 1 85 1 88 1 103 1 106 1 107 16P2f8b59045065aa1c 1 2 64 2 0 1 103 1 64 2 57 1 104 1 2 105 1 106 1P2fbae29a0e5ccd45 0 6 0 1 46 1 50 1 53 1 67 1 68 1P2fe21e302049b5d1 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P3026e5f8584c3e31 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P304a19713e02f0b4 1 2 32 3 0 1 104 1 107 1 32 3 1 1 105 1 106 1 2 108 2 109 2P30a0b66753783a66 1 1 16 2 1 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P31c5f41d0eee6a22 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P32057c10ee322570 0 5 0 1 32 1 45 1 67 1 68 1P320dd71019269daa 1 1 16 2 0 1 67 1 3 4 1 68 1 69 16P34e735d1ba10e317 0 6 0 1 39 1 70 1 81 1 103 1 104 1P3527a59e0c9e8d9a 1 2 16 3 1 1 24 1 68 1 16 3 0 1 25 1 69 1 2 70 1 71 1P372e7cdf0f87cd70 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P37c137007b05ec5f 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P3829fca57d809c84 0 6 0 1 82 1 85 1 88 1 103 1 104 1P382f0aebba41871d 0 5 0 1 32 1 45 1 67 1 68 1P388a69db97ba58e7 0 4 0 1 25 1 87 1 88 1P38a37762f02fe0a5 0 3 0 1 39 1 45 1P38fd2451355606fb 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P39f8d24e7d33b559 1 1 16 3 1 1 24 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P3a3fb91348e11cb7 0 6 0 1 72 1 73 1 74 1 76 1 79 1P3ac3ecb5e29b773b 1 2 32 3 0 1 104 1 107 1 32 10 42 1 57 1 76 1 83 1 84 1 85 1 87 1 90 1 105 1 106 1 2 108 2 109 2P3b1d80d3f3ffb5b6 1 2 16 2 0 1 69 1 16 2 1 1 68 1 2 70 1 71 1P3b5ed01fc5a9f9ff 1 1 16 2 1 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P3be845303e2c239e 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P3c9082692a0c2879 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1P3cafecb4a8d4325c 0 6 0 1 46 1 50 1 53 1 67 1 68 1P3d6fe830789d784e 1 1 16 4 1 1 26 1 35 1 68 1 9 38 1 40 1 47 1 48 1 49 1 50 1 53 1 69 1 70 16P3d85f3ac19daae7c 0 6 0 1 72 1 73 1 74 1 76 1 79 1P3de09df3f8a6ba42 0 10 0 1 61 1 64 1 71 1 72 1 73 1 74 1 77 1 86 1 87 1P3e6c174589188877 1 1 16 3 0 1 105 1 106 1 4 71 1 104 1 107 1 108 16P3ff16414b517dad1 0 8 0 1 46 1 47 1 48 1 50 1 53 1 67 1 68 1N01f85e4d096971afN0293a635919a89e1N04e58a5e38f8cb04N05e80ffbad635c03N06b43f5ea3ada83fN06e7a4bf647a0769N0906a003ba280c5dN09e2b95962a813dcN0a9daf35073545c1N0b39947c33496107N0b857f37de0a7181N0c231eaec2a59659N0dd6952c4948881dN0edc6e50c027a9a0N0ee51d820c667d22N0f2a069c124d5003N1005358d6c3086c2N1422109865edc0b1N142ba76414e8b4aaN14780ded04292652N1644d18157534577N164fa9d76e179033N166fa8cca649c3efN189f22e578b67c71N18b885b5e321fa4bN198f7f4c020a8c0dN19a168ef7642f6e8N19ab3e079ec7cfe8N1bb797302f5e1024N1d5aec22548e0c9dN1e2912267818fa40N1e4bfde6d3c1b65cN1f3e85c19d704197N1f938cc4e12f58ebN20d995f0a2c5218dN22b5fa90a2abfc23N22d6a368bb40787aN238263c1c938a373N2409559f3f946291N253e51d81f9cab9cN2592ed212c470e0eN26432d680d7e17baN27408f091008b8b2N2817d8d1c0473d48N28b61f015de8b87aN28f1014fcd16a48cN290ce6b394ce69e5N29fe5e5ef360484eN2a4e754c51d792cfN2a84374bf8d96601N2af294090a20f09eN2b4c0efd34438840N2b8e4b30bf238d55N2cda475d080539b4N2d760c8faf336747N310c7051b3a3979aN3178fb964e196971N319a89f02cc65000N31e9732a214229c2N325df3c61cea2935N33e48e9b4f8c6370N34ee58e6787c221fN35003091832124caN35851f26d218a58fN35d055c5cd5cd62aN36361f7d181a852bN3717c893c410750bN389cb18cd2ec157bN38a52a83cbba2d15N398bb0af3af360c1N3a51220922898bc3N3a9fb6a810d68b1aN3aeccb371daf64f6N3bd04d49a608a748N3bd7121c6129bd86N3d646101c0b4b4ffN3d756394c1a2b35dN3e074c8db3bc6898N3e851e201ad0ad02"%lxh.
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
Ltac2 gd_tbl_A_fuzz_entry () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.shadow_free"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LX.LxDenot.lx_opq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.P.P_pkcs7_top.pkcs7_zero"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.ATopContract.FUZZ_ENTRY"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Walk.Call.EPOST"].

(* [comment removed for export] *)
#[local] Ltac lx_shbase_norm ::=
  repeat match goal with
  | H : rw_cells ?sg ?m (al_sb ?L0 + (?X + ?k)) ?cs |- _ =>
      lazymatch k with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end;
      replace (al_sb L0 + (X + k)) with (X + al_sb L0 + k) in H by (clear; lia)
  | H : rw_cells ?sg ?m (al_sb ?L0 + ?X) ?cs |- _ => rewrite (Z.add_comm (al_sb L0) X) in H
  | |- context [Z_to_bv 64 (al_sb ?L0 + (?X + ?k))] =>
      lazymatch k with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end;
      replace (al_sb L0 + (X + k)) with (X + al_sb L0 + k) by (clear; lia)
  | |- context [Z_to_bv 64 (al_sb ?L0 + ?X)] => rewrite (Z.add_comm (al_sb L0) X)
  end.


Definition A_UAR_GOT : Z := 0x0f5ea8.      (* [comment removed for export] *)
Definition A_SMALLOC_5 : Z := 0x53710.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SFREE_5 : Z := 0x5391c.       (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SET00 : Z := 0x6b228.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_SETF8 : Z := 0x6b348.         (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_AMEMSET_F : Z := 0x68258.     (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_PKCS7_PARSE_DER : Z := 0x977a8. (* [comment removed for export] *)
Definition A_PKCS7_FREE : Z := 0x9818c.    (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM5 : arl_smalloc R 5 = A_SMALLOC_5.
  Hypothesis SF5 : arl_sfree5 R = A_SFREE_5.
  Hypothesis E00 : arl_set00 R = A_SET00.
  Hypothesis EF8 : arl_setf8 R = A_SETF8.
  Hypothesis AMS : arl_amemset R = A_AMEMSET_F.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NS2 : 0 <= arl_need_setsh R.
  Hypothesis NS3 : 0 <= arl_need_amem R.
  (* [comment removed for export] *)
  Variable P7T : Type.
  Variable p7rep : P7T -> mem -> list blk -> list blk -> Z -> Prop.
  Variable SI : sinv (arl_L R).
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (STKp : Z) (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PARSE : pkcs7_parse_der_stmtA asegs R HIA P7T p7rep SI PHIp FFRp CNTp STKp A_PKCS7_PARSE_DER.
  Hypothesis FREE : pkcs7_free_stmtA asegs R HIA P7T p7rep PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis PHIp_nn : forall n, 0 <= n -> 0 <= PHIp n.
  Hypothesis FFRp_nn : forall n d, 0 <= n -> 0 <= FFRp n d.
  Hypothesis CNTp_nn : forall n, 0 <= n -> 0 <= CNTp n.
  Variable FSTK : Z.
  Hypothesis FSp : 112 + STKp <= FSTK.
  Hypothesis FSf : 112 + STKf <= FSTK.
  Hypothesis FS1 : 128 + arl_need_smalloc R <= FSTK.
  Hypothesis FS2 : 128 + arl_need_setsh R <= FSTK.
  Hypothesis FS3 : 128 + arl_need_amem R <= FSTK.

  Section Call.
  (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (DATA n lo slo : Z) (bs : list byte).
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2^26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CR : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis D47 : n = 0 \/ DATA + n + 8 <= 2 ^ 47.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - FSTK.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 32)%nat.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_5 in SM5;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Ltac call_setsh xx pclit EPC SP1 :=
    lazymatch goal with
    | SS : sshad _ _ ?mc _ _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with
      | HHc : HM _ _ _ ?h1 ?LBc ((?FB, 2048) :: LF) mc, SP1R : 0 <= ?sp1 < 2^64, ESH : shadow_of _ (?FB + 32) = ?sv |- _ =>
        replace (Z_to_bv 64 pclit) with (Z_to_bv 64 (if Z.eqb xx 0 then arl_set00 R else if Z.eqb xx 0xf5 then arl_setf5 R else arl_setf8 R))
          by (cbn [Z.eqb Pos.eqb]; rewrite EPC; reflexivity);
        repeat match goal with P : presW _ _ _ _ _ _ _ _ _ _ mc |- _ => lazymatch type of P with ?t => change t with (hidden t) in P end end;
        let SPEC := fresh "SPEC" in
        pose proof (artA_set_shadow asegs R HIA xx) as SPEC;
        specialize SPEC with (h := h1);
        try (lazymatch goal with E : hcs _ _ _ h1 = _ |- _ => rewrite E in SPEC end);
        callrt sp1 (eapply SPEC with (LB := LBc) (LF := (FB, 2048) :: LF) (A := FB + 32) (s := sv) (n := 180) (lo := lo); clear SPEC;
                    rewrite ?(unsigned_lit sp1) by exact SP1R;
                    first [ exact HHc
                          | exact LOS
                          | reflexivity
                          | lazymatch goal with
                            | |- _ \/ _ \/ _ => first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]
                            | |- (FB + 32) mod 8 = 0 => assumption
                            | |- 0 < 180 => clear; lia
                            | |- crange _ (FB + 32) _ => match goal with C : crange _ FB 2048 |- _ => eapply crange_sub; [exact C| clear; lia| clear; lia] end
                            | |- _ = shadow_of _ _ => symmetry; exact ESH
                            | |- forall x, _ -> _ => let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; right; exists (FB, 2048); split; [left; reflexivity| cbn; clear - Hx; lia]
                            | |- rw_cells _ mc _ _ => match goal with H : rw_cells _ mc (Z.shiftr FB 3 + al_sb _ + 4) _ |- _ =>
                                   lazymatch goal with SH4 : Z.shiftr (FB + 32) 3 = _ |- _ => rewrite SH4 end;
                                   replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) by (clear; lia); exact H end
                            | |- Z.of_nat _ = 180 => cbn; reflexivity
                            | |- stk _ mc lo _ => assumption
                            | |- lo <= _ => clear - FS2 SLO NS2 SP1; lia
                            | |- crange _ lo _ => match goal with C : crange _ lo (bv_unsigned sp - lo) |- _ => eapply crange_sub; [exact C| clear; lia| clear - SP1; lia] end
                            | |- mem_inv _ mc => assumption
                            end
                          | match goal with |- ?g => idtac "SETSH-PRE-LEFT:" g end ]);
        try clear SPEC
      end
    end.

  Ltac after_setsh SP1 :=
    lazymatch goal with
    | MU : munch [(?sv, _); (lo, ?hi)] ?ma ?mb, WM : wmono _ ?ma ?mb, ESH : shadow_of _ (?FB + 32) = ?sv |- evtA _ _ _ _ (MS _ _ _ _ _ ?mb _) =>
        let MU' := fresh "MU'" in pose proof MU as MU'; rewrite <- ESH in MU';
        repeat match goal with P : hidden (presW _ _ _ _ _ _ _ _ ?Wc ?mz ma) |- _ => unfold hidden in P;
          apply (presW_munch_sh R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) Wc mz ma mb (FB + 32) 180 lo hi) in P;
          [ | exact MU' | exact WM
            | match goal with C : crange _ FB 2048 |- _ => eapply crange_sub; [exact C| clear; lia| clear; lia] end
            | assumption
            | exact LOS | clear - SP1; lia | qlia | assumption ] end;
        lazymatch goal with SS : sshad _ _ ma _ _ |- _ =>
          apply (sshad_munch_sh R HIA h ma mb (FB + 32) 180 lo hi) in SS;
          [ | exact MU' | exact WM
            | match goal with C : crange _ (arl_stklo R) _ |- _ => eapply crange_sub; [exact C| clear - SLOS; lia| qlia] end
            | assumption
            | left; qlia
            | exact LOS ] end;
        clear MU';
        (* [comment removed for export] *)
        try (lazymatch goal with H : rw_cells _ ma (Z.shiftr FB 3 + al_sb _ + 4) _ |- _ => clear H end);
        try (lazymatch goal with H : stk _ ma lo _ |- _ => clear H end);
        transport_after_call asegs ma mb MU WM;
        try (lazymatch goal with H : mem_inv _ ma |- _ => clear H end);
        try (lazymatch goal with H : HM _ _ _ _ _ _ ma |- _ => clear H end);
        try (lazymatch goal with H : wmono _ _ mb |- _ => clear H end);
        clear MU WM;
        lazymatch goal with H : rw_cells _ mb (Z.shiftr (FB + 32) 3 + al_sb _) _ |- _ =>
          lazymatch goal with SH4 : Z.shiftr (FB + 32) 3 = _ |- _ => rewrite SH4 in H end;
          replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) in H by (clear; lia);
          change (Z.to_nat 180) with 180%nat in H; rename H into SHOBJ end;
        lazymatch goal with H : HM _ _ _ _ _ _ mb |- _ => rename H into HH1 end;
        lazymatch goal with H : stk _ mb lo _ |- _ => rename H into STC end;
        lazymatch goal with H : mem_inv _ mb |- _ => rename H into MI end
    end.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8705771919.400000<S1c2lq2hq2Hc". (* [comment removed for export] *)
  Lemma lx_opq_presW_cs : ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry ()) "PCS',P,$0.SpPh0,(1.$2.VR,VHIA,)PLB0,(3.$4.)PLF0,(3.$4.)PSP,$0.PSSP,$0.PW,(3.$5.)Pm0,P,(6.&40.)(7.(6.&8.))POK,(3.(8.$0.$0.))PSH,(3.(8.$0.$0.))Pmq,P,(6.&40.)(7.(6.&8.))P,(9.$2.VR,VHIA,R:.R9.R8.R7.R6.R5.R4.R1.)P,(:.(;.(<.VR,))R8.)P,(=.(8.$0.$0.)Liv,(8.$0.$0.)(>.(?.VR,R<.R;.R:.R8.(10.$0.$0.R1.)(11.(12.$0.$0.R1.)(10.$0.$0.R1.)))(13.(14.$2.VR,VHIA,R=.)(10.$0.$0.R1.)(11.(12.$0.$0.R1.)(10.$0.$0.R1.))))R5.)P,(=.(8.$0.$0.)Liv,(8.$0.$0.)(>.(15.$0.(16.(10.$0.$0.R1.)+8.)=)(>.(15.$0.(16.(12.$0.$0.R1.)+8.)=)(>.(13.(14.$2.VR,VHIA,R>.)(10.$0.$0.R1.)(11.(12.$0.$0.R1.)(10.$0.$0.R1.)))(17.VR,R=.R<.R:.(18.$2.VR,VHIA,R>.)(10.$0.$0.R1.)(11.(12.$0.$0.R1.)(10.$0.$0.R1.))))))R5.)(19.$2.(1:.VR,)R?.Lmx,P,(6.&40.)(7.(6.&8.))(9.$2.VR,VHIA,R?.R>.R=.R<.R;.R:.R9.R1.)R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros CS' h0 LB0 LF0 SP SSP W m0 OK SH mq HP HSP HOK HSH.
    pose proof (lx_opq_presW R HIA h0 LB0 LF0 SP SSP W m0 OK SH mq HP HSP HOK HSH) as X.
    split; [exact HP|]. intros W' m1 m2 P1 MU WM FA. apply (proj2 X W' m1 m2 P1 MU WM).
    eapply Forall_impl; [| exact FA]. intros iv [A|A]; [left; exact A| right].
    intros a Ha. destruct (A a Ha) as (c & lq & hq & Hin & Hc & _ & E). exists c, lq, hq.
    split; [exact Hin|]. split; [exact Hc|]. split; [| exact E].
    rewrite Forall_forall in HSH. destruct (HSH (lq, hq) Hin) as (_ & _ & CRq & _). apply CRq. cbn [fst snd]. clear - Hc; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[local] Ltac lxr_pose_presW ::=
    let mx := lxr_cur_mem in
    repeat match goal with
    | HP : presW ?segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 mx |- _ =>
        let AL := lxr_goal_al in let CS := lxr_goal_cs in
        lazymatch goal with
        | _ : lx_opq _ _ _ (fun m => presW segs R HIA h LB LF SP SSP W m0 m) _ _ mx |- _ => fail
        | |- _ => idtac
        end;
        let L := constr:(arl_L R) in
        let CSh := constr:(hcs segs R HIA h) in
        let SHI := constr:(hstkhi segs R HIA h) in
        let cands := lxr_cw_list L constr:([(arl_stklo R, SP)] : list ivl) in
        let cands := lxr_in_list cands in
        let shc := lxr_sf_list R constr:(@nil ivl) in
        let shc := lxr_crfb_list shc in
        lxr_filter cands ltac:(fun lo hi => constr:(wcover R LB LF SP W lo (hi - lo) /\ crange CSh lo (hi - lo)))
          ltac:(split; [ solve_wcover | solve_crange ])
          ltac:(fun ok =>
            lxr_filter shc ltac:(fun lo hi => constr:(lo mod 8 = 0 /\ hi mod 8 = 0 /\ crange CSh lo (hi - lo) /\ shadow_free R LB LF SSP SHI lo (hi - lo)))
              ltac:(split; [ lxr_lia | split; [ lxr_lia | split; [ solve_crange
                      | first [ assumption | eapply shadow_free_sub; [ eassumption | lxr_lia | lxr_lia ]
                              | eapply shadow_free_of_fresh'; [ eassumption | eassumption | eassumption | lxr_lia | lxr_lia | lxr_lia ]
                              | eapply shadow_free_fresh; [ eassumption | destruct HP as (_ & _ & _ & K); exact K | lxr_lia | lxr_lia | lxr_lia
                                                          | first [ assumption | eapply hm_fresh_frame_apart; eassumption ] ] ] ] ] ])
              ltac:(fun sh =>
                let H := fresh "OQP" in
                assert (H : lx_opq segs AL CS (fun m => presW segs R HIA h LB LF SP SSP W m0 m) ok sh mx);
                [ apply (lx_opq_presW_cs CS h LB LF SP SSP W m0 ok sh mx HP); [ lxr_lia | lxr_forall_okw | lxr_forall_okw ] | ]));
        lxr_clear_okw
    end.

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry ()) "Lms,$1;.(1<.$0.LFB,$0.(1<.$0.Lsp1,$0.(1<.(1.$2.VR,VHIA,)Lh1,(1.$2.VR,VHIA,)(1<.P,(6.&40.)(7.(6.&8.))Lm1,P,(6.&40.)(7.(6.&8.))(1<.(6.&40.)Lt0,(6.&40.)(1<.(6.&40.)Lt1,(6.&40.)(1<.(6.&40.)Lt2,(6.&40.)(1<.(6.&40.)La0,(6.&40.)(1<.(6.&40.)La1,(6.&40.)(1<.(6.&40.)La2,(6.&40.)(1<.(6.&40.)La3,(6.&40.)(1<.(6.&40.)La4,(6.&40.)(1<.(6.&40.)La5,(6.&40.)(1<.(6.&40.)La6,(6.&40.)(1<.(6.&40.)La7,(6.&40.)(1<.(6.&40.)Lt3,(6.&40.)(1<.(6.&40.)Lt4,(6.&40.)(1<.(6.&40.)Lt5,(6.&40.)(1<.(6.&40.)Lt6,(6.&40.)(1<.(6.&40.)Lw0,(6.&40.)(1<.(6.&40.)Lw1,(6.&40.)(1<.(6.&40.)Lw2,(6.&40.)(1<.(6.&40.)Ljw,(6.&40.)(1<.(3.$1=.)Lc1,(3.$1=.)(1<.(3.$1=.)Lc3,(3.$1=.)(>.(15.$1;.R1:.(1>.(1?.(20.&40.+976<8.)(20.&40.R18.)Vgp,Vtp,R15.R14.R13.Vsp,(20.&40.R18.)R12.R11.R10.R?.R>.R=.R<.R;.(20.&40.R19.)(20.&40.Vn,)(20.&40.VDATA,)(20.&40.(21.(22.R19.+3.)(23.(1:.VR,))))(20.&40.(21.R19.+20.))(20.&40.(21.(21.(22.R19.+3.)(23.(1:.VR,)))+4.))(20.&40.R19.)Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(20.&40.+976<8.)Vfc,(24.(6.&40.))R16.(25.$2.)))(>.(>.(:.(11.(26.&40.Vsp,)+70.)R18.)(:.R18.(11.(26.&40.Vsp,)+60.)))(>.(15.$0.(16.R18.+20.)=)(>.(27.$2.VR,VHIA,R17.VLB,(28.(8.$0.$0.)(29.$0.$0.R19.+800.)VLF,)R16.)(>.(15.P,$0.Sp(14.$2.VR,VHIA,R17.)(14.$2.VR,VHIA,Vh,))(>.(15.$0.(2:.$2.VR,VHIA,R17.)(2:.$2.VR,VHIA,Vh,))(>.(15.$0.(18.$2.VR,VHIA,R17.)(18.$2.VR,VHIA,Vh,))(>.(15.$0.(2;.$2.VR,VHIA,R17.)(2;.$2.VR,VHIA,Vh,))(>.(15.$0.(2<.$2.VR,VHIA,R17.)(2<.$2.VR,VHIA,Vh,))(>.(15.$0.(2=.$2.VR,VHIA,R17.)(2=.$2.VR,VHIA,Vh,))(>.Pmo,$2>.(2?.(30.$2.VR,VHIA,R18.R1.)(30.$2.VR,VHIA,Vh,R1.))(>.(15.$0.(16.R19.+40.)=)(>.(31.VR,VLB,VLF,R19.+800.)(>.(32.$2.R16.R19.(28.$1=.(33.R6.)(28.$1=.(33.R5.)(28.$1=.(33.R4.)(34.$1=.)))))(>.(35.$2.R16.(21.R19.+20.))(>.(32.$2.R16.(21.(22.R19.+3.)(23.(1:.VR,)))R2.)(>.(15.$36.(37.R2.)#4.)(>.(32.$2.R16.(21.(21.(22.R19.+3.)(23.(1:.VR,)))+4.)(28.$1=.(38.#;4.(39.(6.&8.)(20.&8.=)#;4.))(34.$1=.)))(>.(32.$2.R16.(21.(21.(22.R19.+3.)(23.(1:.VR,)))+;8.)R1.)(>.(15.$36.(37.R1.)#48.)(>.(32.$2.R16.(21.(26.&40.Vsp,)-50.)(28.$1=.(33.Vs8,)(28.$1=.(33.Vs7,)(28.$1=.(33.Vs6,)(28.$1=.(33.Vs5,)(28.$1=.(33.Vs4,)(28.$1=.(33.Vs3,)(28.$1=.(33.Vs2,)(28.$1=.(33.Vs1,)(28.$1=.(33.Vs0,)(28.$1=.(33.Vra,)(34.$1=.))))))))))))(>.(32.$2.R16.(21.R18.+8.)(28.$1=.(33.R3.)(34.$1=.)))(>.(3:.$2.R16.R18.(21.R18.+8.))(>.(3:.$2.R16.(21.R18.+10.)(21.(26.&40.Vsp,)-50.))(>.(3:.$2.R16.Vlo,R18.)(>.(3;.$2.R16.)(>.(9.$2.VR,VHIA,Vh,VLB,VLF,(26.&40.Vsp,)(26.&40.Vsp,)(34.$5.)Vm,R16.)(3<.$2.(1:.VR,)R16.Vslo,(26.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 D47; try lx_pin1 DLO; try lx_pin1 CR; try lx_pin1 HD; try lx_pin1 Hn; try lx_pin1 LEN; try lx_pin1 mo0; try lx_pin1 FSf; try lx_pin1 FSp; try lx_pin1 CNTp_nn; try lx_pin1 FFRp_nn; try lx_pin1 PHIp_nn; try lx_pin1 FFRf_mono; try lx_pin1 PHIf_mono; try lx_pin1 FREE; try lx_pin1 PARSE; try lx_pin1 STKf; try lx_pin1 FFRf; try lx_pin1 PHIf; try lx_pin1 STKp; try lx_pin1 CNTp; try lx_pin1 FFRp; try lx_pin1 PHIp; try lx_pin1 SI; try lx_pin1 p7rep; try lx_pin1 P7T; try lx_pin1 SF5.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "05=0@C17025492443.236D18607476203.125D2457516971.236 D2457697674.165 D29720839482.218D32458870384.236D32458983505.165D32604263315.166D3388433174.164 D41348268325.236D45645629287.236D45646004550.165D45704792743.164D50254960491.126D558665111.92   D55889817356.218D58077997354.126D60109446735.236D62009822325.92 D62011770184.166D68411603285.164D6899542864.164 K30929880107.236K31906528703.236K34467384107.236K36467192360.199K36467192360.216K42335913047.199K42335913047.216K45234819947.236L10596430123.1  L11146046184.1  L11391744879.229L12374178246.3  L13176305223.2  L1358641953.0   L14023416440.213L1540877545.3   L15504783446.150L16203338365.149L16255647091.169L16255647091.170L16410638007.23 L1676958453.148 L1685717371.0   L17398130420.1  L18221343941.3  L18655829980.3  L1910219380.2   L19546883928.149L19685319514.155L19713007734.150L19980016842.12 L2073184050.2   L21101670104.1  L21175742071.23 L21866712442.2  L22941438733.2  L24222075072.2  L25006580377.12 L2503300556.16  L25225054747.2  L25393907176.2  L26562537082.4  L28442596129.0  L28711237604.1  L28728318391.229L29022582655.1  L29738741675.1  L30925983677.2  L31115668968.3  L3156381960.213 L3156381960.229 L31893714473.2  L32454903270.1  L32456886356.144L32879090465.0  L32955242219.9  L33211686944.3  L33472729358.96 L33483560980.13 L33485826452.1  L3426150492.4   L34471870653.2  L35082543424.3  L35251190322.2  L35747972712.1  L36180999398.113L3624015310.2   L36373763625.2  L36446756958.4  L36451124775.4  L36462705086.2  L38088130474.3  L38235734261.1  L3876079316.9   L38903380038.3  L39188636933.0  L40316771656.2  L40367315145.3  L40488651187.2  L41406233680.3  L42340405185.2  L42439184590.3  L43055154860.111L43139178913.0  L43188064477.2  L43300649301.0  L43594773695.147L4373974455.23  L43882045675.4  L44022686142.2  L44077533344.2  L45247174909.2  L46605021561.4  L48117620900.143L48117620911.82 L48119718060.145L48132302231.166L48132467214.12 L49278698542.2  L49292959576.229L49317467472.1  L5000624338.4   L50790731766.11 L5153599366.2   L52118767162.4  L52602698868.2  L5284251404.2   L52944289203.3  L53852861162.144L54304703026.2  L5460295853.7   L54629377307.24 L54946823284.2  L54978688591.230L55588686165.0  L56854270298.93 L57241361229.212L57355539152.136L57387013391.2  L57573747506.231L58077947066.156L58790154276.12 L58790154276.9  L59081452805.3  L59308634497.16 L61437265048.2  L62870069330.3  L6438639736.12  L64657763020.4  L64787780871.1  L65118959387.2  L65935405590.3  L66151427842.16 L66439959418.4  L67412691327.1  L68317847161.4  L68407455972.143L68411655279.143L68442042496.1  L6912107233.143 L7040749983.94  L7049614941.3   L7192656114.9   L8071213206.143 L8265267294.0   L881835912.0    L9080220944.4   L9356559645.16  L9536947392.214 L9787245214.2   O11167175439.236O12422637294.199O12422637294.216O12422637294.236O15317411454.199O15317411454.216O15463198269.199O15463198269.216O16355324352.236O17025492443.236O1803266184.199 O1803266184.216 O24330317025.236O25520546989.236O2956297756.236 O32137156502.199O32137156502.216O33055229292.199O33055229292.216O34900054049.236O40095405918.235O424351700.236  O44961257137.199O44961257137.216O49701823576.235O51899033324.199O51899033324.216O54909507456.199O54909507456.216O54909507456.236O56414299794.199O56414299794.216O58922430686.236O59625529265.199O59625529265.216O59625529265.236O62039387105.236O63308119680.199O63308119680.216O63308119680.236O63908043916.236P18234093395.199P18234093395.216P18643473482.236P21870859916.218P22945712379.218P24217518934.236P26567093740.236P31111702142.199P31111702142.216P35094833878.235P3639265129.236 P36447292849.199P36447292849.216P36450659272.236P40332238735.218P40379732831.236P40492483109.236P41419110342.199P41419110342.216P44009876008.236P46592801519.199P46592801519.216P5012910916.199 P5012910916.216 P52114279852.236P5271375002.235 P52940256805.199P52940256805.216P59079901090.236P62874495940.199P62874495940.216P65949573297.199P65949573297.216P66452773100.236P68330067439.199P68330067439.216Q10533598597.94 Q10592386193.171Q10592533181.236Q10594483353.173Q11561470152.218Q1530342990.126 Q15766564435.236Q22712450012.218Q23937998252.94 Q23937998260.96 Q2513790033.216 Q25513505925.217Q26630670972.214Q26634504698.230Q31021924279.124Q32440833928.170Q35653441506.106Q36068443607.202Q36068443607.219Q38248387216.236Q38248895671.97 Q40271359350.126Q40412085704.218Q42388231288.218Q42437284299.197Q42439168719.124Q42439168719.236Q42439382249.98 Q42439443119.218Q42441479407.178Q43879899724.236Q43880146027.97 Q45720570503.217Q47241206720.94 Q47811973384.218Q48117620903.171Q48118064779.236Q48132270006.202Q48132270006.219Q48132302231.170Q49698585326.216Q50796826103.126Q50840533351.236Q54967541497.218Q56530976407.236Q56531220667.171Q56820930456.236Q56821109172.171Q56823206332.173Q59310664043.170Q59310664043.94 Q59321150555.171Q59321350679.218Q59321559671.236Q59865321072.218Q59865520182.98 Q59865603600.236Q59867617328.178Q59871812884.197Q60109315147.106Q60993511497.214Q60997411791.230Q6192914196.124 Q62022254700.96 Q62022254708.94 Q64681502662.178Q64683599808.98 Q64683667846.218Q64683942374.236Q64685695714.197Q64685727963.202Q64685727963.219Q66954699982.218Q6897428426.175 Q6897428434.170 Q6912046254.218 Q6912107233.172 Q8071213206.172 Q8085894565.170 Q8085894589.175 Q9080751600.215 Q9350270635.180 Q9350270635.197 Q9350548487.107 00000100200300401D01e02F03003104504V05705X05Y05l07K07g08Q08^09A09B09c0:?0:[0;70;S0;o0<K0<g0=C0=G0=K0=n0>90>A0>B0>c0>o0?Z0@E0@k0AQ0B70Be0Bf0Bj0Bk0Bl0C20C]0D80Dd0E<0EB0EG0Em0En0Eo0F00F10Fd0Fj0G00G10G20G60Gd0Gi0Gm0Gn0Go0HP0I10I20I60IL0IM0Ik0J60J70J80J90JF0JG0JH0JN0JR0J`0Ja0Jg0Jh0Ji0Jj0K40K80KZ0Kf0Kg0Kh0Ki0Kj0Kk0Kl0L80Lh0Li0M10M20M`0NF0NU0NV0N^0N_0N`0Od0PW0Q[0R_0SK0SS0T40T80T90TW0T_0T`0Tf0Tg0Th0U>0UD0U\0VD0VJ0WL0WM0X40Y60Y70Y>0Y_0Z>0Z\0[:0[;0[N0[V0[W0[X0[h0[l0\20\30\M0\N0\S0\T0\U0\V0\Z0]00]K0]V0]j0^@0^A0^B0^Q0_C0_d0_j0_k0_l0_m0_n0_o0`00`10`20`30`40`50`60`70`80`90`:0`;0`<0`=0`>0`?0`@0`A0`B0`C0`D0`E0`F0`G0`H0`I0`J0`K0`L0`M0`N0`O0`P0`Q0`R0`S0a\0be0cR0e00fN0g]0hL0i]0jn0l=0l>0lm0m\0nK0o;0oh10o11\12I13X14G15616G17X18G19V1:C1;01;T1<e1>61>Z1?>1?m1@\1AK1AX1An1BD1BZ1CC1C[1DA1E11EM1E]1G11Gd1HH1Hl1IM1IN1J01J[1KF1K_1Kj1L?1Lh1NC1Nd1O<1O]1P01Pd1QE1Qi1R71S@1SN1T71U;1V?1WC1XG1YK1Z21Zf1[J1\31\41\51\K1\a1]71]81]91]:1];1]<1]=1]>1]?1]@1]A1]U1^O1_I1_Z1_d1_n1`_1a?1bC1c41ce1dV1eG1f01fF1f\1gE1g[1h11hG1h]1i:1i\1j>1jWFFFFS1R3HIA1h2LF2sp3TOP3LFB3SPR3sp13H163SP14LFB'2h15Ehtop2FB2pj2F02LJ2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS1R3HIA2LF2sp3LFB3sp13H164LFB'2h12FB2pj2LJFS1R3HIA1h2LF2sp2lo3TOP3LFB3SPR3sp13H163SP14LFB'2h15Ehtop2FB2pj2F02LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJFS1R3HIA1h2LF2sp3LFBS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3SPR3sp13H163SP14LFB'2FB2pj2F02LJ2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H143H164LFB'S1R2LF2sp2lo3LFB3LOS3sp13H164LFB'2FB2pj2LJS1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H164LFB'2FB2pj2LJFS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS1R2LF3LFB4LFB'2FB2pj3APS2LJS2FBS2FBS1R2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2FB3x292HxS2lo3sp1SS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2sp3sp13SP1S2LF2sp3LFB3SPR3sp13H164LFB'2FB2pj2F02F82LJS2LF2sp3LFB3SPR3sp13H164LFB'2FB2pj2F02F82LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJ1c2HcS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJ1c2HcS2FB2r13F641q1r1H2H02q02r02H42H52q12H9S1R2LF2sp3slo4SLOS3LFB3ALO4LFB'2FB2pj2F02F12LJSS2FBFFS1R2FBS2LF2sp3LFB3SPR3sp13H164LFB'2FB2pj2F02F82LJS2LF2sp3LFB3sp13H164LFB'2FBS2LF2sp3LFB3SPR3sp13H164LFB'2FB2pj2F03F8'2LJS1R3HIA1h2sp3TOP3sp13SP1S1R2FBS3sp1S2FB2r13F641q1r1H2H02q02r02H42H52q12H9FFFSS1R3NS14FSTK3FS12sp2lo3SLO3LOS3ALO3ACV3sp13SP14SP1RS1R2FBS1R2FBFSS2FBS1R2LF2sp3LFB3SPR3sp13H164LFB'2FB2pj2F03ESH2LJS3sp1S2FBFFS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2LF2sp3LFB3sp13H164LFB'2FB2pj2LJFS2FBS2LF3LFB4LFB'2FB2pj2LJSS1R4FSTK3FS32sp2lo3SLO3sp13SP1S2sp2lo3sp1FFFS1R3ACV2FB2F1FFS1R2FBS2FBS2LF2sp2bs3LFBFS1R2FBFFFS2FB2x22HxS2loS1R3NS14FSTK3FS12sp2lo3SLO3sp13SP1S2sp3sp13SP1SFFFFFS1R3slo4SLOSS1R3NS13NS24FSTK3FS13FS22LF2sp2lo2bs3SLO3LFB3SPRSS2lo3sp1SS1R2LF2sp3slo4SLOS3LFB3ALO4LFB'2FB2pj2F02F12LJS2FB2r13F641q1r1H2H02q02r02H42H52q12H9S2sp2lo3sp13SP1FS2lo3sp1FFS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALOS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS14FSTK3FS12sp2lo3slo4SLOS4SLOL3SLO3ALOS2lo3sp1S2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2FBFS1R3NS14FSTK3FS12sp2lo3SLO3LOSS2lo3sp1FS1R2FBFFS2LF3LFB4LFB'2FB2pj2LJS1R2FBS1R3HIA1h2sp3TOP3sp13SP1S1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9S1R2FBS1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB3SPR3sp13H163SP14LFB'2FB2pj2F02LJSS2LF2sp3SPA3LFB3SPR3sp13H123H133H143H16S1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB3SPR3sp13H163SP14LFB'2FB2pj2F02LJFS2FB2F0S2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS2LF2sp3LFB3sp13H143H164LFB'2FBS1R4FSTK3FS12sp2lo3SLO3sp13SP1S1R4FSTK3FS22sp2lo3SLO3sp13SP1FS1R3ACV2FB2F02F12KbS2LF3LFBFSS1R2FB4SBlo4SBhiS2spS1R2FBFS2FB2r03F641q1r1H2H02q02H4FS3sp1FFFS2FBS2LF3LFB4LFB'2FB2pj2LJS2LF2sp3LFB3SPR3sp13H123H16S2sp2lo3sp1S1R2lo3LOS3ALO2FB2F1S2LF3LFB4LFB'2FB2pj2LJSSS2sp2lo3sp13SP1S1R3NS14FSTK3FS12sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S2LF2sp3LFB3sp13H164LFB'2FB2pj2LJS1R2FBFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F04SBND2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJ2HB5Ha_st5Hl_stS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJ2HB5Ha_st5Hl_stS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJFS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS2LF2sp3LFB3sp13H144LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R3NS14FSTK3FS12LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS1R3NS14FSTK3FS12LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F02F12LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F04SBND2LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2lo3LFB3LOS3ALO3sp14LFB'2FB2pj2F04SBND2LJS1R2LF2sp3LFBS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS2LF2sp3LFB3sp13H144LFB'S1R2LF2lo3LFB3LOS3ALO4LFB'2FB2pj2F02LJS2LF2sp3LFB3sp13H144LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3lxh3sp13H153SP14LFB'2FB2pj2F02LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS1R3HIA1h2LF2sp3TOP3LFB4HTOP4LFB'FS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS1R2LF3slo4SLOS3LFB3ALO4LFB'2FB2pj2F02F12LJS1R2LF3slo4SLOS3LFB3ALO4LFB'2FB2pj2F02F12LJS2LF2lo3LFB4LFB'2FB2pj2LJS2LF2lo3LFBS1R3HIA1h2LF3LFB4LFB'S2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO3sp13SP14LFB'2FB2pj2F02LJ2HB5Ha_st5Hl_stS1R2LF3slo4SLOS3LFB4LFB'2FB2pj2LJS1R2LF3slo4SLOS3LFB4LFB'S1R2LF3slo4SLOS3LFB4LFB'2FB2pj2LJS1R2LF3slo4SLOS3LFBS1R2LF3slo4SLOS3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS1R2LF3slo4SLOS3LFB4LFB'2FB2pj2LJS2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS2LF2sp2lo3LFBS1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB3sp13SP14LFB'2FB2pj2F02LJ2HB5Ha_st5Hl_stS1R2LF3LFB3ALOS2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3slo4SLOS4SLOL3SLO3LFB3ALO4LFB'2FB2pj2F02LJS2LF3LFB3sp13H154LFB'2FB2pj2LJ2HB5Ha_stS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB4LFB'S2LF2sp2lo3LFB3sp13H144LFB'2FB2pj2LJS2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stFFS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJFFFFFFFFFFS1R2LF2lo2bs3LFB3LOSS1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB3sp13SP14LFB'2FB2pj2F02LJS1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB3sp13SP14LFB'2FB2pj2F02LJS2LF3LFB3sp14LFB'S1R2LF3LFBS1R2LF3LFBS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP4LFB'2FB2pj2F02LJS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOPS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP3sp14LFB'2FB2pj2F02LJ2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP4LFB'2FB2pj2F02LJS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP4LFB'2FB2pj2F02LJS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP4LFB'2FB2pj2F02LJS1R3HIA1h2LF2sp3slo3TOP3LFB4HTOP4LFB'2FB2pj2F02LJS2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB3sp14LFB'2FB2pj2LJ2HB5Ha_st5Hl_stS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB4LFB'2FB2pj2LJS2LF3LFB3sp14LFB'2FB2pj2LJ2HBS2LF3LFB3sp13H153H164LFB'2FB2pj2LJS2LF3LFB3sp13H153H164LFB'2FB2pj2LJS2LF3LFB3sp13H153H164LFB'". (* [comment removed for export] *)
  #[using="LOS LFB TPV SPH SPA TOP SLO SLOL SLOS bs FS3 FS2 FS1 FSTK NS3 NS2 NS1 AMS EF8 E00 SM5 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry ()) "Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)P,(27.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3:.$2.Vm,Vlo,(26.&40.Vsp,))P,(3<.$2.(1:.VR,)Vm,Vslo,(26.&40.Vsp,))P,(3;.$2.Vm,)(3=.$2.(1:.VR,)(14.$2.VR,VHIA,Vh,)$3>.(1>.(1?.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(20.&40.VDATA,)(20.&40.Vn,)R>.R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(20.&40.$3?.)Vfc,(24.(6.&40.))Vm,(25.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST SS MI.
  unfold FUZZ_ENTRY.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(first [ clear - LOS SLO FS1 NS1; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x53710] [] 136%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV FS1 NS1; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(first [ clear - SP1 SLO FS1 NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 341776) with (Z_to_bv 64 (arl_smalloc R 5)) by (rewrite SM5; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 5) with (lo := lo) (sz := 1600); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - FS1 SLO SP1 TOP NS1; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      try clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      try clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; destruct FRSH as (F0 & F1 & _); first [ clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]].
      try clear Kb.
      change (64 * 2 ^ 5) with 2048 in *. change (8 * 2 ^ 5) with 256 in FSH. change (Z.to_nat 2048) with 2048%nat in FRM. change (Z.to_nat 256) with 256%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      assert (INF : In (FB, 2048) ((FB, 2048) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 2048 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 2008) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
      pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m3 FB 2048 HH1) as AP.
      assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      assert (F8' : (FB + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      assert (SHFREE : shadow_free R LB LF (bv_unsigned sp) (hstkhi asegs R HIA h) (FB + 32) (8 * 180)).
      { eapply shadow_free_fresh; [exact FRSH| exact (proj1 WL)| clear; lia| clear; lia| first [ clear - ALO LOS SLO FS1 NS1; lia | lx_side_lia ]| exact AP]. }
      pose proof (art_stk_high asegs R HIA) as STKH.
      assert (SH4 : Z.shiftr (FB + 32) 3 = Z.shiftr FB 3 + 4) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
      assert (SH184 : Z.shiftr (FB + 1472) 3 = Z.shiftr FB 3 + 184) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
      assert (SH200 : Z.shiftr (FB + 1600) 3 = Z.shiftr FB 3 + 200) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
      assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
      assert (ESH : shadow_of AL (FB + 32) = Z.shiftr FB 3 + al_sb AL + 4) by (unfold shadow_of; rewrite SHFB; clear - F64; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      pose proof (apart_shadow_client AL CS FB 2048 FB (shadow_of AL FB) 256 CSOK CFB CFB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as APS.
      unfold shadow_of in APS. rewrite <- SHFB in APS.
      pose proof (hcs_shadow_band asegs R HIA h FB (CFB FB ltac:(clear; lia))) as SBlo. pose proof (hcs_shadow_band asegs R HIA h (FB + 8 * 255) (CFB (FB + 8 * 255) ltac:(clear; lia))) as SBhi.
      rewrite shadow_of_plus in SBhi. unfold shadow_of in SBlo, SBhi. rewrite <- SHFB in SBlo, SBhi.
      assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 256 <= alloc_ceiling) by (first [ clear - SBlo SBhi; lia | lx_side_lia ]). clear SBlo SBhi.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa STx (bv_unsigned sp + -80); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 16) (bv_unsigned sp + -80) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 16) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 16 - Z.of_nat 8) with (sp1 + 8) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 2048 junkf [] [8; 8; 8; 8; 1440; 576]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      (* [comment removed for export] *)
      lazymatch type of FRM with rw_cells _ _ _ [_; _; _; _; CB 1440 ?j; CB 576 ?r] =>
        remember j as pj eqn:EJ; clear EJ; remember r as pjr eqn:EJR; clear EJR end.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat P7C FREST.
      replace (FB + 24 + 8) with (FB + 32) in P7C by (clear; lia). clear FLNK FREST. clear pjr.
      assert (LJ : length pj = 1440%nat) by (destruct P7C as [[W _] _]; cbn in W; exact (proj1 W)).
      cb8_to_c8 FHD (@nil cell).
      (* [comment removed for export] *)
      change 256%nat with (4 + (180 + (16 + 56)))%nat in FSH. rewrite !zcells_app in FSH.
      apply rw_cells_app in FSH. destruct FSH as [SHF1 FSH1]. rewrite cells_size_zcells in FSH1.
      apply rw_cells_app in FSH1. destruct FSH1 as [SHOBJ FSH2]. rewrite cells_size_zcells in FSH2.
      apply rw_cells_app in FSH2. destruct FSH2 as [SHF3 SHREST]. rewrite cells_size_zcells in SHREST.
      change (Z.of_nat 4) with 4 in SHOBJ, SHF3, SHREST. change (Z.of_nat 180) with 180 in SHF3, SHREST. change (Z.of_nat 16) with 16 in SHREST.
      replace (Z.shiftr FB 3 + al_sb AL + 4 + 180) with (Z.shiftr FB 3 + al_sb AL + 184) in SHF3, SHREST by (clear; lia).
      replace (Z.shiftr FB 3 + al_sb AL + 184 + 16) with (Z.shiftr FB 3 + al_sb AL + 200) in SHREST by (clear; lia).
      cbn [zcells] in SHF1, SHF3.
      apply zcells_CB in SHOBJ; [| clear; lia]. apply zcells_CB in SHREST; [| clear; lia].
  (* [comment removed for export] *)
  idtac "HDR-STORES".
  idtac "SB-STORES".
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x6b348] [] 136%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  call_setsh 0xf8 439112 EF8 SP1. 1: { rewrite ESH. reflexivity. }
  after_setsh SP1.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0x6b228] [] 136%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  call_setsh 0 438824 E00 SP1. 1: { rewrite ESH. reflexivity. }
  after_setsh SP1.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. carve_frame 16%nat STC. zstep. zstep. zstep. zstep.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
      assert (OBJ : aobj asegs AL CS m5 (FB + 32) (8 * Z.of_nat 180)).
      { eapply (aobj_of_zshadow asegs AL CS m5 (FB + 32) 180 CSOK); [| eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | first [ clear - F0; lia | lx_side_lia ]].
        rewrite SH4. replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) by (clear; lia). exact SHOBJ. }
      change (8 * Z.of_nat 180) with 1440 in OBJ.
      apply (u8arr_of_rw_cells asegs) in P7C.
      (* [comment removed for export] *)
      replace (Z.shiftr FB 3 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 0) in SHF1 by (clear; lia).
      replace (Z_to_bv 64 426584) with (Z_to_bv 64 (arl_amemset R)) by (rewrite AMS; reflexivity).
      pose proof (artA_amemset asegs R HIA (arl_amemset R)) as SPM. specialize SPM with (h := h1). rewrite Ehcs, Ehtop in SPM.
      callrt (sp1 + -16) (eapply SPM with (LB := LB) (LF := (FB, 2048) :: LF) (DST := FB + 32) (v := 0) (n := 1440) (lo := lo) (ds := pj); clear SPM;
         rewrite ?(unsigned_lit (sp1 + -16)) by (first [ clear - SP1R SP1 SLO LOS ALO ACV FS1 NS1; lia | lx_side_lia ]);
         first [ exact HH1 | exact P7C | exact OBJ | exact LOS | reflexivity
               | lazymatch goal with
                 | |- _ = arl_amemset R \/ _ => left; reflexivity
                 | |- Z.of_nat (length pj) = 1440 => rewrite LJ; reflexivity
                 | |- 0 <= 0 < 256 => clear; lia
                 | |- stk _ m5 lo _ => assumption
                 | |- lo <= _ => first [ clear - FS3 SLO NS3 SP1; lia | lx_side_lia ]
                 | |- crange _ lo _ => eapply crange_sub; [exact SCS| clear; lia| first [ clear - SP1; lia | lx_side_lia ]]
                 | |- mem_inv _ m5 => assumption
                 | |- FB + 32 + 1440 <= lo \/ _ => left; first [ clear - F1 ALO LOS; lia | lx_side_lia ]
                 | |- 1440 = 0 \/ _ => right; first [ clear - F1 ACV; lia | lx_side_lia ]
                 | |- 1440 < _ => clear; lia
                 | |- client_wrange _ _ _ _ _ _ => eapply client_wrange_block; [exact IND| clear; lia| clear; lia]
                 | |- _ <= htop _ _ _ _ => first [ clear - SP1 TOP; lia | lx_side_lia ]
                 end
               | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MEMSET-LEFT:" g end.
      try clear SPM.
      lazymatch goal with MU : munch _ m5 ?mb, WM : wmono _ m5 ?mb |- _ =>
        clear P7C OBJ; transport_after_callA asegs m5 mb MU; transport_after_call asegs m5 mb MU WM;
        try (lazymatch goal with H : mem_inv _ m5 |- _ => clear H end); clear MU WM; rename mb into m6 end.
      lazymatch goal with H : u8arr _ m6 (FB + 32) _ |- _ => apply (rw_cells_of_u8arr asegs) in H; rewrite repeat_length in H; change (Z.to_nat 1440) with 1440%nat in H; rename H into P7Z end.
      lazymatch goal with H : ?x = Z_to_bv 64 (FB + 32) |- _ => subst x end.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with FRw : rw_cells _ ?mc (sp1 + -16) _, STw : stk _ ?mc lo (sp1 + -16) |- _ => release_frame FRw STw sp1 end.
  apply evtA_done. unfold S1P.
      exists FB, sp1, h1, m6. do 15 eexists. eexists _, _, _, _, _, _.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact P7Z|].
      split; [rewrite Z.add_0_r in SHF1; exact SHF1|]. split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]. split; [exact SHOBJ|].
      split.
      { chunk_join SHF3 SHREST SH3R. exact SH3R. }
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES|]. exact SS.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LB3 : list blk) (m0 m2x : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry ()) "Lms,$1;.(1<.P,(6.&40.)(7.(6.&8.))Lm',P,(6.&40.)(7.(6.&8.))(1<.(1.$2.VR,VHIA,)Lh4,(1.$2.VR,VHIA,)(1<.(6.&40.)Lt0,(6.&40.)(1<.(6.&40.)Lt1,(6.&40.)(1<.(6.&40.)Lt2,(6.&40.)(1<.(6.&40.)La1,(6.&40.)(1<.(6.&40.)La2,(6.&40.)(1<.(6.&40.)La3,(6.&40.)(1<.(6.&40.)La4,(6.&40.)(1<.(6.&40.)La5,(6.&40.)(1<.(6.&40.)La6,(6.&40.)(1<.(6.&40.)La7,(6.&40.)(1<.(6.&40.)Lt3,(6.&40.)(1<.(6.&40.)Lt4,(6.&40.)(1<.(6.&40.)Lt5,(6.&40.)(1<.(6.&40.)Lt6,(6.&40.)(>.(15.$1;.R11.(1>.(1?.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(20.&40.=)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(40.Vra,)Vfc,(24.(6.&40.))R10.(25.$2.)))(>.(3;.$2.R10.)(>.(3:.$2.R10.Vlo,(26.&40.Vsp,))(>.(3<.$2.(1:.VR,)R10.Vslo,(26.&40.Vsp,))(>.(9.$2.VR,VHIA,Vh,VLB,VLF,(26.&40.Vsp,)(26.&40.Vsp,)(41.(<.VR,)VSI,)O2.R10.)(>.(9.$2.VR,VHIA,Vh,VLB,VLF,(26.&40.Vsp,)(26.&40.Vsp,)(34.$5.)O1.R10.)(>.(15.P,$0.Sp(14.$2.VR,VHIA,R?.)(14.$2.VR,VHIA,O4.))(>.(15.$0.(2:.$2.VR,VHIA,R?.)(2:.$2.VR,VHIA,O4.))(>.(15.$0.(18.$2.VR,VHIA,R?.)(18.$2.VR,VHIA,O4.))(>.(15.$0.(2;.$2.VR,VHIA,R?.)(2;.$2.VR,VHIA,O4.))(>.(15.$0.(2<.$2.VR,VHIA,R?.)(2<.$2.VR,VHIA,O4.))(>.(15.$0.(2=.$2.VR,VHIA,R?.)(2=.$2.VR,VHIA,O4.))(>.Pmo,$2>.(2?.(30.$2.VR,VHIA,R10.R1.)(30.$2.VR,VHIA,O4.R1.))(27.$2.VR,VHIA,R?.O3.VLF,R10.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lx_cells_blob :=
    repeat match goal with
    | H : rw_cells ?sg ?m ?A ?cs, L : cells_size ?cs = ?k |- _ =>
        is_var cs;
        apply (fun X => CellsX.rw_cells_reshape sg m A cs [CB k (cells_bytes cs)] X
                 ltac:(cbn; split; [rewrite (Cells.cells_bytes_length cs (proj1 (proj1 (proj1 X)))); exact L| exact I]) eq_refl) in H
    end.
  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 D47; try lx_pin1 DLO; try lx_pin1 CR; try lx_pin1 HD; try lx_pin1 Hn; try lx_pin1 LEN; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 FSf; try lx_pin1 FSp; try lx_pin1 CNTp_nn; try lx_pin1 FFRp_nn; try lx_pin1 PHIp_nn; try lx_pin1 FFRf_mono; try lx_pin1 PHIf_mono; try lx_pin1 FREE; try lx_pin1 PARSE; try lx_pin1 STKf; try lx_pin1 FFRf; try lx_pin1 PHIf; try lx_pin1 STKp; try lx_pin1 CNTp; try lx_pin1 FFRp; try lx_pin1 PHIp; try lx_pin1 p7rep; try lx_pin1 P7T; try lx_pin1 AMS; try lx_pin1 E00; try lx_pin1 SM5; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03>0@D1388493450.200 D13948560335.200D18621760331.198D2459793318.140 D2463937847.195 D32452690557.140D3382075924.195 D3388366767.139 D38324300770.195D3886063417.200 D43016287773.141D45639715690.140D45704738334.139D50256927179.199D62011770188.141D62018113012.195D68411655660.139D6899603433.139 K36467192360.177L10133837431.1  L10596430123.1  L10946950954.3  L13176305223.2  L1540877545.3   L15502686288.123L15701667682.2  L15737467458.1  L16203338353.122L16255647091.144L16255647091.145L16421789278.174L1676958453.128 L17832996913.198L18221343941.3  L18808600828.4  L19546883924.122L19710910576.123L20181680106.174L20492587903.1  L2064697276.176 L21175742071.23 L24569601807.2  L25225054747.2  L25393907176.2  L2620076690.1   L2761531724.2   L28295164583.174L28332440793.1  L28711237604.1  L30198445302.2  L31114278105.3  L32088652577.0  L32458983506.119L35655538631.14 L36370515719.2  L36462705086.2  L37292651511.1  L37850309025.0  L38235734261.1  L39188636933.0  L40281191306.3  L41409160545.3  L42262983732.176L42439184590.3  L43188064477.2  L43209802907.2  L43300649301.0  L43359553883.174L43594773695.127L45312697391.2  L46954934750.1  L47491197208.2  L47663688086.1  L47801025836.173L47801036031.171L48117620900.123L48117620902.120L48117620904.118L48132302223.145L48132302223.172L48132302231.144L48132302231.171L48132467214.12 L48555331576.2  L49317467472.1  L5001847267.4   L50542531495.2  L50790731766.11 L51064594356.2  L51878069071.2  L5231810586.1   L52412936479.1  L53850764012.119L53960509302.2  L54292478723.175L54629377307.24 L55588686165.0  L57501846211.2  L58790154276.9  L59507442300.1  L60098763854.6  L60117804535.2  L61883993876.174L62604581868.2  L62871861603.3  L63553610255.2  L64657763020.4  L65560577950.2  L65935405590.3  L66151427842.16 L68040139772.2  L68319102792.4  L68407455976.118L68411655660.120L68442042496.1  L6851356907.2   L68652650564.2  L6912107245.118 L7049614941.3   L8071213210.118 L881835912.0    L9080220944.4   L9356559676.16  L9787245214.2   O12422637294.177O15463198269.177O1803266184.177 O32137156502.177O33055229292.177O51899033324.177O59625529265.177O63308119680.177O63908043916.177P18234093395.177P18823817819.177P31111702142.177P41419110342.177P5012910916.177 P62874495940.177P65949573297.177P68330067439.177Q10592386193.151Q10592386205.146Q10592386207.148Q19959140431.197Q20191066860.175Q20191066868.197Q20193165255.152Q23925414039.155Q27516824080.197Q36068443607.180Q37766821185.175Q37766821185.198Q37766821209.174Q37766821209.197Q37781500006.147Q37781500010.152Q38250992820.154Q42437205103.197Q42439381099.176Q42439381099.199Q42441479407.158Q43878048872.154Q48117620903.151Q48117620907.146Q48132270006.180Q48132302223.150Q48132302231.145Q56821109172.151Q56821109176.146Q56821109178.148Q58465874581.151Q59310664043.145Q59310664043.174Q59310664051.198Q59321150548.147Q59321150551.146Q60382659728.152Q60382659740.147Q60397339043.174Q60397339043.197Q60397339067.175Q60397339067.198Q62009673039.155Q6203789748.197 Q64681502662.158Q64683598658.176Q64683598658.199Q64685727963.180Q6897428426.150 Q6897428434.145 Q6912107245.147 Q6912108138.153 Q7902384038.174 Q7902384038.197 Q7902384062.175 Q7902384062.198 Q7917062805.152 Q7917062809.147 Q8071213210.147 Q8071214109.153 Q8085894565.145 Q8085894589.150 Q8399688099.150 Q9350270635.158 Q9352367266.175 00000Z01=01>01?01@01]01^01_02K02L03203O03l03m04L05105205O05n05o06306=06E06Q07907:07;07c08E08g09o0:`0:a0:b0:c0;F0;o0<U0<Z0=90=_0=`0=f0=l0=m0>30>]0>b0>f0>l0>m0>n0?G0?`0?a0?b0?g0?h0?l0?m0@60@70@e0A10A90A:0A;0Ae0BV0B\0B`0Ba0Bb0Bc0Bd0Ck0E20F90G@0HM0IT0Ja0KM0KN0KR0KS0KT0L20L30L40L50L90LR0LX0M70M_0M`0Ma0NC0NG0NQ0NR0O<0O=0O>0O?0OO0OP0OQ0Ok0Ol0Om0On0Oo0P30P40P50PN0PY0Q20Q30QB0R40R:0R;0R<0R=0R>0R?0R@0RA0RB0RC0SO0TA0UU0VE0WY0Xm0YT0ZF0Z_0[80[Q0\40\50\60\70\X0]V0^D0^E0^F0^G0^H0^I0^J0^f0_P0`40`^0aB0aa0bh0co0e60f=0gD0g]0h60hO0hP0hQ0hR0hS0hT0hU0hV0hW0hX0hY0hZ0h[0i60iY0jN0kC0l>0m30mL0me0n>0nW0o<0og10L11711\12A12Z13313L13e13f14H150S2LF2sp3LFB2FB3sp12c12c33SP13SZ13SZ35SZALLS2LF3LFB2FB3sp12c12c33SZ13SZ35SZALLFFFS2LF3LFB2FB3sp12c12c33SZ13SZ3FFS1R3HIA2LF3LFB2FB3sp12c12c33SZ13SZ35SZALL2h4FS1R3HIA2LF3LFB2h32FB3sp12c12c33SZ13SZ3S2LF3LFB2FB3sp12c12c33SZ13SZ3S2LF3LFB2FB3sp12c12c33SZ13SZ3FS1R2LF3LFB2FB3sp12c12c33SZ13SZ3S1R2LF3LFB2FB3sp12c12c33SZ13SZ35SZALLFS2LF3LFB2FB3sp12c12c33SZ13SZ3S1R2LF3LFB2FB2c12c33SZ13SZ33APSFS2FBS2FB2x02HxS2lo3sp1S2sp3sp13SP1S2LF3LFB2FB3sp12c12c33SZ13SZ34SP1R2F02F8FFS2LF3LFB2FB3sp12c12c33SZ13SZ34SP1R2F02F8S2LF3LFB2FB3sp12c12c33SZ13SZ31c2HcS2LF3LFB2FB3sp12c12c33SZ13SZ31c2HcS1R3NS24FSTK3FS22LF2sp2lo3SLO3LFB2FB3sp12c12c33SP13SZ13SZ34SP1R2F05SZALLS1R2LF2sp3slo4SLOS3LFB2FB2c12c33SZ13SZ33ALO2F02F1FFFS2LF3LFB2FB3sp12c12c33SZ13SZ32F02F8S2LF3LFB2FB3sp12c12c33SZ13SZ34SP1R2F03F8'S2LF2sp3LFB2FB3sp12c12c33SZ13SZ35SZALLS3sp1S1R2LF3LFB2FB3sp12c12c33SZ13SZ3S2FB2r13F641q1r1H2H02q02r02H42H52q12H9FS1R2FBS1R2FBFS1R2FBS2LF2sp3LFB2FB3sp12c12c33SP13SZ13SZ35SZALLS3sp1S2FBS1R2FBFSS2LF3LFB2FB2c12c33SZ13SZ3S1R3HIA1h2sp2lo3TOP5HTOP3FFS3sp1SS2loSS1R3HIA1hFS2LF2sp3SPH3LFB2FB3sp12c12c33SZ13SZ33SPR5SZALLS1R3slo4SLOSS2lo3sp1FSS2LF2sp3LFB2FB3sp12c12c33SP13SZ13SZ35SZALLS1R2LF2sp3slo4SLOS3LFB2FB2c12c33SZ13SZ33ALO2F02F1S1R2FBS2spFFFFS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F05SZALLS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F05SZALLS1R3NS14FSTK3FS12sp2lo3slo4SLOS4SLOL3SLO3ALOFS2FBFFS1R3NS14FSTK3FS12sp2lo3SLO3LOSFFFS2loS2LF3LFB2FB2c12c33SZ13SZ3S1R2FBS1R2LF3LFB2FB3sp12c12c33SZ13SZ3S1R2FB2r13F641q1r1H2H02q02r02H42H52q12H9SFS1R4FSTK3FS22sp2lo3SLO3sp13SP13FS1S2spS1R2lo3LOSFS2LF2sp3LFB2FB3sp12c12c33SP13SZ13SZ35SZALLFFFS1R2FB4SBlo4SBhiFFS2FB2r03F641q1r1H2H02q02H4FFFFS2FBFFS2LF3LFB2FB2c12c33SZ13SZ3S2sp2lo3sp1S2LF3LFB2FB2c12c33SZ13SZ3SS2sp2lo3sp13SP1S1R3NS14FSTK3FS12sp2lo3SLO3LOS3sp13SP13ALO3ACV3SPRS1R2FBFFFFFFFFFS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F04SBNDS1R2LF2lo3LFB3LOS2FB3sp12c12c33SZ13SZ33ALO2F04SBNDS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB3sp12c12c33SP13SZ13SZ33ALO2F04SBNDS1R2LF2lo3LFB3LOS2FB3sp12c12c33SZ13SZ33ALO2F02F1S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB3sp12c12c33SP13SZ13SZ33ALO2F04SBNDS1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB3sp12c12c33SP13SZ13SZ33ALO2F04SBNDS2LF2sp2lo3LFB2FB3sp12c12c33SP13SZ13SZ3S1R2LF2lo3LFB3LOS2FB3sp12c12c33SZ13SZ33ALO2F04SBNDS2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB3sp12c12c33SZ13SZ35SZALLFFFS1R3HIA1h2LF3LFB2FB2c12c33SZ13SZ3S1R3HIA1h2LF2sp3TOP3LFB2h32FB2c12c33ES33SZ13SZ35HTOP32F05SZALLS1R2LF3slo4SLOS3LFB2FB2c12c33SZ13SZ33ALO2F02F1FFFFFFS2LF2lo3LFB2FB2c12c33SZ13SZ3S1R2LF3slo4SLOS3LFB2FB2c12c33SZ13SZ35SZALLS1R2LF3slo4SLOS3LFB2FB2c12c33SZ13SZ3S1R2LF3slo4SLOS3LFB2FB2c12c33SZ13SZ35SZALLS1R2LF3slo4SLOS3LFB2FB2c12c33SZ13SZ3S2LF2sp2lo3LFB2FB2c12c33SZ13SZ3S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S1R3NS34FSTK3FS32LF2sp2lo3slo4SLOS4SLOL3SLO3LFB2FB2c12c33SZ13SZ33ALO2F0S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3FFFFFFFFFFFFS1R2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB3sp12c12c33SZ13SZ35SZALLS1R3HIA1h2LF2sp3slo3TOP3LFB2FB2c12c33SZ13SZ35HTOP32F0S1R3HIA1h2LF2sp3slo3TOP3LFB2FB2c12c33SZ13SZ35HTOP32F0S1R3HIA1h2LF2sp3slo3TOP3LFB2FB2c12c33SZ13SZ35HTOP32F05SZALLS1R3HIA1h2LF2sp3slo3TOP3LFB2FB2c12c33SZ13SZ35HTOP32F0S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F1S1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F15SZALLS1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F1S1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F15SZALLS1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F1S1R2LF3LFB2FB2c12c33SZ13SZ33ALO2F02F1S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3S2LF3LFB2FB2c12c33SZ13SZ3FS2LF3LFB2FB3sp12c12c33SZ13SZ34SP1RS2LF3LFB2FB3sp12c12c33SZ13SZ34SP1R5SZALL". (* [comment removed for export] *)
  #[using="LOS LFB SPH TOP SLO SLOL SLOS bs FS3 FS2 FS1 FSTK NS3 NS2 NS1 EF8 SF5 IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_fuzz_entry ()) "Ph3,(1.$2.VR,VHIA,)PLB3,(3.$4.)Pm0,P,(6.&40.)(7.(6.&8.))Pm2x,P,(6.&40.)(7.(6.&8.))Pmm,P,(6.&40.)(7.(6.&8.))PFB,$0.Psp1,$0.Pxra,(6.&40.)Pt0,(6.&40.)Pt1,(6.&40.)Pt2,(6.&40.)Pa0,(6.&40.)Pa1,(6.&40.)Pa2,(6.&40.)Pa3,(6.&40.)Pa4,(6.&40.)Pa5,(6.&40.)Pa6,(6.&40.)Pa7,(6.&40.)Pt3,(6.&40.)Pt4,(6.&40.)Pt5,(6.&40.)Pt6,(6.&40.)Pw0,(6.&40.)Pw1,(6.&40.)Pw2,(6.&40.)Pjw,(6.&40.)Pc1,(3.$1=.)Pc3,(3.$1=.)Posh,(3.(6.&8.))P,(27.$2.VR,VHIA,R1>.R1=.(28.(8.$0.$0.)(29.$0.$0.R19.+800.)VLF,)R1:.)P,Pb,$4.P,(42.$4.R1.VLB,)(42.$4.R2.R20.)P,Px,$0.P,(14.$2.VR,VHIA,Vh,R1.)(14.$2.VR,VHIA,R22.R2.)P,(15.$0.(2:.$2.VR,VHIA,R21.)(2:.$2.VR,VHIA,Vh,))P,(15.$0.(18.$2.VR,VHIA,R22.)(18.$2.VR,VHIA,Vh,))P,(>.(:.(11.(26.&40.Vsp,)+70.)R1=.)(:.R1=.(11.(26.&40.Vsp,)+60.)))P,(15.$0.(16.R1>.+20.)=)P,(15.$0.(16.R20.+40.)=)P,(31.VR,VLB,VLF,R21.+800.)P,(13.(14.$2.VR,VHIA,Vh,)R22.+800.)P,PB,$0.Pj,$0.P,(42.(8.$0.$0.)(29.$0.$0.R2.R1.)VLF,)(43.(:.(21.R26.+800.)R3.)(:.(21.R3.R2.)R26.))P,(32.$2.R25.R24.(28.$1=.(33.R12.)(28.$1=.(33.R11.)(28.$1=.(33.R10.)(34.$1=.)))))P,(32.$2.R26.(21.(22.R25.+3.)(23.(1:.VR,)))R?.)P,(15.$36.(37.R10.)#4.)P,(32.$2.R28.(21.(21.(22.R27.+3.)(23.(1:.VR,)))+4.)(28.$1=.(38.#;4.R?.)(34.$1=.)))P,(32.$2.R29.(21.(21.(22.R28.+3.)(23.(1:.VR,)))+;8.)R11.)P,(15.$36.(37.R12.)#48.)P,(32.$2.R2;.(21.(26.&40.Vsp,)-50.)(28.$1=.(33.Vs8,)(28.$1=.(33.Vs7,)(28.$1=.(33.Vs6,)(28.$1=.(33.Vs5,)(28.$1=.(33.Vs4,)(28.$1=.(33.Vs3,)(28.$1=.(33.Vs2,)(28.$1=.(33.Vs1,)(28.$1=.(33.Vs0,)(28.$1=.(33.Vra,)(34.$1=.))))))))))))P,(32.$2.R2<.(21.R2:.+8.)(28.$1=.(33.R16.)(34.$1=.)))P,(3:.$2.R2=.R2;.(21.R2;.+8.))P,(3:.$2.R2>.(21.R2<.+10.)(21.(26.&40.Vsp,)-50.))P,(3:.$2.R2?.Vlo,R2=.)P,(3;.$2.R30.)P,(9.$2.VR,VHIA,Vh,VLB,VLF,(26.&40.Vsp,)(26.&40.Vsp,)(41.(<.VR,)VSI,)R33.R31.)P,(9.$2.VR,VHIA,Vh,VLB,VLF,(26.&40.Vsp,)(26.&40.Vsp,)(34.$5.)R33.R32.)P,(3<.$2.(1:.VR,)R33.Vslo,(26.&40.Vsp,))(3=.$2.(1:.VR,)(14.$2.VR,VHIA,R38.)(44.R38.R37.R36.R35.)(1>.(1?.R31.(20.&40.R32.)Vgp,Vtp,R30.R2?.R2>.Vsp,(20.&40.R32.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.(20.&40.R33.)(20.&40.Vn,)(20.&40.VDATA,)(20.&40.(21.(22.R33.+3.)(23.(1:.VR,))))(20.&40.(21.R33.+20.))(20.&40.(21.(21.(22.R33.+3.)(23.(1:.VR,)))+4.))(20.&40.R33.)Vs9,Vs10,Vs11,R25.R24.R23.R22.)VF,(20.&40.+976>0.)Vfc,(24.(6.&40.))R34.(25.$2.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros until osh.
  intros HH3 LBI HCS3 ET3 ES3 SP1 SP1M F64 FRSH CFB AP FHD SHF1 SZ1 SHOBJ SHF3R SZ3 SAVE SLOT STlo SThi STC MI PRES PRES2 SS.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV FS1 NS1; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 2048) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)).
    { eapply crange_mono; [exact HCS3|]. eapply crange_sub; [exact SCS0| first [ clear - LOS SLOS SLOL; lia | lx_side_lia ]| first [ clear - SLO FS1 NS1 TOP HTOP3 ET3 ES3; lia | lx_side_lia ]]. }
  pose proof FRSH as FRSH'.
  destruct FRSH' as (F0 & F1 & F2 & F3).
  pose proof (art_stk_high asegs R HIA) as STKH.
  assert (SH4 : Z.shiftr (FB + 32) 3 = Z.shiftr FB 3 + 4) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
  assert (SHFB : Z.shiftr FB 3 = FB / 8) by (apply Z.shiftr_div_pow2; clear; lia).
  assert (ESH : shadow_of AL (FB + 32) = Z.shiftr FB 3 + al_sb AL + 4) by (unfold shadow_of; rewrite SHFB; clear - F64; Z.div_mod_to_equations; lia).
  pose proof (apart_shadow_client AL CS FB 2048 FB (shadow_of AL FB) 256 CSOK CFB CFB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as APS.
  unfold shadow_of in APS.
  rewrite <- SHFB in APS.
  pose proof (hcs_shadow_band asegs R HIA h FB (CFB FB ltac:(clear; lia))) as SBlo.
  pose proof (hcs_shadow_band asegs R HIA h (FB + 8 * 255) (CFB (FB + 8 * 255) ltac:(clear; lia))) as SBhi.
  rewrite shadow_of_plus in SBhi.
  unfold shadow_of in SBlo, SBhi.
  rewrite <- SHFB in SBlo, SBhi.
  assert (SBND : hl_data_hi L <= Z.shiftr FB 3 + al_sb AL /\ Z.shiftr FB 3 + al_sb AL + 256 <= alloc_ceiling) by (first [ clear - SBlo SBhi; lia | lx_side_lia ]).
  clear SBlo SBhi.
  assert (F8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (F8' : (FB + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (INF : In (FB, 2048) ((FB, 2048) :: LF)) by (left; reflexivity).
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  assert (SHFREE : shadow_free R LB LF (bv_unsigned sp) (hstkhi asegs R HIA h) (FB + 32) (8 * 180)).
    { destruct PRES as (_ & _ & _ & BL). eapply shadow_free_fresh; [exact FRSH| exact BL| clear; lia| clear; lia| first [ clear - ALO LOS SLO FS1 NS1; lia | lx_side_lia ]| exact AP]. }
  apply rw_cells_CB_of in SHF1; [| rewrite SZ1; clear; lia].
  rewrite SZ1 in SHF1.
  apply rw_cells_CB_of in SHF3R; [| rewrite SZ3; clear; lia].
  rewrite SZ3 in SHF3R.
  assert (INH3 : In (FB, 24) (LB3 ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; left; reflexivity).
  assert (IND3 : In (FB + 32, 2008) (LB3 ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  lx_pre. lx_unhide. lxr_path. lxr_abase. lxr_pose.   (* [comment removed for export] *)
  try lxg_b8u. lx_cells_blob. lx_pre. lx_run_tac (PLAN [0x053710; 0x05391c; 0x06b228; 0x06b348; 0x0976c8; 0x097788; 0x0977a8; 0x09818c] [] 136%N).
  lx_tree.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a; try (lazymatch goal with _ : b = b |- _ => idtac | |- _ => pose proof (@eq_refl _ b) as LXENT end) end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x976ec) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6b348) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep; lx_unhide | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => replace (Z.shiftr FB 3 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 0) in SHF1 by (clear; lia) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => call_setsh 0xf8 439112 EF8 SP1; [rewrite ESH; reflexivity|] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => after_setsh SP1 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => replace (Z.shiftr FB 3 + al_sb AL + 0) with (Z.shiftr FB 3 + al_sb AL) in SHF1 by (clear; lia) | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0x97184: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lx_unhide; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x053710; 0x05391c; 0x06b228; 0x06b348; 0x0976c8; 0x097788; 0x0977a8; 0x09818c] [] 136%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x97708) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x5391c) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  lazymatch goal with LXM : lx_callmark |- _ => lx_call_prep; lx_unhide | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename m7 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m7 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => replace (Z.shiftr FB 3 + al_sb AL + 0) with (Z.shiftr FB 3 + al_sb AL) in SHF1 by (clear; lia) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => chunk_join SHF1 SHOBJ SH01 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => chunk_join SH01 SHF3R SHALL | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => assert (SZALL : cells_size ([CB 4 (cells_bytes c1)] ++ [CB 180 (repeat (Z_to_bv 8 248) 180)] ++ [CB 72 (cells_bytes c3)]) = 256%nat) by reflexivity | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => replace (Z_to_bv 64 342300) with (Z_to_bv 64 (arl_sfree5 R)) by (rewrite SF5; reflexivity) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch type of PRES with ?t => change t with (hidden t) in PRES end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch type of PRES2 with ?t => change t with (hidden t) in PRES2 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => callrt sp1 (eapply (art_sfree5 asegs R HIA) with (h := h3) (LB := LB3) (LF := (FB, 2048) :: LF) (FB := FB) (sz := 1600) (lo := lo); rewrite ?(unsigned_lit sp1) by exact SP1R; first [ exact INF | exact SHALL | exact SZALL | exact LOS | reflexivity | lazymatch goal with | |- HM _ _ _ h3 _ _ m7 => assumption | |- stk _ _ lo _ => assumption | |- lo <= _ => first [ clear - FS1 SLO NS1 SP1; lia | lx_side_lia ] | |- crange _ lo _ => eapply crange_sub; [exact SCS3| clear; lia| first [ clear - SP1; lia | lx_side_lia ]] | |- mem_inv _ m7 => assumption end | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SFREE-PRE-LEFT:" g end ]) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SFREE-LEFT:" g end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try (let f := fresh "lxo" in rename HP8 into f) | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with H : presA _ _ _ _ _ _ _ _ m7 ?m8 |- _ => rename H into HP8; cbn [lb_remove fst Z.eqb] in HP8; rewrite Z.eqb_refl in HP8 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch goal with H : exists h' : HST _ _ _, _ |- _ => destruct H as (h4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4); cbn [lb_remove fst Z.eqb] in HH4; rewrite Z.eqb_refl in HH4 end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => unfold hidden in PRES, PRES2 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => lazymatch type of HP8 with presA _ _ _ _ _ _ _ _ m7 ?m8 => apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (si_fp SI) m0 m7 m8 LB3 LF sp1 (arl_stklo R) (hstkhi asegs R HIA h3) []) in PRES; [| exact HP8 | exact LBI | intros b Hb; exact Hb | first [ clear - SP1; lia | lx_side_lia ] | first [ clear - SLOS SLOL SLO FS1 NS1 LOS; lia | lx_side_lia ] | rewrite ES3; clear; lia | intros xo _; exact I ]; apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m2x m7 m8 LB3 LF sp1 (arl_stklo R) (hstkhi asegs R HIA h3) []) in PRES2; [| exact HP8 | exact LBI | intros b Hb; exact Hb | first [ clear - SP1; lia | lx_side_lia ] | first [ clear - SLOS SLOL SLO FS1 NS1 LOS; lia | lx_side_lia ] | rewrite ES3; clear; lia | intros xo _; exact I ] end | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear SHALL; try (lazymatch type of HH1 with HM _ _ _ _ _ _ m7 => clear HH1 end); try (lazymatch type of STC with stk _ m7 _ _ => clear STC end); try (lazymatch type of MI with mem_inv _ m7 => clear MI end) | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => presA_transport HP8 | |- _ => idtac end.   (* [comment removed for export] *)
  lazymatch goal with LXM : lx_callmark |- _ => try clear HP8| |- _ => idtac end.
  all: lazymatch goal with LXM : lx_callmark |- context [seg_rom _] => idtac | LXM : lx_callmark |- ?g => first [ solve [ clear LXM; first [ assumption | reflexivity | lx_arith | lx_side_lia | lx_app ] ] | idtac "lxw: call 0x971a0: side goal left before the continuation:" g; clear LXM] | |- _ => idtac end.
  lazymatch goal with LXM : lx_callmark |- _ => clear LXM; try lxg_b8u; lx_pre; lx_unhide; lxr_path; lxr_abase; lxr_pose; lx_pre; lx_run_tac (PLAN [0x053710; 0x05391c; 0x06b228; 0x06b348; 0x0976c8; 0x097788; 0x0977a8; 0x09818c] [] 136%N); lx_tree | |- _ => idtac end.
  all: try (let f := fresh "lxh" in rename H into f).
  all: try (lazymatch type of LXSAME with ?a = ?b => is_var a; repeat match goal with H : context [a] |- _ => lazymatch type of H with a = b => fail | munch _ _ _ => fail | wmono _ _ _ => fail | _ => clear H end end; subst a end).
  all: lazymatch goal with |- context [seg_rom _] => lxr_leaf; lx_carry | |- _ => idtac end.
  all: try (match goal with E : ?a = ?b |- _ => is_var a; lazymatch goal with |- context [MS _ _ _ _ _ a (seg_rom _)] => subst a end end); try (lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => repeat match goal with H : munch _ _ mx |- _ => clear H| H : wmono _ _ mx |- _ => clear H end end).
  (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS (mkR (Z_to_bv 64 0x97718) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x6b228) _ _ _ (seg_rom _)] => first [ lazymatch goal with _ : lx_callmark |- _ => idtac end | assert (LXCALL : lx_callmark) by exact I ] | |- _ => idtac end.
  all: lazymatch goal with _ : lx_callmark |- _ => idtac | |- _ => shelve end.
  Unshelve.
  all: lazymatch goal with LXM : lx_callmark |- _ => first [ (try lx_rejoin; lx_leaf) | idtac "lxw: no original call block for site 0x971b0 (A_SET00)" ]; try clear LXM| |- _ => idtac end.
  all: lazymatch goal with |- context [MS _ _ (Z_to_bv 64 0x976c8) _ _ _ (seg_rom _)] => try lx_rejoin; lx_apply pro_walk | |- _ => idtac end.   (* [comment removed for export] *)
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => try lx_rejoin; lx_leaf | |- _ => idtac end.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: lazymatch goal with |- stk ?sg ?mc lo (bv_unsigned sp) =>
      lazymatch goal with SL : rw_cells _ mc (?spx + 8) [C8 _], ST0 : stk _ mc lo ?spy |- _ =>
      lazymatch goal with SV : rw_cells _ mc (bv_unsigned sp + -80) _, ST1 : stk _ mc spx (spx + 8), ST2 : stk _ mc (spx + 16) (bv_unsigned sp + -80) |- _ =>
        let K1 := fresh "K1" in let K2 := fresh "K2" in
        pose proof (stk_of_rw_cells sg mc _ _ SL) as K1; pose proof (stk_of_rw_cells sg mc _ _ SV) as K2;
        cbn [cells_size csize Nat.add] in K1, K2;
        replace (spx + 8 + Z.of_nat 8) with (spx + 16) in K1 by (clear; lia);
        replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in K2 by (clear; lia);
        exact (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ (stk_merge _ _ _ _ _ ST0 ST1 ltac:(clear - SP1 SLO FS1 NS1; lia)) K1 ltac:(clear - SP1 SLO FS1 NS1; lia)) ST2 ltac:(clear - SP1 SLO FS1 NS1; lia)) K2 ltac:(clear - SP1 SLO FS1 NS1; lia))
      end end
  | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lxw epi_walk: unexpected leaf left:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  Definition PHI (n : Z) : Z := PHIp n + PHIf (CNTp n).
  Definition FFR (n : Z) : Z := FFRp n 1 + FFRf (CNTp n) 0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0150?L10596430123.1 L11146046184.1 L12707060134.13L13198274409.4 L1388607117.3  L13948747720.1 L14844034785.1 L1540877545.3  L15756274770.4 L16255647091.3 L18314209711.1 L18482352862.8 L19959024712.1 L19980016842.7 L20368475885.7 L21175742071.23L24128180555.1 L2424960062.2  L26892418956.1 L27734943701.16L29149025057.0 L31021792691.6 L31863022963.4 L32454903270.1 L35176931115.1 L35653441506.11L35747972712.1 L35873683881.1 L37327673771.3 L37896445747.12L39188636933.0 L39280637297.0 L40281191306.3 L40536194668.8 L41708090472.1 L43170228250.2 L4373974455.23 L44279994491.16L45393208713.4 L45622492978.3 L4714747663.2  L49799904432.3 L50790731766.11L51592016414.2 L52118754430.14L52976574118.13L54971811087.1 L55588686165.0 L57387013391.2 L59891971727.13L5993630477.1  L60098763854.3 L60109462615.5 L62018535662.1 L62037129548.9 L6203936179.1  L62616353899.9 L66151427842.16L6899380056.1  L696052593.2   L7192656114.6  L8190532385.0  L8464427966.11 L8551249324.9  L9356559645.13 L9631767084.2  L9787245214.2  L9838743115.2  L9873114841.11 00000400800i01801D01I01N01Z01h02102502V02[03303M04304704=04A05805905N05^05b05f06>06B06F06O07;07<07=07F07g07k08308Y09P09]09f09m0:90:W0:]0;Q0<@0<D0<E0<L0=:0=>0=H0=\0=_0>A0>F0>g0?Q0?U0?]0@10@20@\0A<0An0B50B;0BE0C0S2FBS2FBS1R3HIA4FFRp4CNTp4FFRf1h1n2h23LBn4HFR22h34HFR32FMS4DATA1n2FB3APDS2sp3sp13SP1S3sp1S3LBnS2sp3sp13SP1S1R2lo3ALO3LOSS2FB1c2HcS2FBS4STKp4FSTK3FSp2sp2lo3SLO3sp13SP1S3sp1S1R3HIA1h2sp3TOP3sp13SP1S2sp4DATA1n2lo3DLO3sp13SP1S2FB2r13F641q1r1H2H02q02r02H42H52q12H9S2FBS1n2HnS2spS1R3HIA3NS14FSTK3FS11h2sp2lo3SLO3ALO3LOS3sp13SP11a2Ha1HSS1R3HIA1h2sp3TOP4HTOPS2sp3SPH3sp13SP1S2FBS2FBS1R3HIA1h2sp2lo3TOP4HTOPS2FBS2FBS1R2FB2F2S1R3HIA4PHIp4CNTp4PHIf1h1n3BUD2h23LBn3HV22PMSSS1R3HIA1hS4STKf4FSTK3FSf2sp2lo3SLO3sp13SP1S2FBS2LF3LFBS2FB2r13F641q1r1H2H02q02r02H42H52q12H9S1R3NS14FSTK3FS12sp2lo3SLO3ALO3LOS2FB3sp13SP12F11A1k2HAS1R3ALO2FB2F1S1R2FB2F2S2FB2F0S2sp3sp13SP1S1R3NS14FSTK3FS12sp2lo3SLO3LOSS1R2FBS1R3NS14FSTK3FS12sp2lo3SLO3ALO3LOS3sp13SP14DLOW1A2HAS1R3HIA4PHIp4CNTp4PHIf1h1n2h23LBn3HV22h33HV32PMS2FBSS2FB2F0S1R3HIA4FFRp4CNTp4FFRf1h1n4BUDF2h23LBn4HFR22FMS2spS1R2lo3LOSS1R2lo3slo4SLOS4SLOLS1RS1R3NS14FSTK3FS12sp2lo3SLO3SPR3LOSS3sp1S1R3HIA4FFRp4CNTp4FFRf1h1n4BUDF1HS2FB2r03F641q1r1H2H02q02H42sp3SPA3sp14SP1MS2FBS2sp3SPRS1R2lo3ALO3LOS2FB2F1SS1R3NS14FSTK3FS12sp2lo3SLO3ALO3LOS3sp13SP1S1R3HIA4PHIp4CNTp4PHIf1h1n3BUD1HS1R3NS14FSTK3FS12sp2lo3SLO3ALO3ACV3SPR3LOS3sp13SP1S2FB2F0S1R2FBS3sp14SP1RS1R3NS14FSTK3FS12sp2lo3slo4SLOL3SLO3sp13SP1". (* [comment removed for export] *)
  Theorem fuzz_entryA : fuzz_entry_stmtA asegs R HIA SI PHI FSTK FFR FUZZ_ENTRY.
  Proof.
    unfold fuzz_entry_stmtA. intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo DATA n lo slo bs.
    intros HH HK0 BY LEN Hn HD CR OD DLO D47 ST SS SLOS SLOL SLO TOP SPA SPH MI TPV SIP BUD UW BUDF LFB -> ->.
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_val R) as ACV.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP. pose proof (hcs_stack asegs R HIA h) as SCS0.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    assert (LOS : arl_stklo R <= lo) by (clear - SLOS SLOL; lia).
    assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO FS1 NS1 TOP HTOP; lia]).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ _ (conj HK0 (mo_frame_refl mo))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
    { eapply (pro_walk h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DATA n lo slo bs);
        assumption. }
    intros ms1 P1. destruct P1 as (FB & sp1 & h1 & m1 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & w0 & w1 & w2 & jw & c1 & c3
                                 & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & P7Z & SHF1 & SZ1 & SHOBJ & SH3R & SZ3
                                 & SAVE & SLOT & STlo & SThi & ST1 & MI1 & PRES & SS1).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV FS1 NS1; lia).
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. destruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (hm_fresh_frame_apart asegs R HIA h1 LB LF m1 FB 2048 HH1) as AP.
    assert (F8' : (FB + 32) mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (SH4 : Z.shiftr (FB + 32) 3 = Z.shiftr FB 3 + 4) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
    assert (INF : In (FB, 2048) ((FB, 2048) :: LF)) by (left; reflexivity).
    pose proof (hcs_fake asegs R HIA h1 LB _ m1 FB 2048 HH1 INF) as CFB. rewrite Ehcs in CFB.
    assert (IND : In (FB + 32, 2008) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
    assert (INH : In (FB, 24) (LB ++ fdata ((FB, 2048) :: LF))) by (apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES) as HP1.
    assert (CRsp : client_range L (LB ++ fdata LF) (bv_unsigned sp) DATA n) by (eapply client_range_raise; [exact CR| exact DLO]).
    assert (BY1 : bytes_at asegs m1 DATA bs).
    { eapply presA_bytes_at0; [exact HP1| exact BY|]. right. split; [rewrite LEN; exact CRsp| exact I]. }
    assert (OD1 : 1 <= n -> aobj asegs AL (hcs asegs R HIA h) m1 DATA n).
    { intros H1. eapply presA_aobj0; [exact CSOK| exact HP1| exact (OD H1)| intros x Hx; eapply hcs_below_top; exact Hx| right; split; [exact CRsp| clear; lia]]. }
    assert (SIP1 : si_P SI m1).
    { eapply (si_heap_presx asegs L SI); [exact SIP| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP1)| intros a _; exact I]. }
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) 0).
    { eapply uwc_presA; [exact HP1| exact UW| clear; lia| intros a _; exact I| clear - SPR; lia| apply hstkhi_le64].
      clear - LOS SLO SPR FS1 NS1; lia. }
    assert (UWF : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 1).
    { pose proof SAVE as SV. chunk_split SV 8%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -80 + 64) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      rewrite <- (Z_to_bv_bv_unsigned s0) in SV0.
      change 1 with (0 + 1). eapply uwc_frame; [clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| pose proof (bv_unsigned_in_range 64 s0) as XR; unfold bv_modulus in XR; cbn [Z.pow Z.of_N Pos.pow] in XR; exact XR| clear; lia| exact (proj1 SV0)| exact UW1]. }
    clear HP1 BY OD UW SIP.
    assert (OBJ1 : aobj asegs AL (hcs asegs R HIA h1) m1 (FB + 32) 1440).
    { rewrite Ehcs. change 1440 with (8 * Z.of_nat 180).
      eapply (aobj_of_zshadow asegs AL _ m1 (FB + 32) 180 CSOK); [| eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia].
      rewrite SH4. replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) by (clear; lia). exact SHOBJ. }
    assert (CW1 : client_wrange L (LB ++ fdata ((FB, 2048) :: LF)) lo (htop asegs R HIA h) (FB + 32) 1440).
    { eapply client_wrange_block; [exact IND| clear; lia| clear; lia]. }
    assert (CR1 : client_range L (LB ++ fdata ((FB, 2048) :: LF)) lo DATA n).
    { eapply client_range_incl; [exact CR| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    pose proof (fresh_apart_client0 R LB LF lo DATA n FB 2048 FRSH CR ltac:(clear - Hn; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APD.
    destruct (sshad_split asegs AL m1 slo sp1 (bv_unsigned sp) SS1 ltac:(clear - SP1 SLO SLOL FS1 NS1; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia)) as [SSlo SShi].
    (* [comment removed for export] *)
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PARSE with (h := h1) (LB := LB) (LF := (FB, 2048) :: LF) (A := FB + 32) (DATA := DATA) (n := n) (bs := bs) (lo := lo) (slo := slo) (d := 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehtop, ?Estk, ?Evol, ?Efr; unfold PKCS7_SIZE;
        first [ exact HH1 | exact P7Z | exact F8' | exact OBJ1 | exact CW1 | exact BY1 | exact LEN | exact Hn | exact HD | exact CR1 | exact ST1 | exact SSlo | exact SLOS | exact MI1 | exact TPV | exact SIP1 | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- 0 < FB + 32 => clear - F0; lia
                | |- FB + 32 + _ <= arl_stklo R => clear - F1 ALO; lia
                | |- FB + 32 + _ <= hl_data_lo _ \/ _ => clear - F2; lia
                | |- 1 <= n -> _ => intros H1; rewrite Ehcs; exact (OD1 H1)
                | |- DATA + n <= lo \/ _ => clear - DLO SP1; lia
                | |- n = 0 \/ DATA + n + 8 <= _ => exact D47
                | |- n = 0 \/ _ => clear - APD; lia
                | |- slo <= lo => exact SLOL
                | |- lo <= sp1 - STKp => clear - SLO FSp SP1; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => pose proof (PHIf_mono 0 (CNTp n) ltac:(split; [clear; lia| apply CNTp_nn; clear - Hn; lia])); unfold PHI in BUD; clear - BUD H; lia
                | |- uwc _ _ _ _ _ _ _ => exact UWF
                | |- hfr _ _ _ _ + _ <= FR_MAX => pose proof (FFRf_mono 0 (CNTp n) 0 ltac:(split; [clear; lia| apply CNTp_nn; clear - Hn; lia])); unfold FFR in BUDF; clear - BUDF H; lia
                | |- (length _ <= 33)%nat => cbn [length]; clear - LFB; lia
                end
              | match goal with |- ?g => idtac "PARSE-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 mo2 (mo1 & [HK1 MF1] & PO).
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & mo2' & h2 & st & LBn
                    & E2 & MI2 & ST2 & SS2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HCNT & REP2 & HH2 & SIP2).
    injection E2 as Ems Emo. subst ms2 mo2.
    replace (ret_pc (Z_to_bv 64 620248)) with (Z_to_bv 64 620248 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, SS2, HP2 by exact SP1R.
    rewrite Ehtop in HT2. rewrite Estk in HS2, HP2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2. unfold PKCS7_SIZE in HP2.
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R LB LF sp1 sp1 (hstkhi asegs R HIA h) (si_fp SI) m1 m2).
    { eapply (presA_drop_fresh_gen R LB LF sp1 sp1 _ (si_fp SI) FB 2048 (FB + 32) (FB + 32 + 1440) m1 m2); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO SP1 FS1 NS1; lia].
      eapply presA_weaken; [exact HP2| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    (* [comment removed for export] *)
    assert (PRESb : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (si_fp SI) m m2).
    { destruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]|].
      eapply presA_weaken; [exact HP2'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - SP1; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRES2 : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m2 m2).
    { split; [apply presA_refl| exact (proj2 PRES)]. }
    (* [comment removed for export] *)
    assert (SH184 : Z.shiftr (FB + 1472) 3 = Z.shiftr FB 3 + 184) by (rewrite !Z.shiftr_div_pow2 by (clear; lia); clear - F64; Z.div_mod_to_equations; lia).
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 2048 -> cshd R LBq ((FB, 2048) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 2048). split; [left; reflexivity| cbn; exact Hc]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 FB c1 CSOK) in SHF1;
      [| rewrite SZ1; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP2 | rewrite SZ1; intros c Hc; apply CSHD; clear - Hc; lia ].
    rewrite <- Z.add_assoc, (Z.add_comm (al_sb AL) 4), Z.add_assoc, <- SH4 in SHOBJ.
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 (FB + 32) [CB 180 (repeat (Z_to_bv 8 0) 180)] CSOK) in SHOBJ;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    rewrite <- Z.add_assoc, (Z.add_comm (al_sb AL) 184), Z.add_assoc, <- SH184 in SH3R.
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 (FB + 1472) c3 CSOK) in SH3R;
      [| rewrite SZ3; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP2 | rewrite SZ3; intros c Hc; apply CSHD; clear - Hc; lia ].
    (* [comment removed for export] *)
    apply (presA_rw_cells asegs R LB ((FB, 2048) :: LF) sp1 sp1 (hstkhi asegs R HIA h) ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) m1 m2 FB _ HP2) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia]
       | cbn [cells_size csize Nat.add]; apply (proj2 (disjoint_from_app _ _ _ _)); split; [cbn; clear; lia| apply si_disjoint_off; clear - F2; lia] ].
    (* [comment removed for export] *)
    assert (UWF2 : uwc asegs m2 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 1).
    { eapply uwc_presA; [exact HP2'| exact UWF| clear; lia| | clear - SP1R; lia| apply hstkhi_le64].
      intros a Ha. apply si_outside_above. pose proof (art_data_lo asegs R HIA). clear - Ha H ALO LOS SLO SP1 FS1 NS1. lia.
      clear - LOS SLO SPR FS1 NS1; lia. }
    clear UWF OBJ1 BY1 OD1 MI1 ST1 HH1 SSlo SS1 PRES.
    (* [comment removed for export] *)
    pose proof (art_data_lo asegs R HIA) as DLOW.
    assert (DJ : forall A k, sp1 <= A -> disjoint_from ([(FB + 32, FB + 32 + 1440)] ++ si_fp SI) A k).
    { intros A k HA. apply (proj2 (disjoint_from_app _ _ _ _)). split; [cbn; clear - HA F1 ALO LOS SLO FS1 NS1 SP1; lia|].
      apply si_disjoint_off. right. clear - HA DLOW ALO LOS SLO FS1 NS1 SP1. lia. }
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJ; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SLOT; [| apply client_range_stack; clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in STlo; [| clear; lia| apply DJ; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SThi; [| clear; lia| apply DJ; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SShi; [| clear; lia| clear - HTOP TOP; lia].
    clear HP2 HP2' DJ.
    pose proof (sshad_merge asegs AL m2 slo sp1 (bv_unsigned sp) SS2 SShi ltac:(clear - SP1 SLOL SLO FS1 NS1; lia)) as SSm2. clear SS2 SShi.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo) as KINV.
    clear HK1 MF1 MF2 mo1 HK2.
    zstep. zstep.
    assert (OBJ2 : aobj asegs AL (hcs asegs R HIA h2) m2 (FB + 32) 1440).
    { change 1440 with (8 * Z.of_nat 180).
      eapply (aobj_of_zshadow asegs AL _ m2 (FB + 32) 180 (hcs_ok asegs R HIA h2)); [exact SHOBJ| | exact F8' | clear - F0; lia].
      eapply crange_mono; [exact HCS2|]. rewrite Ehcs. eapply crange_sub; [exact CFB| clear; lia| clear; lia]. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply FREE with (h := h2) (LB := LB) (LBn := LBn) (LF := (FB, 2048) :: LF) (A := FB + 32) (lo := lo) (d := 0) (st := st);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?HT2, ?HS2; unfold PKCS7_SIZE;
        first [ exact HH2 | exact HK1 | exact REP2 | exact F8' | exact OBJ2 | exact CW1 | exact ST2 | exact LOS | exact MI2 | exact TPV | reflexivity
              | lazymatch goal with
                | |- 0 < FB + 32 => clear - F0; lia
                | |- FB + 32 + _ <= lo \/ _ => left; clear - F1 ALO LOS; lia
                | |- lo <= sp1 - STKf => clear - SLO FSf SP1; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX =>
                    pose proof (PHIf_mono (Z.of_nat (length LBn)) (CNTp n) ltac:(split; [clear; lia| exact HCNT])) as PM; unfold PHI in BUD; clear - BUD PM HV2; lia
                | |- uw_obj R _ _ _ => left; split; [clear - F1 ALO; unfold PKCS7_SIZE; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX =>
                    pose proof (FFRf_mono (Z.of_nat (length LBn)) (CNTp n) 0 ltac:(split; [clear; lia| exact HCNT])) as FM;
                    pose proof (FFRp_nn n 1 ltac:(clear - Hn; lia)) as FP; unfold FFR in BUDF; clear - BUDF FM FP HFR2; lia
                end
              | match goal with |- ?g => idtac "FREE-PRE-LEFT:" g end ]. }
    cbv beta. intros ms3 mo3 (mo1 & [HK1 MF1] & PO).
    destruct PO as (u0' & u1' & u2' & va0 & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & m3 & mo3' & h3 & LBx
                    & E3 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & ZERO3 & LENx & HH3).
    injection E3 as Ems Emo. subst ms3 mo3.
    replace (ret_pc (Z_to_bv 64 620256)) with (Z_to_bv 64 620256 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    rewrite HT2 in HT3. rewrite HS2 in HS3, HP3. rewrite HF2 in HF3. unfold PKCS7_SIZE in HP3.
    assert (HP3' : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) [] m2 m3).
    { eapply (presA_drop_fresh_gen R LB LF sp1 (arl_stklo R) _ [] FB 2048 (FB + 32) (FB + 32 + 1440) m2 m3); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS SLO SP1 FS1 NS1; lia].
      eapply presA_weaken; [exact HP3| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) (si_fp SI) m m2 m3 LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) []) in PRESb;
      [| exact HP3' | intros b Hb; exact Hb | intros b Hb; exact Hb | clear - SP1; lia | clear - SLOS SLOL SLO FS1 NS1 LOS; lia | clear; lia | intros xo _; exact I ].
    apply (presW_call asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) [] m2 m2 m3 LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) []) in PRES2;
      [| exact HP3' | intros b Hb; exact Hb | intros b Hb; exact Hb | clear - SP1; lia | clear - SLOS SLOL SLO FS1 NS1 LOS; lia | clear; lia | intros xo _; exact I ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 FB c1 CSOK) in SHF1;
      [| rewrite SZ1; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | rewrite SZ1; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 (FB + 32) [CB 180 (repeat (Z_to_bv 8 0) 180)] CSOK) in SHOBJ;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8' | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 (FB + 1472) c3 CSOK) in SH3R;
      [| rewrite SZ3; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | clear - F64; Z.div_mod_to_equations; lia | clear - F0; lia | exact HP3 | rewrite SZ3; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 2048) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(FB + 32, FB + 32 + 1440)] m2 m3 FB _ HP3) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | cbn; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SAVE; [| apply client_range_stack; clear - SP1; lia| exact I].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SLOT; [| apply client_range_stack; clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in STlo; [| clear; lia| exact I].
    apply (presA_stk asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SThi; [| clear; lia| exact I].
    apply (presA_sshad asegs R _ _ _ _ _ _ m2 m3 _ _ HP3') in SSm2; [| exact SLOS| clear - HTOP TOP; lia].
    clear HP3 HP3' OBJ2 MI2 ST2 HH2 REP2.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    clear LAWS KINV HK1 MF1 MF3 mo1.
    rewrite SH4 in SHOBJ. replace (Z.shiftr FB 3 + 4 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 4) in SHOBJ by (clear; lia).
    rewrite SH184 in SH3R. replace (Z.shiftr FB 3 + 184 + al_sb AL) with (Z.shiftr FB 3 + al_sb AL + 184) in SH3R by (clear; lia).
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3, HCS2; rewrite Ehcs; exact Hx).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo).
    { eapply (epi_walk h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DATA n lo slo bs
                SLOS SLOL SLO TOP SPH LFB h3 (LBx ++ LB) m m2 m3 FB sp1) with (c1 := c1) (c3 := c3);
        first [ exact HH3 | exact HCSh3 | exact HT3 | exact HS3 | exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact AP | exact FHD
              | exact SHF1 | exact SZ1 | exact SHOBJ | exact SH3R | exact SZ3 | exact SAVE | exact SLOT | exact STlo | exact SThi | exact ST3 | exact MI3
              | exact PRESb | exact PRES2 | exact SSm2
              | intros b Hb; apply in_app_iff; right; exact Hb
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold fuzz_postA.
    do 14 eexists. exists m9, mo9, h4, LBx.
    split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [exact MF9|].
    split; [exact (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES9)|].
    split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
    split.
    { rewrite E4vol. pose proof (PHIf_mono (Z.of_nat (length LBn)) (CNTp n) ltac:(split; [clear; lia| exact HCNT])) as PM. unfold PHI. clear - HV3 HV2 PM. lia. }
    split.
    { rewrite E4fr. pose proof (FFRf_mono (Z.of_nat (length LBn)) (CNTp n) 0 ltac:(split; [clear; lia| exact HCNT])) as FM. unfold FFR. clear - HFR3 HFR2 FM. lia. }
    split; [exact HH4|].
    (* [comment removed for export] *)
    eapply (si_heap_presx asegs L SI); [exact SIP2| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES29))| intros a _; exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

(* [comment removed for export] *)
