(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_SFree5 AW_FakeDefs AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007dc0a3b3bfaf10 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P01bdde014d72ec5a 1 1 7340032 7 0 2048 35 63488 50 256 64 256 66 256 67 256 68 2048 3 45 1 67 1 69 4096P02ac76cedf3bbf5f 0 4 1 1 20 1 21 1 22 1P049d033ea07146e9 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P04a7355732969ea4 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P04d9ec73a46d0278 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P0529f9852daf90f3 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P05596128d65fe17b 0 2 0 1 54 1P059f9b4b8b3328cd 0 6 0 8 36 8 65 8 66 8 67 8 68 8P05ea08bc82d6e629 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0677b1d0ac59dde8 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P06d39468517bf927 0 2 1 1 40 1P06f33c60d69c201a 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P07888c185a2c43cc 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P07965b01c5855d15 0 6 0 8 36 8 65 8 66 8 67 8 68 8P085ae85afa2d1ffc 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P08fafdfd0ac74d27 0 2 1 1 40 1P097f372004337106 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P097fe9a9ad59ffe1 0 6 0 8 36 8 65 8 66 8 67 8 68 8P0989c8c450da7107 1 1 7340032 7 0 2048 35 63488 50 256 64 256 66 256 67 256 68 2048 3 45 1 67 1 69 4096P09917750c6d4d91f 1 1 8 3 0 1 63 1 64 1 4 38 1 62 1 65 1 66 8P09cf4866a73b5ec1 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P0afce5bb9d6d079d 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0b471c541164b7b5 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0b4f87f317687bd4 1 1 8 3 0 1 61 1 64 1 4 36 1 62 1 63 1 65 8P0c33c081d861aa84 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0cb3c2036adbd947 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P0ceaa9c1e0324941 0 2 0 1 19 1P0dee8c5ef549bfea 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0e14384043e6d06c 0 2 1 1 40 1P0e5475e5040666c3 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P0e826bf1a57a3b43 1 1 7340032 7 0 2048 35 63488 50 256 64 256 66 256 67 256 68 2048 3 45 1 67 1 69 4096P0ea4f6f249b4101f 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0f40dd81a31133ff 0 2 0 1 54 1P0f6ef7960695f2f5 0 2 1 1 40 1P0f8910646774d51b 0 6 0 1 51 1 52 1 57 1 62 1 63 1P0f8b0242c211e07b 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0f91953fc278a339 0 5 0 8 36 8 45 8 65 8 66 8P0fe4fd4c6324914f 0 2 0 1 54 1P106cf0758a2d2041 0 2 1 1 40 1P107276998160769a 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P10756736c25a7810 0 2 1 1 40 1P1142ed0e9a551d35 0 2 0 1 54 1P1208bb55a70a3b75 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P13077a3317073eab 0 2 0 1 19 1P142ecdeeb83971fd 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P144f165df6fb44ff 0 2 0 1 19 1P1478bec7b946963b 0 2 1 1 40 1P14da9f6d4d9a17b2 0 2 1 1 40 1P150f4ee37462565b 0 4 1 1 20 1 21 1 22 1P155a87c9d89bf08a 0 4 1 1 18 1 20 1 21 1P15fb39e761d03ad1 0 2 0 1 13 1P164a8a5e32d2da64 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P166964cd5e7ad39e 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P1691418cb78443cd 0 4 1 1 20 1 21 1 22 1P1693c96cfbb6eca4 0 2 0 1 19 1P16c95614ba126423 0 4 0 8 4 8 65 8 66 8P16fb1c30f72e0231 0 2 1 1 40 1P1704bf74511f91aa 0 6 0 8 36 8 65 8 66 8 67 8 68 8P1723af1695723f39 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P17894c6a36967195 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P178ffa82e8200a3c 1 1 2040 7 0 256 50 1 64 1 65 256 66 1 67 1 68 256 6 35 256 50 1 64 1 66 1 67 1 69 8P17b5cdb9f78252f8 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P17d7385b173b19cf 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P186b3daa81f6f34d 0 2 0 1 15 1P18706777b504862b 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P188222f8caf1f1c2 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P196fccaad989d676 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P19cb29778c32f2bc 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P19e82a52905d8cd3 0 2 1 1 40 1P19f850818a59b0e6 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P1a88b33644b2e013 0 2 0 1 54 1P1b725ba0c67bc68b 0 2 0 1 19 1P1c1df13e8c7231d7 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P1c58122cdb9acba4 0 4 1 1 20 1 21 1 22 1P1c60c448dcfbb39b 0 2 0 1 15 1P1c610e81a5d3696d 0 2 0 1 42 1P1c616547caf813a2 0 2 0 1 42 1P1cc9d22cf59c5bde 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P1d7440f1fe2f7d99 0 4 0 1 14 1 15 1 16 1P1d74eaa2a3307f03 0 4 1 1 20 1 21 1 22 1P1df1b2e334dd0442 0 2 0 1 54 1P1ec219faebe9c200 0 4 0 8 4 8 65 8 66 8P1ef8c52b3b13b731 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1f00006c8db672ae 0 2 0 1 19 1P1f8368e4f2bc11be 0 4 1 1 20 1 21 1 22 1P2177b56522f5977d 0 2 0 1 13 1P2205b60af074f94e 1 1 2040 7 0 256 50 1 64 1 65 256 66 1 67 1 68 256 6 35 256 50 1 64 1 66 1 67 1 69 8P221272669f1cee9a 0 2 0 1 54 1P2240f53a2fac3521 0 2 1 1 40 1P2261df2c5c609e00 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P2263694e411703d3 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P226bc64a95711211 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P229c0ad3be3f32ea 0 4 1 1 18 1 20 1 21 1P237c4548c06d0434 0 8 0 8 34 2048 40 8 49 8 60 8 63 8 65 8 66 8P2389388b159778fa 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P23be7b4d041cd3e4 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P23c0194426e77fd2 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P2459b5b6ee2ba8a1 0 2 1 1 40 1P246b3f9fd9c63241 0 2 1 1 40 1P24f90dcf11dcbd54 0 6 0 8 36 8 65 8 66 8 67 8 68 8P255135a1cef6c86c 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P25abd76091f4058e 0 4 1 1 18 1 20 1 21 1P25d4bb71be912b72 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P262e0d948b0e40e4 1 1 8 3 0 1 62 1 63 1 4 37 1 61 1 64 1 65 8P26a147a625681c5f 0 2 0 1 54 1P2826e8f2d03c1d1b 0 2 1 1 40 1P28d27d079b49169d 0 2 1 1 40 1P291d66430b6a60db 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P293c236f8ddf8312 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P2a0a91accb467b4d 1 1 2040 7 0 256 50 1 64 1 65 256 66 1 67 1 68 256 6 35 256 50 1 64 1 66 1 67 1 69 8P2b0c7c1e80a5489a 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P2b8166e364474ec4 0 6 0 8 36 8 65 8 66 8 67 8 68 8P2c318fcaf61d547a 0 2 0 1 19 1P2cb99a01c8754cf9 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P2d0f4f07f16fb32d 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P2d28874121d095c2 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2d3c36f4eab2ef9b 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P2e7a494c71d8a791 0 2 0 1 19 1P2e8370cde8fc47d8 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2eaca0b5f8585ad1 0 2 1 1 40 1P2ec8d4a280c45a02 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P2f308c8a3bbb5d3e 0 2 1 1 40 1P2f5ee3b0ae4e338d 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2fb50e953988a46f 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2fd4d946da0b8586 0 2 1 1 40 1P3081f17a132f6789 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P30a05c5a9d2f8e26 1 1 2040 7 0 256 50 1 64 1 65 256 66 1 67 1 68 256 6 35 256 50 1 64 1 66 1 67 1 69 8P30c2e469036ec001 0 2 0 1 19 1P30d091f60fae2629 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P31055ad1a81f47e2 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3121b12d742b9f66 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P317eadb928f4ff43 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P31995b66c06ac78d 0 2 0 1 7 1P3251b209936af5ca 0 2 0 1 19 1P32b9b77f7fcb8ab0 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P346475158e750ee4 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P3483a4d1b93c2198 0 2 0 1 19 1P348dd770f2459072 0 6 0 8 36 8 65 8 66 8 67 8 68 8P34b9d2b2f6666d6e 0 2 0 1 54 1P34f52176f5ec0855 0 2 1 1 40 1P35a725f4c2ac0827 1 1 7340032 7 0 2048 35 63488 50 256 64 256 66 256 67 256 68 2048 3 45 1 67 1 69 4096P35abde1413670604 0 2 1 1 40 1P370fd3338e99e9f3 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P37c396cdfeee52a8 0 2 1 1 40 1P37dcc8b95122a84a 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P380cb912cbea5f2e 0 2 0 1 13 1P381cd6d15aeea426 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P385eeccaa906e4cd 0 4 1 1 20 1 21 1 22 1P3885c4551a40ca9e 0 2 1 1 40 1P38d87bf3f28b7cb0 0 2 0 1 13 1P3953cf8606df6a18 0 2 1 1 40 1P3a3beefd3816ac81 0 4 1 1 18 1 20 1 21 1P3b5629751b4e77e9 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3b76835ef73d9683 0 2 0 1 13 1P3c02a863fb5c07ba 0 4 1 1 20 1 21 1 22 1P3ccae1b79c835681 0 2 0 1 54 1P3d1c7fe89ed2de46 0 2 0 1 19 1P3d2c6a5f68669936 0 1 1 1P3d9e4ebea5a0659d 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P3e44f1beb5bce5d7 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3e58861d01f5eebb 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P3e758e377319fe4f 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3f30a8f26f7b0e95 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P3f83df081336946c 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3f870acf45ed5853 0 2 1 1 40 1P3fb2feff81ca8f5e 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P3fcbdd7f7ba8d61d 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8N0007ae46d3cd089fN007d88074179b85fN0080a311d300b2a5N00af420ac25a5a33N00bbecb98f0253d3N01091dc883d1ec55N019dadef14d1c22fN01f250e62315b15bN0220abf7cc0fb074N02565c5d3a9c7e71N0258ce4594670321N0337867459680de1N0344151202237b9dN039568d7087847f2N039756cc44da27deN03c7f18f994edf74N03fc16c81d99f79fN048ae4c85d798638N04adba376b91850bN04cc30d6cb901db4N053e0c57e5829d77N0544b555ccc469d9N058839cd28255e69N062f24a1379ffe74N06454224493f5815N065e21956380f681N06de5b1bee87cdccN06fc99b32f5cf044N0735efc63c526cb8N07531a7ae2772825N08171a5caa1f0d44N082ef8655e42f495N088cd109d8b715f9N08a58a11cf6aab7bN08cdaf8ae4169743N08dd1ef82511f544N0989c7773f1af631N09f119a0abd7b419N0ae709c1a95a6bd5N0b129a75ea9b94fcN0b5ce49e89b10747N0b7638031d7ea57cN0b787b7f2327c578N0c045555b7f48318N0c2aa5d923a7b42aN0c3fef343b905d7fN0c5abf26eeb313fdN0d206b3ba1522fa9N0e283b2ddb7d377bN0e58f09e0d5d455fN0e74e0f75545b923N0e7b480d891237aeN0e89acd2d43933a8N0ebfec4353f2e57eN0f76e5378bb15547N0fcd2199cd325c3fN0fe26c94f637d907N0ff225dd0558c50bN10016575241ca109N10040cba36853f9eN10278722f2b70ba4N1061d5e518a7dcfaN106afcbafa5c0c68N108a8ed7dc8934ccN10b5de2c68445fbfN117fd116669b737eN11c8bbab13bbe0d5N11e4f5fd16219139N11ed8f8243187e47N11ffbc902a331cb1N1212d853d1232cb9N12361284e3f9a73bN12951f1621330ab9N12a7e893647b61dfN12c9f17ec4a3f63dN1304ef7873c3049eN1362aaad7410372bN13beef68f699f843N13cd37474aebdbacN13ea4659dab9f770N1414c5a0955ab4abN14579f10a89840a7N148ec0bb8c490d9dN149463303378b676N14b2c61bfd4972c9N1508ac27a70d30faN15292ac732e78711N152c396820971b15N1537254b798a8149N154b066055ac83a5N1585ed1caa3d7c18N15ace1afa65f819eN16658788e14e914fN16a04c69337add32N16f077f009efd89eN1714b52195de7c5aN1749cbb84363d44cN1753daaafefc153eN177eb012ff3ec495N17cc1126c96e9588N17ffa1cf488da9a4N19587f2d0e517c55N1974a05f470075c1N197a950d79929cddN197ecc0a63c47670N19a4aaf564f8cba9N19ac90b046d7076dN19fcaf79fb1f7a86N19fdbefd1d5c199dN1a1622f2c1ec208dN1a3496d1e9fc0271N1a412916df3a730bN1a5a8155441ebd49N1a77e64e1818b5dfN1ac14b4a23990698N1ae0122074aa7253N1afcaf3e46e3134dN1b3414619d3c1b51N1b9ae3702dadf628N1ba06062030d3cb5N1ba29200d7d0afb6N1c5c3ca53cf7d394N1c7d651c5b78b4a6N1c7fd250c9ac5b98N1cc0855945537feeN1cd2610f40b881c5N1cd527ba75b9f12aN1d4491b7d32612d6N1e235d54c5fd6ee8N1eab496f434d4f66N1f4eebd3564b6d67N1f6ed898d1121b57N1fd6850969b2603bN1ff7d7e492feea3bN208a828ff3343aa4N20a91e10c544e710N20d404ce360cef93N210ed9a5867cbca4N21313f01c04de249N2137412dd1f6a956N214d7c803bc3605fN21525902dbd4d404N2167433e21156f2dN217311456915b393N21798d6bf409ba51N21d70b3ed95ed0f3N21f7e060f6134cccN220323dfb99a1855N220c00d3a8b4d5efN227082d6b6358a09N2323b7d64e1f360eN232a2b521ecc5a0fN232cdc19fe15e427N23550cc727fd35bbN23e2f187eeb984dfN246eaafc1da48870N24f9c549e354890cN257f0acb92411adaN258197ae26c53a39N25aef84169bc366aN25ba5c0cc212c99fN25d2a7bf4bf6ce39N25d31982c7e2fb0bN25d7cf7bff60343cN25e0298665aa0793N25f541966bbba639N26559064695e2d71N2713d6cd57cabd82N27f2e38b60c04e73N2812312140929e45N286bb68f00ede23cN291fe41aa6e94dcfN2930d29ef7c419a6N29476c1ebedf1fcfN2955d370abd6b44dN2967b29d4d56f441N2985e2b39e642e16N299ecd5a9df1daeaN29b4bca37dab6305N29dbc0e2255e9203N2a4b91d8d7abecb9N2afe7f703eff477aN2bed3dd21da2ecb4N2cabebc29e6c3709N2cca6c1d4d2703d7N2cda3e3e6d9ff866N2ced641446ba7906N2d34ad986179b527N2e0da401f059b8b6N2e6a5bcbf7ad483dN2e82a91d4682b26eN2e8f8fd34713658cN2eb20e1d6849be38N2ebf81910ea0fa55N2f13c217c208fc81N2f366ad88d9bd8a0N2f6fedb25aa1afd4N2f90d6da7c29c317N2f9510ead40e11dcN2fa8767f1419b20fN3001ab57586d6211N30e70a816e957cbaN3190285f14319b98N31d3fb6cfb2181d7N31dc15525b0fd6a7N31e7c7c91b00243dN31ec3d1b337f1c0aN3254d149903afcacN32be90b3cd43b5b3N330d092564db68ceN33681a51d6e3c42bN3377c903dc48c569N33fb4e4bdb09939bN3410e5e8114653bdN346d5e157b4a2f30N34ab022f07a7ae50N34cac3122bfde405N3506f63e46c20c6fN351caf7ad37e35afN35507333ebb7cb0eN35aa0e2c9b8af221N35af6e187b6a4d35N3674ac0124529bdfN36d1d29c80d5afdbN3709d8e6b447a5f2N3711f28b76ee43aaN373d4cc1f5e75a79N37840d43c788e3beN37e35ad5b94aa90dN38280239eb65a41fN3863b5834c3f522eN3872abcb8d60d85eN38be98ebb73298b4N38befbebc6ccb643N38bf6f67d68a1142N38e4687267e6ff02N390d68f8abc56503N396490866b2b5230N39980fc2bea6a3f7N3a25e24930ff0fe2N3ac57b12f837e149N3b36e2ec4c0785e3N3bbb007dd9238d1bN3bd5571bdce5c7e7N3c1b83d96ca3af83N3c33a85b507209f2N3c412f15fb4a6a99N3c6e5d2b90b4e3adN3c898bd448040f66N3c971531d7ed5dc2N3d0e82389c34f3f1N3d15efc8e7a8e834N3dd0c81905577dbfN3dd722e73dc764d8N3e66780c70b62141N3e792670b11f8c0fN3e843eb5ccae6d04N3ee2424ca7bbfbb7N3ef7c6714fefdbfbN3f63e7f9eab035ebN3f6d91ebae8a4cc5"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_SMalloc2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_SM2_RA"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.SMalloc2.sm2_regs"; "ARUN_1.A_SM2_FOUND"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "ARUN_1.A_SM2_NONE"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.SMalloc2.scan2_post"; "ARUN_1.A_SM2_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.smalloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.SMalloc2.sm2_A_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.A_SMALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.shd"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.SMalloc2.sm2_found_post"; "ARUN_1.SMalloc2.smalloc2_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SM2_RA : Z := 0x53220.      (* [comment removed for export] *)
Definition A_SM2_LOOP : Z := 0x53290.    (* [comment removed for export] *)
Definition A_SM2_NONE : Z := 0x532ac.    (* [comment removed for export] *)
Definition A_SM2_FOUND : Z := 0x53308.   (* [comment removed for export] *)

Section SMalloc2.
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
  Definition sm2_regs (SP FS : Z) (gp x5 t1 t2 a0 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "(0.(1.&40.$2.)(1.&40.(3.O18.-20.))O16.(1.&40.$4.)O15.O14.O13.(1.&40.O18.)(1.&40.O17.)O12.(1.&40.(3.O17.+1000.))O11.(1.&40.(3.O17.+7000.))(1.&40.+???.)O10.O?.O>.(1.&40.+14.)O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition scan2_post (SP FS : Z) (gp t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m : mem) (r cur : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Lms',$5.(6.(7.$8.Lr',$8.(7.$8.Lc,$8.(7.$8.Lpos,$8.(7.(9.&8.)Lb,(9.&8.)(:.(:.(;.=R3.)(<.R3.(=.+2.+40.)))(:.(>.$8.R2.(?.R3.+1000.))(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.R2.))(13.(9.&8.)R1.))(:.(>.$8.(14.&8.R1.)=)(>.$5.R5.(15.(16.O19.O18.O17.(1.&40.=)O16.O15.(1.&40.R4.)(1.&40.R3.)(1.&40.(3.(3.O18.+7000.)R2.))O14.(1.&40.R2.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$17.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))))(:.Pj,$8.P,(:.(;.=R1.)(<.R1.O2.))(7.(9.&8.)Lb,(9.&8.)(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.(?.(3.O1.R3.)+1000.)))(13.(9.&8.)R1.))(1;.(>.$8.(14.&8.R1.)=))))(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(>.$5.R5.(15.(16.O19.O18.O17.R4.O16.O15.(1.&40.=)R3.R2.O14.R1.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$1<.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11608399893.9L3579524304.1200000100?SS3cur1j1q2rr1D". (* [comment removed for export] *)
  Lemma scan2_shift : forall cur j, (((cur + 1) mod 2^64) + (j - 1)) mod 4096 = (cur + j) mod 4096.
  Proof.
    intros cur j. pose proof (Z.div_mod (cur + 1) (2^64) ltac:(lia)) as D.
    set (q := (cur + 1) / 2^64) in *. set (rr := (cur + 1) mod 2^64) in *.
    replace (cur + j) with ((rr + (j - 1)) + (q * (2^64 / 4096)) * 4096) by (change (2^64 / 4096) with 4503599627370496; lia).
    rewrite Z_mod_plus_full. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12529075241.4 L13278302029.2 L16980495076.53L18941427511.49L23970772284.56L2625671488.7  L28925203287.44L29008555810.55L3396492593.5  L36364150030.53L59310648043.5 L60519880076.2 L6343387025.5  L64930759789.5 L8929160544.6  00000;00C00]00m01D01U03<03S03b04<04O04U04^04m05:S1r1j2Hj2NES3cur2PBS3hAR2nn1r3cur2FS2fl2Hn2PBS3hAR2nn1r2fl2HnS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Kr1j2HjS3hAR2AL2CS1r3cur2gp2x52t12t22a63x153x172s32s42s52s62s72s82s93s103s112t32t42t52t62SP2FS2fl1F2fc1m2Hn2HrS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Hr2KrS3hAR2nn1r3cur2FS2fl2Hn2PBS3cur2fl3FLL2PB3NTHS1r2HrS2nn1r2HnS2nn1r2Hn2Hr2KrS2nn1r3cur2Hn". (* [comment removed for export] *)
  Lemma scan2_loop : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Pnn,$1=.Pr,$8.Pcur,$8.Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa6,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(>.$8.(20.R1=.)R1<.)P,(:.(;.+1.R1=.)(;.R1=.+1000.))P,(:.(;.=R1=.)(<.R1=.(=.+2.+40.)))P,(21.$1:.R4.(3.R8.+7000.)R7.)P,(>.$8.(20.(22.(9.&8.)R8.))+1000.)P,(23.VCS,(3.R:.+7000.)+1000.)P,(;.+65?000.R;.)P,(;.(3.R<.+;09000.)(24.VhAR,))P,(25.$1:.R9.)(26.$1:.VAL,VCS,(27.R?.R>.R23.R21.R20.R1?.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R<.R;.R=.R:.R25.R24.)(15.(16.R?.R>.R23.R22.R21.R20.(1.&40.R25.)(1.&40.R24.)R1>.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R<.(1.&40.$28.)R;.(18.(9.&40.))R:.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    induction nn as [|nn IH]; intros r cur gp x5 t1 t2 a6 x15 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS fl F fc m
      Hn Hr Hc FLA FLL FLCS FS0 FS1 MI; [lia|].
    facts. unfold sm2_regs, A_SM2_LOOP, A_SM2_RA, A_TP in *.
    pose proof (Z.mod_pos_bound cur 4096 ltac:(lia)) as PB.
    destruct (nth_error fl (Z.to_nat (cur mod 4096))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear -NTH PB FLL; lia].
    pose proof (u8arr_read asegs m (FS + 28672) fl (cur mod 4096) b _ FLA NTH ltac:(clear -PB; lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. first [rewrite (land_4095 cur) | rewrite Z.land_comm, (land_4095 cur)].
    zstep. zstep. clear RD.
    zstep. if_cases Kb; zify_cond Kb.
    - cbv beta. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      replace (Z_to_bv 64 (bv_unsigned b)) with (Z_to_bv 64 0) by (rewrite Kb; reflexivity).
      apply evtA_done. left. exists r, cur, (cur mod 4096), b.
      split; [exact Hc|]. split; [reflexivity|]. split; [exact NTH|]. split; [exact Kb| reflexivity].
    - (* [comment removed for export] *)
      cbv beta in Kb. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      assert (NZ0 : exists b0 : byte, nth_error fl (Z.to_nat ((cur + 0) mod 4096)) = Some b0 /\ bv_unsigned b0 <> 0).
      { exists b. rewrite Z.add_0_r. split; [exact NTH| exact Kb]. }
      (* [comment removed for export] *)
      zstep. rewrite (swrap32_small (r + -1)) by (clear -Hr; lia).
      zstep.
      zstep. if_cases Kr; zify_cond Kr.
      + rewrite <- (zbv_mod64 (cur + 1)).
        eapply evtA_mono.
        * eapply (IH (r + -1) ((cur + 1) mod 2^64)); try eassumption; try (clear -Hn Hr Kr; lia).
          all: pose proof (Z.mod_pos_bound (cur + 1) (2^64) ltac:(clear; lia)) as MPB; clear -MPB; lia.
        * cbv beta. intros ms' [P | [ALL P]]; [left; exact P| right]. split; [| exact P].
          intros j Hj. destruct (Z.eq_dec j 0) as [->|NE]; [exact NZ0|].
          destruct (ALL (j - 1) ltac:(clear -Hj NE; lia)) as (b1 & N1 & Z1). exists b1. rewrite <- (scan2_shift cur j). split; [exact N1| exact Z1].
      + apply evtA_done. right. split.
        * intros j Hj. replace j with 0 by (clear -Kr Hr Hn Hj; lia). exact NZ0.
        * unfold A_SM2_NONE. replace (r + -1) with 0 by (clear -Kr Hr Hn; lia). do 4 eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sm2_A_post (SP FS lo hint : Z) (ra gp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm1,P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(16.O1=.O1<.O18.O17.O16.O15.(1.&40.+1000.)(1.&40.O1:.)(1.&40.(3.O1:.+???.))(1.&40.(3.O1:.+1000.))O12.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(1.&40.$28.)O2.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2=.(2;.$8.$8.)))O1.R1.)(:.(2>.$1:.O1.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.O1=.-20.)(2:.$30.(31.O11.)(2:.$30.(31.O13.)(2:.$30.(31.O14.)(2:.$30.(31.O19.)(2=.$30.))))))(32.$1:.R1.O1;.(3.O1=.-20.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11330676608.7 L11923395103.4 L16143243576.5 L24735900088.5 L26238223716.5 L26680464573.65L27846297964.3 L29753927507.3 L38235734261.1 L3958017386.4  L3958017390.4  L41451455265.0 L41599022925.2 L9448615682.3  L9448615686.2  L9678154644.12 00000F00T00i01>01N01^01e02002402502602702>02?02G02oS3hAR2SP1T2lo2TH5LOIMGS3hAR2lo5LOIMGS3hAR2FS2lo3FSH5LOIMGS3hAR2FS2lo3FSH5LOIMGS2SP2lo2A'2n'2H'S3hAR2SP2lo1y2HyS2SP2loS2SP2lo3SPLS2loFFSS2SP2loFS2SP3SPHS3hAR2SP3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'". (* [comment removed for export] *)
  Lemma sm2_A : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R8.)(6.(;.(3.R8.+1000.)+10000.)(;.+65?000.R8.)))P,(;.(3.R9.+1000.)(24.VhAR,))P,(;.+65?000.R8.)P,(;.(3.R9.+10000.)(24.VhAR,))P,(:.(;.+1000.R;.)(6.(;.(3.R;.+1000.)+10000.)(;.+65?000.R;.)))P,(;.(3.R<.+1000.)(24.VhAR,))P,(:.(;.+65?000.R?.)(6.(;.(3.R?.$33.)+7???7000.)(;.+10007???8000.R?.)))P,(;.(3.R10.$33.)(24.VhAR,))P,(:.(;.=R<.)(<.R<.(=.+2.+40.)))P,(34.R:.R12.R11.R10.R?.)P,(23.VCS,R12.+1000.)P,(23.VCS,R11.+10000.)P,(23.VCS,R13.+1000.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R10.(3.R16.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R?.(3.R17.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R10.(3.R18.+10.)(2:.$30.(31.(1.&40.R13.))(2=.$30.)))P,(23.VCS,R19.+1000.)P,(32.$1:.R12.R16.R1;.)P,(;.(24.VhAR,)R17.)P,(;.R18.(37.R1=.+=0.))P,(;.R1>.(=.+2.+3>.))P,(23.VCS,R1:.(37.R1?.R1:.))P,(25.$1:.R17.)(26.$1:.VAL,VCS,(38.R21.R20.R1<.R1;.R3>.R3=.R3<.R3;.R3:.R39.R38.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1:.R19.R18.)(15.(0.R3>.(1.&40.R21.)R3=.(1.&40.$4.)R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R1:.(1.&40.(39.+2.))R19.(18.(9.&40.))R18.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m
      BL BH CL CH TL TH FSL FSH HNT SS BCS CCS TCS TT HDR HC FCS ST LOIMG SPL SPH SCS MI.
    unfold kHighMemBeg, kFakeBytes in *. cbn [A_SMALLOC].
    flat constr:(SS) 6%nat. intros _ _ _ _ TPFS _. unfold A_TP in TPFS.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide SS. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x5d06c] [] 20%N). lx_unhide.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -32) |- _ =>
      eapply evtA_cut; [eapply (tga_spec AL IMG ALWF CS CSOK) with (SP := SP + -32) (FS := FS) (BLK := BLK) (T := T) (CTX := CTX) (lo := lo) (m := mx);
        first [exact BL | exact BH | exact CL | exact CH | exact TL | exact TH | exact BCS | exact CCS | exact TCS | exact LOIMG | assumption
              | eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL CH BH; lia
              | (flat constr:(TT) 3%nat; flclear TT; intros tb te TT'); exists tb, te; eapply ro_cells_transport; [exact TT'| exact MUl| cbn; clear -LOIMG SPL TH; lia]
              | clear -SPL; lia | clear -SPH; lia
              | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia] ] |] end.
    cbv beta; intros ms1 (mA & x11 & x12 & x13 & MU1 & WM1 & MI1 & ST1 & ->).
    unfold A_TP in *; replace (ret_pc (Z_to_bv 64 0x53220)) with (Z_to_bv 64 0x53220) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP + -32)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRl : rw_cells _ _ (SP + -32) _, TPl : ro_cells _ _ 6539920 _,
                        HDRl : ro_cells _ ?mx' (FS + 88) _, HCl : rw_cells _ ?mx'' (FS + 16) _ |- _ =>
      assert (FR1 : rw_cells asegs mA (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FRl| exact MU1| exact WM1| cbn; clear; lia]);
      assert (TPFS' : ro_cells asegs mA 6539920 [C8 (Z_to_bv 64 FS)])
        by (eapply ro_cells_transport; [exact TPl| exact MU1| apply LO1; cbn; clear -LOIMG H; lia]);
      assert (HDR1 : ro_cells asegs mA (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)])
        by (eapply ro_cells_transport; [exact HDRl| exact MU1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (HC1 : rw_cells asegs mA (FS + 16) [C8 (Z_to_bv 64 hint)])
        by (eapply rw_cells_transport; [exact HCl| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (MU2 : munch [(lo, SP)] m mA) by (lx_munch MUl MU1);
      pose proof (wmono_trans asegs _ _ _ WMl WM1) as WM2;
      clear MU1 WM1 ST MI TPFS HDR HC SS TT; lx_clear_mem mx; rename MU2 into MU; rename WM2 into WM; rename MI1 into MI; rename ST1 into ST
    end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x53290] [] 40%N).
    apply evtA_done. unfold sm2_A_post, sm2_regs, A_SM2_LOOP, A_SM2_RA, A_TP. exists lxm.
    lx_ands; [ lx_mseq | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sm2_none : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Pra,(9.&40.)Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Px12,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+65?000.R7.)(6.(;.(3.R7.$33.)+7???7000.)(;.+10007???8000.R7.)))P,(;.(3.R8.$33.)(24.VhAR,))P,(2?.$1:.R3.(3.R9.+10.)(2:.$30.(31.(1.&40.R7.))(2=.$30.)))P,(23.VCS,R:.+1000.)P,(2?.$1:.R5.(3.R<.-20.)(2:.$30.(31.R1:.)(2:.$30.(31.R1>.)(2:.$30.(31.R1?.)(2:.$30.(31.R24.)(2=.$30.))))))P,(32.$1:.R6.R;.(3.R=.-20.))P,(;.(24.VhAR,)R<.)P,(;.R=.(37.R?.+20.))P,(;.R10.(=.+2.+3>.))P,(23.VCS,R?.(37.R11.R?.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R10.R12.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R11.+10.)(3.R11.+18.))(2=.(2;.$8.$8.))))R<.R;.)P,(2>.$1:.R=.R<.)P,(25.$1:.R=.)(26.$1:.VAL,VCS,Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(0.R2?.(1.&40.R17.)R2>.(1.&40.$4.)R2=.R2<.R2;.R2:.R29.(1.&40.=)(1.&40.(3.R16.+1000.))R28.(1.&40.(3.R16.+7000.))(1.&40.+???.)R27.(1.&40.(3.R14.+1000.))R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R13.(3:.R2?.)R12.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.R15.R17.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R16.+10.)(3.R16.+18.))(2=.(2;.$8.$8.))))R11.R1.)(:.(2>.$1:.R11.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.R16.+10.)(2:.$30.(31.(1.&40.(3.R14.+1000.)))(2=.$30.)))(32.$1:.R1.R15.R17.)))))))(15.(16.R15.R14.R2<.R2;.R2:.R29.(1.&40.=)R26.R25.(1.&40.(3.R12.+1000.))R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(1.&40.$1<.)R10.(18.(9.&40.))R>.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp x5 t1 t2 s0 s1 x12 x15 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo hint F fc m0 m
      FSL FSH HC FCS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm2_regs, A_SM2_NONE, A_SM2_RA, A_TP in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_post.
  Qed.

  Definition sm2_found_post (SP FS lo pos c : Z) (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1<.+2.O1:.)(:.(>.$5.R=.(15.(0.O18.(1.&40.O1=.)O17.(1.&40.$4.)R<.O16.O15.O14.O13.(1.&40.R1.)R;.R:.R9.R8.R7.R6.R5.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(3:.O18.)O3.(18.(9.&40.))R4.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1<.+10.)(3.O1<.+18.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1<.+7000.)O1:.)(3.(3.(3.O1<.+7000.)O1:.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+100.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+20.))(2=.(2;.$8.$8.)))))))O1.R4.)(:.(2>.$1:.O1.R4.)(:.(25.$1:.R4.)(:.(2?.$1:.R4.(3.O1<.+10.)(2:.$30.(31.(1.&40.(3.O19.+1.)))(2=.$30.)))(:.(21.$1:.R4.(3.O1<.+7000.)(3=.(9.&8.)O2.(12.O1:.)(1.&8.+1.)))(:.(2?.$1:.R4.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1=.))(2:.$30.(3>.#=8.R2.)(2:.$30.(31.(1.&40.(3.(3.O1<.+7000.)O1:.)))(2=.$30.))))))(:.(2?.$1:.R4.(3<.R1.)(2:.$30.(3>.#20.(3?.(9.&8.)(1.&8.=)#20.))(2=.$30.)))(:.(40.R4.)(32.$1:.R4.O1;.O1=.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0@L10187340561.104L12378669435.2  L12381266366.102L13335596837.101L13335596837.102L14726470595.3  L1641455751.101 L17120848823.0  L18254172213.2  L21943567510.16 L24642758929.104L24973756177.104L25456994354.101L25458997615.103L27048764373.97 L29984749841.104L3129187939.104 L35842253073.104L38364278545.104L38618536125.2  L38911551578.2  L39188636933.0  L40612932963.104L44706278166.104L45867630865.104L51489812398.73 L53830988561.104L54961663500.97 L55204150092.1  L55588686165.0  L57794683085.104L62746513610.104L65271643703.0  L785926455.9    L8618464589.2   L8701783640.3   00000T00\01001T02802D02^02_02g03Z04>04b05J06206D06h06i07M08108208:08;08R09M0:10:P0;40;F0;J0;K0<60=50=60=Y0=a0=lS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3posS3hAR2FS3pos1c2fl2FBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos3DFSS3hAR2SP2FS2lo3pos1c2fl2FBSS2FS3posS3hAR2SP2FS2lo3pos2FB5LOIMG2PB3FBR2SR4FSL02A'2n'2H'S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos2fl2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0FS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0FS2FS3posSS3hAR2FS3pos1c2fl2FB2PBS3hAR2FS3pos1c2fl2FB3FSA2Hc2HP3HFB3DFS3FBR2SR3FBA4FSL04FSL1S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB1y2HyS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos2fl2PBS2FBSS3hAR2FS3pos1c2fl2FB2Hc2HP3HFB3DFS3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB3FSH2Hc2HP5LOIMG3SPL3HFB3DFS3FBR4FSL0SS3hAR2FS3pos2FB3FSL3FSH3HFB3DFS3FBRS3pos2PBS2FS3pos2PB". (* [comment removed for export] *)
  Lemma sm2_found : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa6,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Ppos,$8.Pc,$8.Pr',$8.Ph0,(9.&40.)Pfl,(1>.(9.&8.))Pjunk,(1>.(9.&8.))Psj,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))ZFB,$8.(3;.R=.+2.R;.)P,(:.(;.+65?000.R>.)(6.(;.(3.R>.$33.)+7???7000.)(;.+10007???8000.R>.)))P,(;.(3.R?.$33.)(24.VhAR,))P,(>.$8.(?.R10.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(>.$8.R10.(?.R?.+1000.))P,(2?.$1:.R7.(3.R13.+10.)(2:.$30.(31.R>.)(2=.$30.)))P,(21.$1:.R8.(3.R14.+7000.)R>.)P,(>.$8.(20.(22.(9.&8.)R?.))+1000.)P,(2?.$1:.R:.R9.(2:.$30.(3>.#100.R?.)(2=.$30.)))P,(2?.$1:.R;.(3<.R:.)(2:.$30.(3>.#20.R?.)(2=.$30.)))P,(23.VCS,R18.$33.)P,(40.R=.)P,(2?.$1:.R>.(3.R1;.-20.)(2:.$30.(31.R29.)(2:.$30.(31.R2;.)(2:.$30.(31.R2<.)(2:.$30.(31.R30.)(2=.$30.))))))P,(32.$1:.R?.R1:.(3.R1<.-20.))P,(;.(24.VhAR,)R1;.)P,(;.R1<.(37.R1>.+20.))P,(;.R1?.(=.+2.+3>.))P,(23.VCS,R1>.(37.R20.R1>.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R1?.R21.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R20.+10.)(3.R20.+18.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.R20.+7000.)R1>.)(3.(3.(3.R20.+7000.)R1>.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R13.(3.R13.+100.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R13.)(3.(3<.R13.)+20.))(2=.(2;.$8.$8.)))))))R15.R14.)P,(2>.$1:.R16.R15.)P,(25.$1:.R16.)(26.$1:.VAL,VCS,(41.R24.R23.R22.R21.R20.R39.R38.R37.R36.R35.R34.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1:.R19.R1=.R18.)(15.(16.R24.R23.R38.(1.&40.=)R37.R36.(1.&40.R1?.)(1.&40.R20.)(1.&40.(3.(3.R23.+7000.)R21.))R33.(1.&40.R21.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R1:.(1.&40.$17.)R19.(18.(9.&40.))R17.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' h0 fl junk sj F fc m0 m FB
      FSL FSH FSA Hc HP HC FLA FLL FRM FSHD FCS PS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm2_regs, A_SM2_FOUND, A_SM2_RA, A_TP in *.
    assert (HFB0 : FB = fsk_frame FS 2 pos) by reflexivity. clearbody FB. unfold shd in *.
    assert (HFB : FB = FS + 36864 + 2097152 + pos * 256) by (rewrite HFB0; unfold fsk_frame; clear; lia).
    pose proof (Z.mod_pos_bound c 4096 ltac:(clear; lia)) as PB. rewrite <- HP in PB.
    pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
    assert (FB8 : FB = (FS / 4096 * 512 + 4608 + 262144 + pos * 32) * 8) by (rewrite HFB; clear -DFS; lia).
    assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 262144 + pos * 32) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; rewrite FB8, Z.div_mul; [reflexivity| clear; lia]).
    assert (FBR : FS + 36864 <= FB /\ FB + 256 <= FS + 36864 + 6 * 2^20) by (rewrite HFB; clear -PB; lia).
    assert (SR : 0x80000000 <= 2147450880 + Z.shiftr FB 3 /\ 2147450880 + Z.shiftr FB 3 + 32 <= 0x10007fff8000) by (rewrite FBD; clear -FBR FSL FSH DFS HFB; lia).
    assert (FBA : FB mod 8 = 0) by (rewrite FB8; apply Z_mod_mult).
    clear FB8 FBD.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP); (FS + 16, FS + 24); (FS + 28672 + pos, FS + 28672 + pos + 1); (FB, FB + 256); (2147450880 + Z.shiftr FB 3, 2147450880 + Z.shiftr FB 3 + 32)] m) as MUS.
    pose proof (wmono_refl asegs m) as WMS.
    flat constr:(PS) 10%nat. intros _ GSB SBC GMB MB GME ME GHE HE _.
    unfold A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND in GSB, SBC, GMB, MB, GME, ME, GHE, HE.
    lx_hide PS. lx_aceil. flat constr:(FSL) 2%nat. flclear FSL. intros FSL0 FSL1. flat constr:(FLA) 2%nat. flclear FLA. intros FLAb FLAw.
    (* [comment removed for export] *)
    lx_run (PLAN [0x53318] [] 10%N).
    (* [comment removed for export] *)
    lazymatch goal with FLAl : bytes_at _ ?mx (FS + 28672) fl, WMl : wmono _ m _ |- _ =>
      pose proof (conj FLAl (wr_at_transport _ _ _ _ _ FLAw WMl) : u8arr asegs mx (FS + 28672) fl) as FLAx; clear FLAl FLAb end.
    pose proof (u8arr_store_ok asegs _ (FS + 28672) fl pos _ FLAx ltac:(rewrite FLL; clear -PB; lia) eq_refl) as SOK.
    zstep. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      pose proof (u8arr_write asegs mx (FS + 28672) fl pos (Z_to_bv 8 1) FLAx ltac:(rewrite FLL; clear -PB; lia)) as FLA'
    end.
    store_done. try clear FLAx. try clear SOK.
    flat constr:(FLA') 2%nat. flclear FLA'. intros FLAb2 FLAw2.
    assert (FLz : Z.of_nat (length (upd fl (Z.to_nat pos) (Z_to_bv 8 1))) = 4096) by (rewrite upd_length; exact FLL).
    (* [comment removed for export] *)
    lx_run (PLAN [0x53338] [] 20%N).
    repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] =>
      lazymatch b with context [pos] => replace (a + b) with FB by (rewrite HFB; clear; lia) end end.
    (* [comment removed for export] *)
    destruct FSL1 as [FSLO|FSHI]; lx_run (PLAN [] [] 90%N); lx_unhide;
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', FLl : bytes_at _ ?mx'' (FS + 28672) _ |- _ =>
        apply evtA_done; unfold sm2_found_post; cbv zeta; rewrite <- HFB0; unfold shd;
        lx_exs; lx_ands;
        [ lx_mseq
        | eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUl]; lx_subfp]
        | exact (wmono_trans asegs _ _ _ WM WMl)
        | assumption | assumption
        | split; [exact FLl| rewrite upd_length; exact (wr_at_transport _ _ _ _ _ FLAw WMl)]
        | match goal with K : rw_cells _ _ FB [_; _; _; C8 (Z_to_bv 64 ?e)] |- _ => replace e with (FS + 28672 + pos) in K by (clear; lia); exact K end
        | replace (2147450880 + Z.shiftr FB 3) with (Z.shiftr FB 3 + 2147450880) by (clear; lia);
          eapply rw_cells_reshape; [eassumption| cbn; split; [reflexivity| exact I] | vm_compute; reflexivity]
        | eapply (poison_statics_transport _ _ _ PS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL FSL0 FBR SR PB H; lia
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition smalloc2_post (SP FS BLK T CTX lo hint : Z) (fl : list byte)
      (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.$8.Lr,$8.(:.(>.$5.R;.(15.(0.O17.(1.&40.O1?.)O16.(1.&40.$4.)R:.O15.O14.O13.O12.(1.&40.R1.)R9.R8.R7.R6.R5.R4.R3.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(3:.O17.)O2.(18.(9.&40.))R2.(19.$1:.)))(:.(2>.$1:.O1.R2.)(:.(25.$1:.R2.)(:.(32.$1:.R2.O1:.O1?.)(:.(34.R2.O1>.O1=.O1<.O1;.)(:.(40.R2.)(7.$8.Lpos,$8.(7.$8.Lc,$8.(7.(9.&8.)Lb,(9.&8.)(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1>.+2.R5.)(:.(>.$8.R7.R1.)(:.(:.(;.=R5.)(<.R5.(=.+2.+40.)))(:.(>.$8.R6.(?.R5.+1000.))(:.(>.(10.(9.&8.))(11.(9.&8.)O18.(12.R6.))(13.(9.&8.)R4.))(:.(>.$8.(14.&8.R4.)=)(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1:.O1?.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1>.+10.)(3.O1>.+18.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1>.+7000.)R6.)(3.(3.(3.O1>.+7000.)R6.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+100.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+20.))(2=.(2;.$8.$8.)))))))O1.R8.)(:.(2?.$1:.R8.(3.O1>.+10.)(2:.$30.(31.(1.&40.(3.R5.+1.)))(2=.$30.)))(:.(21.$1:.R8.(3.O1>.+7000.)(3=.(9.&8.)O18.(12.R6.)(1.&8.+1.)))(:.(2?.$1:.R8.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1?.))(2:.$30.(3>.#=8.R2.)(2:.$30.(31.(1.&40.(3.(3.O1>.+7000.)R6.)))(2=.$30.))))))(2?.$1:.R8.(3<.R1.)(2:.$30.(3>.#20.(3?.(9.&8.)(1.&8.=)#20.))(2=.$30.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L16648947209.1 L17120848823.0 L18254172213.2 L2106043955.7  L21943567510.23L222370686.1   L226564034.2   L22706556426.7 L2416881682.3  L24737832984.5 L25336979675.2 L25640760266.1 L27157704107.5 L32165929634.0 L34462518909.3 L36518867962.2 L39188636933.0 L45051584734.1 L47128140407.9 L52172457863.2 L55588686165.0 L62083074719.1 L63489361093.10L63489361093.6 L65271643703.0 L785959728.7   L8618464589.2  L9678154644.5  00000400500=00X02002102:02P02[03103203603L03M03Y03b03c03g04K04L04M04Q05605M05N05k06306CS2FSSS2FS3posS3hAR2FS2lo5LOIMG3pos2FB2SRS3hAR2SP2FS3BLK3CTX2lo2BH2CH3BHI3CHI4SEP14SEP25LOIMG4FSL'4FSH'3pos2PB2FB3HFB2SR2A'2n'2H'FS2FS4FSL'S2SP2FS2lo3pos2FB1y2HyS2SP2lo3SPLS3hAR2FS2lo5LOIMG4FSH'FS2FSS3hAR2FS2lo5LOIMG4FSH'SS2FS3pos3DFSS4hint2i0SS2FSS3hAR2FS2lo5LOIMG4FSH'3pos2PB2FB3HFBFSS2FSS3hAR3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'S3hAR2lo5LOIMG2A'2n'2H'SS3hAR2FS4FSL'4FSH'3pos2PB3DFSS3pos2PBS2SP2lo2A'2n'2H'". (* [comment removed for export] *)
  Lemma smalloc2_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc2 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R9.)(6.(;.(3.R9.+1000.)+10000.)(;.+65?000.R9.)))P,(;.(3.R:.+1000.)(24.VhAR,))P,(;.+65?000.R9.)P,(;.(3.R:.+10000.)(24.VhAR,))P,(:.(;.+1000.R<.)(6.(;.(3.R<.+1000.)+10000.)(;.+65?000.R<.)))P,(;.(3.R=.+1000.)(24.VhAR,))P,(:.(;.+65?000.R10.)(6.(;.(3.R10.$33.)+7???7000.)(;.+10007???8000.R10.)))P,(;.(3.R11.$33.)(24.VhAR,))P,(>.$8.(?.R12.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(:.(:.(;.+1000.R13.)(6.(;.(3.R13.+1000.)+10000.)(;.+65?000.R13.)))(6.(;.(3.R13.+1000.)+7???7000.)(;.+10007???8000.R13.)))P,(:.(;.+65?000.R12.)(6.(;.(3.R12.+10000.)+7???7000.)(;.+10007???8000.R12.)))P,(6.(;.(3.R13.+10000.)R16.)(;.(3.R16.$33.)R13.))P,(6.(;.(3.R16.+1000.)R17.)(;.(3.R17.$33.)R16.))P,(34.R?.R18.R17.R16.R15.)P,(40.R10.)P,(23.VCS,R19.+1000.)P,(23.VCS,R18.+10000.)P,(23.VCS,R1:.+1000.)P,(23.VCS,R1=.$33.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R17.(3.R1>.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R16.(3.R1?.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R17.(3.R20.+10.)(2:.$30.(31.(1.&40.R1;.))(2=.$30.)))P,(21.$1:.R18.(3.R21.+7000.)R1;.)P,(>.$8.(20.(22.(9.&8.)R1<.))+1000.)P,Pi,$8.Pb,(9.&8.)P,(:.(;.=R2.)(<.R2.+1000.))P,(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R3.))(13.(9.&8.)R2.))P,(>.$8.(14.&8.R3.)=)(7.(1>.(9.&8.))Ljunk,(1>.(9.&8.))(7.(1>.(9.&8.))Lsj,(1>.(9.&8.))(:.(2?.$1:.R21.(3;.R2:.+2.R7.)(2:.$30.(3>.#100.R2.)(2=.$30.)))(2?.$1:.R21.(3<.(3;.R2:.+2.R7.))(2:.$30.(3>.#20.R1.)(2=.$30.))))))P,(7.$8.Li0,$8.(7.(9.&8.)Lb0,(9.&8.)(:.(:.(;.=R2.)(<.R2.+1000.))(:.(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R2.))(13.(9.&8.)R1.))(>.$8.(14.&8.R1.)=)))))P,(32.$1:.R1<.R21.R26.)P,(;.(24.VhAR,)R22.)P,(;.R23.(37.R28.+=0.))P,(;.R29.(=.+2.+3>.))P,(23.VCS,R25.(37.R2:.R25.))P,(25.$1:.R21.)(26.$1:.VAL,VCS,(42.R2<.R2;.R2:.R29.R28.R27.R26.R25.R49.R48.R46.R45.R44.R43.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R24.R23.R22.)(15.(0.R49.(1.&40.R2<.)R48.(1.&40.$4.)R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R24.(1.&40.(39.+2.))R23.(18.(9.&40.))R22.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
      BL BH CL CH TL TH FSL FSH FSA HNT BHI CHI SEP1 SEP2 SS PS BCS CCS TCS FCS TT HDR HC FLA FLL HFR FREE ST LOIMG SPL SPH SCS MI.
    pose proof FSL as FSL'. pose proof FSH as FSH'. unfold kHighMemBeg, kFakeBytes in FSL', FSH', BHI, CHI, SEP1, SEP2.
    eapply evtA_cut.
    { eapply (sm2_A ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m);
        first [eassumption | eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia]]. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    assert (FLA1 : u8arr asegs m1 (FS + 28672) fl)
      by (eapply u8arr_transport; [exact FLA| exact MU1| exact WM1| apply LO1; rewrite <- (Nat2Z.id (length fl)), FLL; clear -LOIMG FSH'; lia]).
    assert (HC1 : rw_cells asegs m1 (FS + 16) [C8 (Z_to_bv 64 hint)])
      by (eapply rw_cells_transport; [exact HC| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH'; lia]).
    assert (SS1 : smalloc_statics m1 FS BLK T CTX)
      by (eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG CH BH; lia).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ _ _ PS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG; lia).
    eapply evtA_cut.
    { eapply (scan2_loop (Z.to_nat 4096) 4096 hint); first [reflexivity | exact HNT | exact FLA1 | exact FLL | exact MI1 | clear; lia | idtac];
        [eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia] | clear -FSL'; lia | exact FSH']. }
    cbv beta. intros ms2 [(r' & c & pos & b & Hc & HP & NTH & Hb & ->) | (ALL & x5 & x12 & x15 & x17 & ->)].
    - assert (PB : 0 <= pos < 4096) by (rewrite HP; apply Z.mod_pos_bound; clear; lia).
      destruct (HFR pos b ltac:(clear -PB; lia) NTH Hb) as (junk & sj & FRM & FSHD).
      set (FB := fsk_frame FS 2 pos) in *.
      assert (HFB : FB = FS + 36864 + 2097152 + pos * 256) by (subst FB; unfold fsk_frame; clear; lia).
      pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
      assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 262144 + pos * 32).
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
        replace FB with ((FS / 4096 * 512 + 4608 + 262144 + pos * 32) * 8) by (rewrite HFB; clear -DFS; lia). rewrite Z.div_mul; [reflexivity| clear; lia]. }
      assert (SR : 0x80000000 <= shd FB /\ shd FB + 32 <= 0x10007fff8000) by (unfold shd; rewrite FBD; clear -PB FSL' FSH' DFS; lia).
      assert (FRM1 : rw_cells asegs m1 FB [CB 256 junk])
        by (eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH' HFB PB; lia]).
      assert (FSHD1 : rw_cells asegs m1 (shd FB) [CB 32 sj])
        by (eapply rw_cells_transport; [exact FSHD| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG SR; lia]).
      assert (MUW : munch [(lo, SP); (FS + 16, FS + 24); (FS + 28672 + pos, FS + 28672 + pos + 1); (FB, FB + 256); (shd FB, shd FB + 32)] m m1).
      { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros y Hy. lia. }
      eapply evtA_mono.
      { eapply (sm2_found ra gp t1 t2 s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' _ fl junk sj F fc m m1);
          first [sassumption | cassumption | exact FSL | exact FSH | exact FSA | exact Hc | exact HP | exact HC1 | exact FLA1 | exact FLL | exact FRM1 | exact FSHD1
                | exact FCS | exact PS1 | exact FR1 | exact ST1 | exact LOIMG | exact SCS | exact MUW | exact WM1 | exact MI1
                | clear -SPL; lia | clear -SPH; lia]. }
      cbv beta. intros ms3 (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m3 & j1 & j2 & -> & MU3 & WM3 & MI3 & HC3 & FLA3 & FRM3 & FSH3 & PS3 & ST3).
      unfold smalloc2_post. exists x5, x11, x12, x13, x14, x15, x16, x17, m3, FB.
      split; [reflexivity|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU3). intros A' n' H'. cbn. change (fsk_frame FS 2 pos) with FB.
               clear -H' LOIMG CH BH FSL' FSH' HFB SR PB BHI CHI SEP1 SEP2. lia. }
      split; [exact PS3|].
      exists pos, c, b, j1, j2. cbv zeta.
      split; [reflexivity|]. split; [exact Hc|]. split; [exact HP|]. split; [exact NTH|]. split; [exact Hb|].
      split; [exact MU3|]. split; [exact HC3|]. split; [exact FLA3|]. split; [exact FRM3| exact FSH3].
    - (* [comment removed for export] *)
      exfalso. flat constr:(FREE) 5%nat. flclear FREE. intros i0 b0 Hi0 N0 Z0.
      destruct (ALL ((i0 - hint) mod 4096) ltac:(apply Z.mod_pos_bound; clear; lia)) as (b1 & N1 & Z1).
      rewrite Zplus_mod_idemp_r in N1. replace (hint + (i0 - hint)) with i0 in N1 by (clear; lia).
      rewrite Z.mod_small in N1 by exact Hi0. rewrite N0 in N1. injection N1 as <-. exact (Z1 Z0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SMalloc2.

End ARUN_1.
