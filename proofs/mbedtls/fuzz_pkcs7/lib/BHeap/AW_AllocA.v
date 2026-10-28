(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001afba451cfdb2b 0 2 0 1 40 1P00f4055dace2efda 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P019bfe5e36248b4a 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0201388d6b7d3e6f 0 4 0 16 53 16 55 16 56 16P02082cff4b1b58b3 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P020af67e60b3fb48 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P022468fdeb4a774e 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0290bd555422c697 0 4 0 16 53 16 55 16 56 16P0291246af879ac34 0 6 1 16 52 16 54 16 55 16 56 16 57 16P02a3f84bd6630170 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P02dcb0bc0ca69d1c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P035a92798b6b3d3b 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P037dc5cb3341494a 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P03ae3802b0345ddf 1 1 16 2 1 1 53 1 5 49 1 51 1 52 1 54 1 55 16P053eec529f04427c 1 2 16 2 0 1 54 1 16 2 1 1 53 1 2 55 1 56 1P059092d9ddac94f3 0 4 0 16 53 16 55 16 56 16P05c1ad16239f342a 1 1 16 2 1 1 74 1 5 60 1 69 1 70 1 75 1 76 16P05d77947c737842d 0 2 0 1 1 1P0608a530f41353ea 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0686fba8ce23a3db 0 4 0 16 53 16 55 16 56 16P06a7754b87e71882 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P06fc01c088f7cc8e 0 4 0 16 53 16 55 16 56 16P0738d552d927b687 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P07529b20d40cfc46 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0806f177d565affa 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P08258437f1576859 0 4 0 16 53 16 55 16 56 16P08b0270acc170f4a 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P093243d2f9ca2be1 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P099ef520923c7e92 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P09db7786b9737c7b 0 4 0 16 53 16 55 16 56 16P0a1f6c50bde9c8be 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0aa1ed41c748847d 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P0aac411454d0a226 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0ab0822a7256ebd7 1 1 16 2 1 1 74 1 5 60 1 69 1 70 1 75 1 76 16P0ac7a7c52533d427 1 1 16 2 1 1 74 1 5 60 1 69 1 70 1 75 1 76 16P0ae68e3cd8398cc8 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0b31eaec951657c7 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0b7776daca716160 0 2 0 1 1 1P0b83f4b7407be61b 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0bcc9fb02f54dda9 0 4 0 16 53 16 55 16 56 16P0c2ca8b8d90ec7c9 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0c3d6ac573275fc5 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0c82653853ce9f26 0 2 0 1 46 1P0ca37616177fd860 0 4 0 16 53 16 55 16 56 16P0cae1de07f6cd284 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0cc5bed399e5014e 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0d4c7c24b7782049 0 2 0 1 41 1P0d5cc685c6c7b92a 0 4 0 16 53 16 55 16 56 16P0dc191318d4f99af 0 2 0 1 42 1P0de1f0c824e25796 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0df3243c559415be 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0e0d561981a5151c 0 2 0 1 42 1P0e106b7b2e4bdb90 0 4 0 16 53 16 55 16 56 16P0e16b882843ade14 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0e1d8f7d50a82b10 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0e40e4d4df90758e 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0e4c471adb03b2bb 0 4 0 16 53 16 55 16 56 16P0ecd9f9a66bbd773 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P0f161160006904ea 0 4 0 16 53 16 55 16 56 16P0f6f1fd97f179648 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0f8e8e08994d1bf9 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P0f8eb4f93f6af32d 0 2 0 1 40 1P0f97ae33f65e3c2d 0 4 0 16 68 16 73 16 74 16P0fab1dccab1e1c92 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P100940964cc5f683 0 6 1 16 60 16 69 16 70 16 74 16 75 16P1011fb934e01b078 0 4 0 16 53 16 55 16 56 16P105c0695434633ca 0 2 0 1 40 1P10df526b2a675e6d 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P10e4c2ab59ae0012 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P111f27633a686d41 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P112a63f34b898fc2 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P112b818b3ef82005 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P114540d659878973 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P12584cca42debf5b 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P129000d28732d9d0 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P12932599e74bd756 0 2 0 1 46 1P12b2d9b6a35dd3d3 1 1 16 2 1 1 53 1 5 49 1 51 1 52 1 54 1 55 16P13817db8b37ac7d8 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P13ad71d20c156aa1 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P13d13fd25c187bd4 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P13e7e511816b4815 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P13fcf092951e3961 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P148bc236df117a9e 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P148ef5967d749b0d 0 4 0 16 53 16 55 16 56 16P14f64bb9da7a3320 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P15f6afd90f57ba00 0 4 0 16 53 16 55 16 56 16P16100432a343f5ab 0 4 0 16 53 16 55 16 56 16P16133aeeb2c33767 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1684058e0e95de36 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P169288bdc3255139 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1697e69c875ed8ce 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P16bc324e5ca7b445 0 4 0 16 53 16 55 16 56 16P1742c7ee079682c8 0 6 1 1 69 1 70 1 72 1 74 1 75 1P1794a56a71edc5c4 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P179adedb1f13f489 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P17bfbe47ef5fcd1c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P17cc2547c3b9c814 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P18815fc082bd0142 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P188d8ee447e13ed9 0 2 0 1 1 1P18a15ce97c05c804 0 2 0 1 72 1P18a5b179162c6670 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P192f8c8aacfad9bc 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P19a9f7bf902c5d27 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1a125540ffb431b2 0 4 0 16 53 16 55 16 56 16P1a21c54910f6c380 0 2 0 1 1 1P1a474f32d7998566 1 2 16 2 0 1 54 1 16 2 1 1 53 1 2 55 1 56 1P1ac0c0290860ed8c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1ad613f4904bfd9e 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P1ae8ab485698b7bf 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1b27db6af6d39677 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1bcb9179cf8a8cc0 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1c2535affd5d46d9 0 4 0 16 53 16 55 16 56 16P1c377af6bb419f2a 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1c48a4207e7be5c3 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P1c4ab92931063dd3 0 4 0 16 50 16 52 16 53 16P1cb35f246317b1db 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1d52957641e9f6c2 0 2 0 1 1 1P1d6efd87182b78da 0 4 0 16 53 16 55 16 56 16P1db6f9fbd205c0fb 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1db8bd0162610110 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P1db8cfdb8d6cc349 0 4 0 16 53 16 55 16 56 16P1e16dcf11dd3efa5 1 2 16 2 0 1 54 1 16 2 1 1 53 1 2 55 1 56 1P1e1dacd96c16c27f 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1e9aa1655e46cf29 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P1ecf63a216ff2a49 0 4 0 16 53 16 55 16 56 16P205a9f9ec60bb83e 0 4 0 16 68 16 73 16 74 16P2064a18228769ee9 0 2 0 1 42 1P21213357fa7298c8 0 4 0 16 53 16 55 16 56 16P213b32c6b692743a 0 4 0 16 53 16 55 16 56 16P215ca85a0bc57b2f 0 4 0 16 53 16 55 16 56 16P217ff5996c5bb03b 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P219a5faacbebb4a9 0 3 0 1 58 1 70 1P21ad2c1a80f76de7 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P220e5ce0f95ac670 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P22120402a679cb7e 0 4 0 16 53 16 55 16 56 16P22170030e8c7a372 0 2 0 1 39 1P22398fadf92fcd5d 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2242655da946c107 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P227094456f48e340 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P22a65af5409227c6 0 2 0 1 44 1P22ab6ac80a6aa34b 0 6 1 16 52 16 54 16 55 16 56 16 57 16P23037f206a3d5bb0 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2318027ddeb4526c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2327eaa212b8f349 0 2 0 1 48 1P236b197a5eeaf6f0 0 4 0 16 53 16 55 16 56 16P2395029e4658ec5e 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P239a000d694a0add 0 4 0 16 53 16 55 16 56 16P23c4f39f1b58e20a 0 6 1 16 52 16 54 16 55 16 56 16 57 16P2459a55a091621ef 0 2 0 1 41 1P2596d83b7d5f68a4 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P25eb5bc1cd410d82 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2638ba4620dac028 1 1 16 2 1 1 53 1 5 49 1 51 1 52 1 54 1 55 16P26457b1f429bc78c 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2663a3df480a6f8e 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2698ae1ee9ce57f5 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2747375ca799c22a 0 6 1 16 52 16 54 16 55 16 56 16 57 16P2750f6f3f1514a56 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P27729b648f984f0d 0 2 0 1 40 1P27cc54d2f56f72bd 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P27f961b93135c8b6 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2828322c20b589ae 0 4 0 16 53 16 55 16 56 16P284cdc1b8278c4f7 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P285ff144371fa767 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P28a04ea8de10f77d 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P28f0fa61c5b0214a 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P29485db2e824923d 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2959571969c5b087 0 2 0 1 39 1P2979859d57d372be 0 4 0 16 53 16 55 16 56 16P2a0e778346922bbe 0 4 0 16 53 16 55 16 56 16P2a270a6a72333caf 0 2 0 1 40 1P2a56704bd0f59907 0 2 0 1 40 1P2aad424056d73821 0 6 1 16 52 16 54 16 55 16 56 16 57 16P2acd2997537ec5e8 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2ad6e282b55dd94f 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2b0f6e9209f83a03 1 2 16 2 0 1 54 1 16 2 1 1 53 1 2 55 1 56 1P2bb8b303ce91e6ce 0 4 0 16 53 16 55 16 56 16P2c14fbcbce9c5751 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P2c40cf5d3d443a3a 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2c90a22660de1d4d 0 4 0 16 53 16 55 16 56 16P2cae523fa5556687 1 2 16 2 0 1 54 1 16 2 1 1 53 1 2 55 1 56 1P2cceed99946c91e0 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2db02999306cfe5b 1 1 16 2 1 1 74 1 5 60 1 69 1 70 1 75 1 76 16P2dc8d9a9a3454dc0 0 2 0 1 72 1P2e18e3730678d46c 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P2e449ad4af7fb322 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2e5c8ebe787c3f30 0 6 1 16 52 16 54 16 55 16 56 16 57 16P2e6226765d01cb66 0 6 1 16 52 16 54 16 55 16 56 16 57 16P2e7f28583e1a80aa 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2ed80df696da4486 0 2 0 1 41 1P2f132cf143444aa4 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P2f427e8a38987b1b 0 2 0 1 39 1P2fb37e6b2fb2c4d0 0 2 0 1 1 1P2fda8fcf005fef8d 1 1 16 2 1 1 53 1 5 49 1 51 1 52 1 54 1 55 16P306cc10600ef1035 0 6 1 16 52 16 54 16 55 16 56 16 57 16P309f3cb34d2fb5e5 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P311baa2e13e87b38 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P31211590a924c63a 0 4 0 16 53 16 55 16 56 16P3169f411ce24a78e 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P31a8079e4a4de868 0 4 0 16 53 16 55 16 56 16P31ac45ab5b6e0c0a 0 6 1 16 52 16 54 16 55 16 56 16 57 16P31c14926f7427ba9 0 4 0 16 53 16 55 16 56 16P31f91e08627f5a13 0 6 1 16 52 16 54 16 55 16 56 16 57 16P325031089976dee1 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P32999188b76fb097 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P32cc899ab8358081 0 4 0 16 50 16 52 16 53 16P32e745ef4901494c 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P32f36ca616eb7431 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3302cb754baf141c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P333336b2b0fa9c55 0 4 0 16 53 16 55 16 56 16P335a14a66467d957 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P33c25fb0b0a79a49 0 4 0 16 50 16 52 16 53 16P33cbbbb6264110f6 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P33ce406b406c8089 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3401a8ea8317fb24 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P340fa61872fd077c 0 2 0 1 43 1P349d5d0d6d254555 0 4 0 16 53 16 55 16 56 16P34c6ea6fb1798d7d 1 1 16 2 1 1 53 1 5 49 1 51 1 52 1 54 1 55 16P3623c72b84576214 0 2 0 1 23 1P365513c69814e563 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P36bce298a6a48a27 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P36bcf8b1eb182561 0 6 1 16 52 16 54 16 55 16 56 16 57 16P36be47d84241d93d 0 6 1 16 49 16 51 16 52 16 53 16 54 16P370992d06f94bdc8 0 4 0 16 53 16 55 16 56 16P3734d3854941c529 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P37e00dd09b4b6650 0 6 1 16 52 16 54 16 55 16 56 16 57 16P37eebf02998a3e81 0 2 0 1 1 1P37f5044b3ce711c7 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P38089bf835e24769 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P38118f00b6f24a4b 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P382e22ca46f95f05 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P38347e20e5d1d4a0 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P385491b2b9608dfe 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P38d0f0dce55928b0 1 1 16 2 1 1 74 1 5 60 1 69 1 70 1 75 1 76 16P38f65bb5a557ad24 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P38fc9c6de2eb00e9 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P391300b37dc80553 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P391e6fb5c5d1edb3 0 6 1 16 52 16 54 16 55 16 56 16 57 16P399a37933d9e250f 0 2 0 1 38 1P39ceb3d7141d1798 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P39d81fccc91f5dec 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3a61c754a23c5111 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3a76d512a9126e36 0 4 0 16 53 16 55 16 56 16P3a793f3f0e354951 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3ac17f15802fac08 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3ad27911d766d045 0 4 0 16 68 16 73 16 74 16P3b13e1e2f7a2fe3f 0 6 1 16 52 16 54 16 55 16 56 16 57 16P3b5594faa7b44161 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3b5d032615f0c3b6 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3b9d49229081f70c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3bc97e102ae3f84f 0 4 0 16 53 16 55 16 56 16P3c23c9ebc402f7e4 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3c548cb7cc7f82c2 0 2 0 1 45 1P3caa4de03af2c142 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3cbaa3c8c9eaeb30 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3cd233419db31b8c 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3ce5af1e85fc9e47 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3d02348a007746b9 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3d0a6a47d7046c0c 0 4 0 16 53 16 55 16 56 16P3d5935659d325b1b 0 4 0 16 53 16 55 16 56 16P3d6845d91b4d6354 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3dc426757dd6f72d 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3dd3ba19d133cd6d 0 6 1 16 52 16 54 16 55 16 56 16 57 16P3de96f93ffd01c84 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3e0eacc6911ec4d7 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3e2317097812c6d7 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3e475cd3b9ee452b 0 4 0 16 53 16 55 16 56 16P3e5c313a765e321d 0 4 0 16 53 16 55 16 56 16P3e6204f6d69516f9 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3e905309ab994f50 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3ebe3e3025448cde 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3ec2b750ad9feabf 1 1 16 2 1 1 56 1 5 52 1 54 1 55 1 57 1 58 16P3f33485d8690d18f 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1P3f3792d9f565dd4f 1 2 16 2 0 1 57 1 16 2 1 1 56 1 2 58 1 59 1N028ba766812bda51N04ff071dae67cb9bN076f646c75aafa22N0c6c4e1bfa6b4c60N0e83bbd47676649bN0e86d421791b77e7N108ab60d59bafaddN139c463ddc061007N158b6adc81565bb2N1657dc0ec5dc2445N17d868f9f55b1b74N1833083a7f735bb6N1af2e4390e7b6f34N1c0370627bdbdbceN1c78cdcaa59374e4N1da6536824d791b5N2163a8b7e2625f02N2165ca81323c4643N2348ccd503236f8aN24a72c7120aa1882N2504191ab91031c1N27caa50534169b39N2bb03784d9990d52N2daba70ddacd64a6N2dbe651054d9a254N31614fa966c22a6aN37116e11487438b5N38c8bad1fb263e0bN399f78d1cdfcf3b6N3a5797a0f3638d7bN3ada6e9c3f81728fN3b2c188c4978da68N3cecd69f69ebaa5cN3e5e5dca7d1286ed"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_AllocA () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "A_RSS_CELL"; "A_DEBRUIJN"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "DEBRUIJN"; "Stdlib.ZArith.BinInt.Z.add"; "A_LOGTBL1"; "A_LOGTBL2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_MINRZ"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_MAXUSER"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_log"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "ARUN_2.AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "ARUN_2.AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_2.AllocA.proA_post"; "A_ALLOCATE"; "Stdlib.ZArith.BinInt.Z.max"; "ARUN_2.AllocA.proB_post"; "Stdlib.ZArith.BinInt.Z.b2z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "A_COMBINED"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_2.AllocA.proC_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_ALLOCATE : Z := 0x47a94.
Definition A_COMBINED : Z := 0x4c008.
Definition A_RSS_CELL : Z := 0x18bc62.       (* [comment removed for export] *)
Definition A_DEBRUIJN : Z := 0x10418.       (* [comment removed for export] *)
Definition DEBRUIJN : Z := 0x218a392cd3d5dbf.
Definition A_LOGTBL1 : Z := 0x104a8.        (* [comment removed for export] *)
Definition A_LOGTBL2 : Z := 0x105a8.        (* [comment removed for export] *)

End ARUN_1.
Ltac rz_decide := unfold rz_log; repeat (first [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]); reflexivity.
Section ARUN_2. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L17356128428.3000005S1n1H". (* [comment removed for export] *)
Lemma rz_log_0 : forall n, n < 49 -> rz_log n = 0. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L17356128428.3L56068765100.3L57140556900.300000100600;FS1n1HS1n1H". (* [comment removed for export] *)
Lemma rz_log_1 : forall n, 49 <= n < 97 -> rz_log n = 1. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L17356128428.3L47373472684.3L56068765100.3L57140556900.3L60863097700.300000100600700<00AFS1n1HFS1n1HS1n1H". (* [comment removed for export] *)
Lemma rz_log_2 : forall n, 97 <= n < 449 -> rz_log n = 2. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070>L17356128428.3L29161183148.3L45333870948.3L47373472684.3L56068765100.3L57140556900.3L60863097700.300000100600;00<00=00B00GFS1n1HS1n1HFFS1n1HS1n1H". (* [comment removed for export] *)
Lemma rz_log_3 : forall n, 449 <= n < 0xf81 -> rz_log n = 3. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L17356128428.3L29161183148.3L38369545572.3L45333870948.3L47373472684.3L56068765100.3L57140556900.3L60863097700.3L63436230572.300000100200700<00=00>00C00H00MFFS1n1HS1n1HFFS1n1HS1n1HS1n1H". (* [comment removed for export] *)
Lemma rz_log_4 : forall n, 0xf81 <= n < 0x3f01 -> rz_log n = 4. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L17356128428.3L18059527524.3L29161183148.3L38369545572.3L45333870948.3L47373472684.3L56068765100.3L57140556900.3L60863097700.3L63436230572.3L63605612460.300000100600700<00A00B00C00H00M00N00SFS1n1HFS1n1HS1n1HFFS1n1HS1n1HFS1n1H". (* [comment removed for export] *)
Lemma rz_log_5 : forall n, 0x3f01 <= n < 0x7e01 -> rz_log n = 5. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L17356128428.3L18059527524.3L29161183148.3L38369545572.3L43163612516.3L45333870948.3L47373472684.3L56068765100.3L57140556900.3L60863097700.3L63436230572.3L63605612460.3L63929712556.300000100600700<00A00F00G00H00M00R00S00T00YFS1n1HFS1n1HS1n1HS1n1HFFS1n1HS1n1HFFS1n1H". (* [comment removed for export] *)
Lemma rz_log_6 : forall n, 0x7e01 <= n < 0xfc01 -> rz_log n = 6. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0>L17356128428.3L18059527524.3L29161183148.3L38369545572.3L41853474148.3L43163612516.3L45333870948.3L47373472684.3L56068765100.3L57140556900.3L60863097700.3L63436230572.3L63605612460.3L63929712556.300000100600700<00A00F00K00L00M00R00W00X00Y00ZFS1n1HFS1n1HS1n1HS1n1HS1n1HFFS1n1HS1n1HFFF". (* [comment removed for export] *)
Lemma rz_log_7 : forall n, 0xfc01 <= n -> rz_log n = 7. Proof. intros; rz_decide. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L19034901317.2L21577958693.2L33983525829.2L36375269189.2L43182339909.2L45574144709.2L51324417989.2L60522744645.2000001002003004005006007008SSSSSSSS". (* [comment removed for export] *)
Lemma rz_log_bound : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <? _)); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section AllocA.
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

  (* [comment removed for export] *)
  Definition allocA_statics (m : mem) (T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "(0.(1.$2.O3.$3.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O3.$9.(4.$5.(6.(7.&8.=))(8.$5.)))(0.(1.$2.O3.$:.(4.$5.(;.(7.&40.$<.))(8.$5.)))(0.(1.$2.O3.(=.$>.+4.)(4.$5.(6.(7.&8.+3.))(8.$5.)))(0.(1.$2.O3.(=.$?.+8.)(4.$5.(6.(7.&8.+4.))(8.$5.)))(0.(1.$2.O3.(=.$?.+31.)(4.$5.(6.(7.&8.+;.))(8.$5.)))(0.(1.$2.O3.$10.(4.$5.(11.(7.&40.+10.))(4.$5.(11.(7.&40.+800.))(8.$5.))))(0.(1.$2.O3.$12.(4.$5.(;.(7.&40.(13.+2.+28.)))(8.$5.)))(0.(1.$2.O3.$14.(4.$5.(6.(7.&8.+1.))(4.$5.(15.#3.(4.(16.&8.)(7.&8.=)(4.(16.&8.)(7.&8.=)(4.(16.&8.)(7.&8.=)(8.(16.&8.))))))(4.$5.(17.(7.&40.=))(8.$5.)))))(0.(1.$2.O3.$18.(4.$5.(;.(7.&40.$19.))(8.$5.)))(0.(1.$2.O3.$19.(4.$5.(;.(7.&40.O1.))(8.$5.)))(1.$2.O3.(=.O1.+98.)(4.$5.(;.(7.&40.O2.))(8.$5.))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition allocA_frame (m : mem) (SP : Z) (fr0 : list byte) (fill : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "(1:.$2.O11.(=.O10.-80.)(4.$5.(15.#8.O?.)(4.$5.(;.(7.&40.O>.))(4.$5.(;.(7.&40.+10.))(4.$5.(;.O1.)(4.$5.(;.O2.)(4.$5.(;.O3.)(4.$5.(;.O4.)(4.$5.(;.O5.)(4.$5.(;.O6.)(4.$5.(;.O7.)(4.$5.(;.O8.)(4.$5.(;.O9.)(4.$5.(;.O:.)(4.$5.(;.O;.)(4.$5.(;.O<.)(4.$5.(;.O=.)(8.$5.))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition proA_post (SP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a6 a7 t3 t4 t5 t6 : word)
      (n STK fill lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Lms',$1;.(1<.(16.&40.)Lx10,(16.&40.)(1<.(16.&40.)Lx11,(16.&40.)(1<.(16.&40.)Lx12,(16.&40.)(1<.(16.&40.)Lx13,(16.&40.)(1<.P,(16.&40.)(1=.(16.&8.))Lm',P,(16.&40.)(1=.(16.&8.))(1<.(1>.(16.&8.))Lfr0,(1>.(16.&8.))(0.(1?.$1;.R7.(20.(21.(7.&40.+47:?0.)(7.&40.(=.O20.-80.))O1>.O1=.O1<.O1;.O1:.(7.&40.+8.)(7.&40.O5.)R6.R5.R4.R3.(7.&40.+1.)(7.&40.O5.)O=.O<.(7.&40.+8.)(7.&40.(22.O7.))O15.(7.&40.O7.)(7.&40.$23.)(7.&40.O6.)O11.(7.&40.+7.)(7.&40.+106;97.)(7.&40.+1.)O;.O:.O9.O8.)O3.(7.&40.+47<00.)O2.(24.(16.&40.))R2.(25.$2.)))(0.(26.(4.(27.$28.$28.)(29.$28.$28.O4.O20.)(8.(27.$28.$28.)))O1.R2.)(0.(2:.$2.O1.R2.)(0.(2;.$2.R2.)(0.(2<.R2.O20.R1.O5.O1?.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.)(2=.$2.R2.O4.(=.O20.-80.)))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0?L10711076974.72L10711078244.54L10711078373.57L10711078498.60L10711078627.63L10711078752.66L10711078881.69L11339729534.73L13700313714.61L13700313843.64L13700313968.67L13700314097.70L13700314238.73L13766775150.1 L17362434077.73L17362435351.55L17362435478.58L17362435601.61L17362435728.64L17362435859.67L17362435986.70L20692068597.58L20692068976.67L20692069105.70L20692069234.61L20692069363.64L20692069758.73L21044257011.64L21044257136.67L21044257265.70L21044258430.73L26031137406.73L26031138160.67L26031138289.70L41855577557.73L41922550398.73L41922551281.70L42604162436.2 L4581284169.100L4581284169.88 L4581284169.90 L4581284169.92 L4581284169.94 L4581284169.96 L4581284169.98 L7365970328.1  00000?00N00]00l01;01J01Y01k02=02>02?02@02A02E02F02T02U02V02W02X02Y02k02l02m02n02o03003B03C03D03E03F03X03Y03g03h04:04D04L04T04\04d04l05405<05@S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP1n3H133H14S3hAR2SP1n3H133H14FFFFS2SPFS3hAR2SP1n3H13FFFFFS3hAR2SP1n3H133H14FFFFFS3hAR2SP1n3H133H14FFFFS3hAR2SP1n3H133H14FS3hAR2SP1n3H13FS3hAR2SP1n3H133H14S3STK4STKBS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS2SP". (* [comment removed for export] *)
  Lemma alloc_proA : ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Pra,(16.&40.)Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Ps0,(16.&40.)Ps1,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps2,(16.&40.)Ps3,(16.&40.)Ps4,(16.&40.)Ps5,(16.&40.)Ps6,(16.&40.)Ps7,(16.&40.)Ps8,(16.&40.)Ps9,(16.&40.)Ps10,(16.&40.)Ps11,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PSP,$28.Pn,$28.PSTK,$28.Pfill,$28.Plo,$28.PT,$28.PCTX,$28.PF,(2>.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(1=.(16.&8.))P,(0.(2?.=R9.)(30.R9.(13.+2.+20.)))P,(0.(30.=R9.)(30.R9.(13.+2.+40.)))P,(0.(2?.=R9.)(2?.R9.+1.))P,(31.R4.R8.R7.)P,(2=.$2.R5.R:.R>.)P,(2?.(32.VhAR,)R;.)P,(2?.R<.(33.R10.+80.))P,(2?.R11.(13.+2.+3>.))P,(1?.$28.(34.R12.+10.)=)P,(35.VCS,R?.(33.R13.R?.))P,(2;.$2.R;.)(36.$2.VAL,VCS,(37.R15.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R25.R24.R19.R18.R17.R16.R14.R13.R12.R11.R>.R=.R<.)(20.(21.R2=.(7.&40.R15.)R2<.R2;.R2:.R29.R28.R27.R26.(7.&40.$23.)(7.&40.R14.)(7.&40.+8.)(7.&40.R13.)(7.&40.+1.)(7.&40.R12.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R>.(7.&40.$38.)R=.(24.(16.&40.))R<.(25.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP n STK fill lo T CTX F fc m
      NB STKB FB (INI & RSS & DBR & LT1 & LT2a & LT2b & RZC & MXU & TSD & TPC & TSA & CTH) ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_ALLOCATE, A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE,
      A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
    change (1074072 + 3624) with 1077696 in RZC. change (1074072 + 3616) with 1077688 in MXU.
    change (66728 + 4) with 66732 in LT1. change (66984 + 8) with 66992 in LT2a. change (66984 + 49) with 67033 in LT2b. unfold DEBRUIJN in DBR.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (STK0 : 0 <= STK < 2^64) by (clear - STKB; lia).
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x47c00] [(0x47bf8, DSplit)] 150%N);
      (lx_junk_under lo (SP + -120) 8%nat fr0 FRa;
       apply evtA_done; unfold proA_post, allocA_frame;
       first [ rewrite (rz_log_0 n) by lx_arith | rewrite (rz_log_1 n) by lx_arith | rewrite (rz_log_2 n) by lx_arith
             | rewrite (rz_log_3 n) by lx_arith | rewrite (rz_log_4 n) by lx_arith | rewrite (rz_log_5 n) by lx_arith
             | rewrite (rz_log_6 n) by lx_arith | rewrite (rz_log_7 n) by lx_arith ];
       lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRa | assumption ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition proB_post (SP : Z) (gp tp t0 t1 t2 a6 a7 s4 s8 t3 t4 t5 t6 : word)
      (n STK fill : Z) (F : bvmap 5 word) (fc : bv 32) (m' : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Lms',$1;.(1<.(16.&40.)Lx11,(16.&40.)(1<.(16.&40.)Lx12,(16.&40.)(1<.(16.&40.)Lx13,(16.&40.)(1<.(16.&40.)Lx14,(16.&40.)(1?.$1;.R5.(20.(21.(7.&40.+47<2<.)(7.&40.(=.O14.-80.))O13.O12.O11.O10.O?.(7.&40.+8.)(7.&40.=)(7.&40.(39.O6.+8.))R4.R3.R2.R1.(7.&40.O4.)O>.O=.(7.&40.+8.)(7.&40.(22.O6.))(7.&40.+10000.)(7.&40.O6.)(7.&40.$23.)(7.&40.O5.)(7.&40.+????.)(7.&40.+7.)(7.&40.+106;97.)(7.&40.+1.)O:.O9.O8.O7.)O3.(7.&40.+47<48.)O2.(24.(16.&40.))O1.(25.$2.)))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L20421102057.83L20421102057.85L21979910410.83L26680464049.57L26680464178.54L44421293205.1 L44625906644.1 L53525265936.55L53525266065.52L61477322479.83L61477322479.85L8457590638.85 00000K00f01901I01Y01]01a02002?02Z03503HS3hAR2SP1n2lo5LOIMG3SPL3H13S3hAR2SP1n2lo5LOIMG3SPL3H13S3hAR2SP2RZ3RZB3H14S3hAR2SP2lo1y2H0S3hAR2SP2lo1y2H0S2SPS2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP1n2lo5LOIMG3SPL3H13S3hAR2SP1n2lo5LOIMG3SPL3H13S3hAR2SP2RZ3RZB3H14". (* [comment removed for export] *)
  Lemma alloc_proB : ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Px10,(16.&40.)Px11,(16.&40.)Px12,(16.&40.)Px13,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Ps4,(16.&40.)Ps8,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PSP,$28.Pn,$28.PSTK,$28.Pfill,$28.Plo,$28.PT,$28.PCTX,$28.PF,(2>.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(1=.(16.&8.))PW,(1>.(27.$28.$28.))Pm0,P,(16.&40.)(1=.(16.&8.))P,(0.(2?.=R;.)(30.R;.(13.+2.+20.)))P,(31.R4.R8.R7.)P,(2=.$2.R5.R:.(=.R>.-80.))P,(2?.(32.VhAR,)R;.)P,(2?.R<.(33.R10.+200.))P,(2?.R11.(13.+2.+3>.))P,(1?.$28.(34.R12.+10.)=)P,(35.VCS,R?.(33.R13.R?.))P,(26.(4.(27.$28.$28.)(29.$28.$28.R10.R14.)R:.)R9.R;.)P,(2:.$2.R:.R<.)P,(2;.$2.R=.)(36.$2.VAL,VCS,Lms',$1;.(1<.P,(16.&40.)(1=.(16.&8.))Lm',P,(16.&40.)(1=.(16.&8.))(0.(3:.R19.R2:.R29.R28.R27.R26.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R18.R17.R16.R12.R11.R1.R2.)(0.(26.(4.(27.$28.$28.)(29.$28.$28.R15.R19.)R?.)R>.R1.)(0.(2:.$2.R>.R1.)(0.(2;.$2.R1.)(0.(26.(4.(27.$28.$28.)(29.$28.$28.R15.(=.R19.-80.))(8.(27.$28.$28.)))R10.R1.)(2=.$2.R1.R15.(=.R19.-80.))))))))(20.(21.(7.&40.+47:?0.)(7.&40.(=.R17.-80.))R28.R27.R26.R25.R24.(7.&40.+8.)(7.&40.R14.)R23.R22.R21.R20.(7.&40.+1.)(7.&40.R14.)R1?.R1>.(7.&40.+8.)(7.&40.(22.R16.))R1=.(7.&40.R16.)(7.&40.$23.)(7.&40.R15.)R1<.(7.&40.+7.)(7.&40.+106;97.)(7.&40.+1.)R1;.R1:.R19.R18.)R10.(7.&40.+47<00.)R?.(24.(16.&40.))R>.(25.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 x10 x11 x12 x13 a6 a7 s4 s8 t3 t4 t5 t6 SP n STK fill lo T CTX F fc m W m0
      NB (INI & RSS & DBR & LT1 & LT2a & LT2b & RZC & MXU & TSD & TPC & TSA & CTH) ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE,
      A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
    change (1074072 + 3624) with 1077696 in RZC. change (1074072 + 3616) with 1077688 in MXU.
    change (66728 + 4) with 66732 in LT1. change (66984 + 8) with 66992 in LT2a. change (66984 + 49) with 67033 in LT2b. unfold DEBRUIJN in DBR.
    pose proof (rz_log_bound n) as RZB. unfold proB_post. set (RZ := rz_log n) in *. clearbody RZ.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP + -128)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x47c48] [] 150%N); lx_unhide; lx_stk_grow_to lo (SP + -128);
      (lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ =>
         apply evtA_done; eexists; split;
         [ lx_exs; lx_mseq
         | lx_ands; [ lx_munch MU MUl | lx_wmono WM WMl | assumption | first [exact MUl | eapply munch_weaken; [| exact MUl]; lx_subfp] | assumption ] ] end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition proC_post (SP : Z) (gp tp t0 t1 t2 t3 t4 t5 t6 : word)
      (n STK fill T : Z) (F : bvmap 5 word) (fc : bv 32) (m' : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Lms',$1;.(1<.(16.&40.)Lx14,(16.&40.)(1<.(16.&40.)Lx15,(16.&40.)(1<.(16.&40.)Lx16,(16.&40.)(1<.(16.&40.)Lx17,(16.&40.)(1?.$1;.R5.(20.(21.(7.&40.+47=34.)(7.&40.(=.O11.-80.))O10.O?.O>.O=.O<.(7.&40.(3;.(3<.O7.)))(7.&40.(3=.O7.))(7.&40.$23.)(7.&40.(=.O4.+=0.))(7.&40.(3>.O7.))(7.&40.+8.)R4.R3.R2.R1.(7.&40.+8.)(7.&40.(3>.O7.))(7.&40.(3?.O7.))(7.&40.O7.)(7.&40.$23.)(7.&40.O6.)(7.&40.-8.)(7.&40.+7.)(7.&40.O4.)(7.&40.+1.)O;.O:.O9.O8.)O3.(7.&40.$40.)O2.(24.(16.&40.))O1.(25.$2.)))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L13799037830.10L18705599522.8 L41415983884.8 L41422282358.9 L4501551771.10 L5361208676.9  L5367500830.8  L57654798521.8 00000300900:00=00E00K00Q00WS1rS1r2HrSS1rS1r2Hr1HS1r2HrS1r2HrS1r2Hr". (* [comment removed for export] *)
  Lemma sllw_rz : forall r, 0 <= r <= 7 -> bv_swrap 32 (Z.shiftl 16 (r mod 32)) = 16 * 2^r.
  Proof.
    intros r Hr. rewrite Z.mod_small, Z.shiftl_mul_pow2 by lia.
    assert (2 ^ r <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ r) by (apply Z.pow_pos_nonneg; lia).
    unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ (Z.of_N 32 - 1)) with 2147483648. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    rewrite Z.mod_small by lia. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11811878010.9 L41415991886.9 L41422282358.8 L48287995616.10L6648657248.8  00000500800900A00FS1n1HS1nSS1n1H2H1S1n1H". (* [comment removed for export] *)
  Lemma rz_size_bound : forall n, 16 <= rz_size n <= 2048.
  Proof.
    intros n. unfold rz_size. pose proof (rz_log_bound n).
    assert (2 ^ 0 <= 2 ^ rz_log n) by (apply Z.pow_le_mono_r; lia). assert (2 ^ rz_log n <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia).
    change (2^0) with 1 in *. change (2^7) with 128 in *. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L20865074130.9L57661298842.900000800>S1n2Hn1lS1n2n0". (* [comment removed for export] *)
  Lemma nfix_code : forall n, 0 <= n -> n + Z.b2z (n <? 1) = nfix n.
  Proof. intros n Hn. unfold nfix. destruct (Z.ltb_spec0 n 1); cbn [Z.b2z]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L24925869840.9L24927942988.900000800@S1n2n01lS1n1l2n0". (* [comment removed for export] *)
  Lemma from_primary_ltb : forall n, from_primary n = (needed n <? 65537).
  Proof.
    intros n. unfold from_primary, kMaxSize.
    destruct (Z.leb_spec0 (needed n) 65536); destruct (Z.ltb_spec0 (needed n) 65537); try reflexivity; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L10462164249.70L10462164376.71L11834439766.70L12478301996.73L12500492489.4 L13817065824.4 L14948183328.68L15786651444.2 L18757073916.73L19496485691.73L22826012676.2 L2424857170.2  L26522664644.3 L26680463670.56L29784562668.2 L34017711404.73L3751653459.67 L38910395904.68L39932046602.74L39932046989.75L39932187962.68L39944773306.2 L44421293205.1 L44625906644.1 L49742853912.73L51464948129.67L51464949290.2 L52065441557.67L52067065252.68L53522110849.73L53526894667.54L58260520914.3 L58263076050.3 L59308628304.3 L59308628433.4 L59308628566.3 L61030807031.67L61074555238.73L61929654688.68L61929812241.73L63374621462.68L63742164343.2 L8603669553.67 L8606080640.68 L8929572112.68 00000:00D00N00`00o01;01<01B01C01D01J01P01W01i01l02302=02G02[02\03003803<03@03A03O03V03W03X03h04904D04P04Y04g05005:05I05V05c05m06506?06I06JS3hAR2SP1nS3hAR2SP1nS3hAR2SP1nS3hAR2AL1n4IMG'2RBS1n4RZSB3MX82RBS1n3MX81H2H0FS1n2NBFFS1n2RBS1n2NBS1n3NDBS3hAR2SP1n2lo1y2H0S1nS3hAR1nS3hAR2SP1nS3hAR2SP1nS3hAR2SP1n2NB2RB3N2BFS3hAR2SP1n2NB2RB3RZBS1n4RZSBS2SPS2SPFS3hAR2SP1n3MX8S1n3MX8FFS3hAR2AL1n5ALWF'S3hAR2SP1n2lo3SPLS1n4RZSB2RBS1n4RZSB3NDBS1n2NB2K1S1n3MX83N2B2K2S1n2NB2K3S3hAR2SP1nS3hAR2AL1n4IMG'S3hAR2SP1n2NBS3hAR2SP1n2NBS3hAR2SP1nS1n4RZSBS3hAR2SP1nS3hAR2SP1nF". (* [comment removed for export] *)
  Lemma alloc_proC : ltac2:(CDefT.buildp (gd_tbl_AW_AllocA ()) "Pgp,(16.&40.)Ptp,(16.&40.)Pt0,(16.&40.)Pt1,(16.&40.)Pt2,(16.&40.)Px11,(16.&40.)Px12,(16.&40.)Px13,(16.&40.)Px14,(16.&40.)Pa6,(16.&40.)Pa7,(16.&40.)Pt3,(16.&40.)Pt4,(16.&40.)Pt5,(16.&40.)Pt6,(16.&40.)PSP,$28.Pn,$28.PSTK,$28.Pfill,$28.Plo,$28.PT,$28.PCTX,$28.PF,(2>.&5.(16.&40.))Pfc,(16.&20.)Pm,P,(16.&40.)(1=.(16.&8.))PW,(1>.(27.$28.$28.))Pm0,P,(16.&40.)(1=.(16.&8.))P,(0.(2?.=R;.)(30.R;.(13.+2.+20.)))P,(31.R4.R8.R7.)P,(2?.+65?000.R8.)P,(2?.(=.R9.+10000.)(32.VhAR,))P,(0.(2?.+1000.R;.)(41.(2?.(=.R;.+1000.)+10000.)(2?.+65?000.R;.)))P,(2?.(=.R<.+1000.)(32.VhAR,))P,(35.VCS,R<.+10000.)P,(35.VCS,R>.+1000.)P,(2=.$2.R;.R10.(=.R14.-80.))P,(2?.(32.VhAR,)R11.)P,(2?.R12.(33.R16.+200.))P,(2?.R17.(13.+2.+3>.))P,(1?.$28.(34.R18.+10.)=)P,(35.VCS,R15.(33.R19.R15.))P,(26.(4.(27.$28.$28.)(29.$28.$28.R16.R1:.)R10.)R?.R11.)P,(2:.$2.R10.R12.)P,(2;.$2.R13.)P,(1?.(16.&40.)R2;.(7.&40.$42.))(36.$2.VAL,VCS,Lms',$1;.(1<.P,(16.&40.)(1=.(16.&8.))Lm',P,(16.&40.)(1=.(16.&8.))(0.(43.R20.R2?.R2>.R2=.R2<.R2;.R24.R23.R22.R21.R1?.R1>.R1=.R1;.R19.R18.R1.R2.)(0.(26.(4.(27.$28.$28.)(29.$28.$28.R1<.R20.)R16.)R15.R1.)(0.(2:.$2.R15.R1.)(0.(2;.$2.R1.)(0.(26.(4.(27.$28.$28.)(29.$28.$28.R1<.(=.R20.-80.))(8.(27.$28.$28.)))R17.R1.)(2=.$2.R1.R1<.(=.R20.-80.))))))))(20.(21.(7.&40.+47<2<.)(7.&40.(=.R1>.-80.))R2=.R2<.R2;.R2:.R29.(7.&40.+8.)(7.&40.=)(7.&40.(39.R1=.+8.))R28.R27.R26.R25.(7.&40.R1;.)R24.R23.(7.&40.+8.)(7.&40.(22.R1=.))(7.&40.+10000.)(7.&40.R1=.)(7.&40.$23.)(7.&40.R1<.)(7.&40.+????.)(7.&40.+7.)(7.&40.+106;97.)(7.&40.+1.)R22.R21.R20.R1?.)R17.(7.&40.+47<48.)R16.(24.(16.&40.))R15.(25.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 x11 x12 x13 x14 a6 a7 t3 t4 t5 t6 SP n STK fill lo T CTX F fc m W m0
      NB (INI & RSS & DBR & LT1 & LT2a & LT2b & RZC & MXU & TSD & TPC & TSA & CTH) C0 C1 T0 T1 CTXCS TCS ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE,
      A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP, A_COMBINED in *.
    change (1074072 + 3624) with 1077696 in RZC. change (1074072 + 3616) with 1077688 in MXU.
    pose proof (rz_log_bound n) as RZB. pose proof (rz_size_bound n) as RZSB.
    assert (MX8 : 0 <= Z.max n 8 < 2^33) by (clear - NB; lia).
    pose proof (munch_refl [(lo, SP + -128)] m) as MU1.
    unfold proC_post.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. change (Z.land 0 8) with 0. rewrite Z.add_0_r.
    rewrite (land_align3 (Z.max n 8 + 7)) by (clear - MX8; lia).
    replace (Z.max n 8 + 7) with (Z.max n 8 + 8 - 1) by lia. change ((Z.max n 8 + 8 - 1) / 8 * 8) with (rounded n).
    assert (RB : 8 <= rounded n <= Z.max n 8 + 7 /\ rounded n mod 8 = 0).
    { unfold rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      split; [clear - H H0 MX8; lia|]. apply Z_mod_mult. }
    zstep. replace (Z.land (rounded n) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones; clear - RB; lia).
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (sllw_rz (rz_log n)) by exact RZB. change (16 * 2 ^ rz_log n) with (rz_size n).
    change (Z.b2z (8 <? 65537)) with 1.
    rewrite (nfix_code n) by (clear - NB; lia).
    replace ((rounded n + rz_size n) mod 18446744073709551616) with (needed n) by (unfold needed; rewrite Z.mod_small; [reflexivity| clear - RB RZSB MX8; lia]).
    change (rounded n + rz_size n) with (needed n).
    assert (NDB : 24 <= needed n <= Z.max n 8 + 2055) by (unfold needed; clear - RB RZSB; lia).
    rewrite <- from_primary_ltb.
    replace (rz_size n mod 18446744073709551616) with (rz_size n) by (rewrite Z.mod_small; [reflexivity| clear - RZSB; lia]).
    assert (E1 : Z.land 1 (Z.b2z (from_primary n)) = Z.b2z (from_primary n)) by (destruct (from_primary n); reflexivity).
    rewrite !E1.
    assert (E2 : Z.land ((Z.b2z (from_primary n) + -1) mod 18446744073709551616) (rz_size n) = needed2 n - needed n).
    { unfold needed2. destruct (from_primary n); cbn [Z.b2z].
      - change ((1 + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l. lia.
      - change ((0 + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_m1_64 by (clear - RZSB; lia). lia. }
    rewrite !E2. replace (needed2 n - needed n + needed n) with (needed2 n) by lia.
    assert (N2B : 24 <= needed2 n <= Z.max n 8 + 4103) by (unfold needed2; destruct (from_primary n); clear - NDB RZSB; lia).
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 NB. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 N2B MX8. lia. }
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. unfold nfix in K3. clear - K3 NB. lia. }
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    lx_run (PLAN [0x4c008] [] 60%N); lx_unhide; lx_stk_grow_to lo (SP + -128);
      (lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _ |- _ =>
         apply evtA_done; eexists; split;
         [ lx_exs; lx_mseq
         | lx_ands; [ lx_munch MU MUl | lx_wmono WM WMl | assumption | first [exact MUl | eapply munch_weaken; [| exact MUl]; lx_subfp] | assumption ] ] end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End AllocA.

End ARUN_2.
