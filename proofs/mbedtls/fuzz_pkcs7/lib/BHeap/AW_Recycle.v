(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_Drain AW_Blist AW_DoRecycle.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import AW_Blist.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0042bbeafb4b66ba 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P00566da20582591c 0 4 0 16 32 16 40 16 41 16P00721bbac9c87a3b 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P00b833a28f5ef8c0 0 4 0 1 34 1 42 1 43 1P01321ab5287cd0d2 0 4 0 16 32 16 40 16 41 16P01607178cb5ac670 1 1 8 2 0 1 43 1 3 34 1 44 1 45 8P016670faeb5cb137 0 2 0 1 35 1P01b8a0d6091445c2 0 6 1 8 34 8 39 8 40 8 44 8 45 8P01fab8e8462efd9d 0 2 0 1 24 1P022f14416be7e062 1 1 8 2 1 1 48 1 3 39 1 49 1 50 8P02d26672d4dab7d7 0 3 0 1 26 1 41 1P02e03eac049c23fa 0 6 0 8 33 8 38 8 39 8 43 8 44 8P0324b25fb6cef4c5 0 4 0 1 31 1 38 1 39 1P0379fd843ab0b827 0 4 0 16 32 16 40 16 41 16P039a9989dbea53fa 0 3 0 1 27 1 29 1P03a45c2311d21d68 0 2 0 1 21 1P03e12c9c9b3a3450 0 3 0 1 37 1 41 1P03ea873dd768c92e 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P04097cb08273b928 1 1 100 1 0 1 2 37 1 43 1P04bba0ce96fa6fe0 0 4 0 16 32 16 40 16 41 16P04fde14b1a952ed5 0 3 0 1 17 1 41 1P0640cb70b8dc3b2b 0 6 1 8 33 8 38 8 39 8 43 8 44 8P06ae00b1c41932cf 0 2 0 1 32 1P06e376516652b864 0 4 0 1 34 1 42 1 43 1P06f43ab2443145b0 0 4 0 16 32 16 40 16 41 16P06fa6da7b246c519 0 4 0 16 32 16 40 16 41 16P070331e10c0783ee 0 2 0 1 32 1P07e3b3e76a22f69b 0 2 0 1 37 1P080ba0d4e763f6ac 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P083e8c35a160375b 0 6 0 8 37 8 42 8 43 8 47 8 48 8P0879b2dc06a814c6 0 4 0 1 32 1 42 1 43 1P08bd5fba63ef817b 0 6 1 8 34 8 39 8 40 8 44 8 45 8P08c227e5ad1cb841 0 3 0 1 26 1 41 1P08e13c18511bbca8 1 1 8 2 1 1 44 1 3 35 1 45 1 46 8P09541e3cdf855c2a 0 4 0 16 32 16 40 16 41 16P0984f061b9d69050 0 4 0 1 32 1 42 1 43 1P09e3d22c20832072 0 2 0 1 34 1P09f2697754c78f54 0 4 0 1 34 1 42 1 43 1P0a9f583ff58e645d 1 1 8 2 1 1 43 1 3 34 1 44 1 45 8P0aa26f36305d512a 0 4 1 1 32 1 39 1 40 1P0b34cdf2f9b54206 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P0b68bd0464949cb6 1 1 8192 1 0 1 2 38 1 42 1P0b7c07d2d014c313 1 1 8 2 1 1 47 1 3 38 1 48 1 49 8P0b934148a9b880e8 0 1 1 1P0c1c4f7bacde017c 2 32 0 4 0 8 2 8 49 8 50 8 1 1 8 4 0 1 3 1 49 1 50 1 2 38 1 51 1P0c3fc68f51124257 0 2 0 1 28 1P0c86ba9e768b2cd6 0 4 1 1 31 1 38 1 39 1P0ced513588b0c2bf 1 1 8 2 0 1 42 1 3 33 1 43 1 44 8P0d50b2cfe99a0cc5 0 2 0 1 27 1P0d82abe849703269 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P0db0a95a38a53b3e 0 2 0 1 41 1P0dccf2357950341f 0 2 0 1 42 1P0e5171edebc34ece 1 1 8 2 1 1 47 1 3 38 1 48 1 49 8P0f622a35527dcebd 0 4 1 1 33 1 43 1 44 1P0f953f88de551513 0 6 0 8 37 8 42 8 43 8 47 8 48 8P0fa24e8854272e6f 0 2 0 1 42 1P0fdd6f835feb911a 1 1 8 2 1 1 48 1 3 39 1 49 1 50 8P0fe4cf6ae574b4c4 0 4 0 16 32 16 40 16 41 16P1010ca86968dfbea 0 2 0 1 38 1P10343a94c84fee30 0 4 0 16 32 16 40 16 41 16P10759bbc4d12c0bb 0 4 0 16 32 16 40 16 41 16P1088f08c685f861f 0 3 0 1 27 1 29 1P10b587f0a81b2369 0 7 2 8 33 64 34 8 39 8 40 8 44 8 45 8P11bc2aa4aac83b3d 0 2 0 1 35 1P11bffd224664f9ad 0 2 0 1 37 1P11d108cad3898f55 1 1 8 2 0 1 43 1 3 34 1 44 1 45 8P125519d1bc15be88 0 6 1 8 33 8 38 8 39 8 43 8 44 8P12646567b2c0056b 0 2 0 1 37 1P12810a066b25fbf4 0 4 0 1 31 1 38 1 39 1P1370a31d10ecf583 0 7 2 8 34 64 35 8 40 8 41 8 45 8 46 8P137ccf22dd9b2b9c 0 1 1 1P138cbd9f4632cb35 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P13b829387cb59416 1 1 8 2 0 1 46 1 3 37 1 47 1 48 8P141b57d9d7a82f36 0 4 1 1 32 1 42 1 43 1P143c4cdbcfe8fd58 1 2 100 1 0 1 8192 3 38 1 42 1 43 1 2 39 1 44 1P144c634ef52451f4 0 2 1 1 35 1P1487477cf77b9587 0 4 1 1 32 1 42 1 43 1P14939f063b400e1d 0 2 0 1 34 1P15054068659a0abb 0 4 1 1 35 1 43 1 44 1P151a88adff264b00 1 1 8 2 1 1 44 1 3 35 1 45 1 46 8P1558ba4efe5db7b6 0 2 0 1 21 1P155a525b4e68700a 0 4 0 16 32 16 40 16 41 16P1592ef3c33995906 0 2 0 1 38 1P15c3939d8dde839a 0 7 2 8 37 64 38 8 43 8 44 8 48 8 49 8P15d5c3bea6f38e04 1 1 8 2 0 1 47 1 3 38 1 48 1 49 8P165df207e218d190 0 4 1 1 35 1 43 1 44 1P16844cf6c3f69c88 0 7 2 8 38 64 39 8 44 8 45 8 49 8 50 8P16d5e3f849b0361d 0 2 0 1 21 1P171b079139b978fe 0 6 1 8 38 8 43 8 44 8 48 8 49 8P177ffba5f9aac254 0 4 0 1 32 1 42 1 43 1P17d831959f990149 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P1868491088e7a280 0 4 0 16 32 16 40 16 41 16P18b46e00e12f8e3a 1 1 8 2 0 1 47 1 3 38 1 48 1 49 8P18d11b4ca5872673 0 4 0 16 32 16 40 16 41 16P1905dd6d4a82b356 0 2 0 1 27 1P191095e450cdb4af 0 4 0 16 32 16 40 16 41 16P1990b86fe239c119 0 2 0 1 28 1P1994a129a7059de1 0 3 0 1 27 1 45 1P19bf69a16f5ec4e0 0 3 0 1 26 1 28 1P1a0ba36a30008f15 0 7 2 8 34 64 35 8 40 8 41 8 45 8 46 8P1acf193f615d3e4a 0 4 0 16 32 16 40 16 41 16P1aedf3ba7afcc308 0 3 0 1 27 1 45 1P1b8393b39fd3e3b8 0 4 0 16 32 16 40 16 41 16P1c0202ec8a7d58a1 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P1c1b8dc6ddb6cf34 0 4 0 1 31 1 41 1 42 1P1c7ef02b784b01e2 1 1 8 2 0 1 42 1 3 33 1 43 1 44 8P1d61fba1a4f7b403 0 2 0 1 37 1P1d661f615523df58 0 4 0 16 32 16 40 16 41 16P1d6a8580e83a2421 1 1 8 2 0 1 46 1 3 37 1 47 1 48 8P1daa9fc37cb6abec 0 2 0 1 41 1P1e787e8bdc140545 0 4 0 1 34 1 42 1 43 1P1eecacce01158a5f 0 2 0 1 38 1P1f02e74ac346ce51 0 4 0 16 32 16 40 16 41 16P1f298865f2eb9605 1 1 8 2 0 1 47 1 3 38 1 48 1 49 8P1f832e3294c077da 0 4 0 16 32 16 40 16 41 16P1fa030d101f68270 0 2 0 1 38 1P201d8429657b0056 0 6 1 8 37 8 42 8 43 8 47 8 48 8P2051bb95e3c65290 0 4 0 1 33 1 41 1 42 1P20899c9635f513a7 1 1 8 2 0 1 43 1 3 34 1 44 1 45 8P21215220f88e2e8a 1 1 8 2 1 1 48 1 3 39 1 49 1 50 8P214ca0a7e4b0ad0f 0 2 0 1 32 1P215f64646ebe9d11 0 2 0 1 34 1P21c334f6f3378b96 0 2 0 1 41 1P21d734b21c2695cc 0 2 0 1 28 1P21ed56641a80f5ac 0 4 0 1 34 1 42 1 43 1P22542f52cb5a36a3 0 2 0 1 36 1P22a6ada30f3d733c 0 2 0 1 20 1P233feb44767def3e 0 4 0 16 32 16 40 16 41 16P238e7a66f0460e28 1 1 8 2 0 1 47 1 3 38 1 48 1 49 8P238fa451c84e0692 0 2 0 1 35 1P23a09c04d1de7f19 0 2 0 1 37 1P23ed613b94855021 1 1 8 2 1 1 44 1 3 35 1 45 1 46 8P240f8809988b6e75 0 4 1 1 32 1 39 1 40 1P2445e1a26b16a7ad 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P24956d79cecf25b3 1 1 8192 3 0 1 37 1 41 1 2 38 1 42 1P2520ab36957d4dca 0 6 1 8 34 8 39 8 40 8 44 8 45 8P253b9e82b3d7c7bd 0 4 1 1 33 1 43 1 44 1P254ab7f818ed8dc1 0 4 1 1 31 1 38 1 39 1P25760a9d0d756be0 0 2 0 1 22 1P257f6f54c66f5451 1 1 8 2 0 1 47 1 3 38 1 48 1 49 8P2585dc06bba95674 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P25e1d90f10e06524 0 2 0 1 20 1P26394517e96bf41b 0 7 2 8 33 64 34 8 39 8 40 8 44 8 45 8P26e5c52373af0c3d 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P274c3b102f81116f 0 4 1 1 33 1 43 1 44 1P279012d5e5fb1155 0 3 0 1 26 1 28 1P27e1ce74d9b7600d 0 2 0 1 42 1P27ebc908dc527cfb 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P282e2a804c42c1da 0 4 0 1 32 1 42 1 43 1P283f2ecea29c1dc7 0 6 1 8 34 8 39 8 40 8 44 8 45 8P285f164287b283b8 1 1 8 2 1 1 48 1 3 39 1 49 1 50 8P28c8a379e600372e 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P28d88b803009c4f2 0 4 0 1 31 1 38 1 39 1P2976ba02b2bd393b 0 2 0 1 20 1P29a07b16f212abf4 0 4 0 1 31 1 38 1 39 1P29e9948b0fbae649 0 6 1 8 33 8 38 8 39 8 43 8 44 8P2a0b77a88d2f0fd6 0 6 1 8 38 8 43 8 44 8 48 8 49 8P2a10d1aa6e4755bf 0 1 1 1P2a29c50017144bcb 0 4 0 1 30 1 37 1 38 1P2a5d996ca7cfeea9 0 7 2 8 38 64 39 8 44 8 45 8 49 8 50 8P2aa61056eae63279 0 3 0 1 18 1 45 1P2ac9c4569ab3ca96 0 2 0 1 35 1P2b4cbb646aea397b 0 4 0 1 34 1 42 1 43 1P2ba827a9a8f10f44 0 2 0 1 42 1P2bb2a58ecaa526ff 0 7 2 8 37 64 38 8 43 8 44 8 48 8 49 8P2bc7e6d0c706b142 1 1 8 2 1 1 43 1 3 34 1 44 1 45 8P2c262e8a47121732 0 2 0 1 18 1P2c7739f56233c4af 1 1 1638400 1 0 1 2 39 1 43 1P2c7b8e1f1d1da7fc 0 2 0 1 41 1P2cb0d0e93e8f43a1 0 6 1 8 38 8 43 8 44 8 48 8 49 8P2cc96555153f5d1a 1 1 8 2 1 1 43 1 3 34 1 44 1 45 8P2d55b11ab8700056 0 2 0 1 42 1P2d7e80e872188e12 0 2 0 1 37 1P2dc209a3f7c20e0f 0 3 0 1 18 1 45 1P2e174c3ed05efa70 0 2 1 1 35 1P2e1ccf4d125ff169 0 2 0 1 19 1P2e2711ea73d7c824 0 2 0 1 42 1P2e42286104b55306 1 2 16 2 0 1 42 1 16 2 1 1 41 1 2 43 1 44 1P2e4f059dc11e17cd 0 4 0 16 32 16 40 16 41 16P2e6155d84b148e8b 0 4 0 16 32 16 40 16 41 16P2e6af58622bef995 0 4 0 1 31 1 38 1 39 1P2e6e195c58f719d1 0 7 2 8 34 64 35 8 40 8 41 8 45 8 46 8P2e8f914af16ce441 2 32 0 4 0 8 2 8 49 8 50 8 1 1 8 4 0 1 3 1 49 1 50 1 2 38 1 51 1P2f41337b6b141126 0 7 2 8 34 64 35 8 40 8 41 8 45 8 46 8P2f616d347c45a5f4 0 7 2 8 33 64 34 8 39 8 40 8 44 8 45 8P2f773955d738ef57 1 1 8 2 1 1 44 1 3 35 1 45 1 46 8P2f7b2e797752581c 1 1 8 2 0 1 42 1 3 33 1 43 1 44 8P2f8d2ffc8772ad3b 0 6 1 8 33 8 38 8 39 8 43 8 44 8P2fd68e446d6ed8e9 0 2 0 1 24 1P2fdc040309ff57cb 0 2 0 1 19 1P2ff121d1ef43c57f 0 3 0 1 17 1 41 1P30182c64bbb16531 0 4 1 1 31 1 38 1 39 1P3121d2a5a3f747d8 0 4 0 16 32 16 40 16 41 16P31473d35459bbf95 1 1 8 2 0 1 46 1 3 37 1 47 1 48 8P3159c5f3a6b3aedd 0 1 1 1P318c61999b4e1048 1 1 8 2 1 1 47 1 3 38 1 48 1 49 8P31e259661ff05a13 0 6 0 8 33 8 38 8 39 8 43 8 44 8P31e720cb864a8886 0 7 2 8 38 64 39 8 44 8 45 8 49 8 50 8P3200b79ebef4c979 0 4 1 1 32 1 39 1 40 1P3202967639b0e16f 0 2 0 1 37 1P3286312a1992ce64 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P32b56980c4ce6af3 0 2 0 1 19 1P32f45a0d59bad8fc 0 4 1 1 33 1 43 1 44 1P33166675e57d2f1f 0 7 2 8 38 64 39 8 44 8 45 8 49 8 50 8P3362b04574ac2806 0 2 0 1 22 1P3368f7de70b082e3 0 4 1 1 34 1 42 1 43 1P33b9350816c77219 0 2 0 1 38 1P348add8c1e747fd2 0 4 1 1 35 1 43 1 44 1P34a8bcce60543aa4 0 6 1 8 38 8 43 8 44 8 48 8 49 8P34d738a87dfa0e8c 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P357e48da546d83d0 0 2 0 1 32 1P35ae38ce3cdf537c 0 2 0 1 37 1P35bda9621c681f0c 0 4 0 1 33 1 41 1 42 1P3617919233deb45d 1 1 8 2 1 1 48 1 3 39 1 49 1 50 8P365a20cd8cf4e926 0 4 0 16 32 16 40 16 41 16P36ac758b4f8d7004 0 4 0 16 32 16 40 16 41 16P37053b6d12cb1258 0 2 0 1 27 1P3875b40c64fcb01d 0 4 0 16 32 16 40 16 41 16P388de7ed1c93c798 0 2 0 1 42 1P395a58d826845446 1 1 8 2 0 1 43 1 3 34 1 44 1 45 8P398ceab2a1e7cc80 0 2 0 1 38 1P39c90af5dc3890c6 0 4 1 1 35 1 43 1 44 1P39cfa8b71279d69c 1 1 8192 3 36 1 37 1 41 1 2 0 1 42 8192P3a0b829d0e8b1ccb 0 4 1 1 32 1 39 1 40 1P3a49cc3b726fa421 0 2 0 1 38 1P3a55dd49c30e1720 0 7 2 8 33 64 34 8 39 8 40 8 44 8 45 8P3b064ba0cd1e0891 0 6 1 8 37 8 42 8 43 8 47 8 48 8P3b7bfb1b68c88f58 0 4 0 1 32 1 42 1 43 1P3bbc2f64e7db8ad3 0 4 0 16 32 16 40 16 41 16P3c06249345f4a394 0 2 0 1 38 1P3c0e164771e3f460 1 1 8 2 1 1 44 1 3 35 1 45 1 46 8P3c2dfabcdb583e90 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P3c55a92aa6312e6e 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16P3c56153289d5a2d4 0 4 1 1 34 1 42 1 43 1P3c71cc40a9f7fa86 0 4 1 1 31 1 38 1 39 1P3cc10e27103c2067 0 4 0 16 32 16 40 16 41 16P3e0bfc42a0d2e125 0 2 0 1 18 1P3e5cc83d6faa1b52 0 2 0 1 19 1P3e906a96d7c61557 0 2 0 1 42 1P3ea2b05422d4467f 0 2 0 1 35 1P3ec88c2ae43944ce 0 4 0 16 32 16 40 16 41 16P3f253c8899c909db 1 1 8 2 0 1 43 1 3 34 1 44 1 45 8P3f310b52c134a950 1 2 1638400 1 0 1 8192 2 1 1 37 1 2 43 1 44 1P3fd06e81e1f50f23 1 1 16 2 1 1 41 1 5 30 1 33 1 34 1 42 1 43 16N00836530f635577bN008c763e852b7defN0170b83d60f88b81N01c2e9ba28bae263N031f6fb9439e537dN0351364dc742ba8cN04c2137f62c9bc26N064a3869f88cce58N06b517bd7ae9245aN0a778723ce354e7cN0aac273ce0335aa8N0b3cb15ff6f2d79eN0c4b2a40da437d6fN0c53ebce281904e8N0c73cba1b4f450d8N0e9547b7e870bfc0N101ae4f617a21898N1061380dcc87ba90N1062b365713daca8N107033bcfa9b993aN113c591f2c7486ebN117d07392d4ea0f9N1203ce7517bb631eN128859e7931e6c74N12c9f6b86be20783N130a8449cce71f01N142ebe06246b6abbN147b0981c5df38cfN15571e2ae1d1fbdbN156bc27424ca06aaN15aba18220910f73N15f1a76819f9496aN18cf79a96e32c2baN195c7b928679c562N1ad160afbb8b89daN1c0a8e08e62e3623N1c4d5d211ad61905N1c9b26580dd96c71N1ca3c5070d4d4297N1db892146730f97bN1e1c89826bd8555eN1e2bfa51b3702a6dN1eac5e9c2c23d9b8N1f4b83532ea9ac39N1f74a9e1f3041df1N1f8ef14660a14567N1ff775ebe840454aN208e57ececee70baN2246c704f5803655N22da7bd3aaf0b49fN236cd485557868aeN253444f1bc480fd2N275b52d20c8c1a26N28f1abdc0c07f4f3N2910010d6cf00122N299ff180294a177bN2a128b6adf97d6c3N2c35d000675ea6daN2e5cd7a823fbdff8N2f04f63a381091e2N2fafb2cd5e22eb10N2ffd32a2235748afN304778110b0199feN30c5b038bb24d7f9N310da22ab320b2f2N31fa628e3e62172bN320f9922055be01bN3235b3c62beb69cfN32e0f381e6b72eceN33b48434282a8667N33bbc307e18a2340N33c829ad3fa8c77fN37144fab424b2cbfN3775706d52d7da20N387a54d55ba70981N3966404e7c9c1875N3bd38ff27f722140N3ce88c049938f145N3fe5af2cce6ae47e"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Recycle () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.eq"; "ARUN_1.Recycle.pop_Wb"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_ok"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.hd_addr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Recycle.pop_body_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.Recycle.pop_regs"; "ARUN_1.A_REC_LOOP"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bwf"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blist"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.last_addr"; "ARUN_1.Recycle.pop_W"; "ARUN_1.Recycle.pop_post"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Drain.qmutex_cells"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.pair"; "ARUN_1.Recycle.rec_frame"; "ARUN_1.A_REC_MB_BACK"; "ARUN_1.A_MERGEB"; "ARUN_1.A_REC_B"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Drain.A_RECYCLE"; "ARUN_1.A_REC_C"; "ARUN_1.A_REC_D"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.A_DORECYCLE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MERGEB : Z := 0x49904.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_REC_MB_BACK : Z := 0x497c8.     (* [comment removed for export] *)
Definition A_REC_B : Z := 0x497dc.           (* [comment removed for export] *)
Definition A_REC_LOOP : Z := 0x4981c.        (* [comment removed for export] *)
Definition A_REC_C : Z := 0x49878.           (* [comment removed for export] *)
Definition A_REC_D : Z := 0x49890.           (* [comment removed for export] *) (* [comment removed for export] *)

Section Recycle.
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
  Definition rec_frame (m : mem) (SPR : Z) (s4 s3 s2 s1 s0 ra : word) : Prop :=
    rw_cells asegs m (SPR + 32) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition pop_regs (SPR : Z) (ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (MIN tlen TL glen gfirst : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "(0.O1=.(1.&40.O1>.)O1<.O1;.(1.&40.O1.)O1:.O19.O18.O17.(1.&40.(2.$3.+2=8.))(1.&40.O5.)O16.O15.(1.&40.O4.)(1.&40.O3.)(1.&40.O2.)O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition pop_Wb (lo SPR : Z) (b : bnode) (tlen TL : Z) : list (Z * Z) :=
    (lo, SPR + 32) :: (A_INSTANCE + 888, A_INSTANCE + 920) :: (bn_addr b, bn_addr b + 8) :: (if tlen =? 0 then [] else [(TL, TL + 8)]).

  Definition pop_body_post (SPR : Z) (ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (MIN tlen TL glen : Z) (glast : word) (gbytes : Z) (b : bnode) (rest : list bnode) (tl0 tfirst tl2 : word) (tbytes lo : Z)
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (Wb : list (Z * Z)) : machine_state -> Prop :=
    fun ms' => exists (m' : mem),
      munch Wb m0 m'
      /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (A_INSTANCE + 888) [C8 (Z_to_bv 64 (glen - 1)); C8 (Z_to_bv 64 (hd_addr rest));
                                               C8 (if hd_addr rest =? 0 then Z_to_bv 64 0 else glast); C8 (Z_to_bv 64 (gbytes - bn_size b))]
      /\ bnode_at m' b 0
      /\ (tlen <> 0 -> rw_cells asegs m' TL [C8 (Z_to_bv 64 (bn_addr b))])
      /\ stk asegs m' lo SPR
      /\ ( (MIN < gbytes - bn_size b
            /\ rw_cells asegs m' SPR [C8 tl0; (if tlen =? 0 then C8 (Z_to_bv 64 (bn_addr b)) else C8 tfirst); C8 tl2; C8 (Z_to_bv 64 (tbytes + bn_size b))]
            /\ exists t1 t2 a7, ms' = MS (pop_regs SPR ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                                MIN (tlen + 1) (bn_addr b) (glen - 1) (hd_addr rest))
                                      F (Z_to_bv 64 A_REC_LOOP) fc None m' (seg_rom asegs))
        \/ (gbytes - bn_size b <= MIN
            /\ rw_cells asegs m' SPR [C8 (Z_to_bv 64 (tlen + 1)); (if tlen =? 0 then C8 (Z_to_bv 64 (bn_addr b)) else C8 tfirst);
                                    C8 (Z_to_bv 64 (bn_addr b)); C8 (Z_to_bv 64 (tbytes + bn_size b))]
            /\ exists t0 t1 t2 a4 a5 a6 a7, ms' = MS (mkR ra (Z_to_bv 64 SPR) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 MIN) a2 a3
                                                    a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (Z_to_bv 64 A_REC_C) fc None m' (seg_rom asegs)) ).

  (* [comment removed for export] *)
  Ltac pop_leaf b rest tlen MU WM NB2 NB3 djtac :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MUl : munch _ _ mx, WMl : wmono _ _ mx |- _ =>
      apply evtA_done; unfold pop_body_post, bnode_at, pop_regs, A_INSTANCE, A_REC_LOOP, A_REC_C; cbn [Z.eqb Z.add Pos.add];
      first [ replace (hd_addr rest =? 0) with false by (symmetry; apply Z.eqb_neq; lx_arith)
            | replace (hd_addr rest) with 0 in * by lx_arith; cbn [Z.eqb] ];
      try replace (tlen =? 0) with false by (symmetry; apply Z.eqb_neq; assumption);
      exists mx; lx_ands;
      [ eapply munch_trans; [exact MU| exact MUl] | eapply wmono_trans; [exact WM| exact WMl] | assumption
      | match goal with K : rw_cells _ mx 1074960 _ |- _ => lx_rwx K end
      | lx_ands; [ match goal with K : rw_cells _ mx (bn_addr b) _ |- _ => lx_rwx K end
                 | eapply (u64arr_transport asegs); [exact NB2| exact MUl| exact WMl| cbn [disjoint_from]; djtac]
                 | exact (wr_at_transport _ _ _ _ _ NB3 WMl) ]
      | first [intros X; exfalso; exact (X eq_refl) | intros _; match goal with K : rw_cells _ mx ?a [_] |- rw_cells _ mx ?a' _ => lx_rwx K end]
      | assumption
      | first [ left; split; [lx_arith| split; [match goal with K : rw_cells _ mx ?a _ |- rw_cells _ mx ?a' _ => constr_eq a a'; lx_rwx K end| do 3 eexists; lx_mseq]]
              | right; split; [lx_arith| split; [match goal with K : rw_cells _ mx ?a _ |- rw_cells _ mx ?a' _ => constr_eq a a'; lx_rwx K end| do 7 eexists; lx_mseq]] ] ]
    end end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L11301590957.72 L11301590957.77 L1210898687.8   L27005134993.72 L27005134993.77 L28569514381.81 L30264290226.10 L307552425.3    L33785052499.72 L33785052499.77 L33785052884.71 L33785052884.76 L34620732896.3  L49373238342.0  L64090904472.101L64093000595.92 L780073989.72   L780073989.77   L780074882.71   L780074882.76   00000D00X01801G01V01c02L02Z02o03D03Y03n04;04<04J04X04m05B05W05lS3hAR1b4rest4HDRB2H6S3hAR1b4rest4HDRB2H7S3hAR3SPR2lo1b5LOIMG3OB03OB13OB4S3hAR1b4rest2H6S3hAR1b4rest2H7S3hAR1b2r02H1S3hAR3SPR2TL2lo1b5LOIMG3OB03OB13OB45TLSEPS3hAR4rest3HDRS3hAR3MIN6gbytes1b2H5S3hAR3MIN6gbytes1b2H6S3hAR3MIN6gbytes1b2H5S3hAR3MIN6gbytes1b2H6S4tlen3TLB2T0SS3hAR6tbytes1bS3hAR6tbytes1bS3hAR3MIN6gbytes1b2H5S3hAR3MIN6gbytes1b2H6S3hAR3MIN6gbytes1b2H5S3hAR3MIN6gbytes1b2H6". (* [comment removed for export] *)
  Lemma rec_pop_body : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pglast,(4.&40.)Ptl0,(4.&40.)Ptfirst,(4.&40.)Ptl2,(4.&40.)PSPR,$5.PMIN,$5.Ptlen,$5.PTL,$5.Pglen,$5.Pgbytes,$5.Ptbytes,$5.Plo,$5.Pb,$6.Prest,(7.$6.)PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm0,P,(4.&40.)(9.(4.&8.))Pm,P,(4.&40.)(9.(4.&8.))PWb,(7.(:.$5.$5.))P,(;.(7.(:.$5.$5.))R1.(<.R8.R?.R7.R=.R<.))P,(=.(>.=R=.)(?.R=.(10.+2.+40.)))P,(=.(>.=R10.)(?.R10.R<.))P,(?.R=.(10.+2.+3>.))P,(=.(>.=(11.R;.))(>.(11.R;.)R>.))P,(=.(>.+1.R10.)(?.R10.(10.+2.+3>.)))P,(=.(>.=R13.)(?.R13.(10.+2.+3>.)))P,(>.=R10.)P,(?.(2.R11.(11.R?.))(10.+2.+3>.))P,(12.VhAR,R10.)P,(13.$6.(12.VhAR,)R10.)P,(14.$15.R=.(2.$3.+378.)(16.$17.(18.(1.&40.R16.))(16.$17.(18.(1.&40.(19.R12.)))(16.$17.(18.R1>.)(16.$17.(18.(1.&40.R15.))(1:.$17.))))))P,(1;.R>.R13.(1<.R12.))P,(1=.VCS,(19.R14.)+2000.)P,P,(1>.(;.$5.R1;.=))(=.(14.$15.R11.R1;.(16.$17.(18.(1.&40.=))(1:.$17.)))(=.(1=.VCS,R1;.+8.)(=.(>.+65?000.R1;.)(=.(>.(2.R1;.+2000.)(1?.VhAR,))(20.(>.(2.R1;.+2000.)(19.R16.))(>.(2.(19.R16.)+2000.)R1;.))))))P,(14.$15.R11.R1>.(16.$17.(18.R21.)(16.$17.(18.R20.)(16.$17.(18.R1?.)(16.$17.(18.(1.&40.R18.))(1:.$17.))))))P,(21.$15.R12.R18.R1?.)P,(>.(1?.VhAR,)R19.)P,(>.R1:.R21.)P,(>.(2.R22.+50.)(10.+2.+3>.))P,(1=.VCS,R1<.(22.(2.R23.+50.)R1<.))P,(23.R16.R18.R17.)P,(24.$15.R19.R18.)P,(25.$15.R19.)(26.$15.VAL,VCS,(27.R27.R43.R42.R41.R3>.R3=.R3<.R3;.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R26.R25.R24.R23.R2;.R22.R1?.R1>.R2:.R29.R28.R21.R20.R1=.R1<.R1;.R19.)(28.(29.R27.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R26.R25.R24.R23.(19.R1?.))R1=.(1.&40.$2:.)R1<.(2;.(4.&40.))R1:.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 glast tl0 tfirst tl2 SPR MIN tlen TL glen gbytes tbytes lo b rest F fc m0 m Wb
      HWb TLR0 MB GB SZB GL TLB TB0 TB1 OKb OKr QG NB BCS TLAST TMP ST LOIMG SPL SPH SCS MU WM MI.
    unfold pop_regs, bnode_at, pop_Wb in *. unfold A_REC_LOOP, A_REC_C, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 920) with 1074992 in *. change (1074072 + 728) with 1074800 in *.
    flat constr:(NB) 3%nat. flclear NB. intros NB1 NB2 NB3. flat constr:(OKb) 5%nat. intros OB0 OB1 OB2 OB3 OB4. unfold bn_count in *.
    assert (HDR : hd_addr rest = 0 \/ 0x65f000 <= hd_addr rest < ACEIL).
    { destruct rest as [|r0 rr]; [left; reflexivity| right]. inversion OKr; subst. unfold bn_ok in *. cbn. lia. }
    assert (HDRB : 0 <= hd_addr rest < ACEIL) by (clear -HDR; lia). clear HDR.
    lx_aceil. lx_hide MU. lx_hide WM.
    destruct (Z.eq_dec tlen 0) as [T0 | T0].
    - (* [comment removed for export] *)
      clear TLAST. rewrite T0 in HWb. cbn [Z.eqb] in HWb. subst Wb. subst tlen.
      pose proof (munch_refl [(lo, SPR + 32); (1074960, 1074992); (bn_addr b, bn_addr b + 8)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
      (* [comment removed for export] *)
      lx_run (PLAN [A_REC_LOOP; A_REC_C] [] 40%N).
      all: lx_unhide; pop_leaf b rest 0 MU WM NB2 NB3 ltac:(clear -OB0 OB1 OB4 LOIMG; lia).
    - specialize (TLAST T0). flat constr:(TLAST) 5%nat. flclear TLAST. intros TLC TLCS TL0 TL1 TLSEP.
      replace (tlen =? 0) with false in HWb by (symmetry; apply Z.eqb_neq; exact T0). subst Wb.
      assert (TP : 0 < tlen) by (clear -T0 TLB; lia).
      pose proof (munch_refl [(lo, SPR + 32); (1074960, 1074992); (bn_addr b, bn_addr b + 8); (TL, TL + 8)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
      (* [comment removed for export] *)
      lx_run (PLAN [A_REC_LOOP; A_REC_C] [] 40%N).
      all: lx_unhide; pop_leaf b rest tlen MU WM NB2 NB3 ltac:(clear -OB0 OB1 OB4 LOIMG TLSEP; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition pop_W (lo SPR : Z) (W : list (Z * Z)) : list (Z * Z) :=
    (lo, SPR + 32) :: (A_INSTANCE + 888, A_INSTANCE + 920) :: W.

  Definition pop_post (SPR : Z) (ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (MIN : Z) (GLAST : word) (gs ts : list bnode) (lo : Z) (W : list (Z * Z))
      (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (m' : mem) (gs1 gs2 : list bnode) (t0 t1 t2 a4 a5 a6 a7 : word),
      gs = gs1 ++ gs2 /\ gs1 <> [] /\ bsum gs2 <= MIN
      /\ munch (pop_W lo SPR W) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (A_INSTANCE + 888) [C8 (Z_to_bv 64 (Z.of_nat (length gs2))); C8 (Z_to_bv 64 (hd_addr gs2));
                                               C8 (match gs2 with [] => Z_to_bv 64 0 | _ => GLAST end); C8 (Z_to_bv 64 (bsum gs2))]
      /\ blist m' gs2 /\ blist m' (ts ++ gs1)
      /\ rw_cells asegs m' SPR [C8 (Z_to_bv 64 (Z.of_nat (length (ts ++ gs1)))); C8 (Z_to_bv 64 (hd_addr (ts ++ gs1)));
                                C8 (Z_to_bv 64 (last_addr 0 (ts ++ gs1))); C8 (Z_to_bv 64 (bsum (ts ++ gs1)))]
      /\ stk asegs m' lo SPR
      /\ ms' = MS (mkR ra (Z_to_bv 64 SPR) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 MIN) a2 a3
                    a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_REC_C) fc None m' (seg_rom asegs).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L10050109936.2 L10064840514.7 L1210900322.8  L12487233674.3 L14779594682.6 L15264956577.0 L1527669678.4  L16497335090.6 L21120261442.3 L22516270820.4 L30251493648.10L30251591623.9 L30264179467.8 L32562146300.4 L32562146300.5 L37620523917.3 L37622622339.3 L39170601649.3 L4380007556.5  L46771139321.3 L50915746944.5 L58290980727.3 L59308532193.4 L59308634630.6 L60608693226.83L62919296925.3 L63347032562.1 L63466355679.7 L64112405833.11L67458179888.1 L68506332615.3 L7834591868.1  L9313704054.5  00000=00`01?01M01g01h02:02S02`03603`04F04h05;05R05\05d06006E06S06j07807J07a08908F08I08g09H09L09[09_0:3S6gbytes4SUMBS6gbytes6tbytes3ts02tl3HTB4SUMB3TB0S3hAR1b3SPR2lo5LOIMG2b'3AP'3OK'S3hAR2tl5OKtl'S1b4rest6gbytes2HB4SUMB2RBSS1b4rest6gbytes2HBS1b4rest3MIN6gbytes2HB2KxS4tlen3ts02HTS1b6gbytes6tbytes4SUMBS3hAR1b3SPR2lo2tl5LOIMG2b'3AP'3OK'3AP23AP1S3hAR1b3SPR2lo2tl5LOIMG4APtl5OKtl'3OKcS3hAR1b3SPR2lo2tl5LOIMG4APtl5OKtl'S4rest4glen2HG4LENBS4rest4glen2HG3ts04LENBS2tl1x3NtlS1b1x2NbS3hAR1b4OKb'S1b6tbytes3ts02tl3HTBS4rest4glen2HGS4rest4tlen3ts02HT4LENBS3hAR2tl5OKtl'S3MIN6gbytes2HB2MBS1b3MIN6gbytes2HB2MB2KcS3hAR1b2r02rr2ts4LENB2H1S4tlen3ts02HTS1bS3hAR1b4rest6gbytes2HB2RB4OKb'S1b4rest6gbytes6tbytes2HB4SUMB2RBS2tlS1b6gbytes4SUMBS2tlS1b3MIN6gbytes2MB2Kc". (* [comment removed for export] *)
  Lemma rec_pop : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pgs,(7.$6.)Pts,(7.$6.)Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)PGLAST,(4.&40.)Ptl0,(4.&40.)Ptf,(4.&40.)Ptl2,(4.&40.)PSPR,$5.PMIN,$5.Ptlen,$5.PTL,$5.Pglen,$5.Pgbytes,$5.Ptbytes,$5.Plo,$5.PW,(7.(:.$5.$5.))PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm0,P,(4.&40.)(9.(4.&8.))Pm,P,(4.&40.)(9.(4.&8.))P,(;.$5.R9.(2=.(2>.$6.R2;.)))P,(;.$5.R9.(2?.R2<.))P,(;.$5.R=.(2=.(2>.$6.R2<.)))P,(;.$5.R:.(2?.R2=.))P,(=.(>.=R10.)(?.R10.R<.))P,(?.(2.R<.R=.)(10.+2.+3>.))P,(?.(2=.(2>.$6.(30.$6.R30.R31.)))(10.+2.+28.))P,(=.(>.=R11.)(?.R11.(10.+2.+40.)))P,(31.VhAR,(30.$6.R32.R33.))P,Pb,$6.P,(32.$6.R1.(30.$6.R34.R35.))(1=.VCS,(19.R2.)+2000.)P,Pb,$6.Px,$5.P,(32.$6.R2.(30.$6.R36.R37.))P,(33.R12.R2.)(1>.(=.(>.(19.R4.)R3.)(?.R3.(2.(19.R4.)+8.))))P,(14.$15.R<.(2.$3.+378.)(16.$17.(18.(1.&40.R14.))(16.$17.(18.(1.&40.(1<.R36.)))(16.$17.(18.R1<.)(16.$17.(18.(1.&40.R13.))(1:.$17.))))))P,(34.R=.R37.)P,(34.R>.R37.)P,P,(1>.(;.$5.R19.=))(=.(;.$5.R19.(35.=R39.))(;.(4.&40.)R1>.(1.&40.(1<.R39.))))P,(14.$15.R10.R1<.(16.$17.(18.R1?.)(16.$17.(18.R1>.)(16.$17.(18.R1=.)(16.$17.(18.(1.&40.R16.))(1:.$17.))))))P,(21.$15.R11.R16.R1=.)P,(>.(1?.VhAR,)R17.)P,(>.R18.R1?.)P,(>.(2.R20.+50.)(10.+2.+3>.))P,(1=.VCS,R1:.(22.(2.R21.+50.)R1:.))P,(23.(36.R1;.R22.R1:.)R17.R16.)P,(24.$15.R18.R17.)P,(25.$15.R18.)(26.$15.VAL,VCS,(37.R25.R41.R40.R3?.R3<.R3;.R3:.R39.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R24.R29.R43.R42.R1>.R1=.R1<.R1;.R1:.)(28.(29.R25.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R24.R23.R22.R21.(1<.R43.))R1<.(1.&40.$2:.)R1;.(2;.(4.&40.))R19.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    induction gs as [|b rest IH]; intros ts ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GLAST tl0 tf tl2
      SPR MIN tlen TL glen gbytes tbytes lo W F fc m0 m HG HB HT HTB MB SUMB LENB TLB WF CSN NW QG BG BT TLD TMP ST LOIMG SPL SPH SCS MU WM MI.
    { exfalso. cbn in HB. clear -HB MB. lia. }
    cbn [hd_addr hd_addrT] in *.
    pose proof (bwf_app_r _ _ WF) as WFg. flat constr:((bwf_cons_inv _ _ WFg)) 3%nat. intros OKb WFr APb.
    pose proof (proj1 WFr) as OKr. pose proof (proj1 (bwf_app_l _ _ WF)) as OKts.
    pose proof (bsum_nonneg rest OKr) as RB. pose proof (bsum_nonneg ts OKts) as TB0.
    pose proof OKb as OKb'. unfold bn_ok in OKb'.
    cbn [bsum] in HB. pose proof LENB as LENB0. rewrite app_length in LENB. cbn [length] in LENB. cbn [length] in HG.
    flat constr:(BG) 2%nat. flclear BG. intros NB BR. change (hd_addrT rest 0) with (hd_addr rest) in NB.
    assert (INb : In b (ts ++ b :: rest)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (HDR : rest <> [] -> hd_addr rest =? 0 = false).
    { intros NE. destruct rest as [|r0 rr]; [congruence|]. inversion OKr; subst. unfold bn_ok in *. cbn. apply Z.eqb_neq. lia. }
    destruct (snoc_or_nil ts) as [Ets | (ts0 & tl & Ets)]; subst ts.
    - (* [comment removed for export] *)
      cbn [length Z.of_nat app] in HT. subst tlen. cbn [bsum] in HTB. subst tbytes. clear TLD BT OKts TB0.
      eapply evtA_cut.
      { eapply (rec_pop_body ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GLAST tl0 tf tl2
                  SPR MIN 0 TL glen gbytes 0 lo b rest F fc m m); try reflexivity.
        all: try first [exact NB | exact OKb | exact OKr | exact QG | exact TMP | exact ST | exact LOIMG | exact SPL | exact SPH | exact SCS | exact MI
                         | apply munch_refl | apply wmono_refl].
        + exact TLB.
        + exact MB.
        + clear -SUMB. lia.
        + clear -HB RB OKb'. lia.
        + clear -HG LENB. lia.
        + clear. lia.
        + clear -SUMB HB RB. lia.
        + apply CSN. exact INb.
        + intros T0. exfalso. apply T0. reflexivity. }
      intros ms' POST. cbv beta in POST. unfold pop_body_post, pop_Wb in POST. cbn [Z.eqb] in POST.
      flat constr:(POST) 9%nat. flclear POST. intros m' MU' WM' MI' QG' NB' _ ST' POST.
      assert (MU2 : munch (pop_W lo SPR W) m0 m').
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pop_W. cbn [outside].
        intros x (O1 & O2 & O3). pose proof (NW b x INb O3) as Nb.
        split; [exact O1|]. split; [exact O2|]. split; [clear -Nb; lia| exact I]. }
      pose proof (wmono_trans asegs _ _ _ WM WM') as WM2.
      assert (BR' : blistT m' rest 0).
      { eapply blistT_transport; [exact BR| exact OKr| exact MU'| exact WM'|].
        intros b' Hb'. pose proof (APb b' Hb') as AP'. rewrite Forall_forall in OKr. pose proof (OKr b' Hb') as OK'. unfold bn_ok in OK'.
        unfold A_INSTANCE. cbn [disjoint_from]. clear -AP' OK' LOIMG. lia. }
      clear MU' WM' MU WM BR NB QG TMP ST MI.
      destruct POST as [(Kc & TMP' & t1' & t2' & a7' & ->) | (Kx & TMP' & t0' & t1' & t2' & a4' & a5' & a6' & a7' & ->)].
      + (* [comment removed for export] *)
        assert (NE : rest <> []) by (intros E; subst rest; cbn [bsum] in HB; clear -Kc MB HB; lia). rewrite (HDR NE) in QG'.
        eapply evtA_mono.
        { eapply (IH [b] ra gp tp t1' t2' s0 s1 a2 a3 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GLAST tl0 (Z_to_bv 64 (bn_addr b)) tl2
                    SPR MIN (0 + 1) (bn_addr b) (glen - 1) (gbytes - bn_size b) (0 + bn_size b) lo W F fc m0 m').
          all: try first [exact QG' | exact BR' | exact TMP' | exact ST' | exact LOIMG | exact SPL | exact SPH | exact SCS | exact MU2 | exact WM2 | exact MI' | exact WF | exact CSN | exact NW | exact LENB0].
          * clear -HG. lia.
          * clear -HB. lia.
          * reflexivity.
          * cbn. clear. lia.
          * clear -Kc MB. lia.
          * clear -SUMB. lia.
          * clear -OKb'. lia.
          * cbn. split; [exact NB'| exact I].
          * intros _. split; reflexivity. }
        intros ms2 PP. unfold pop_post in PP |- *.
        flat constr:(PP) 13%nat. flclear PP. intros m2 gs1 gs2 x0 x1 x2 x4 x5 x6 x7 E NE1 PP. subst rest.
        exists m2, (b :: gs1), gs2, x0, x1, x2, x4, x5, x6, x7. split; [reflexivity|]. split; [congruence|].
        cbn [app] in PP |- *. exact PP.
      + (* [comment removed for export] *)
        apply evtA_done. unfold pop_post. exists m', [b], rest, t0', t1', t2', a4', a5', a6', a7'.
        split; [reflexivity|]. split; [congruence|]. split; [clear -Kx HB; lia|].
        split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|].
        split. { replace (Z.of_nat (length rest)) with (glen - 1) by (clear -HG; lia). replace (bsum rest) with (gbytes - bn_size b) by (clear -HB; lia).
                 destruct rest as [|r0 rr]; [cbn [hd_addr hd_addrT Z.eqb] in QG'; exact QG'|]. rewrite (HDR ltac:(congruence)) in QG'. exact QG'. }
        split; [exact BR'|]. split; [cbn; split; [exact NB'| exact I]|].
        split; [cbn [app length Z.of_nat Pos.of_succ_nat hd_addr hd_addrT last_addr bsum]; cbn [Z.add] in TMP'; rewrite Z.add_0_r; exact TMP'|].
        split; [exact ST'| reflexivity].
    - (* [comment removed for export] *)
      rewrite zlen_app1 in HT. rewrite app_length in LENB. cbn [length] in LENB.
      assert (T0 : tlen <> 0) by (clear -HT; lia).
      flat constr:((TLD T0)) 2%nat. intros ETL Etf. rewrite last_addr_snoc in ETL. subst TL.
      unfold blist in BT. rewrite blistT_snoc in BT. flat constr:(BT) 2%nat. flclear BT. intros B0 Btl.
      assert (OKtl : bn_ok tl) by (eapply bwf_ok_in; [exact WF|]; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (INtl : In tl (ts0 ++ [tl])) by (apply in_or_app; right; left; reflexivity).
      assert (APtl : bn_addr tl + 8192 <= bn_addr b \/ bn_addr b + 8192 <= bn_addr tl)
        by (eapply bwf_app_apart; [exact WF| exact INtl| left; reflexivity]).
      pose proof OKtl as OKtl'. unfold bn_ok in OKtl'.
      flat constr:(Btl) 3%nat. flclear Btl. intros R1 R2 R3.
      pose proof (proj1 (rw_cells_app asegs m (bn_addr tl) [C8 _] [C8 _; C8 _]) R1) as [R1a R1b]. clear R1.
      assert (CStl : crange CS (bn_addr tl) 8192) by (apply CSN; apply in_or_app; left; exact INtl).
      eapply evtA_cut.
      { eapply (rec_pop_body ra gp tp t1 t2 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GLAST tl0 tf tl2
                  SPR MIN tlen (bn_addr tl) glen gbytes tbytes lo b rest F fc m m); try reflexivity.
        all: try first [exact NB | exact OKb | exact OKr | exact QG | exact TMP | exact ST | exact LOIMG | exact SPL | exact SPH | exact SCS | exact MI
                         | apply munch_refl | apply wmono_refl].
        + exact TLB.
        + exact MB.
        + clear -SUMB TB0 HTB. lia.
        + clear -HB RB OKb'. lia.
        + clear -HG LENB. lia.
        + clear -HT LENB. lia.
        + subst tbytes. exact TB0.
        + clear -SUMB HB RB TB0 HTB. lia.
        + apply CSN. exact INb.
        + intros _. split; [exact R1a|]. split; [eapply crange_sub; [exact CStl| clear; lia| clear; lia]|].
          split; [clear -OKtl'; lia|]. split; [clear -OKtl'; lia|]. exact APtl. }
      intros ms' POST. cbv beta in POST. unfold pop_body_post, pop_Wb in POST.
      replace (tlen =? 0) with false in POST by (symmetry; apply Z.eqb_neq; exact T0).
      flat constr:(POST) 9%nat. flclear POST. intros m' MU' WM' MI' QG' NB' TLC' ST' POST. specialize (TLC' T0).
      assert (MU2 : munch (pop_W lo SPR W) m0 m').
      { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. unfold sub_fp, pop_W. cbn [outside app].
        intros x (O1 & O2 & O3). pose proof (NW b x INb O3) as Nb. pose proof (NW tl x ltac:(apply in_or_app; left; exact INtl) O3) as Ntl.
        split; [exact O1|]. split; [exact O2|]. split; [clear -Nb; lia|]. split; [clear -Ntl; lia| exact I]. }
      pose proof (wmono_trans asegs _ _ _ WM WM') as WM2.
      assert (BR' : blistT m' rest 0).
      { eapply blistT_transport; [exact BR| exact OKr| exact MU'| exact WM'|].
        intros b' Hb'. pose proof (APb b' Hb') as AP'. rewrite Forall_forall in OKr. pose proof (OKr b' Hb') as OK'. unfold bn_ok in OK'.
        pose proof (bwf_app_apart _ _ tl b' WF INtl ltac:(right; exact Hb')) as AP2.
        unfold A_INSTANCE. cbn [disjoint_from app]. clear -AP' AP2 OK' LOIMG. lia. }
      (* [comment removed for export] *)
      assert (BT' : blist m' ((ts0 ++ [tl]) ++ [b])).
      { unfold blist. rewrite blistT_snoc. split; [| exact NB']. rewrite blistT_snoc. split.
        - eapply blistT_transport; [exact B0| exact (proj1 (bwf_app_l _ _ (bwf_app_l _ _ WF)))| exact MU'| exact WM'|].
          intros b' Hb'. rewrite Forall_forall in OKts. pose proof (OKts b' ltac:(apply in_or_app; left; exact Hb')) as OK'. unfold bn_ok in OK'.
          pose proof (bwf_app_apart _ _ b' b WF ltac:(apply in_or_app; left; exact Hb') ltac:(left; reflexivity)) as AP1.
          pose proof (bwf_app_apart _ _ b' tl (bwf_app_l _ _ WF) Hb' ltac:(left; reflexivity)) as AP2.
          unfold A_INSTANCE. cbn [disjoint_from app]. clear -AP1 AP2 OK' LOIMG. lia.
        - split; [|split].
          + apply (proj2 (rw_cells_app asegs m' (bn_addr tl) [C8 _] [C8 _; C8 _])). split; [exact TLC'|].
            eapply rw_cells_transport; [exact R1b| exact MU'| exact WM'|].
            unfold A_INSTANCE. cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear -APtl OKtl' LOIMG. lia.
          + eapply u64arr_transport; [exact R2| exact MU'| exact WM'|].
            pose proof OKtl as OKc. unfold bn_ok, bn_count in OKc.
            unfold A_INSTANCE. cbn [disjoint_from app]. clear -APtl OKtl' OKc LOIMG. lia.
          + eapply wr_at_transport; [exact R3| exact WM']. }
      clear MU' WM' MU WM BR NB QG TMP ST MI B0 R1a R1b R2 R3.
      destruct POST as [(Kc & TMP' & t1' & t2' & a7' & ->) | (Kx & TMP' & t0' & t1' & t2' & a4' & a5' & a6' & a7' & ->)].
      + (* [comment removed for export] *)
        assert (NE : rest <> []) by (intros E; subst rest; cbn [bsum] in HB; clear -Kc MB HB; lia). rewrite (HDR NE) in QG'.
        eapply evtA_mono.
        { eapply (IH ((ts0 ++ [tl]) ++ [b]) ra gp tp t1' t2' s0 s1 a2 a3 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GLAST tl0 tf tl2
                    SPR MIN (tlen + 1) (bn_addr b) (glen - 1) (gbytes - bn_size b) (tbytes + bn_size b) lo W F fc m0 m').
          all: rewrite <- ? (app_assoc (ts0 ++ [tl]) [b] rest); cbn [app].
          all: try first [exact QG' | exact BR' | exact TMP' | exact ST' | exact LOIMG | exact SPL | exact SPH | exact SCS | exact MU2 | exact WM2 | exact MI' | exact WF | exact CSN | exact NW | exact LENB0].
          * clear -HG. lia.
          * clear -HB. lia.
          * rewrite 2 zlen_app1. clear -HT. lia.
          * rewrite bsum_app. cbn [bsum]. clear -HTB. lia.
          * clear -Kc MB. lia.
          * clear -SUMB. lia.
          * clear -OKb'. lia.
          * exact BT'.
          * intros _. rewrite last_addr_snoc, hd_addr_app_ne by (destruct ts0; cbn; congruence). split; [reflexivity| exact Etf]. }
        intros ms2 PP. unfold pop_post in PP |- *.
        flat constr:(PP) 13%nat. flclear PP. intros m2 gs1 gs2 x0 x1 x2 x4 x5 x6 x7 E NE1 PP. subst rest.
        exists m2, (b :: gs1), gs2, x0, x1, x2, x4, x5, x6, x7. split; [reflexivity|]. split; [congruence|].
        rewrite <- (app_assoc (ts0 ++ [tl]) [b] gs1) in PP. cbn [app] in PP. exact PP.
      + (* [comment removed for export] *)
        apply evtA_done. unfold pop_post. exists m', [b], rest, t0', t1', t2', a4', a5', a6', a7'.
        split; [reflexivity|]. split; [congruence|]. split; [clear -Kx HB; lia|].
        split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|].
        split. { replace (Z.of_nat (length rest)) with (glen - 1) by (clear -HG; lia). replace (bsum rest) with (gbytes - bn_size b) by (clear -HB; lia).
                 destruct rest as [|r0 rr]; [cbn [hd_addr hd_addrT Z.eqb] in QG'; exact QG'|]. rewrite (HDR ltac:(congruence)) in QG'. exact QG'. }
        split; [exact BR'|]. split; [exact BT'|].
        split. { rewrite 2 zlen_app1, <- HT, last_addr_snoc, bsum_app, <- HTB, hd_addr_app_ne by (destruct ts0; cbn; congruence).
                 cbn [bsum]. rewrite Z.add_0_r, <- Etf. exact TMP'. }
        split; [exact ST'| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac recA_leaf SP :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with FRl : rw_cells _ mx (SP + -80) _ |- _ =>
        let FRz := fresh "FRz" in let FRf := fresh "FRf" in
        chunk_split FRl 4%nat FRz FRf; replace (SP + -80 + 32) with (SP + -48) in FRf by (clear; lia) end;
      apply evtA_done; exists mx; lx_exs; lx_ands;
      [ assumption .. | first [ left; split; [lx_arith| split; [lx_arith| lx_mseq]] | right; split; [lx_arith| lx_mseq] ] ]
    end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L10520132463.73L11502783125.1 L16940323564.67L17411292651.67L17411292909.63L17771283496.72L3379728136.75 L35264783175.76L37742961844.72L434141041.74  L46812718316.76L47594381514.3 L4979469410.72 L53522094981.72L56607117747.63L56607118005.67L58541538367.72L63865721896.72L66434281969.0 00000I00M00d01;01R01_02002T02Y02d03;03L03Y03g03h04@04A04F04GS3hAR2SP2lo5LOIMG3SPL3SPAS2SPS3hAR2SP4glen6gbytes2H9S3hAR2SP4glen6gbytes2H9S3hAR2SP4glen6gbytes2H9S3hAR2AL4IMG'S3hAR2SP2HB5Ha_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hARS3hAR2SP2HBS3hAR2SP2HB5Ha_st5Hl_stS4glen6gbytes3GOVS3hAR2AL4IMG'S3hAR2AL5ALWF'FS3hAR2SP4glen6gbytes3H10FS3hARS". (* [comment removed for export] *)
  Lemma rec_A : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pgfirst,(4.&40.)Pglast,(4.&40.)PSP,$5.PT,$5.PSTK,$5.PMIN,$5.Pglen,$5.Pgbytes,$5.Plo,$5.PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(9.(4.&8.))P,(=.(>.+1000.R9.)(20.(>.(2.R9.+1000.)+10000.)(>.+65?000.R9.)))P,(>.(2.R:.+1000.)(10.+2.+2?.))P,(=.(>.=R:.)(?.R:.(10.+2.+40.)))P,(=.(>.=R:.)(?.R:.(10.+2.+3>.)))P,(>.=R:.)P,(>.(38.R;.+2000.)R:.)P,(?.R;.(10.+2.+28.))P,(14.$15.R8.(2.$3.+370.)(39.=+1.))P,(14.$15.R9.(2.$3.+378.)(16.$17.(18.(1.&40.R>.))(16.$17.(18.R14.)(16.$17.(18.R13.)(16.$17.(18.(1.&40.R=.))(1:.$17.))))))P,(21.$15.R:.R=.R13.)P,(>.(1?.VhAR,)R>.)P,(>.R?.(22.R15.+50.))P,(>.R16.(10.+2.+3>.))P,(;.$5.(3:.R17.+10.)=)P,(1=.VCS,R12.(22.R18.R12.))P,(25.$15.R10.)(26.$15.VAL,VCS,Lms',$3;.(3<.P,(4.&40.)(9.(4.&8.))Lm',P,(4.&40.)(9.(4.&8.))(3<.(4.&40.)Lx5,(4.&40.)(3<.(4.&40.)Lx6,(4.&40.)(3<.(4.&40.)Lx14,(4.&40.)(3<.(4.&40.)Lx15,(4.&40.)(3<.(4.&40.)Lx17,(4.&40.)(=.(23.(16.(:.$5.$5.)(3=.$5.$5.R1;.R21.)(16.(:.$5.$5.)(3=.$5.$5.(2.$3.+370.)(2.$3.+374.))(1:.(:.$5.$5.))))R18.R6.)(=.(24.$15.R18.R6.)(=.(25.$15.R6.)(=.(14.$15.R6.(2.$3.+370.)(39.+1.+1.))(=.(14.$15.R6.(2.$3.+378.)(16.$17.(18.(1.&40.R1=.))(16.$17.(18.R23.)(16.$17.(18.R22.)(16.$17.(18.(1.&40.R1<.))(1:.$17.))))))(=.(14.$15.R6.(2.R21.-50.)(16.$17.(18.(1.&40.=))(16.$17.(18.(1.&40.=))(16.$17.(18.(1.&40.=))(16.$17.(18.(1.&40.=))(1:.$17.))))))(=.(3>.R6.(2.R21.-50.)R2?.R30.R31.R36.R37.R3=.)(=.(21.$15.R6.R1;.(2.R21.-50.))(20.(=.(?.(38.R1=.+2000.)R1<.)(=.(?.(38.R1<.+64.)(38.R1=.+190000.))(;.$3;.R7.(28.(0.(1.&40.$3?.)(1.&40.(2.R21.-50.))R3<.R3;.R5.R4.R38.(1.&40.(2.$3.+378.))(1.&40.R1>.)(1.&40.(2.$3.+378.))(1.&40.(2.R21.-50.))(1.&40.(2.R20.+=0.))(1.&40.R1?.)R3.R2.(1.&40.R1=.)R1.(1.&40.(2.$3.+2=8.))(1.&40.R1?.)(1.&40.(2.R20.+=0.))R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R1:.(1.&40.$40.)R19.(2;.(4.&40.))R6.(2<.$15.)))))(=.(1>.(=.(?.(38.R1=.+2000.)R1<.)(?.(38.R1<.+64.)(38.R1=.+190000.))))(;.$3;.R7.(28.(0.R3=.(1.&40.(2.R21.-50.))R3<.R3;.R5.R4.R38.R37.R36.(1.&40.(2.$3.+2=8.))(1.&40.R1>.)(1.&40.(2.R20.+=0.))(1.&40.R1?.)R3.R2.(1.&40.R1=.)R1.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R1:.(1.&40.$41.)R19.(2;.(4.&40.))R6.(2<.$15.)))))))))))))))))))(28.(0.R36.(1.&40.R1:.)R35.R34.R33.R32.R31.R30.R2?.(1.&40.(2.$3.+2=8.))(1.&40.R17.)(1.&40.(2.R19.+=0.))(1.&40.R18.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R13.(1.&40.$42.)R12.(2;.(4.&40.))R11.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gfirst glast SP T STK MIN glen gbytes lo F fc m
      TB1 TB2 STKB MINB GL0 GOV GBB QMU QG ST LOIMG SPL SPH SPA SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold qmutex_cells, rec_frame in *. unfold A_RECYCLE, A_INSTANCE, A_MERGEB, A_REC_MB_BACK, A_REC_B in *.
    change (1074072 + 880) with 1074952 in *. change (1074072 + 884) with 1074956 in *. change (1074072 + 888) with 1074960 in *.
    change (1074072 + 728) with 1074800 in *.
    pose proof (munch_refl [(lo, SP); (1074952, 1074956)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    assert (GOV' : 8192 * glen <= gbytes) by (clear -GOV; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    lx_run (PLAN [0x4975c] [] 20%N).
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mx 1074952 _ |- _ =>
      apply (rw_cells_reshape asegs _ 1074952 _ [C4 (Z_to_bv 64 256)]) in H; [| cbn; tauto | bytes_eq] end.
    zstep. rewrite (sx32_small 256) by (clear; lia).
    zstep. zstep. zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ ?mx 1074952 [C4 ?v] |- _ =>
      apply (rw_cells_reshape asegs mx 1074952 _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x49904; A_REC_B] [] 30%N).
    - recA_leaf SP.
    - recA_leaf SP.
    - recA_leaf SP.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L28602898301.48L35865049143.48L53534663706.48L65991419447.4800000900B00L00MS2AL4IMG'S2AL4IMG'S2AL5ALWF'S". (* [comment removed for export] *)
  Lemma rec_MB_back : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pgf,(4.&40.)Pgl,(4.&40.)PSPR,$5.PT,$5.PSTK,$5.PMIN,$5.Pglen,$5.Pgbytes,$5.PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(9.(4.&8.))P,(=.(>.=R5.)(?.R5.(10.+2.+40.)))P,(14.$15.R2.(2.$3.+378.)(16.$17.(18.(1.&40.R6.))(16.$17.(18.R<.)(16.$17.(18.R;.)(16.$17.(18.(1.&40.R5.))(1:.$17.))))))P,(25.$15.R3.)(26.$15.VAL,VCS,Lms',$3;.(;.$3;.R1.(28.(0.R28.(1.&40.R=.)R27.R26.R25.R24.R23.(1.&40.(2.$3.+378.))(1.&40.R:.)(1.&40.(2.$3.+2=8.))(1.&40.R:.)(1.&40.(2.R<.+=0.))(1.&40.R;.)R1>.R1=.(1.&40.R9.)R1;.(1.&40.(2.$3.+2=8.))(1.&40.R;.)(1.&40.(2.R<.+=0.))R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R7.(1.&40.$41.)R6.(2;.(4.&40.))R5.(2<.$15.)))(28.(0.R27.(1.&40.R<.)R26.R25.R24.R23.R22.(1.&40.(2.$3.+378.))(1.&40.R9.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(1.&40.(2.$3.+2=8.))(1.&40.R:.)(1.&40.(2.R;.+=0.))R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R6.(1.&40.$3?.)R5.(2;.(4.&40.))R4.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gf gl SPR T STK MIN glen gbytes F fc m GL QG MI.
    facts. unfold A_REC_MB_BACK, A_REC_B, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 728) with 1074800 in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L1122830793.60 L11946690999.60L20891441591.60L22601928941.61L31440207392.3 L31751401824.60L34020880659.60L42386907283.61L47937465853.60L50401463955.61L52214089945.61L52284912211.61L53524211262.61L53534663706.60L59407556966.3 L6932510272.60 L7182396401.60 00000100:00;00<00J00O00T00U00^00g01001501?01I01W01\01aFS2AL4IMG'SFS3MIN6gbytes1KS3SPRS3SPRSS2AL4IMG'S2AL4IMG'S2AL4IMG'S3SPRS2AL5ALWF'S2AL5ALWF'S3MIN6gbytes1KS3SPRS3SPR". (* [comment removed for export] *)
  Lemma rec_B : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Ptf,(4.&40.)Pgl,(4.&40.)PSPR,$5.PMIN,$5.Pglen,$5.Pgfirst,$5.Pgbytes,$5.Ptlen,$5.PTL,$5.Ptbytes,$5.PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(9.(4.&8.))P,(=.(>.=R:.)(?.R:.(10.+2.+40.)))P,(=.(>.=R8.)(?.R8.(10.+2.+40.)))P,(=.(>.=R:.)(?.R:.(10.+2.+40.)))P,(=.(>.=R9.)(?.R9.(10.+2.+40.)))P,(=.(>.=R9.)(?.R9.(10.+2.+40.)))P,(>.=R10.)P,(>.(2.R11.+50.)(10.+2.+3>.))P,(14.$15.R8.(2.$3.+378.)(16.$17.(18.(1.&40.R10.))(16.$17.(18.(1.&40.R?.))(16.$17.(18.R13.)(16.$17.(18.(1.&40.R>.))(1:.$17.))))))P,(14.$15.R9.R13.(16.$17.(18.(1.&40.R>.))(16.$17.(18.R15.)(16.$17.(18.(1.&40.R=.))(16.$17.(18.(1.&40.R<.))(1:.$17.))))))P,(1=.VCS,R14.+50.)P,(25.$15.R;.)(26.$15.VAL,VCS,Lms',$3;.(20.(=.(?.R16.R13.)(3<.(4.&40.)Lt1',(4.&40.)(3<.(4.&40.)Lt2',(4.&40.)(;.$3;.R3.(28.(29.R19.R36.R35.R34.R2.R1.R30.R2?.R2>.R2=.(1.&40.R15.)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R18.R14.R13.R17.R16.)R11.(1.&40.$2:.)R10.(2;.(4.&40.))R?.(2<.$15.))))))(=.(>.R13.R16.)(3<.(4.&40.)Lt0',(4.&40.)(3<.(4.&40.)Lt1',(4.&40.)(3<.(4.&40.)Lt2',(4.&40.)(3<.(4.&40.)La4',(4.&40.)(3<.(4.&40.)La5',(4.&40.)(3<.(4.&40.)La6',(4.&40.)(3<.(4.&40.)La7',(4.&40.)(;.$3;.R8.(28.(0.R3;.(1.&40.R1>.)R3:.R39.R7.R6.R5.R35.R34.(1.&40.(2.$3.+2=8.))(1.&40.R1=.)R33.R32.R4.R3.R2.R1.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R16.(1.&40.$43.)R15.(2;.(4.&40.))R14.(2<.$15.))))))))))))(28.(0.R33.(1.&40.R16.)R32.R31.R30.R2?.R2>.R2=.R2<.(1.&40.(2.$3.+2=8.))(1.&40.R15.)R2;.R2:.R29.R28.(1.&40.R14.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R>.(1.&40.$41.)R=.(2;.(4.&40.))R<.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 tf gl SPR MIN glen gfirst gbytes tlen TL tbytes F fc m
      MINB GBB GFB TLB TLR SP0 SP1 QG TMP SCS MI.
    facts. unfold pop_regs. unfold A_REC_B, A_REC_LOOP, A_REC_C, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 728) with 1074800 in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - apply evtA_done. right. split; [clear -K; lia|]. do 7 eexists. reflexivity.
    - (* [comment removed for export] *)
      zstep. zstep. apply evtA_done. left. split; [clear -K; lia|]. do 2 eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L14129987602.50L17771772049.48L28011462041.49L3379728136.50 L3379728136.51 L3381681140.49 L3381681140.50 L40580442539.49L40580442539.50L434141041.49  L4979380443.48 L52355520409.49L53520115492.49L53522310972.48L62191353811.49L63866038417.4800000400=00F00P00Z00^00b00f00j00n01701801B01L01U01VS2HBS2AL4IMG'S2AL4IMG'S2HB5Ha_stS2HB5Ha_stS2HBS2HBS2HBS2HBS2HBS2AL4IMG'SS2AL5ALWF'S2AL5ALWF'S2AL4IMG'S". (* [comment removed for export] *)
  Lemma rec_C : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)PSPR,$5.PMIN,$5.PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(9.(4.&8.))P,(>.=R5.)P,(>.(2.R6.+50.)(10.+2.+3>.))P,(14.$15.R3.(2.$3.+370.)(39.+1.+1.))P,(25.$15.R4.)(26.$15.VAL,VCS,Lms',$3;.(3<.P,(4.&40.)(9.(4.&8.))Lm',P,(4.&40.)(9.(4.&8.))(=.(23.(16.(:.$5.$5.)(3=.$5.$5.(2.$3.+370.)(2.$3.+374.))(1:.(:.$5.$5.)))R7.R1.)(=.(24.$15.R7.R1.)(=.(25.$15.R1.)(=.(14.$15.R1.(2.$3.+370.)(39.==))(;.$3;.R2.(28.(0.(1.&40.$44.)(1.&40.R;.)R26.R25.R24.R23.R22.R21.R20.(1.&40.(2.$3.+2=8.))(1.&40.R;.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R9.(1.&40.$45.)R8.(2;.(4.&40.))R1.(2<.$15.))))))))(28.(0.R25.(1.&40.R9.)R24.R23.R22.R21.R20.R1?.R1>.(1.&40.(2.$3.+2=8.))(1.&40.R8.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R7.(1.&40.$43.)R6.(2;.(4.&40.))R5.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SPR MIN F fc m SP0 SP1 QMU MI.
    facts. unfold qmutex_cells in *. unfold A_REC_C, A_REC_D, A_DORECYCLE, A_INSTANCE in *.
    change (1074072 + 880) with 1074952 in *. change (1074072 + 884) with 1074956 in *. change (1074072 + 728) with 1074800 in *.
    pose proof (munch_refl [(1074952, 1074956)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L1167164263.64 L13203986535.64L14480557498.65L14796371642.64L19231034343.64L19231098492.63L20015785146.64L34078451998.62L37283107431.64L37794465338.64L40600209466.64L43308582375.64L446963258.65  L4705632186.65 L48109499377.63L48317960604.64L51602192058.65L53397530938.65L55616696633.65L67674516410.64L68666318138.64L7195277031.64 00000@00P00Y00e01501E01Q01Z01j02602B02R02[02d02m03=03F03O03X03d04004@S3hAR3SPR2lo3SPLS3hAR3SPR2lo3SPLS3hAR3SPRS3hAR3SPR2loS3hAR3SPR2lo3SPLS3hAR3SPR2lo3SPLS3hAR3SPR2loS3hAR3SPRS3hAR3SPR2lo3SPLS3hAR3SPR2loS3hAR3SPR2loS3hAR3SPR2lo3SPLS3hAR3SPRS3hAR3SPRS3hAR3SPRS3hAR3SPR2lo3SPLS3hAR3SPRS3hAR3SPRS3hAR3SPRS3hAR3SPR2loS3hAR3SPR2loS3hAR3SPR2lo3SPL". (* [comment removed for export] *)
  Lemma rec_D : ltac2:(CDefT.buildp (gd_tbl_AW_Recycle ()) "Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pq4,(4.&40.)Pq3,(4.&40.)Pq2,(4.&40.)Pq1,(4.&40.)Pq0,(4.&40.)Pqra,(4.&40.)Pw0,(4.&40.)Pw1,(4.&40.)Pw2,(4.&40.)Pw3,(4.&40.)PSPR,$5.Plo,$5.PF,(8.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(9.(4.&8.))P,(>.=R5.)P,(>.(2.R6.+50.)(10.+2.+3>.))P,(14.$15.R3.R7.(16.$17.(18.R;.)(16.$17.(18.R:.)(16.$17.(18.R9.)(16.$17.(18.R8.)(1:.$17.))))))P,(3>.R4.R8.R12.R11.R10.R?.R>.R=.)P,(21.$15.R5.R8.R9.)P,(>.(1?.VhAR,)R9.)P,(>.R:.R;.)P,(1=.VCS,R;.(22.(2.R<.+50.)R;.))P,(25.$15.R9.)(26.$15.VAL,VCS,Lms',$3;.(3<.P,(4.&40.)(9.(4.&8.))Lm',P,(4.&40.)(9.(4.&8.))(=.(23.(16.(:.$5.$5.)(3=.$5.$5.R?.(2.R10.+50.))(1:.(:.$5.$5.)))R<.R1.)(=.(24.$15.R<.R1.)(=.(25.$15.R1.)(=.(21.$15.R1.R?.(2.R10.+50.))(;.$3;.R2.(28.(0.R15.(1.&40.(2.R10.+50.))R37.R36.R35.R34.R33.R16.R17.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R18.R19.R1:.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R>.(46.R15.)R=.(2;.(4.&40.))R1.(2<.$15.))))))))(28.(0.(1.&40.$44.)(1.&40.R>.)R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R<.(1.&40.$44.)R;.(2;.(4.&40.))R:.(2<.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q4 q3 q2 q1 q0 qra w0 w1 w2 w3 SPR lo F fc m
      SP0 SP1 TMP FR ST LOIMG SPL SCS MI.
    facts. unfold rec_frame in *. unfold A_REC_D in *.
    pose proof (munch_refl [(lo, SPR + 80)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame TMP ST (SPR + 32). release_frame FR ST (SPR + 80).
    apply evtA_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Recycle.

End ARUN_1.
