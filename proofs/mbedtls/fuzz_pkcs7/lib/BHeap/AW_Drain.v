(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000e9128bf182ded 2 46 0 2 0 1 1 1 0 3 0 1 2 1 45 1P0026d37526e57c6e 0 4 0 1 40 1 42 1 43 1P00914c1ed941767d 0 2 3 1 27 1P009d56d26f18660a 0 2 0 1 48 1P00f3ba36616cae2b 0 4 0 1 43 1 47 1 48 1P010da76c69953a07 0 2 2 1 28 1P012528668bbfb1c6 0 2 0 1 42 1P01c88d5c680dbda1 0 4 0 1 43 1 47 1 48 1P022d23d502908f89 0 3 0 1 2 1 45 1P02612c35148ae988 2 40 0 2 0 1 1 1 0 3 0 1 2 1 45 1P026d16a35360055e 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P028863c6238da72b 0 2 2 1 28 1P02968c65e9056dfd 0 4 1 1 40 1 44 1 45 1P031797e2271fe3b8 0 2 3 1 27 1P03481a1325d9e78f 0 2 3 1 29 1P03bb413bf9c2595b 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P03f59f431e5d9bf5 0 2 3 1 27 1P043b69f57734b58f 0 4 1 1 38 1 40 1 41 1P0467dc240cc4871b 0 2 0 1 26 1P047895acad766dcd 0 4 1 1 40 1 44 1 45 1P04c872df0cd12730 0 2 0 1 52 1P04d7e6d86ab7e295 0 2 1 1 45 1P0505f803c9e55956 0 2 2 1 26 1P05686a8985dc13fb 0 2 0 1 52 1P05757607eca37512 0 2 0 1 43 1P05938bddaa421412 0 4 1 1 38 1 40 1 41 1P05a2b8ac2d6cb3fe 0 2 0 1 43 1P05aa28c0b3a83140 0 2 3 1 29 1P05eb6559d612d15b 0 2 0 1 43 1P061d5448af0a7430 0 5 0 1 2 1 41 1 43 1 44 1P066cace0ffc5618c 0 2 3 1 29 1P0720472839640e64 0 2 0 1 45 1P0758b7b5134db2ef 0 2 2 1 28 1P079287f25c07cb22 0 2 3 1 27 1P07a57aa612e8ae95 0 2 3 1 29 1P084c310f7f5f885b 0 2 2 1 28 1P08880b50e2404a19 0 4 1 1 38 1 40 1 41 1P089a7ac3283227e1 0 2 3 1 27 1P090c866ba7203c0e 0 4 0 1 43 1 47 1 48 1P0942c08fd1311a85 0 4 1 1 38 1 40 1 41 1P09af7e81b9e1ae5e 0 2 3 1 29 1P09d191baee67316b 0 2 3 1 29 1P09e14a80e808733e 0 2 3 1 27 1P09ebfd5fe5378d81 0 2 2 1 28 1P0a00abc88667d00d 0 2 2 1 26 1P0a818741bb1d3a53 0 4 1 1 40 1 44 1 45 1P0afe03f12c1484cc 2 46 0 2 0 1 1 1 0 3 0 1 2 1 45 1P0b133d60d0329847 0 3 1 1 44 1 46 1P0b37149ae84ecab7 0 2 0 1 47 1P0b8f24ab85cd3b27 0 4 1 1 40 1 44 1 45 1P0bc90436a98d8354 0 2 3 1 29 1P0c2a765385c409df 0 3 0 1 44 1 45 1P0c3e4cacdb4f80d6 0 2 0 1 39 1P0c5ee9570994f6a5 0 2 0 1 47 1P0cde5af8bd73757f 0 2 3 1 29 1P0d76b5c54bd52522 0 2 0 1 47 1P0da385cf17dc3bb0 0 4 0 1 43 1 47 1 48 1P0da42bd9923b160b 0 4 1 1 40 1 44 1 45 1P0ddfa0a793057598 0 2 0 1 39 1P0de05e7777b90aea 0 2 3 1 29 1P0e01b38a1f134469 2 39 0 2 0 1 1 1 0 3 0 1 2 1 41 1P0e48f951e4d79ced 0 2 3 1 29 1P0e99663da297b369 2 46 0 2 0 1 1 1 0 3 0 1 2 1 45 1P0e9bd132b8156845 0 2 2 1 26 1P0ea7274eb7e5c2ae 0 2 3 1 27 1P0ec025f515b217b2 0 4 1 1 40 1 44 1 45 1P0ef69186ca7cd736 0 4 1 1 38 1 40 1 41 1P0f409259b4c2d9c2 0 2 0 1 39 1P0f55c7d4c9e30e11 0 2 2 1 28 1P0fb5e47275d5e572 0 4 1 1 38 1 40 1 41 1P100c68c684ed2f83 0 2 2 1 26 1P1020e0ce6f3a67ec 0 2 2 1 28 1P104abe0e18a43c0c 0 3 0 1 49 1 50 1P1066950b2d8b418b 0 2 3 1 27 1P1080ff80c3e660aa 0 2 0 1 47 1P109c9cef9abf4897 0 2 2 1 28 1P10a4422b95a1b1a6 0 2 0 1 53 1P10f9a61a181d886d 0 2 0 1 45 1P110da8b857372fd5 0 2 0 1 45 1P111541c58dbfa8c1 0 2 0 1 45 1P11cf43fe9bb97e4c 0 4 1 1 38 1 40 1 41 1P122fcc5efc7e4648 0 2 2 1 28 1P12668f52182e0304 0 2 0 1 48 1P127dd15f3c47cb28 0 2 3 1 29 1P128351185914608f 0 2 3 1 27 1P129a019c6efc4b6d 0 2 2 1 28 1P129f5461312a5434 0 2 3 1 29 1P12f2a4851bf3be0e 0 2 0 1 49 1P132c449b766424d5 0 2 2 1 28 1P133299e1dbc9d14e 0 2 0 1 51 1P13440e4b9f3f7f4d 0 2 0 1 24 1P134b48877aa0b544 0 4 1 1 40 1 44 1 45 1P135babf97d4bd176 0 2 0 1 45 1P13f46be357d1c213 0 3 1 1 44 1 46 1P1402c7cfabf3ac89 0 2 3 1 27 1P141a655a04fbebe6 0 2 0 1 47 1P1451d6067a2c1764 0 2 2 1 28 1P146e15d3fa70b627 0 2 2 1 26 1P14a449f65b8aae79 0 2 0 1 43 1P14a6ba6348125cf6 0 3 1 1 44 1 46 1P14d7eed6d97e2fd1 0 2 0 1 47 1P150f6de2abd65398 0 2 2 1 26 1P1540f5e23f6f6a93 2 40 0 2 0 1 1 1 0 3 0 1 2 1 45 1P15681093021abcbf 0 2 0 1 42 1P15cafb2ec3154584 0 4 1 1 40 1 44 1 45 1P15cb2ed2ff068c0f 0 2 0 1 43 1P15e66dd7fddde37a 0 2 2 1 26 1P15fe5df067009636 0 2 0 1 43 1P1632ba1ff5a19d33 0 4 1 1 38 1 40 1 41 1P166e7c5d2c724a31 2 39 0 2 0 1 1 1 0 3 0 1 2 1 41 1P1684b3f2a9733e47 2 42 0 2 0 1 2 1 0 3 0 1 1 1 43 1P16c29ca186a8185b 0 2 0 1 43 1P16cfb659313c34c5 0 4 0 1 40 1 42 1 43 1P171e0b0a8fb8fd76 0 2 2 1 28 1P173be51fc344e522 0 2 0 1 43 1P1776361a69ba633b 0 2 3 1 29 1P17a94b4abf3a5c6d 0 5 0 1 2 1 43 1 47 1 48 1P17b337e68d778d06 0 2 0 1 42 1P17cf91c80de8f9f3 0 2 0 1 45 1P17e2526cc49dfb8c 0 2 0 1 1 1P17e42adaeeba5264 0 2 1 1 45 1P185583aee7d734b0 0 2 2 1 26 1P188a158e64b298db 0 2 2 1 28 1P18977956c6840cf1 0 2 3 1 29 1P18cf209e153140e0 0 2 0 1 39 1P1908681c718c8541 0 2 0 1 39 1P1973357e32cf91db 2 46 0 2 0 1 1 1 0 3 0 1 2 1 45 1P197a2baf4da3d663 0 2 0 1 47 1P198221a7327e9776 0 2 2 1 28 1P19a208dd9031e9bc 0 2 3 1 27 1P19b7c4d4087cf675 0 2 2 1 26 1P19c34fe81f2308b5 0 3 0 1 50 1 51 1P19d33b70118487fd 0 2 2 1 26 1P19e43431a661be8d 0 2 3 1 29 1P19ff7fc52b78b273 0 4 1 1 38 1 40 1 41 1P1a465cd55a0eebd0 0 2 2 1 26 1P1a7ad02c09693b2d 0 2 0 1 51 1P1a8504da64c2e7fb 0 2 0 1 39 1P1a9ea5ac7019b58c 0 2 3 1 29 1P1ab5db45ecd6b4c2 0 2 3 1 27 1P1b0069570f178a04 0 4 0 1 43 1 47 1 48 1P1b1a8365cc4096a9 2 42 0 2 0 1 2 1 0 3 0 1 1 1 43 1P1b7d5a63545d92cd 0 2 3 1 27 1P1b8265ca84a47635 2 42 0 2 0 1 2 1 0 3 0 1 1 1 43 1P1bb906624c712afb 0 2 0 1 47 1P1bc1c336af8b7691 0 2 2 1 28 1P1c12d4597dbceb1f 0 2 3 1 29 1P1c8025a63624881d 0 2 3 1 29 1P1c86da532daa580e 0 2 0 1 44 1P1cdb8ecb90afa77d 0 2 2 1 28 1P1cff527ebca0561d 0 2 2 1 26 1P1d58d46ff3ab2e1f 0 2 0 1 43 1P1da5c261ba40b98d 0 2 2 1 28 1P1dcb50731d1aa8e8 0 2 3 1 29 1P1e72b50212d6c6d2 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P1f1c52726d2d82dc 0 3 1 1 44 1 46 1P1f4225fd5b6e4c4d 0 2 3 1 27 1P1f908fc9d48f4287 0 2 3 1 29 1P1f9e05f605cdcec1 0 2 0 1 42 1P1fd2e075f9326e97 0 2 3 1 29 1P1feff1cc98509f16 0 2 2 1 28 1P203a0b212dbd0cef 0 2 3 1 29 1P20801f9880acdbf4 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P20872ce65db5885c 0 2 0 1 47 1P208bc8d22bd425f3 0 2 0 1 39 1P2152adac3e926017 0 2 2 1 26 1P218406183a8444d1 0 2 0 1 47 1P21b86c0f46b8784c 0 2 3 1 27 1P21ce41733891b974 0 3 1 1 44 1 46 1P22046cbc0fe6abcb 0 2 2 1 26 1P220b124cd4e5d62c 0 4 1 1 40 1 44 1 45 1P2212a2a9e66d7af4 0 2 2 1 28 1P224165cb7d4ebf92 0 2 0 1 48 1P2249e6ff9ee9d9a5 0 2 3 1 29 1P22b6f6cf84d5efca 0 4 1 1 40 1 44 1 45 1P2306d3b094f365de 0 2 3 1 27 1P23209d00d0afc2d0 0 2 2 1 28 1P233f00e52c54ae14 0 2 2 1 28 1P23d9df7365548416 0 3 0 1 50 1 52 1P242274ef67d56477 0 2 0 1 47 1P2427ca8d0156830c 0 2 0 1 42 1P243ab95b577e40e9 0 2 0 1 1 1P243dd2eec8319879 0 2 3 1 29 1P248db571cc9e91e8 0 4 1 1 40 1 44 1 45 1P24fe8103f6ac491e 0 4 0 1 43 1 47 1 48 1P2542d587d1ae00cc 0 2 2 1 28 1P25aca74e1b0a36bb 0 2 3 1 29 1P25c38c4da15dba47 0 2 0 1 39 1P260410e1251f536e 0 2 0 1 39 1P261817c242ef95dc 0 2 0 1 42 1P262494dce16b08ce 0 2 3 1 29 1P26340ead41512f1a 0 2 3 1 27 1P26be963a88618f87 0 2 2 1 26 1P26dca3318f120a08 0 2 0 1 45 1P2749c389a8b8c55f 2 40 0 2 0 1 1 1 0 3 0 1 2 1 45 1P2759c643ef15c7aa 0 2 0 1 47 1P275faa0b298354d7 0 2 2 1 28 1P278a67fb69338e21 0 4 1 1 40 1 44 1 45 1P278e13f482f205f9 0 4 1 1 38 1 40 1 41 1P279a517a091d7878 0 2 3 1 27 1P2821e42e2eab9ea4 0 4 1 1 40 1 44 1 45 1P28239d825a78037e 2 39 0 2 0 1 1 1 0 3 0 1 2 1 41 1P284004e686df5715 2 40 0 2 0 1 1 1 0 3 0 1 2 1 45 1P28e055858e405baa 0 4 0 1 40 1 42 1 43 1P297c41bb2b0ac155 0 2 0 1 24 1P29e5646169d138e6 0 4 1 1 40 1 44 1 45 1P2a34e1bd69be1098 0 2 2 1 26 1P2a636d153b29bb70 0 2 0 1 47 1P2a6fc2d66110515e 0 2 3 1 27 1P2a958044fa3d1536 0 2 0 1 43 1P2b2229f0ef7ba1f5 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P2b4fed55d2913245 0 4 1 1 38 1 40 1 41 1P2c326224aaec2174 0 2 0 1 42 1P2c897a24e002e387 0 4 0 1 43 1 47 1 48 1P2c98d0340296dac4 0 2 0 1 43 1P2ca20fe6268cadff 0 2 2 1 26 1P2d0b0ec930e8ea89 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P2d0d0f2b67615a34 0 2 0 1 39 1P2d4e460b6cbf9b0d 0 3 0 1 50 1 52 1P2d9268b3839fd865 2 46 0 2 0 1 1 1 0 3 0 1 2 1 45 1P2dc1232854743bdb 0 2 0 1 45 1P2de85190c9749fa0 2 39 0 2 0 1 1 1 0 3 0 1 2 1 41 1P2ecc7e0d40dee71d 2 40 0 2 0 1 1 1 0 3 0 1 2 1 45 1P2ecfd3de932d01ec 0 2 0 1 49 1P2edd1904e63fc9df 0 4 0 1 40 1 42 1 43 1P2f2917a61672cd50 0 2 3 1 27 1P2f2c3ed67b81f5d6 0 2 2 1 28 1P2fc6a33fef04f3df 2 44 0 2 0 1 2 1 0 3 0 1 1 1 48 1P30213d81da443141 0 2 0 1 51 1P30f632c2439e825a 0 3 1 1 44 1 46 1P3120240d9962217b 0 2 3 1 29 1P314fbd9ffad3251a 2 39 0 2 0 1 1 1 0 3 0 1 2 1 41 1P31dd0edb148fdae0 0 2 3 1 29 1P31e0689b5b011914 0 2 2 1 26 1P32c916834f5810e3 0 2 0 1 42 1P32cfe2636dc231f9 0 2 2 1 28 1P3318ddedac6b81e3 0 2 2 1 28 1P33217ecac1467b44 0 2 0 1 47 1P332a500a9e6f28e3 0 2 0 1 39 1P3337e190748a12db 0 2 3 1 29 1P3340aac922e52b50 0 2 3 1 29 1P33a3389fc292caa2 0 2 0 1 42 1P33df4873bf0d36b5 0 4 1 1 40 1 44 1 45 1P33e436a42bf8943a 0 2 0 1 48 1P340ff745e0ee2f60 0 2 0 1 39 1P34344e00d76d2b35 0 2 0 1 53 1P345034c7351e436e 0 2 0 1 42 1P34bc6cd536751ab8 0 2 2 1 26 1P35267d0c0aeab083 0 4 1 1 38 1 40 1 41 1P35de49dd65784d6f 0 2 0 1 43 1P360df9860f4c0eb6 0 2 0 1 43 1P360f94d855ab64db 0 2 2 1 26 1P3619d2e745c8bb7f 0 2 3 1 29 1P364aa76d0a3aab69 0 4 0 1 43 1 47 1 48 1P3679838706a73565 0 4 1 1 38 1 40 1 41 1P36e66b86dbd5e234 0 2 3 1 29 1P37131de24e3c1dba 0 2 3 1 27 1P373a2e4e6affc57c 0 2 1 1 45 1P382d16188274e3cf 0 2 3 1 29 1P38552738c4ec4d10 0 2 0 1 45 1P38edc4020b9243a2 0 2 0 1 26 1P396428bb65185504 0 2 3 1 27 1P399a7f3d668430f4 0 2 0 1 44 1P39cb73f77c1be4a2 0 2 0 1 39 1P39f06d11394d0eba 0 2 3 1 27 1P3a1846796d30eeca 0 2 0 1 39 1P3a1a4d9f38e1ef12 0 4 1 1 38 1 40 1 41 1P3a2f0b28131881db 0 2 2 1 28 1P3a4e227ffdaf09d7 0 2 3 1 29 1P3a8ff8fd044abc9d 0 2 0 1 47 1P3aa113a236d8efcb 0 2 0 1 43 1P3abaf8f55e85de60 0 2 3 1 29 1P3ae94533e27bb0e5 0 2 2 1 26 1P3b31a2227c6b9b3e 0 3 1 1 44 1 46 1P3b3452771bfef17e 0 2 0 1 47 1P3b8ab762524f5686 0 2 0 1 43 1P3b9fc97e9ec300a5 0 2 2 1 28 1P3bdcc44f4917276f 0 2 0 1 42 1P3be857787fb3d2cc 0 2 0 1 39 1P3c3274b0b6a31c1a 0 2 2 1 26 1P3c34985acbd4f8a2 0 2 0 1 47 1P3c3b7be10ff3b99f 0 2 2 1 28 1P3c9788e6677fc002 0 2 3 1 29 1P3ca9f476ce2ba8f7 0 2 3 1 27 1P3cc2dd03bf502ba5 0 2 0 1 47 1P3cc34b6bff472229 0 2 3 1 29 1P3cc7d773ca6e333c 0 2 2 1 28 1P3cd0f4830f5ce85a 0 2 0 1 43 1P3cf0c4c278b2a83b 0 2 2 1 26 1P3d054887f5de1584 0 4 1 1 38 1 40 1 41 1P3d15f64c816a2ea8 0 2 3 1 29 1P3d38f408e68935f7 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P3d9a2c88f5026ee3 0 2 3 1 29 1P3ddc0d19732d141a 0 2 3 1 29 1P3e0f603daa3b49da 0 3 1 1 44 1 46 1P3e900ee1aef59145 0 4 0 1 40 1 42 1 43 1P3f431e2a5e0ac66d 0 2 2 1 28 1P3f772d3ade7e0b0b 0 2 2 1 26 1P3f94c604c81c7efc 0 4 0 1 43 1 47 1 48 1P3f9e5086edc94723 2 50 0 2 0 1 2 1 0 3 0 1 1 1 48 1P3ffb376cf70b4b28 2 42 0 2 0 1 2 1 0 3 0 1 1 1 43 1P3ffd9ad195cf6afd 0 3 0 1 49 1 50 1N003a38800eb817faN003c4a9d20636b3dN0057020787e095b3N019598905631f7efN01b391534169d551N01ef8726c1ed2f3cN0273cac1bdb13b58N02906a7b0a0bb3ccN02aa5546fa9d8c39N032b1a9461467828N0351b4209a6b8689N035948eaaa6945d0N0493e2cd46366badN050d1db395261c8aN0529854b4b3c49c8N055c77aa297f93e7N058136c32916b469N0590d4418a8fde91N0668c3e5445856fbN07a09e5ced3710abN07e761570939d9d5N082ad749c0c2dde8N0849159f84011364N08ad7123ef20ac7eN093b5970228ce761N0952499cfb02b349N096378d53bcec763N0a539fe47038f9e1N0ad572261803934eN0adcd080d0d4da1fN0add82a9fadd2487N0b96309e8e721c2bN0ba3760072f33183N0c2d5cf8761af266N0c7ca71133a66c35N0c8ab73eb49346e4N0ccc9a4ff515bef3N0d085b6afce83260N0d6b04d8c236f04fN0d78aa2e3f01f62aN0d819fc712d4b938N0dfc4c4ad8219f0bN0e7c2d90f69509dfN0ea0f0e8ff87147aN0f0ba75bf2de1642N0f8d5a4d4ad11eb4N0f8e63e0567498c3N0fa2fa9dc9e90382N0fe120f8fb15a8c1N104bd4318f83414cN10539b769b36cb98N10e52161754ac028N10e86e27386a2655N1136b00622afb642N119fc1de18672462N11d603b40aceabbeN11f176ec97f8a862N120f665114ccb606N1345f68d1f2586ddN1435cfaa60fd896fN1479477c612fe65fN156cc8e91e5c8f7fN159f202e14e2a300N161fc09e536173d5N16dc725ad4fce966N17b1edb0b6e1376cN18af4ed9876c5158N190042cae1bc47e5N194d8dc881bb8fe4N19743549db0d9567N1996e8e0ed1fac5eN19c571065f7d370bN1a3874cd0b2ad054N1aa25c5551c012f0N1b5e8219d8a08b38N1c2b8c4b1e453aabN1c3967b0908e54e7N1c675f9ffbcacf40N1c687b113af31828N1cf6026f4599460bN1d9eaa6b5d7a9eb9N1e01ac1ed7b00c84N1e5b2bafd68d6021N1e9cc85110cbb146N1eb14c5942d19156N1ecb2bedf01f554cN1efe195898314dcbN1f037d99baa5d828N1f6a185e633d9682N1f786d7c7fea6233N1fc96de7e875fe34N200c7a2552283f21N20103b538741434dN2051b4f1f4869bb2N20721c40a0f05ebeN20a7a65bec69af4bN20afa9c911fbc005N20ce187150a0960bN21527260d66af46bN216e432ebb7061efN2206ccb739bb77fbN2222996862ce2c44N22c5e07af21f1500N230815f2637b00e5N2312132b2d8fdf4bN23bd4029691b7d32N23d4ebd568fba1b7N23dd7dd8d916afc1N24a0f96879182a3eN251852ea89b74acaN25c51004c59071baN25cf644966859df5N261191e98bf97d90N262f5f23400bea6aN266b37f05a1629b6N27795ca63eeedfedN2785913c0d741ceeN27a8b1cef3eebe4cN27c1653499c681a4N28767fc14b2bc8acN2883eaa058686613N2921f918f6c4301eN297c7778f2b6fa26N29bfd432c1ba1c52N29da06a8a7da4aebN2a9fcbf4822b589dN2ad117417650b5feN2b84704047559008N2ba2abfefc6b1fc3N2bb7f7d236863339N2bc4b4927f5bdcb5N2c317ad857c53db0N2c5231d8dcdae6c1N2c68f15570a52f72N2cb671706e100f76N2ce40c59a87256d1N2dcedf044ed271adN2e7b6384d2d66edeN2eb50d7d6137d16dN2ebe5dc0dd9261adN2efbc933d62b28b8N2f288b1fa5db5f31N2f9c900f5ab2e4e7N2fc8bd317f42389dN2fec6527b9a2bdc2N3086b3bb54d2f5b5N3108735295de1481N320d16b3cf848333N32b494528da600e3N330ce52befca7d7fN3317665e61043c08N332f974d73d5a2d7N34328b8c8eb2ebdaN34a43ed6ba6a2b79N354ebe0e78562a94N357afe4028fc7315N360e3201a1b240abN3664e6fb9a1f6731N37a36daa5cf814c5N37c5a3d2e4da5cfbN394db03c35d996b6N39ea1a6250f0ca13N3b7c15f9482cc9f5N3c36c2f807c621e5N3c5e30969c6a22bfN3c75ba01738f9c62N3c909143278773a2N3c941cd205da7904N3ccb66cf535dd3edN3d7835aeaab2449fN3eaca391acb3d302N3f4538d4e0ee20edN3f5e31fdde1c146dN3fa17bc42d89be61N3fddd220888bfcf2"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition A_RECYCLE : Z := 0x49720.         (* [comment removed for export] *) (* [comment removed for export] *)

Section Drain.
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
  Definition qmutex_cells (cm rm : Z) : list cell := [C1 (Z_to_bv 8 cm); C1 (Z_to_bv 8 rm); C2 (Z_to_bv 64 0)].

  Definition drain_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (T STK len first last bytes glen gfirst glast gbytes lo : Z) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (m' : mem),
      munch ((lo, SP) :: (A_INSTANCE + 880, A_INSTANCE + 884) :: (A_INSTANCE + 888, A_INSTANCE + 920) :: (T + 80, T + 112)
             :: (if glen =? 0 then [] else [(glast, glast + 8)])) m0 m'   (* [comment removed for export] *)
      /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (A_INSTANCE + 888) (qc_cells (glen + len) (if glen =? 0 then first else gfirst) last (gbytes + bytes))
      /\ rw_cells asegs m' (T + 80) (qc_cells 0 0 0 0)
      /\ (glen <> 0 -> rw_cells asegs m' glast [C8 (Z_to_bv 64 first)])
      /\ stk asegs m' lo SP
      /\ ( (gbytes + bytes <= kQuarantineMax
            /\ rw_cells asegs m' (A_INSTANCE + 880) (qmutex_cells 0 0)
            /\ exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word),
                ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m' (seg_rom asegs))
        \/ (kQuarantineMax < gbytes + bytes
            /\ rw_cells asegs m' (A_INSTANCE + 880) (qmutex_cells 0 1)
            /\ exists (t0 t1 t2 a4 a5 a6 a7 : word),
                ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1
                             (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 kQuarantineMin) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 A_RECYCLE) fc None m' (seg_rom asegs)) ).

  (* [comment removed for export] *)
  Ltac leaf fin :=
    apply evtA_done; unfold drain_post, qc_cells, qmutex_cells, A_INSTANCE, A_RECYCLE, kQuarantineMax, kQuarantineMin;
    change (1074072 + 880) with 1074952; change (1074072 + 888) with 1074960; change (1074072 + 884) with 1074956; change (1074072 + 920) with 1074992;
    change (1074072 + 728) with 1074800; cbn [Z.eqb];
    try match goal with G : ?g <> 0 |- context [?g =? 0] => rewrite (proj2 (Z.eqb_neq g 0) G) end;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx;
      lx_ands;
        [ lx_munchx | assumption | assumption
        | match goal with K : rw_cells _ mx 1074960 (_ :: _ :: _ :: _ :: nil) |- _ => lx_rwx K end
        | match goal with K : rw_cells _ mx (_ + 80) _ |- _ => lx_rwx K end
        | first [ intros X; exfalso; exact (X eq_refl)
                | intros _; match goal with K : rw_cells _ mx ?a (C8 _ :: nil) |- rw_cells _ _ ?a' _ => constr_eq a a'; lx_rwx K end ]
        | assumption
        | fin mx ] end.
  Ltac fin_ret mx := left; split; [lx_arith| split; [match goal with K : rw_cells _ mx 1074952 _ |- _ => lx_rwx K end| do 11 eexists; lx_mseq]].
  Ltac fin_rec mx := right; split; [lx_arith| split;
    [ match goal with H : rw_cells _ mx 1074952 [C4 _] |- _ =>
        apply (rw_cells_reshape asegs mx 1074952 _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 0)]) in H; [exact H| cbn; tauto | bytes_eq] end
    | do 7 eexists; lx_mseq]].
  (* [comment removed for export] *)
  Ltac body :=
    (* [comment removed for export] *)
    lx_run (PLAN [0x495a4] [] 20%N);
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mx 1074952 _ |- _ => apply (rw_cells_reshape asegs mx 1074952 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end;
    zstep; rewrite (sx32_small 0) by (clear; lia);
    do 6 zstep;
    match goal with H : rw_cells _ ?mx 1074952 [C4 ?v] |- _ =>
      apply (rw_cells_reshape asegs mx 1074952 _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end;
    (* [comment removed for export] *)
    lx_run (PLAN [0x4966c; 0x49720] [] 60%N).
  Ltac dead_global := exfalso; match goal with K : (zlow 64 1074960 =? zlow 64 (?t + 80)) = true, T1 : Timg ?t, T2 : ?t + 4096 <= _ |- _ =>
    clear -K T1 T2; lx_bool_norm; unfold zlow in K; rewrite !Z.mod_small in K by lia; lia end.
  Ltac trylock lo :=
    (* [comment removed for export] *)
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      match goal with H : rw_cells _ mx 1074952 _ |- _ =>
        apply (rw_cells_reshape asegs mx 1074952 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | bytes_eq] end end;
    zstep; rewrite (sx32_small 0) by (clear; lia);
    do 9 zstep;
    (* [comment removed for export] *)
    lx_run (PLAN [0x49720] [] 20%N); lx_same; lx_stk_grow lo.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01K0@L10185232398.82 L10185232652.73 L10373701077.91 L10375797086.105L10520132705.84 L10520133090.91 L10522229097.105L10522229216.95 L11347017180.1  L11369369836.108L11369369836.87 L11369369836.94 L11369369836.98 L17370830481.108L17370830481.95 L17371178260.96 L17371178265.108L17495670838.7  L17771283109.91 L17771283238.84 L17773381166.105L17773381287.95 L1859783825.73  L1859784083.82  L20486103781.100L20486103781.111L20486103781.88 L20486103781.96 L25158854670.1  L2637103485.2   L31530343868.2  L32196183388.1  L32407777148.110L32407777148.96 L32785383721.108L33271108968.2  L3379728136.107 L3379728136.86  L3379728136.93  L3379728136.97  L3501778309.2   L35956561725.2  L37740865083.95 L37740865202.105L37742961209.91 L37742961594.84 L38204529748.2  L41587601925.1  L42548201415.110L42548201415.88 L42548201415.96 L42548201415.99 L42579855365.1  L434141041.110  L434141041.86   L434141041.95   L434141041.98   L43772006277.1  L46812718316.108L46812718316.87 L46812718316.94 L46812718316.98 L4979469039.91  L4979469164.84  L4981567076.105 L4981567213.95  L51578832762.4  L53051764561.0  L53506509622.7  L53519997194.95 L53519997315.105L53522095243.84 L53522095368.91 L54071965718.4  L57634915959.95 L57634916094.105L57637012085.91 L57637012470.84 L58541537970.91 L58541538097.84 L58543636025.105L58543636144.95 L59321099895.4  L59321099895.7  L62261865510.73 L62261865764.82 L63863625262.105L63863625383.95 L63865721509.91 L63865721638.84 L64260578181.1  00000F00\00]00^00c00h00m01201301G01[01o02C02U02g03903K03a03n04;04H04U04d05305M05g06A06[06_06`06a06b07@07^07l07m08;08I08W08e08f08g08l09109609;09<09=09a0:E0:i0;M0;N0;V0;^0;f0;n0;o0<C0<W0<k0=?0=L0=Y0=f0>30>>0>?0>@0>N0>\0>j0?80?;0?<0?=0?>0??0?@0?A0?B0?C0?O0?a0@70@M0@R0@W0@\0@a0@bS3hAR5bytes6gbytes3H14S3hAR5bytes6gbytes3H12FFS3hARS3hARS3hARS3hARFS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR5bytes6gbytesS3hAR5bytes6gbytesS3hAR5bytes6gbytesS3hAR5bytes6gbytesS3len4glen2LB3GLB4SUMBS3hAR2AL4IMG'S3hAR2AL4IMG'S3hAR2AL4IMG'S3hAR2AL4IMG'S3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR1T3TB12HB5Ha_st5Hl_stS3hAR1T3TB12HB5Ha_st5Hl_stS3hAR1T3TB12HB5Ha_st5Hl_stS3hAR1T3TB12HB5Ha_st5Hl_stS2SPFFFS3hAR5glast3GL02HB5Ha_st5Hl_stS3hAR5glast3GL02HB5Ha_st5Hl_stS3hAR3len4glenFS3hAR2HB5Ha_stS3hAR2HB5Ha_stS3hAR2HB5Ha_stS3hAR2HB5Ha_stFFS3hARS3hARS3hARS3hARFFS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stFS3hAR2HBS3hAR2HBS3hAR2HBS3hAR2HBFS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR2HB5Ha_st5Hl_stS3hAR2AL4IMG'S3hAR2AL4IMG'S3hAR2AL4IMG'S3hAR2AL4IMG'S1T3TB13TB2SSS3hAR2AL5ALWF'S3hAR2AL5ALWF'S3hAR2AL5ALWF'S3hAR2AL5ALWF'S1TFFFFFFFFS1T3TB14LXKTS4glen3GLB2G04LXKTS3hAR5bytes6gbytes3H13S3hAR5bytes6gbytes3H15S3hARS3hARS3hARS3hARF". (* [comment removed for export] *)
  Lemma drain_spec : forall
      (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (gnext : word)
      (SP T STK len first last bytes glen gfirst glast gbytes lo : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      Timg T -> T + 4096 <= 2^47 -> 0 <= STK < 2^64 ->
      1 <= len -> 0 <= glen -> glen + len < 2^63 -> 0 <= first < 2^64 -> 0 <= last < 2^64 -> 0 <= gfirst < 2^64 ->
      0 <= bytes -> 0 <= gbytes -> gbytes + bytes < 2^63 ->
      rw_cells asegs m (T + 80) (qc_cells len first last bytes) -> crange CS T 4096 ->
      rw_cells asegs m (A_INSTANCE + 880) (qmutex_cells 0 0) ->
      rw_cells asegs m (A_INSTANCE + 888) (qc_cells glen gfirst glast gbytes) ->
      ro_cells asegs m A_Q_MAX [C8 (Z_to_bv 64 kQuarantineMax); C8 (Z_to_bv 64 kQuarantineMin); C8 (Z_to_bv 64 kQuarantineCache)] ->
      (glen <> 0 -> rw_cells asegs m glast [C8 gnext] /\ crange CS glast 8 /\ 0x65f000 <= glast /\ glast + 8192 <= 2^47
                    /\ (T + 4096 <= glast \/ glast + 8192 <= T) /\ (SP <= glast \/ glast + 8192 <= lo)) ->
      stk asegs m lo SP -> ACEIL <= lo -> lo <= SP - 48 -> SP <= 2^62 -> (SP <= T \/ T + 4096 <= lo) ->
      crange CS lo (SP - lo) -> mem_inv asegs m ->
      evtA asegs AL CS (drain_post SP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 T STK len first last bytes glen gfirst glast gbytes lo F fc m)
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1
                (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_DRAIN) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gnext SP T STK len first last bytes glen gfirst glast gbytes lo F fc m
      TB1 TB2 STKB LB GLB SUMB FB LAB GFB BY0 GBY0 BYS QC TCS QMU QG QMX GLAST ST LOIMG SPL SPH SEP1 SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold qc_cells, qmutex_cells in *. unfold A_DRAIN, A_Q_MAX, A_INSTANCE, A_RECYCLE, kQuarantineMax, kQuarantineMin, kQuarantineCache in *.
    change (1074072 + 880) with 1074952 in *. change (1074072 + 888) with 1074960 in *. change (1074072 + 792) with 1074864 in *.
    change (1074072 + 728) with 1074800 in *. change (1074072 + 884) with 1074956 in *. change (1074072 + 920) with 1074992 in *.
    pose proof (wmono_refl asegs m) as WM. lx_aceil.
    destruct (Z.eq_dec glen 0) as [G0 | G0].
    { clear GLAST. subst glen. pose proof (munch_refl [(lo, SP); (1074952, 1074956); (1074960, 1074992); (T + 80, T + 112)] m) as MU.
      body. all: try dead_global. all: lx_deads.
      { leaf fin_ret. }
      { trylock lo. leaf fin_rec. } }
    destruct (GLAST G0) as (GL & GLCS & GL0 & GL1 & GSEP1 & GSEP2). clear GLAST.
    pose proof (munch_refl [(lo, SP); (1074952, 1074956); (1074960, 1074992); (T + 80, T + 112); (glast, glast + 8)] m) as MU.
    body. all: try dead_global. all: lx_deads.
    (* [comment removed for export] *)
    all: try (exfalso; match goal with K : (zlow 64 ?g =? zlow 64 0) = true, G : ?g <> 0, B : 0 <= ?g, S : ?g + ?l < 2 ^ 63, L : 1 <= ?l |- _ =>
      clear -K G B S L; lx_bool_norm; unfold zlow in K; rewrite !Z.mod_small in K by lia; lia end).
    { leaf fin_ret. }
    { trylock lo. leaf fin_rec. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Drain.

End ARUN_1.
