(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0075d48a6b16598b 0 3 0 1 24 1 36 1P01629ac6d25278f9 0 2 0 1 15 1P01a3813432b25b2c 0 2 0 1 23 1P02b008507a3a1879 0 2 0 1 5 1P02f4b1eaac15e2e5 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P03006c61682aa4e2 2 16 1 1 4 3 2 1 30 1 31 1 5 0 4 19 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P03d950d12a0ef5f1 0 2 0 1 1 1P0475d20c775e05f4 0 4 0 1 3 1 30 1 31 1P04b8fcd7900bc2f2 1 1 2 1 0 1 2 20 1 36 1P0501cde38adba0aa 0 2 0 1 27 1P053879fd1ccd47ac 0 2 0 1 23 1P055209c11fd8d453 0 2 0 1 3 1P0554d7dfa1b4e234 0 3 0 1 30 1 42 1P05eaf1c8435cb51b 0 2 0 1 24 1P061de3e17bd8663d 0 5 0 1 13 2 16 1 17 1 29 1P0634d33c73459622 0 2 0 1 19 1P063e5c8b209bba11 0 2 0 1 31 1P06615d65896951fa 0 2 0 1 30 1P06c007bba866bee0 1 1 4 3 0 1 29 1 32 1 4 2 4 30 4 31 4 33 16P06f5cea975fd8d53 0 2 0 1 2 1P077abfecf5507d28 0 2 0 1 1 1P07a3eddade9e78ad 2 37 1 1 4 3 1 1 51 1 52 1 5 0 4 41 4 50 4 53 4 54 16 1 1 4 3 2 1 50 1 53 1 4 0 4 51 4 52 4 54 16P0816a9c842276da0 0 2 0 1 2 1P0884abd16fb1a064 0 3 0 1 14 1 26 1P08e4b0c19d2348cf 0 2 0 1 3 1P09ae3f4a4e4f5eeb 0 2 0 1 31 1P0a5220f0a995144f 0 2 0 1 1 1P0a5c5edb8340597a 2 17 1 1 8 3 1 1 30 1 31 1 5 0 2 20 2 29 2 32 2 33 16 1 1 8 3 2 1 29 1 32 1 4 0 2 30 2 31 2 33 16P0a859a0ea8ae03a1 0 3 0 1 20 1 32 1P0a8d1fcdc34d4f8d 0 2 0 1 1 1P0aad0be95c668a6a 0 7 0 1 4 1 5 1 28 1 31 1 32 1 33 1P0bef3e3051f71a75 0 3 0 1 1 1 3 10P0c1f55cda7100025 0 2 0 1 2 1P0c3edcc3659cad8f 2 29 1 1 4 3 1 1 43 1 44 1 5 0 4 33 4 42 4 45 4 46 16 1 1 4 3 2 1 42 1 45 1 4 0 4 43 4 44 4 46 16P0c43364f650b7bf5 1 1 19807040627459279754006364160 1 0 1 2 40 1 42 1P0cb59c4fcc8055fd 0 2 0 1 23 1P0ce91b09e0da9215 0 3 0 1 22 1 34 1P0cf264a81cce19bd 0 2 0 1 28 1P0d07f3f5b7ca0add 0 2 0 1 2 1P0dde09c34c076d54 0 2 0 1 24 1P0e2a85e82caf158e 1 1 8 3 1 1 29 1 32 1 4 2 2 30 2 31 2 33 16P0eddb7336761f65b 0 2 0 1 37 1P0f86a7f552421bca 2 33 1 1 4 3 1 1 47 1 48 1 5 0 4 37 4 46 4 49 4 50 16 1 1 4 3 2 1 46 1 49 1 4 0 4 47 4 48 4 50 16P0f8aba1af9efcbe4 0 2 0 1 40 1P0fdd2ed171490380 0 2 0 1 19 1P100ec353bb3e5d7c 0 2 0 1 32 1P101b0a4f570582ae 0 3 0 1 12 1 24 1P10534d29c3533322 1 1 8 3 0 1 30 1 31 1 5 2 2 20 2 29 2 32 2 33 16P10c2bac047d40e07 0 2 0 1 38 1P112e0af1ac06a60c 0 2 0 1 19 2P11a652d9b44c4573 0 3 0 1 1 1 3 10P11c700fcc25358bc 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P11fcad92a5f95a0b 0 4 0 1 2 1 29 1 30 1P12293a5de321f5eb 0 2 0 1 1 1P126432be1ea64fb3 0 2 0 1 21 1P12970dabfd381772 0 2 0 1 5 1P12af7e589618d3c9 1 1 4951760156864819938501591040 1 0 1 2 43 1 45 1P12cb42deabc44225 0 2 0 1 1 1P12e7671ba7ef0672 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P133afc0d0139c844 2 16 1 1 4 3 2 1 30 1 31 1 5 0 4 19 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P13be697908b783dd 0 2 0 1 1 1P13d8ce9f1da5bfb5 0 2 0 1 2 1P140ac967f02685ab 0 2 0 1 1 1P145b4671b411fd6e 0 2 0 1 1 1P14df4ef2d79275ec 0 2 0 1 1 1P14f58d12756b0d47 0 2 0 1 35 1P152c04e3f8187820 0 2 0 1 2 1P154c30cba111b3d0 0 2 0 1 5 1P15587957e8b93d4a 0 2 0 1 36 1P162975c97898a95f 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P164cd0d24bdf7732 0 2 0 1 16 1P16a6a41679e70591 0 2 0 1 1 1P16bc43b1ce743b4c 0 7 0 1 4 1 5 1 28 1 31 1 32 1 33 1P16d991f3cd180baa 0 2 0 1 5 1P17235b16a32741fb 2 16 1 1 4 3 2 1 30 1 31 1 5 0 4 19 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P17389564f233e1b4 0 2 0 1 2 1P175d8e0c4d9a3009 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P178d354ded16fb8e 1 1 2 1 0 1 2 19 1 36 1P17a5e6aed0e06f55 2 16 1 1 4 3 2 1 30 1 31 1 5 0 4 19 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P17e544660afa59ae 0 2 0 1 19 2P17faeed8169422e3 0 3 0 1 2 1 4 10P189bcab85d7dedae 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P1907ad23dbeef0d2 0 2 0 1 5 1P192764e8dc7e800d 0 2 0 1 23 1P193a2897e786efc1 0 2 0 1 27 1P19bdd50b3be9aecd 0 3 0 1 1 1 22 1P19f1c8143598baf9 0 2 0 1 2 1P1a6ea8cd45fb8fc4 0 2 0 1 30 1P1ad48612a6ae15ea 0 2 0 1 24 1P1b14c5f7ecb3b75d 0 2 0 1 7 1P1b4b76ebcb6592a6 0 2 0 1 2 1P1c503090a29c071b 1 1 4 3 1 1 30 1 31 1 5 2 4 20 4 29 4 32 4 33 16P1c6fde75ef78ff15 0 5 1 1 3 1 21 1 30 1 31 1P1c99eca3df53c550 0 2 0 1 31 1P1d1755b1bef51e30 0 2 0 1 32 1P1d27a2f31b5ddcc1 0 2 0 1 17 1P1d45e77b78112094 1 1 2 1 0 1 2 19 1 36 1P1d627fe1d4da397c 0 3 0 1 18 1 30 1P1d898310e21a6686 0 2 0 1 2 1P1e0a8b01d975d6af 2 30 1 1 4 3 1 1 48 1 49 1 5 0 4 34 4 47 4 50 4 51 16 1 1 4 3 2 1 47 1 50 1 4 0 4 48 4 49 4 51 16P1e210720f3365495 0 2 0 1 6 1P1e94b26d15ff4034 0 2 0 1 41 1P1e99f342cbb132a9 0 2 0 1 2 1P1f9f0cfde8f09289 0 3 0 1 22 1 34 1P1fcfb3bbbd655f9f 0 2 0 1 1 1P20abdedfd9a1e1f8 0 4 0 1 6 1 8 1 36 1P20c7b872e19d6cf6 0 2 0 1 22 1P22460dd447cd38c8 1 1 8 3 1 1 30 1 31 1 4 2 2 29 2 32 2 33 16P224e0a77492f492c 0 2 0 1 27 1P2276de44f0e008cf 0 2 0 1 25 1P22980e473cb7a9c8 1 1 19807040627459279754006364160 1 0 1 2 40 1 42 1P22a21697360ee942 0 2 0 1 20 2P22cfcf6bf37d9089 0 2 0 1 22 1P233ec068589ae063 0 2 0 1 16 1P23dfd4111d7444aa 0 2 0 1 2 1P23e271cb6e6fa8b7 0 2 0 1 16 1P23e83158bb41e267 0 2 0 1 26 1P2420adc769318172 0 2 0 1 44 1P242bfb5062c48921 0 2 0 1 36 1P24c4d7dd66eb785b 2 21 1 1 4 3 1 1 35 1 36 1 5 0 4 25 4 34 4 37 4 38 16 1 1 4 3 2 1 34 1 37 1 4 0 4 35 4 36 4 38 16P2509ff9ae0573274 1 1 8 2 21 1 28 1 3 0 1 27 1 29 8P2525e976e5b946d3 0 2 0 1 13 1P255b3e5ff618fb02 0 2 0 1 36 1P269397f950935e7e 0 2 0 1 34 1P26d9aa533b0cfc11 0 2 0 1 15 1P26db67f12cb5f9ad 0 2 0 1 29 1P26e32544619629dc 2 25 1 1 4 3 1 1 39 1 40 1 5 0 4 29 4 38 4 41 4 42 16 1 1 4 3 2 1 38 1 41 1 4 0 4 39 4 40 4 42 16P26e5a36ed525bf80 2 21 1 1 8 3 1 1 36 1 37 1 5 0 2 24 2 35 2 38 2 39 16 1 1 8 3 2 1 35 1 38 1 4 0 2 36 2 37 2 39 16P274cd9efdebb06c4 0 5 0 1 17 1 20 1 21 1 23 1P2750f5b9326ee0d9 0 2 0 1 32 1P279d15003dea710c 0 2 0 1 24 1P279ec60e3ad222a9 0 3 0 1 26 1 38 1P27bc9db260fa65a4 2 16 1 1 4 3 2 1 30 1 31 1 5 0 4 19 4 29 4 32 4 33 16 1 1 4 3 1 1 29 1 32 1 4 0 4 30 4 31 4 33 16P27e6de5bc70567c8 1 1 18446744072678759465 1 0 1 2 43 1 45 1P2940d94925c146f5 0 2 0 1 43 1P294e9cd7b6e04682 0 2 0 1 2 1P2999a4317a356b91 0 2 0 1 26 1P29a5e24ed3201a5e 0 2 0 1 1 1P2a4f2d5dae94716b 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P2a9f7e46aaeda67d 0 2 0 1 2 1P2af0ecf25e875984 0 5 0 1 1 2 20 1 21 1 33 1P2b0a23e60b2725ce 0 4 0 1 16 1 25 1 26 1P2b2ef24183c73a64 0 3 0 1 18 1 30 1P2b36a7e797a01dd1 1 1 18446744072678759465 1 0 1 2 40 1 42 1P2b43bd469e731a0d 0 3 0 1 2 1 4 10P2c800a0190b5789c 0 2 0 1 37 1P2cda2deab7cda384 0 4 0 1 17 1 27 1 28 1P2cec1b6dc51abd86 0 3 0 1 7 1 35 1P2d0c537b2ebe61c7 0 5 1 1 2 1 20 1 29 1 30 1P2d4ec87b8b50e0a7 0 2 0 1 12 1P2d565b669766157e 0 3 0 1 16 1 28 1P2dceddd750e1c63c 0 3 0 1 16 1 28 1P2e22a6dcafde247c 0 2 0 1 30 1P2e415802376ecd5e 0 2 0 1 36 1P2fa2295b29afcf17 0 5 0 1 11 2 14 1 15 1 27 1P3043c50f28f6e964 0 2 0 1 2 1P309cc4cbf6bd0737 2 24 1 1 4 3 1 1 40 1 41 1 5 0 4 28 4 39 4 42 4 43 16 1 1 4 3 2 1 39 1 42 1 4 0 4 40 4 41 4 43 16P30bc8a66e670f42b 0 2 0 1 2 1P30d5fd248bd5d502 0 2 0 1 1 1P3156d6520acecf0e 0 2 0 1 31 1P318ec1ccb532776d 2 17 1 1 8 3 2 1 30 1 31 1 5 0 2 19 2 29 2 32 2 33 16 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P320b70edf59a8708 0 2 0 1 28 1P32441af960bfc8d0 0 2 0 1 1 1P324a5a908334cbbd 0 2 0 1 48 1P32914125d3f01b21 0 1 1 1P329c0ef9a6d807be 1 1 16 4 16 1 17 1 18 1 28 1 3 0 1 27 1 29 16P34e7ac653d007912 0 2 0 1 1 1P35b3682e11548240 0 3 0 1 24 1 36 1P35daffcc18b020f3 0 2 0 1 3 1P362f0dee8eb2c5f9 1 1 8 3 0 1 30 1 31 1 5 2 2 20 2 29 2 32 2 33 16P3731111d82b99a52 1 1 8 3 1 1 29 1 32 1 4 2 2 30 2 31 2 33 16P3734a9a48b7dd707 0 2 0 1 23 1P3739268efdd69790 0 2 0 1 37 1P375b927157ca2815 0 5 0 1 3 2 22 1 23 1 35 1P37e47a1024733c42 2 17 1 1 4 3 1 1 31 1 32 1 5 0 4 21 4 30 4 33 4 34 16 1 1 4 3 2 1 30 1 33 1 4 0 4 31 4 32 4 34 16P381d891fff54bc7a 0 4 0 1 2 1 31 1 32 1P386ff2a11f7dce7e 0 2 0 1 26 1P3879ec231cdb7cc9 0 3 0 1 28 1 40 1P393e99d79be19913 0 2 0 1 24 1P397b8f083f52ec31 0 2 0 1 3 1P3a2a5ba24327c4d0 0 2 0 1 15 1P3a4569923f398951 0 3 0 1 1 1 3 10P3a4bfdbadb1c6703 0 2 0 1 23 1P3a6a3fc77ba24c39 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P3a72d3c76db662c7 0 2 0 1 40 1P3adf8439b6b1d15e 0 3 0 1 2 1 4 10P3aff280e21f9aedc 1 1 4951760156864819938501591040 1 0 1 2 43 1 45 1P3bfb05859ba323ed 2 15 0 5 0 1 3 1 20 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P3c6a966331423b58 0 2 0 1 20 2P3ce538a5ff11e2b4 0 2 0 1 2 1P3da62381680a4013 1 1 2 1 0 1 2 20 1 36 1P3e4973e09600a9dd 0 2 0 1 3 1N002247d6a3e5201aN002da1ffc0126eb1N002fd42a7b10baa0N0067c7a4e7742284N008dd3ab13b3602bN00913052f772ae79N009f220941f2faabN00a5de0b2dff71d0N00a64174694ee29bN00b8eb129884a72aN00be4cc3cb93bae2N00d157c8323cc588N00e914cfe8987c1bN01092b52c48e175eN011487dc7396c6e0N0121f4dbc5833598N012c32055c5d7a21N01413420bf5eda13N0178517ddd663942N018cf9ff1fa882cbN019254dee3f54962N01a89ed552323884N01b43d2fcf0835f9N01b51b6d3e6005edN01e93724ff4b2eccN022533174106872bN02303c902b0d0174N0246e050f5cba8efN024a31e5c4bed4f0N026d254cbd163573N0278cd5dcb4c380fN02a310db636a28fbN02afbf5e117d966fN030ac5dc76f9eb5fN030d493862dde112N03134bbdc739b721N03417169b92d3ce8N03553e258b7fd342N03571f4ef0d5815dN03683abb36d4047fN036c2db21d69add4N03a709014ea3ebfbN03b35363a0774932N03d4ed1b914b1847N03e487f93004e3caN03e4ae84d6a74488N040976a2d5b4e561N042d02e66d98edb1N044698aa37c9cfa9N048d95475d2ca035N04b8f2fb6c27896aN04d9c576bc0f7906N04f8bd68ca385ef2N05154ca564069f7cN055ac9f35c34bacaN058f3993ee9df4e5N05a77dd0a7edf79aN05afc6befb5bee64N05b53ba08b52a08cN05e1c7704fdf8013N0607217cf7730180N063037399d621e7fN064ff18589ba1bd5N06641c629ccad199N067d9fdc34ed8767N06816b3505823264N0691e5a98a20c34cN06a5f81beffddd8eN06b567827d91645aN06be6d02d82f8038N072612bda163b83fN0745dffee15ae854N075c3481fc9d6e53N0787aed7d5bd03adN079ed351807b1683N07acfde3690515cfN07bc121356540d01N07d78c34ae081cbeN07dd2e3f67cbd082N07de9a11348150c7N07fac8d5f497f4a0N082c8fcc5fbb4509N083412b45f2cf7abN08354d84833836e5N08907921a61e1679N08a20225ccea69b1N08c344021f56cbbbN08f93df1628e8f76N0907581ea6daa53bN092b3d6c51967619N0937d50d8d810cd0N0962ea09e66b7fcbN098854754bef2cdcN09e8e86ba5f25ac5N0a1726c3d23179beN0a2c950a4f0cea9aN0a3e623df154ed76N0a528cba2aab52b7N0a6735c9db87a6bfN0a88610246c00eb4N0ac0bcbfc638e046N0ac4436475fa489eN0adf42f021a0bf15N0affdbe9d46ecd90N0b1f29490c9f45a2N0b5984ef1dbb5408N0b67ba14e062ecbbN0b84b69240d93a47N0b8d57eeb8b21a51N0ba96018e8244f2cN0bd82fa45f2e3ac4N0bf0260cdd83e6d2N0bf7216efdd2ed3bN0c0f522be83948b5N0c1736870a6a66ddN0c186bb4e944a735N0c19bdfafb9a7c10N0c206ec6ace163daN0c381e2e90cbda87N0c3ac0c27b5c65f0N0c426c0d2baff1e7N0c70a9fb6f557a9cN0ca5d5d0169276ecN0cb3cabeff80a5b8N0cbefd1a61391589N0cd14c8ee6879001N0d033839a96bb18bN0d10f35c7e4bae67N0d380d8ca7438430N0d3faa20a2869fb7N0d536c6c7f83de7aN0d653017ce17e5c2N0d655641462da76fN0d7256bcd21b016fN0d8f05088dbae8c9N0daccc5e86c30a4cN0df3d90bba8ff6beN0dfab3d8433d8ee7N0e28e6b329cf90f0N0e31c85903ada305N0e3d57780e7b1a98N0e42cd9a128c4051N0e53a8bab7ff3bbaN0e62c4bbb7bd0c93N0e96294732913a45N0ead0f0474644bd1N0f5809091ec42ee8N0f63b9ece1bdcb02N0f89ff40348ef004N0fa94d652dbda4d9N0fccb315ca5bae56N0fdc5d97dd014bc1N0fecc94d5ede1eb8N101ce1468fb29c2dN10421d9e0d6a647fN105f5c9dbb66c0f4N10681e9419e3d9d9N107f9aa2f843b966N1094187d7155d3a7N10a1d3a21321f0baN10b8758c8f3549d9N10bc41fd3374cd78N110ad2cbb4caf013N113ce1d6fdeaaa85N1186bb8cdfc5aed9N119a6bdb50187845N123f56ee619fcc2bN1250332fea891538N1272ed82607a73e2N12744c04bcd6f59bN12745bd329f6cd1cN12bb035d3cccfd68N12c37be2c22a9f83N12d78ee8ff871d72N12e2ad2954a53076N12eb4343469342a0N13289896337abdf0N133109b96e8b4004N135775158dad09d0N1377fab1df82a274N1378a84d95ea9415N139841aa0fa7fb36N13a6450df2ae1391N13ac53a4759711e1N13ac706a446a6dcbN13bb1665849f3073N1412fff0dedf13c9N141a39eb500a80d6N1420ddd2a2b1db2aN144690faa478b498N146388eefd15e1d7N1464d4b4315ce1f4N14653eb085844676N147149ef297af1f7N1471f17296ecfbe6N149739d0cff4506eN14c1f2fc9575013eN14c28b13c9a590fcN14f8c7d354b39e74N150262ae8ac7bc3dN150d9432a8c0a53dN151467e6376c03efN1528446529e9f1f6N15295ac2eb2ea3f4N1530b8c0c6e6b6d6N153eb91b55ea98e4N1558dc205474b0caN155aacaf4fc63a4fN155ce21b9a6a5d28N15789c40f7280ff8N15baf2b6bc4bd37eN15cc802704d38539N15f49d3940d156aeN1601422a5a55ba56N1613c75fc629a0f5N1614d150ef8aac54N163a853ab77d023eN1646df838cc689e3N1654439383c94d3aN1682c5ccafef40c3N16ad7de929219ce3N16c772d8a3a82adfN16d7d8ddcb871a79N16e00c6525ea135cN16e74d94adb142f9N1747f9e242017044N176e967a1e2edafeN17994e3e2bc367b2N17f22be7c6b10232N17fd4ca6dfa98bb2N18251ad46ceae405N183ff037c32735f3N184a35dfc75d1f04N184ecf68c3739eb1N18a22d3aa24c1519N18a5ea54e4de0606N18cd8afcd039e7feN18ff217f1f37362dN19018df5f60dc2b1N192a4060e5840a40N192ea923bdc13691N19548d221883becbN197117b2ef812811N19740cd3594a43e8N199b1fd3f1fff3c6N19ae86b3e2547729N1a039c8eeab27d0cN1a0df17c531fe82cN1a713f5069795521N1a72f1af78fa3f28N1a77bcc25904cc4cN1a8f525fd81ffccdN1a9b118bf3d96592N1a9e5565264fa76aN1ab3f7082b22b531N1acfc6121a82f992N1b3fc32139bef9fdN1b48395cb419b135N1b49d5b906cd04f8N1b50ba0fce771d43N1b73aa47b6a6903dN1b788be880329981N1b86c5d7d89ff031N1b8be7a93404f195N1ba4ee10a1dc6a8fN1bb14c139aee8cb3N1bd95529198ba520N1be0340636a77b14N1bec359d4a18fe97N1beed6441a86bed2N1c0a04172fcaf167N1c124a7e2fd383c7N1c1ac187f065f481N1c204b1dd6282367N1c2ca2b8fa4353e1N1c4a8acc603c04b3N1c572d04dcb9310fN1c60fe498996f304N1c8e3ecb58e2f85bN1c90a4acfc15d397N1cc20cf7335554b6N1cc9b814d2879868N1ce585e683230916N1d0fb3ada9e8b191N1d21e919d66f13fdN1d2a7f27e9952af5N1d3f7e8c6495738dN1d4a3816d11f70b9N1d66a72feeac7d4eN1d7343383ec34563N1db520535808fe00N1db568e7ae1d991bN1db980cab0f2e7abN1dd0603e377dc49bN1dd1244e2cd3b705N1dd8736bc5910a9cN1dd913dfb9faa9bbN1df1b77a5047239eN1e059d538b104debN1e87d44ea168caefN1eae0c089a802c51N1edbd79a2fff0e4aN1ee3e0eb084c082dN1ee480bf4f05f0fcN1f174cfddc9d5e88N1f1bb58c8b0841c7N1f40126c6adf13ceN1f4d822426fca0daN1f557f268f2df306N1f603b3cf7349dd8N1f63100aa61a6bccN1f71df04614bc9c3N1f9c95d15b758d23N1fc52d15951b5901N1fcccde86e852526N20008fd17052d8ddN200a020d47a8ba83N201e7b5cb39f107aN203f076da6b1c180N20426287c9bd68feN20442f949bbc9a04N2044fbd45ce753d8N2067766a81576603N2069ea631ef564d2N206a5f70b942f768N208c2a76990e2b99N208cfcfd56b7f908N20c9a41360aefa89N2144c35b6abb883eN214f4fe2ae733bf5N216dada55b9e778dN219571cd880899bfN219a04d754442a33N21a0376d5f672f1fN21e5980d3a1abed9N21f4409fb48ce9c4N21fd3f738841d034N21ff09a0cac2057aN220a462994734c40N222eee31221b9d1cN223b1e521040cef7N223f3842807a930eN225f1eacf803bba8N228d95b9902c1469N22a691709decaffbN22bb35a5041b940aN22f449a87901f0e8N233408263de6f24dN2343d009fee56bceN2356b9ab3c0ee966N23688099289ccb71N236d67737a0aba56N2374c0a3a9eaa085N23a111efe21ee530N23ed159706f49cc3N241736e3f52abf07N24308fc179c0d68dN2480789e2f94b8f9N24b7fcb78a944ec5N24cda416e9211164N25345b0e21b9c0cdN25364f8733d00980N2551d9b140d213beN25540adf73b6e570N255b6d5925d998aaN2560bfb249a6eebdN256c5860dd281bfcN256ecff95d6b0972N257542ccb18c3d69N258e790cfd913b29N25ad0e6ab356e6f0N25e4308c8daeebddN25eeee8f51ccbeb7N26054ad957ff9c0fN260c7a85086228abN260df4572d54d849N261018a7f90ccd04N2634865133307394N263fb66de69b749bN26472f71bc89592eN266cc1833494f60eN2674f64772884e27N2693107caffcf984N26a7e4ab0fb33526N26bea2fcff640e19N272f3cdaca8c9dd5N2730066e603562b3N27319b2745e4179bN277874efc8dc40b7N27b21a54c4dd0976N27bfa38b5acbab4bN27d6e218cd2ba9f4N27e63bdf59dd58aeN27e6960954f683b6N282a8ca081eb769aN28550722e884c5d3N2861e9d074e37942N289c403665084a43N289f55af3fee3678N28a32337de8606c6N28a751a958c72bdcN28af917700a40d2dN28bfc80364743633N28c0a8001f425a83N28cc6921bef5e766N2901612ac848bd65N2916eef257aa0ef7N2917dc6e4fb9c361N2923acf9d19102adN2930d821fa11ecb0N2938a964b668b16eN293d8b11b78d3d46N29b4e9309e482d7cN29bd6019153da1a8N29c1f4ea93a4a2e9N29eab272aebcb39aN2a788faedf3ad610N2a850a4b04b4f5e2N2a9edf0ed356eb82N2ac3a62be077038aN2ae956c9ab243c20N2aeb83f4107039b6N2aed9e99d26e1ce1N2b823ae247a52117N2bb9baf03b6462aaN2be4c09c960441f0N2c07d350d0e8f3deN2c1561713cb95360N2c29f4e50e48967cN2c3092f278df0fa4N2c4449563e4139d3N2c6b1adcfb9f0be4N2ca0d4721560ad30N2cb76fc2f2306addN2cf357a7574616b4N2cf7161cdc45c80cN2cf7c5ef495eb69cN2d39481bba9fe6caN2d4d91953ad6b27bN2d571ea9dd4d7cb2N2d5f8a3b3c5d3b7dN2d6e65265c625a87N2d7fae23db555ff6N2da2da08f8e9253dN2dcf0e560d69a963N2df3acf8ba996fb9N2e1a97bcc48e9886N2e22a2a742798c35N2e35dbedf3145273N2e40ec691874c127N2e4ff90af93ee635N2e5b5286f0704078N2e68bd913a928335N2e7681293b497c41N2ecbc19ef7372863N2eeee21bef8756b7N2f01c8494b739c14N2f168c451417a97fN2f1e7c22b49c5a1dN2f528eb05b19c7b3N2f54454dfc2fa0d4N2f795057f207dd82N2f7f60ce8b10f1d6N2f8752ed41d72d27N2faaaec3dec9077cN2ffaab467a65ab35N3015ec07dd2fbef5N305b1d75422127b4N3061688b99460c47N30657e2e580afa43N3071bf944452672eN3073f5b297761a1aN309f0ddcaaae7eeaN30be440424d53452N30c423d638e77bd7N30dc63e921d113d3N30f94d32ac265f08N30fb0113937dcd59N3112bd59e0b75833N31168ecc1a0586a7N313264f839342891N31391dccb78566fdN313ba01b38f6e71eN316be7b7a26a10aeN316dd1f8cedef511N3195181f25d61c78N319dc9d6ec075e0aN31a2ffe2b11b638eN31c16ebc6f11cf0fN321e7395203a976dN3241ff660affa569N32637e8ed993a168N329ff87571fae298N32a02056423700adN32a243a09eaeeb3bN32acdd766c8ac30bN32b102f6ac7cc281N32c63b2446247ff1N32f5c5afb0a744b7N3315217a19c63bf9N331f58cebe0bf74eN3339bd228bbf86eeN333c0b8e4f9b6d8cN333f487892ed838eN334bcac1a4cd256bN335634af16280647N33960dda93179f85N339fe5f1dfbaa90aN33a7b6473878ea8aN33cc42440561740dN33f511260f636d53N3423389e86bb0c18N3463d4ca458be4d9N3487867ac7591a4bN34f14cb4e8275b9bN350a9ec6bc3253b4N353beb0ef8772861N354a901bfda6dd70N355df09486a83bc4N358c8f1926f8bf4fN35bbd92b4e3a043aN35f067df74b45a60N36017fef9d82619dN3612699c2d44288bN3635b282770ea31fN363c49b64efe4b87N364162978d06e58bN3654b10dd1a26d8aN365717da3b7c5895N365cee0cec682e22N36832b102e08e521N3689e489d3718fe5N36987856a5fff572N36b1a734b6976d9cN36b287078670dec0N36c102c2e039dc73N36cfe1b854309954N36dbedc415792a92N36e78ec98ac3c927N3713b767eb247aa6N371f071e266983bfN375dae4e0f52161bN37610e44cec1d062N3769d067943b7b8fN37701c8a0fca173dN3782f783ae661c4aN378433f1a17eda0bN37aab30cdcb95669N37afd4897d6bf401N37b12f4e855310c3N37cf9f1837469107N37e0c8a7a7432152N37e4a2c8e9cffc48N37ec20f07a553137N37f4590d1cdf073dN37f50595efcb0511N38116d961ab72868N384a3566d8608ec3N387f967131b11f68N38917b7c2efc8c67N38bddebd69f0c13cN38c95c74d4aaf88eN38ebac9d7ab61be5N38f2764f3d08bf5dN391a2fbac59bcb28N392581391b3e2615N3932ccc47a43e2cbN3963bcb87c5fe186N398426b388e36768N399015927316f1d5N3992204b606acdeeN3999ff4639822d3fN39a74b746fb38d12N39af3438df211a79N3a039823a0f75f3eN3a2cf7a61f7119ecN3a3bf3152d24cbcfN3a3c7d6ee1ae428eN3a4d4e8585d98e8dN3a5a325927b2b292N3a5c2f6dfeba4505N3a7d5422a09be321N3a8c8f3ce699be9bN3ab0e569e46f8991N3abdebd70413f18eN3acc78a2994aa0d1N3afc2978408c0259N3b02c4cd4311f153N3b0c647799093093N3b160c0eddd912bbN3b25336aadba17ebN3b5a70b09df7d334N3b5b735a9908a6a7N3b5f0b72816e3c64N3b7e1ee7ca8a56bfN3b92af715ed709efN3b9c0147e5a49781N3bae55667fa21dd8N3bbb4350b489751dN3c395196c51f15abN3c47adb04cb8be72N3c4bf9301a4aa5c3N3c58aac463ae18e0N3c5ca8402d6c3578N3c6ba104307f085eN3c72fa314725201aN3c95bdd328c2672fN3cb16a6b50846a90N3ce6831a5cc89721N3ce9ef92ee55e419N3cea006a548635a0N3cfb5f30c6860c16N3d174f76f57170acN3d2538e2aa65e2c4N3d3d4f9d8b12ec29N3d56562a0ffb5217N3d875e5d45b290bbN3da087d399d0e1ccN3da7015e66906d16N3dafa3ed5ebbdefbN3db36caac92d9bebN3de269f1420c7e83N3df861c9cac54bf4N3e24aa4b89dbc2b5N3e8652a8c938f8b1N3ea10527b644885eN3ea62e3b88d3e371N3eab0936d80b12ecN3ece2389f1c57675N3ed5d1e76b220042N3eff56858757e2d9N3f342fe28269638bN3f55d3a3462878acN3f57b7609d3325aeN3f641abaea117975N3f7cf417232d6774N3f97b6badb77fe20N3fb3b7a52d14ea79N3fc5b5f85469c9abN3fca812e03f78edeN3fdd25b11516c086"%lxh.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_X509_GET_TIME : Z := 0x28008.
Notation X509_GET_TIME_STACK := 48 (only parsing).

Definition time_cells (y mo d h mi s : word) : list cell := [C4 y; C4 mo; C4 d; C4 h; C4 mi; C4 s].

Definition x509_get_time_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP TM P END lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r p' : Z) (y mo d h mi s : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(PP, PP + 8); (TM, TM + 24); (bv_unsigned sp - X509_GET_TIME_STACK, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 r /\ (-0x3000 < r <= 0)
    /\ rw_cells segs m' PP [C8 (Z_to_bv 64 p')]
    /\ rw_cells segs m' TM (time_cells y mo d h mi s)
    /\ stk segs m' lo (bv_unsigned sp)
    /\ P <= p' <= END.

Definition x509_get_time_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP TM P END BUF lo : Z) (bs : list byte) (y0 mo0 d0 h0 mi0 s0' : word),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m TM (time_cells y0 mo0 d0 h0 mi0 s0') ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= TM \/ TM + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (TM + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= TM) ->
  PP mod 8 = 0 -> TM mod 4 = 0 -> 0 < PP -> 0 < TM -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_TIME_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (TM + 24 <= lo \/ bv_unsigned sp <= TM) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 TM ->
  evt segs (x509_get_time_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP TM P END lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Walk.
  Context {L : heap_layout}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (PP TM P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= TM \/ TM + 24 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : TM + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= TM.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : TM mod 4 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < TM.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 48.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : TM + 24 <= lo \/ bv_unsigned sp <= TM.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis PPB : PP + 8 <= 2^64.
  Hypothesis TMB : TM + 24 <= 2^64.

  Notation W := [(PP, PP + 8); (TM, TM + 24); (bv_unsigned sp - 48, bv_unsigned sp)].
  Notation POST := (x509_get_time_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP TM P END lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation FRAME mm lw := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 lw; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Lemma exit_walk : forall (a0w : word) (r p' : Z) (lw y mo d h mi s : word)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) mm,
    a0w = Z_to_bv 64 r -> -0x3000 < r <= 0 -> P <= p' <= END ->
    FRAME mm lw -> stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p')] -> rw_cells usegs mm TM (time_cells y mo d h mi s) ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 a0w x11 x12 x13 x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28204) fc None mm (seg_rom usegs)).
  Proof.
  intros a0w r p' lw y mo d h mi s x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 mm -> Hr Hp FR ST HPP HTM MI MU WM.
  lxp_run (PLAN [0x1e4e4; 0x28008; 0x28070; 0x280d0; 0x28234; 0x283b0; 0x283e8] [] 250%N).
  lxp_ret.
Qed.

  (* [comment removed for export] *)
  Ltac go_exit := eapply exit_walk; [ fin_goal | | | eassumption .. ]; plia.

  (* [comment removed for export] *)
  Lemma days_walk : forall (p' : Z) (lw y mo d h mi s : word)
      (x1 x5 x6 x7 x8 x9 x10 x16 x17 x18 x19 x28 x29 x30 x31 vmd vday vyear vhour vmin vsec vlow : word) mm,
    P <= p' <= END ->
    FRAME mm lw -> stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p')] -> rw_cells usegs mm TM (time_cells y mo d h mi s) ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 x10 vmd vsec vyear vlow vday vhour vmin x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x283e8) fc None mm (seg_rom usegs)).
  Proof.
  intros p' lw y mo d h mi s x1 x5 x6 x7 x8 x9 x10 x16 x17 x18 x19 x28 x29 x30 x31 vmd vday vyear vhour vmin vsec vlow mm Hp FR ST HPP HTM MI MU WM.
  lxp_run (PLAN [0x1e4e4; 0x28008; 0x28070; 0x28204; 0x280d0; 0x28234; 0x283b0] [] 250%N).
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Lemma valid_walk : forall (p' : Z) (lw y mo d h mi s : word)
      (x1 x6 x8 x9 x10 x28 x16 x17 x18 x19 x29 x30 x31 vmon vday vyear vhour vmin vsec vlow : word) mm,
    P <= p' <= END ->
    FRAME mm lw -> stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p')] -> rw_cells usegs mm TM (time_cells y mo d h mi s) ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp (Z_to_bv 64 12) x6 (Z_to_bv 64 (-9)) x8 x9 x10 vsec vyear vlow vday vmon vhour vmin x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x283b0) fc None mm (seg_rom usegs)).
  Proof.
  intros p' lw y mo d h mi s x1 x6 x8 x9 x10 x28 x16 x17 x18 x19 x29 x30 x31 vmon vday vyear vhour vmin vsec vlow mm Hp FR ST HPP HTM MI MU WM.
  lxp_run (PLAN [0x1e4e4; 0x28008; 0x28070; 0x28204; 0x280d0; 0x28234; 0x283e8] [] 250%N).
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply days_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply days_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply days_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply days_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply days_walk.  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Ltac hide1 e := let w := fresh "w" in let E := fresh "Ew" in remember (Z_to_bv 64 e) as w eqn:E; clear E.
  Ltac hide_arith :=
    repeat match goal with
    | |- context [Z_to_bv 64 (Z.lor ?a ?b)] => hide1 (Z.lor a b)
    | |- context [Z_to_bv 64 (Z.land ?a ?b + ?c)] => hide1 (Z.land a b + c)
    | |- context [Z_to_bv 64 ((Z.land ?a ?b + ?c) mod ?n)] => hide1 ((Z.land a b + c) mod n)
    | |- context [Z_to_bv 64 (bv_swrap ?k ?a)] => hide1 (bv_swrap k a)
    | |- context [Z_to_bv 64 (Z.land (Z.b2z ?a) ?b)] => hide1 (Z.land (Z.b2z a) b)
    | |- context [Z_to_bv 64 (?a * ?b + ?c)] => hide1 (a * b + c)
    | |- context [Z_to_bv 64 ((?a * ?b + ?c) mod ?n)] => hide1 ((a * b + c) mod n)
    | |- context [Z_to_bv 64 (?a * ?b)] => hide1 (a * b)
    | |- context [Z_to_bv 64 ((?a * ?b) mod ?n)] => hide1 ((a * b) mod n)
    | |- context [Z_to_bv 64 (Z.b2z ?a)] => hide1 (Z.b2z a)
    | |- context [Z_to_bv 64 ((bv_unsigned ?x + ?c) mod ?n)] => hide1 ((bv_unsigned x + c) mod n)
    | |- context [Z_to_bv 64 (Z.land (bv_unsigned ?x) 255 + ?c)] => hide1 (Z.land (bv_unsigned x) 255 + c)
    | |- context [Z_to_bv 64 ((Z.land (bv_unsigned ?x) 255 + ?c) mod ?n)] => hide1 ((Z.land (bv_unsigned x) 255 + c) mod n)
    | |- context [Z_to_bv 64 (Z.land (bv_unsigned ?x) 255)] => hide1 (Z.land (bv_unsigned x) 255)
    end.
  Ltac hz := zstep; hide_arith.

  Ltac rdb HBUF bs off :=
    let bb := fresh "bb" in let NB := fresh "NB" in let RD := fresh "RD" in
    get_byte bs off bb NB; read_at HBUF NB off RD; zstep; clear RD NB.

  (* [comment removed for export] *)
  Lemma tail_walk : forall (p' d : Z) (lw y mo dd h mi s : word)
      (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 vbase vlow : word) mm,
    P <= p' <= END -> BUF <= d -> d + 12 <= END ->
    FRAME mm lw -> stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p')] -> rw_cells usegs mm TM (time_cells y mo dd h mi s) ->
    bytes_at usegs mm BUF bs ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 TM) (Z_to_bv 64 d) vbase vlow x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28234) fc None mm (seg_rom usegs)).
  Proof.
  intros p' d lw y mo dd h mi s x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 vbase vlow mm Hp Hd1 Hd2 FR ST HPP HTM HBUF MI MU WM.
  unfold time_cells in HTM.
  lxp_run (PLAN [0x1e4e4; 0x28008; 0x28070; 0x28204; 0x280d0; 0x283b0; 0x283e8] [] 250%N).
  lxp_apply valid_walk.  (* [comment removed for export] *)
Qed.

  (* [comment removed for export] *)
  Lemma parse_walk : forall (q sv : Z) (lw Lw y mo dd h mi s : word)
      (x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word) mm,
    0 <= sv <= 1 -> P + 2 <= q -> 12 + 2 * sv <= bv_unsigned Lw -> q + bv_unsigned Lw <= END ->
    FRAME mm lw -> stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 q)] -> rw_cells usegs mm TM (time_cells y mo dd h mi s) ->
    bytes_at usegs mm BUF bs ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 sv) x9 (Z_to_bv 64 TM) (Z_to_bv 64 q) Lw (Z_to_bv 64 PP) x14 x15 x16 x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x280d0) fc None mm (seg_rom usegs)).
  Proof.
  intros q sv lw Lw y mo dd h mi s x1 x5 x6 x7 x9 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 mm Hsv Hq HL HE FR ST HPP HTM HBUF MI MU WM.
  pose proof (bv_unsigned_in_range 64 Lw) as LR.
  unfold bv_modulus in LR.
  cbn in LR.
  unfold time_cells in HTM.
  lxp_run (PLAN [0x1e4e4; 0x28008; 0x28070; 0x28204; 0x28234; 0x283b0; 0x283e8] [] 250%N).
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply tail_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply tail_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply tail_walk.  (* [comment removed for export] *)
  }
Qed.

  (* [comment removed for export] *)
  Lemma body_walk : forall (sv : Z) (j : list byte) (x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word)
      (y mo dd h mi s : word) mm,
    0 <= sv <= 1 -> P + 1 <= END ->
    rw_cells usegs mm (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -48) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 P)] -> rw_cells usegs mm TM (time_cells y mo dd h mi s) ->
    bytes_at usegs mm BUF bs ->
    mem_inv usegs mm -> munch W m mm -> wmono usegs m mm ->
    evt usegs POST
      (MS (mkR ra SPF gp tp x5 x6 x7 (Z_to_bv 64 sv) (Z_to_bv 64 (12 + 2 * sv - 10)) (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 TM) (Z_to_bv 64 P) x14 x15 x16 x17
              x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28070) fc None mm (seg_rom usegs)).
  Proof.
  intros sv j x5 x6 x7 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 y mo dd h mi s mm Hsv HP1 FR ST HPP HTM HBUF MI MU WM.
  unfold time_cells in HTM.
  (* [comment removed for export] *)
  pose proof (@sums2_ok _) as LXSUMS.
  lxp_run (PLANS [0x28008; 0x28204; 0x280d0; 0x28234; 0x283b0; 0x283e8] [] 250%N SUMS2).
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply parse_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply parse_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
Qed.
End Walk.

Lemma U_x509_get_time_spec {L : heap_layout} : x509_get_time_stmt usegs U_X509_GET_TIME.
Proof.
  unfold x509_get_time_stmt, U_X509_GET_TIME.
  intros until s0'.
  intros HPP HTM HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HTM) as TMB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ time_cells] in TMB.
  change (Z.of_nat 24) with 24 in TMB.
  pose proof (munch_refl [(PP, PP + 8); (TM, TM + 24); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold time_cells in HTM.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums2_ok _) as LXSUMS.
  lxp_run (PLANS [0x28070; 0x28204; 0x280d0; 0x28234; 0x283b0; 0x283e8] [] 250%N SUMS2).
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply exit_walk ] | solve [ eapply exit_walk with (bs := bs); lxp_apply_post ] | lxp_apply exit_walk ].
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply body_walk ] | solve [ eapply body_walk with (sv := 0); lxp_apply_post ] | lxp_apply body_walk ].  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply exit_walk ] | solve [ eapply exit_walk with (bs := bs); lxp_apply_post ] | lxp_apply exit_walk ].  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply body_walk ] | solve [ eapply body_walk with (sv := 1); lxp_apply_post ] | lxp_apply body_walk ].  (* [comment removed for export] *)
  }
Qed.
