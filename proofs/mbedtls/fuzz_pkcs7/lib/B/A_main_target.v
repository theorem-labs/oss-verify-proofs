(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape ZBridge HeapIface Asn1Aux Arr SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk MemcpyLib ShapeLaws SymDriveX LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_file.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw NodesA SymDriveA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rt_facts.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals ARestrict A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_unreg_globals A_tailkit_defs A_oomtail A_rip A_icpt_read A_main_tails.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_printf1 A_printfN0 A_printfN2 A_printfN4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import ATopContract ATopContract24 A_main_inv A_main_loop A_main_fin A_main_hdr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance Lib.PropExec.fx0.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0148c6925a3157ca 0 4 0 1 37 1 53 1 54 1P017b71ad4f04dc43 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0223da5a939c3d70 0 4 0 1 37 1 53 1 54 1P0395ddc68bba93ee 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P03ea7f723726c64b 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P04724fb0910cd326 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P0550ef69dc0a24a4 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P0602d725157441e3 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P06fb0d46221ca9da 0 4 1 16 41 16 54 16 55 16P07345f9bc0eae093 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P075d9349974d4075 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P0783ccec78a97dcd 0 4 0 1 37 1 53 1 54 1P0795bbd41ef179d4 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P0861eb33a7381fce 0 4 1 16 41 16 54 16 55 16P08980b210c7b9da1 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0905550a0b0d1d5e 0 4 1 16 41 16 54 16 55 16P090e63f0c7e8d4ff 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0926322f21969e2f 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P09b84c45a677ed9b 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0a0db28040d91673 0 4 0 1 37 1 53 1 54 1P0a925e1cd7ab7499 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P0a9c75ebd092f111 0 2 0 1 25 1P0b0e6b62448724d4 0 4 0 1 37 1 53 1 54 1P0b3f1cfd334ee98e 0 4 0 1 37 1 53 1 54 1P0bbf11999be8bc65 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0c044ff86e1f129e 0 4 0 1 37 1 53 1 54 1P0c6875fd41701689 0 4 0 1 37 1 53 1 54 1P0c91edaba8aba027 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0cb4c73764d3de13 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P0cb5852683810f3b 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0cbc740dde5d4156 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0cea4103ac6db05d 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P0d6b70d413344e7c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P0e1cc04fc2ac2367 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P0e50c9c61c1460bc 0 2 0 1 27 1P0e6de508556c6ca6 0 2 0 1 27 1P0f2205d5cf0f901b 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P0f91ce2acc677e49 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1022f1677bf8e0b1 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P104cdf7389cfe25a 0 4 0 1 37 1 53 1 54 1P10c92f84834cb33a 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P10cbe4dbbe5093d6 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P11342c588b01dec0 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P118e55c26bdc753f 0 2 0 1 27 1P11c2991271955eb1 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P11ed1387db5e48bb 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P11f301300dd580b4 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P11ff89206277e6a8 0 4 1 16 41 16 54 16 55 16P120ec71738df7818 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P12ba5fb981900262 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P12d9fb7bac4c1647 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P12e8720a8ad80000 0 2 0 1 26 1P132a0c071e99d24c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P146fcb016e6eafe3 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1482ba8b3f9f3d97 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P148cd916db35ea6d 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P149c1736ed642c9c 0 4 0 1 37 1 53 1 54 1P14c132928e443168 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1566789b6fe6e865 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P15ecf988cade27bc 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P15fda08c24a0435d 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P1689f1bc41ebbbac 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P16c43be790d05c65 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P172a9c4e38b1a261 0 4 0 1 37 1 53 1 54 1P1760c7ca1b170e17 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P190cef67125e5824 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1a516f25a92e0f2a 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1a56ff87289c6007 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1a78a0aa87374eb6 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1ad921b99dbd65d3 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1b230f96d0139f32 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1b2d7e5cc44f1a78 0 4 0 1 37 1 53 1 54 1P1b456c748f5e92c2 0 4 1 16 41 16 54 16 55 16P1b47d767d7810495 0 2 0 1 26 1P1b56eb22b3ceba3f 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1b6552cac16527e2 0 4 0 1 37 1 53 1 54 1P1bac70abce72a702 0 4 0 1 37 1 53 1 54 1P1bcff0ed702acb3d 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P1c2dc1a7f6ca617d 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1c499ecba068e2c5 0 4 0 1 37 1 53 1 54 1P1c6e3f603f1d4c63 1 1 16 2 0 1 54 1 3 41 1 55 1 56 16P1cb9413860702e0e 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1d6ff6f55f3aca75 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P1d7c42c16be0ecf3 0 4 0 1 37 1 53 1 54 1P1db5b08247b796c6 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1dfa1e115935462e 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P1e84958857db1fff 0 4 1 16 41 16 54 16 55 16P1f71d4126f44017b 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P1fdc94d71bca85f3 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P201e5e3651d3af04 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P20c5925513d0b31c 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2161d12d25e881dd 0 4 1 16 41 16 54 16 55 16P217145fd2c5a3e5c 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P21c2cb3ce4274fc7 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P226eb8cd64d7941c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2314983fa93c26f2 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2319819e49122d40 0 4 0 1 37 1 53 1 54 1P234653483b7bcbc8 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P241f1e92a6a90c0a 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P24386a4a0ed16e09 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P251d30bec4ef9c23 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P252a9d71f7fcc40b 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P25c8f4369f81cdd3 0 4 0 1 37 1 53 1 54 1P25d7a4bb51466e6a 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P26ea9eec8699c5b9 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P27005a8b2fbfdae6 0 4 0 1 37 1 53 1 54 1P27b82c8c2cec4aaa 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P27b9bdfab1b5a2ef 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P27dbdfda8e075379 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P27ecbc34b1e8bf6b 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2909c11f77f05ada 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2958adbcda5a9fe3 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2994a907b196081e 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P29b7ee7af58bf5c5 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2a431b61ba81b0bc 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2a9394d95ed6d997 1 1 16 2 0 1 54 1 3 41 1 55 1 56 16P2a94d443dc092a6d 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2ac92af5ec9b9f60 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2acb49f8072bb2e0 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2b0d9064083b185a 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2b6111ce0b07b67f 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2b7f7f09e71a8ff3 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2b8af0a312999254 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2ba3089ca73f8951 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2bb1e3fcd7fc20f8 1 1 16 2 0 1 54 1 3 41 1 55 1 56 16P2cadffef1800ba3a 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2cc331f1279e9d2f 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2d5053cde62cf08c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2de9a5396c44cb2b 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2df3a0a238231b6c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2e5302fd471b0534 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P2e687bfc2a7dc7f6 0 4 0 1 37 1 53 1 54 1P2eb7d60c86f9e925 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2eccd1dd334d0892 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P2f16c3456042e528 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P2ff4c8b63d0eb473 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P3056fbc99b46c5f7 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P31192a232d48e04a 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P313db0300afc42a7 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P31b53f2c4757be85 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P31cacd0f68e5d39d 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P322488d7695d5dbe 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P3281a972533297d0 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P32f4e81e5df22a98 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P3351aebf9d3b4ea7 0 4 0 1 37 1 53 1 54 1P346d55ac28cda125 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3567f2006e408ad8 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P3617adeade1f4266 0 4 0 1 37 1 53 1 54 1P368d6e62ca2519ed 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P36fed9347c97a6d6 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P37a7bb273949f2b5 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P37bf2c22194c0a18 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P38c346822effa01e 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P38f3c6f786962fbe 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P393033ea0d30a538 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3950de0b5293873a 0 4 1 16 41 16 54 16 55 16P399b78eb571b8412 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P3a04e16111fe6a9c 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3a1fe04c3767ab1c 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P3a56712671ef2097 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P3a60e56bc829077f 0 4 0 1 37 1 53 1 54 1P3bb98b083e5f6c7a 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P3bbc39ab4ea516b4 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3c23eee1e234b031 0 2 0 1 25 1P3c2ed8b0979a9fbe 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16P3c863835639c89af 0 4 0 16 41 16 54 16 55 16P3ce8ef112fe3e131 0 4 1 16 41 16 54 16 55 16P3d89bba16febc127 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3eae9a46f8ef9718 1 2 16 2 0 1 55 1 16 2 1 1 54 1 2 56 1 57 1P3ebf23709c7a0260 0 4 1 16 41 16 54 16 55 16P3fb97c849e94695a 1 1 16 2 1 1 54 1 3 41 1 55 1 56 16P3fe332fc8f428d03 1 1 16 2 0 1 53 1 3 40 1 54 1 55 16N007fc6537dcdf0a6N0096aeb9da43f018N00fa71abe33a01d6N0162d94d8a47fffbN016ce45b7318c8c5N01ff3df34ff2df75N0237ad9adf5e444bN029d97ac0f0fe0a4N02cc6497ebe980acN035f67f537922cc3N068bc2e5e9c405efN06f03bedeef3b5d3N07fbeda475b3fddeN0843f9be66e1d825N08812b40160a04c0N08be9949299e0cf8N090b43caa63ab84fN09f7b5a15ffa7f39N0b3200381008bf52N0c4fc54bff4390f7N0d0197403e1219f7N0d64a340c3c5f39aN0d85159f40d45be2N0dcf5b15150a7720N0e76974d894b0b71N1085d30e5a7b2f07N1201d3bf556e491eN13ad53de57fea9b9N149f5c9e41cfe589N152a6aef5faaaffcN153bdaea316a6609N156da341e1205dc1N1597e68b8adef1c1N15cc0b82d1dc24e3N17471ed627db77a9N192898c6de9d3845N19cb3056446669ebN19cf4c9bf7a6206dN1a0fd493349f59f9N1a79fcab555b66b2N1afb1d37d0029062N1ca51c9253bfdcf4N1cab5b13212be862N1d6f8191b31c1852N1db27f2202a9006aN1de5f13eb348a1d6N1e4344c51be833deN21b547c19e9c17c3N21d80874627a9993N23575dd8e6af8b48N23740c4addaa59daN23f1c1b22b3cc017N24cda1fb2f69ad20N262860670f50d367N2adaf23139fe4649N2b25b219d5b38ef4N2c03d49ec8178ce9N2cc67ca7d8e4bfb1N2cd89477688d1acdN2dbf94645cd14673N2ec4797eb652f885N2ed0457697e2d393N2f4b5ae2295a43adN2fa2a3d2a1f63ce5N2fb60c9f8afb9ba8N31eb1b45a5faa34fN32a0d443867bfdbcN3355b4a9caf8d4cfN378dd210505412aaN38e5b80e00cf66b7N39f33914f49b3716N3bfc5d9b8546b712N3c6e49a8434f49acN3cf644d715d1c229N3ee1873743c41685N3f1948ddf899f384"%lxh.
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
Ltac2 gd_tbl_A_main_target () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.B.A_main_inv.RS"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sxb"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Target.T1W"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Target.TRFA"; "RocqVerifyHarness.AgentSubmission.B.A_exit_front1.atexit_cells"; "Stdlib.ZArith.BinInt.Z.eqb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Target.T1_post"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Target.TMEM"; "Target.tcell"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.drv_static"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_shadow_ok"; "Target.incbA"; "Target.TREGS"; "RocqVerifyHarness.AgentSubmission.B.ATopContract.FUZZ_ENTRY"; "Target.RREGS"; "RocqVerifyHarness.AgentSubmission.B.A_main_hdr.status"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.B.A_main_fin.xmemA"; "Stdlib.Lists.List.In"; "Target.xmem_cells"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.file_clean"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.B.A_printf1.pf_mem"; "RocqVerifyHarness.AgentSubmission.B.A_printfN0.pn_memA"; "RocqVerifyHarness.AgentSubmission.B.A_printfN0.WP"; "RocqVerifyHarness.AgentSubmission.B.A_printfN2.pn_memA"; "RocqVerifyHarness.AgentSubmission.B.A_printfN2.WP"; "RocqVerifyHarness.AgentSubmission.B.A_printfN4.pn_memA"; "RocqVerifyHarness.AgentSubmission.B.A_printfN4.WP"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "RocqVerifyHarness.AgentSubmission.B.A_main_fin.xoutA"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.zero_lines"; "Corelib.Init.Nat.sub"; "Target.PLoopA.PLA"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_fp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.Spec.SInv.si_P"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "Target.out_state"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_main_hdr.FDS2"; "RocqVerifyHarness.AgentSubmission.B.A_main_fin.atx_clause"; "RocqVerifyHarness.AgentSubmission.B.A_main_loop.FRAMEA"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "Corelib.Init.Nat.add"; "Target.rsum"; "Target.fsum"; "Target.csum"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"].

#[local] Unset Lia Cache.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41415985948.2000001S". (* [comment removed for export] *)
Lemma land3_mod4 : forall b : Z, 0 <= b -> Z.land b 3 = b mod 4.
Proof. intros b Hb. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma zero_lines_app : forall a b, zero_lines (a + b) = zero_lines a ++ zero_lines b.
Proof. induction a as [|a IH]; intros b; [reflexivity|]. cbn [zero_lines Nat.add app]. rewrite IH. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L41773568036.2000006S1n2IH". (* [comment removed for export] *)
Lemma zero_lines_length : forall n, length (zero_lines n) = (2 * n)%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma status0 : forall b, status 0 b = 0.
Proof. intros b. unfold status. destruct (128 <=? bv_unsigned b); reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L56765667309.2L59308579027.400000600?S1a2HaS1a2Ha2H0". (* [comment removed for export] *)
Lemma ro_addr_geA : forall a : Z, 0x0f1000 <= a < 2^64 -> ro_addr asegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
  unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  repeat match goal with
  | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
  | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end.
  repeat match goal with |- context [if ?c then _ else _] =>
    let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
  reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14366366347.11L989271055.2   00000500;S1a1HS2V01H". (* [comment removed for export] *)
Lemma mem_inv_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))P,(4.$5.R2.)P,(6.R4.R3.R2.)P,Px,$7.P,(8.(9.=R1.)(:.R1.(;.+2.+40.)))P,(<.(=.R7.R2.))(>.$?.(10.$5.(11.R3.))$12.)(4.$5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' MI MU RO a b Hb. pose proof (u64_range a).
  destruct (outside_dec W (bv_unsigned a)) as [O|NO].
  - rewrite (MU a O) in Hb. exact (MI a b Hb).
  - rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply RO; [lia | exact NO].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Target.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Variable HID : artD asegs R HIA.
  Let AL := arl_AL R.
  Let L := arl_L R.
  #[local] Existing Instance L.   (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis HMALLOC : arl_malloc R = 0x69480.
  Hypothesis HFREE : arl_free R = 0x6947c.
  Hypothesis HMEMCPY : arl_memcpy_i R = 0x67db8.
  Hypothesis HTP : arl_tp R = 0x63ca90.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).

  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (path : list byte) (pathp : word) (fs0 : Fs) (fdata : list byte).
  Hypothesis Hfs : fs_lookup fs0 path = Some fdata.
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Variables (TOP STKHI V0 : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis HV0 : V0 + 2^29 <= AVOL_SPLIT.      (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L989271055.2000006S2V01H". (* [comment removed for export] *)
  Let HV0M : V0 + 2^29 <= AVOL_MAX.                (* [comment removed for export] *)
  Proof. pose proof HV0 as H. unfold AVOL_SPLIT, AVOL_MAX in *. clear - H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.   (* [comment removed for export] *)
  Hypothesis SICS : forall a, ~ outside (si_fp SI) a -> cstatic R a.
  Variable PHI : Z -> Z.
  Variable FPHI : Z.
  Hypothesis PHI_max : forall n, 0 <= n < 2^26 -> 0 <= PHI n <= FPHI.
  Hypothesis HVF : V0 + 2^28 + 4 * FPHI + 8 * AVOL_CALL <= AVOL_MAX.
  Variable FSTK : Z.
  Hypothesis FSTK_range : 0 <= FSTK <= 2^22.
  (* [comment removed for export] *)
  Variable FFR : Z -> Z.
  Variable FFFR : Z.
  Hypothesis FFR_max : forall n, 0 <= n < 2^26 -> 0 <= FFR n <= FFFR.
  Variable FR0 : Z.
  Hypothesis HFRF : FR0 + 4 * FFFR + 16 <= FR_MAX.
  Variable pad : list byte.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable C24f : Z.
  Hypothesis C24F_max : C24f <= 65536.
  Hypothesis FUZZ : fuzz_entry_stmtA24 asegs R HIA SI PHI FSTK C24f FFR FUZZ_ENTRY.

  Let msp : Z := bv_unsigned sp0 - 128.     (* [comment removed for export] *)
  Let tsp : Z := bv_unsigned sp0 - 208.     (* [comment removed for export] *)
  Let Ln : Z := Z.of_nat (length fdata).

  Ltac done_regs := apply evtA_done; unfold mkR; repeat (first [ reflexivity | lia | progress f_equal ]).
  Ltac solve_condb :=
    cbn [negb]; unfold bv_eqb, bv_ltu; rewrite ?bv_lts_zero_r; rewrite ?unsigned_lit by lia;
    repeat (first [ apply (proj2 (Bool.negb_true_iff _)) | apply (proj2 (Bool.negb_false_iff _)) ]);
    first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply Z.leb_le; lia | apply Z.leb_gt; lia ].
  Ltac ifc b :=
    lazymatch goal with
    | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_condb]
    end.

  Ltac reg_lit pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

  (* [comment removed for export] *)
  Ltac zlit := try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity);
               try replace (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity);
               try replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity);
               try replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).

  (* [comment removed for export] *)
  Definition TRFA (junk : list byte) (x7 : word) (b1 : byte) (plen PAY cl buf : Z) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(13.$14.(15.#8.O7.)(13.$14.(16.O6.)(13.$14.(16.(17.&40.$18.))(13.$14.(16.(19.O5.))(13.$14.(16.(17.&40.O4.))(13.$14.(16.(17.&40.O3.))(13.$14.(16.(17.&40.O2.))(13.$14.(16.(17.&40.O1.))(13.$14.(16.(17.&40.(1:.O1.+2.)))(13.$14.(16.(17.&40.+97254.))(1;.$14.)))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition CS0 (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(1<.(8.(9.(1=.VR,)O1.)(:.O1.(1>.(1?.&40.Vsp0,)+80.)))(1<.(8.(9.+63<050.O1.)(:.O1.+63<051.))(8.(9.+65<:>0.O1.)(:.O1.(1:.+65<:>0.+130.)))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L13954246606.80L35076877299.82L38219161452.66L59577380367.6400000_01K01n02DS1R3sp05fdata3msp3tsp2Ln2SL2SH2SK1c2Hc1q1r1H2H0S3sp05fdata3msp3tsp2Ln2SL1c1i2Hc2Hi1q1r1H2H0S3sp04SPlo5fdata3msp3tsp2Ln2SL1i2HiS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma cs0_ok : cs_ok AL CS0.
  Proof.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (EG & ELO & EHI & EGS).
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    unfold cs_ok, CS0, shadow_of. rewrite ASB, EG, EGS.
    split; [| split; [| split]].
    - intros c Hc. rewrite SK in Hc. Z.div_mod_to_equations. lia.
    - intros i Hi. rewrite SK. lia.
    - intros c i Hc Hi. rewrite SK in Hc. Z.div_mod_to_equations. lia.
    - lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition T1W : list ivl := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(13.(20.$7.$7.)(21.$7.$7.(1>.Vtsp,+30.)Vmsp,)(13.(20.$7.$7.)(21.$7.$7.+63<050.+63<051.)(13.(20.$7.$7.)(21.$7.$7.+65<:>8.+65<:><.)(13.(20.$7.$7.)(21.$7.$7.+65<;08.+65<;10.)(13.(20.$7.$7.)(21.$7.$7.+65<<08.+65<<10.)(1;.(20.$7.$7.)))))))")
(* [comment removed for export] *).
  Definition T1_post (t0 t1 t2 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (buf cl plen : Z) (b1 fv : byte) (jp jq jf : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Lms',$22.(23.(2.&40.)Lra',(2.&40.)(23.(2.&40.)La0',(2.&40.)(23.(2.&40.)La1',(2.&40.)(23.(2.&40.)La2',(2.&40.)(23.(2.&40.)La3',(2.&40.)(23.(0.(2.&8.))Ljunk,(0.(2.&8.))(23.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(8.(>.$22.R8.(24.(25.R7.(17.&40.Vtsp,)(17.&40.+10800.)(17.&40.+63<:90.)O15.O14.O13.(17.&40.O7.)(17.&40.(1:.(1:.(1:.O9.+2.)O8.)+4.))R6.R5.R4.R3.O12.O11.O10.O?.(17.&40.O8.)(17.&40.(1:.O9.+2.))(17.&40.+63<050.)(19.O6.)(17.&40.$18.)O>.(17.&40.=)(17.&40.=)(17.&40.=)(17.&40.=)O=.O<.O;.O:.)(26.&5.(2.&40.))(17.&40.+973?8.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))(8.(6.$29.O1.R1.)(8.(2:.$5.O1.R1.)(8.(4.$5.R1.)(8.(2;.$5.R1.(1=.VR,)Vtsp,)(8.(2<.$5.R1.Vtsp,(2=.R2.O>.O6.O7.(1:.(1:.(1:.O9.+2.)O8.)+4.)O8.O9.))(2>.(2?.(1?.&8.O5.)=)R1.(17.&8.=)O4.O3.O2.))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L12334604646.98 L18624851236.4  L23675193604.96 L31712192013.1  L32114292796.91 L33590315222.2  L3395516745.98  L41465653183.100L47663894086.2  L47663894086.93 L51723045823.92 L56118415926.112L56118416180.111L59667284135.111L59667284389.112L62412168876.111L62412169134.112L62902335768.3  L63492974498.98 L67775568160.112L67775568160.11300000>00J00`00e01:01@01V01d01j02=02P02^02l03:03H03]04204>04L04b058S3sp05fdata2LnS1R3sp01x2HxS1R3sp05STKLO5fdata2LnS3sp0S1R3sp05fdata2Ln1x2HxS1x2HxS1R3sp05STKLO5fdata2LnS3sp05fdata2LnS1x2HxS3sp05fdata2Ln1x2HxS3sp05fdata2Ln1x2HxS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2Ln3buf2clS3sp05fdata2Ln3buf2clS2fz3FVr3FV0S3sp05fdata2LnS1R3sp05STKLO5fdata2LnS1R3sp05STKLO5fdata2Ln". (* [comment removed for export] *)
  Lemma T1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pbuf,$7.Pcl,$7.Pplen,$7.Pb1,(2.&8.)Pfv,(2.&8.)Pjp,(0.(2.&8.))Pjq,(0.(2.&8.))Pjf,(0.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(2;.$5.R1.(1=.VR,)Vmsp,)P,(4.$5.R2.)P,(30.R18.(1=.VR,)(1>.Vmsp,(1=.VR,)))P,(2<.$5.R4.+63<050.(13.$14.(31.R8.)(1;.$14.)))P,(30.R1:.+63<050.+1.)P,(32.R6.)P,(2>.$12.R7.(17.&8.=)R:.R9.R8.)P,(30.R1=.+65<:>0.+130.)P,(33.$5.R9.+65<=23.(13.$14.(31.(17.&8.=))(1;.$14.)))(34.$5.VAL,R1?.(35.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)(24.(25.(17.&40.+97254.)(17.&40.Vmsp,)(17.&40.+10800.)(17.&40.+63<:90.)R1>.R1=.R1<.(17.&40.(1:.R12.+2.))(17.&40.R12.)(17.&40.(1:.R12.+2.))(17.&40.R11.)(17.&40.(1:.(1:.(1:.R12.+2.)R11.)+4.))(17.&40.R10.)R1;.R1:.R19.R18.(17.&40.R11.)(17.&40.(1:.(1:.(1:.R12.+2.)R11.)+4.))(17.&40.R10.)(19.R?.)(17.&40.$18.)R17.(17.&40.=)(17.&40.=)(17.&40.=)(17.&40.=)R16.R15.R14.R13.)(26.&5.(2.&40.))(17.&40.+973;0.)(17.&20.=)(27.(2.&40.))R:.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    pose proof cs0_ok as CSOK. pose proof (art_alwf _ _ HIA : al_wf AL) as ALWF.   (* [comment removed for export] *)
    intros * ST MI SCS FL FCS RTC AT ACS NL. unfold T1_post, T1W. subst msp tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    assert (GSB0 : al_gsb AL = 0x1099f8) by (destruct IMG' as (_ & _ & _ & G); exact G). clear GSB.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (evtA_cs_mono asegs AL CS0 CS); [| intros x Hx; destruct Hx as [Hx|[Hx|Hx]]; [apply SCS | apply FCS | apply ACS]; clear - Hx; lia ].
    assert (SCS0 : crange CS0 (arl_stklo R) (bv_unsigned sp0 - 128 - arl_stklo R)) by (intros x Hx; unfold CS0; left; lia).
    assert (FCS0 : crange CS0 0x63c050 1) by (intros x Hx; unfold CS0; right; left; lia).
    assert (ACS0 : crange CS0 0x65cae0 304) by (intros x Hx; unfold CS0; right; right; lia).
    clear SCS FCS ACS.
    pose proof (munch_refl [(bv_unsigned sp0 - 208 - 48, bv_unsigned sp0 - 128); (0x63c050, 0x63c051); (0x65cae8, 0x65caec); (0x65cb08, 0x65cb10); (0x65cc08, 0x65cc10)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold atexit_cells in AT. cbn [negb andb orb] in AT.
    repeat match type of AT with context [if false then ?a else ?b] => change (if false then a else b) with b in AT end.
    pose proof (asan_rtc_cell m 0x0f6ab8 8%nat 0 RTC ltac:(unfold rtc_cells; cbn [In]; tauto)) as GOTI. cbn [rtc_mkcell] in GOTI.
    pose proof (bv_unsigned_in_range 8 fv) as FVr. unfold bv_modulus in FVr. cbn in FVr.
    pose proof SPlo as SL. pose proof SPhi as SH. pose proof STKLO as SK.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. carve_frame 48%nat ST.
    replace fv with (Z_to_bv 8 (bv_unsigned fv)) in FL by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    remember (bv_unsigned fv) as fz eqn:EFZ.   (* [comment removed for export] *)
    destruct (Z.eq_dec fz 0) as [FV0|FV0].
    - (* [comment removed for export] *)
      replace (fz =? 0) with true by (symmetry; apply Z.eqb_eq; exact FV0).
      lx_run_tac (PLAN [0x0973f8] [] 150%N). lx_tree.
      (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with Hf : rw_cells _ mx (bv_unsigned sp0 + -256) _, STq : stk _ mx _ (bv_unsigned sp0 + -256) |- _ =>
          chunk_split Hf 6%nat FRlo FRhi;
          lazymatch type of FRhi with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp0 - 208) in FRhi by (clear; lia) end;
          release_frame FRlo STq (bv_unsigned sp0 - 208)
        end end.
      replace (buf + (cl + 6)) with (buf + 2 + cl + 4) in * by lia.
      replace (bv_unsigned sp0 + -256) with (bv_unsigned sp0 - 208 - 48) in * by lia.
      unfold TRFA. finish. all: try eassumption.
    - (* [comment removed for export] *)
      replace (fz =? 0) with false by (symmetry; apply Z.eqb_neq; exact FV0).
      assert (FV1 : 1 <= fz) by (clear - FV0 FVr; lia).
      lx_run_tac (PLAN [0x0973f8] [] 60%N). lx_tree.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with Hf : rw_cells _ mx (bv_unsigned sp0 + -256) _, STq : stk _ mx _ (bv_unsigned sp0 + -256) |- _ =>
          chunk_split Hf 1%nat FRlo FRhi;
          lazymatch type of FRhi with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp0 - 208) in FRhi by (clear; lia) end;
          release_frame FRlo STq (bv_unsigned sp0 - 208)
        end end.
      replace (buf + (cl + 6)) with (buf + 2 + cl + 4) in * by lia.
      replace (bv_unsigned sp0 + -256) with (bv_unsigned sp0 - 208 - 48) in * by lia.
      unfold TRFA. finish. all: try eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition TREGS (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 : word) (plen : Z) (s1 s2 s3 : word) (s5 : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(25.O17.(17.&40.Vtsp,)(17.&40.+10800.)(17.&40.+63<:90.)O16.O15.O14.(17.&40.O5.)O4.O13.O12.O11.O10.O?.O>.O=.O<.O3.O2.(17.&40.+63<050.)(17.&40.O1.)O;.O:.(17.&40.=)(17.&40.=)(17.&40.=)(17.&40.=)O9.O8.O7.O6.)")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Notation LS6 := (Z_to_bv 64 0).
  Notation LS7 := (Z_to_bv 64 (-2)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L15425253222.94L15425253222.95L19392081570.0 L27193321446.94L27193321446.95L40829904044.93L41481127826.92L44533710052.92L5054431440.92 L5060493202.93 L52755101919.93L53517175698.92L53519037842.94L53519037842.95L55804373005.94L57426247314.94L57426247314.95Q17434541659.92Q3015442457.92 Q62504204322.92Q62926358776.9200000P01801901Y02902K02d03A03^04;04U04g05<05Q06006M06j07C07Y08;08YS3sp05fdata3msp2Ln2cl4plen2Hp2P0S3sp05fdata3msp2Ln2cl4plen3Hcl2Hp3CL02P0SS3sp05fdata3msp2Ln2cl4plen2Hp2P0S3sp05fdata3msp2Ln2cl4plen2Hp2P0S3sp05fdata3msp2LnS3sp05fdata3msp2Ln2cl3HclS3sp05fdata3msp2Ln2cl3Hcl3CL0S3sp05fdata3msp2Ln2cl3Hcl3CL0S3sp05fdata3msp2Ln2cl3Hcl3CL0S3sp05fdata3msp2Ln2b24RB2rS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2clS3sp05fdata3msp2Ln2clS3sp04SPlo5fdata3msp2Ln2b24RB2rS3sp05fdata3msp2Ln2cl4plen2HpS3sp05fdata3msp2Ln2cl4plen2HpS3sp05fdata3msp2Ln3buf2HBS3sp05fdata3msp2Ln3bufS3sp05fdata3msp2Ln3buf3cap3HBC3HC3S3sp05fdata3msp2Ln3buf3cap3HC3". (* [comment removed for export] *)
  Lemma T2_steps : forall (CS : Z -> Prop) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 s5 : word) (buf cap cl plen PAY : Z) (b2 : byte) m,
    0 <= cl < 2^40 -> 0 <= plen < 2^27 -> 0 < buf -> buf + cap < 2^47 -> 3 <= cap ->
    (cl <> 0 -> ov_read_bytes asegs m (wa (buf + 2)) 1 = Some [b2]) -> crange CS buf cap ->
    b2 = nth 2 fdata (Z_to_bv 8 0) ->
    evtA asegs AL CS
      (fun ms' => exists a0', ms' = MS (TREGS ra t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RS) x7 t3 t4 t5 t6 plen (Z_to_bv 64 PAY) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) (Z.of_nat (CALLS fdata cl)))
                           bvmap_empty (Z_to_bv 64 (if plen =? 0 then 0x097458 else 0x09740c)) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (mkR ra (Z_to_bv 64 tsp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
               (Z_to_bv 64 plen) (Z_to_bv 64 PAY) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 0x63c050) s5 (Z_to_bv 64 RS) x7
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0973f8) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hcl Hp HB HBC HC3 RB2 CR Hb2. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep.                                          (* [comment removed for export] *)
    destruct (Z.eq_dec cl 0) as [CL0|CL0].
    - ifc true. zstep. zstep.                       (* [comment removed for export] *)
      assert (SV : 1 = Z.of_nat (CALLS fdata cl)).
      { unfold CALLS. replace (cl =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      destruct (Z.eq_dec plen 0) as [P0|P0].
      + ifc false. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite SV. apply evtA_done; eexists; reflexivity.
      + ifc true. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite SV. apply evtA_done; eexists; reflexivity.
    - ifc false. specialize (RB2 CL0).
      zstep.                                        (* [comment removed for export] *)
      zstep. zstep.                                 (* [comment removed for export] *)
      zstep.                                        (* [comment removed for export] *)
      pose proof (bv_unsigned_in_range 8 b2) as RB2r. unfold bv_modulus in RB2r. cbn in RB2r.
      match goal with |- ?g => idtac "T2A" g end.
      assert (SV : Z.land (bv_unsigned b2) 3 + 1 = Z.of_nat (CALLS fdata cl)).
      { unfold CALLS. replace (cl =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- Hb2.
        rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned b2) 4 ltac:(lia)). lia. }
      destruct (Z.eq_dec plen 0) as [P0|P0].
      + ifc true. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite <- SV. apply evtA_done; eexists; reflexivity.
      + ifc false. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- SV. apply evtA_done; eexists; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition out_state (d : nat) (m : mem) : Prop :=
    match d with
    | O => forall a : Z, 0x0fa488 <= a < 0x0fa780 -> m (Z_to_bv 64 a) = None        (* [comment removed for export] *)
    | S k => stdout_bufferedA m (0x65d1a0 + 2 * Z.of_nat k)
             /\ rdn asegs m (Z_to_bv 64 0x65d1a0) (2 * k)%nat = Some (zero_lines k)  (* [comment removed for export] *)
             /\ (k <= 3)%nat
    end.
  Record TMEM (d : nat) (m : mem) : Prop := MKTMEM {
    tx_x : xmemA (bv_unsigned sp0 - 48) m tid wp0 rp0;
    tx_can : rdn asegs m (Z_to_bv 64 0x65cad0) 8 = Some (word_to_le_bytes 8 can);
    tx_out : out_state d m
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L25396113663.63L31232925311.6300000M00jS3sp05fdata3msp3tsp2Ln1a2Ha1lS3sp05fdata3msp3tsp2Ln1a2Ha1l". (* [comment removed for export] *)
  Lemma tmem_of_tail : forall m, tail_memA (Z_to_bv 64 msp) m can tid wp0 rp0 wp1 rp1 -> files_pristine m -> TMEM 0 m.
  Proof.
    intros m TM FI. split.
    - exact (xmem_of_tail _ _ _ _ _ _ _ _ _ TM).
    - exact (tm_can _ _ _ _ _ _ _ _ TM).
    - cbn. intros a Ha. destruct (Z_lt_le_dec a 0x0fa578); [apply (tm_err _ _ _ _ _ _ _ _ TM); lia | apply FI; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition tcell (a : Z) : Prop := drv_static a /\ (a < 0x63c050 \/ 0x63c0a0 <= a) /\ (a < 0x65cae0 \/ 0x65cc10 <= a).
  Definition tcell_compl : list ivl := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(13.(20.$7.$7.)(21.$7.$7.=+?:360.)(13.(20.$7.$7.)(21.$7.$7.+?:400.+?:460.)(13.(20.$7.$7.)(21.$7.$7.+?:780.+106390.)(13.(20.$7.$7.)(21.$7.$7.+106391.+62<050.)(13.(20.$7.$7.)(21.$7.$7.+63<050.+63<180.)(13.(20.$7.$7.)(21.$7.$7.+63<9><.+63<9?0.)(13.(20.$7.$7.)(21.$7.$7.+63<:38.+63<:40.)(13.(20.$7.$7.)(21.$7.$7.+63<:88.+63<::4.)(13.(20.$7.$7.)(21.$7.$7.+63<:;0.+63<:<0.)(13.(20.$7.$7.)(21.$7.$7.+65<:>0.+65<<10.)(13.(20.$7.$7.)(21.$7.$7.+65<=50.+65<=58.)(13.(20.$7.$7.)(21.$7.$7.+65=:;0.(;.+2.+40.))(1;.(20.$7.$7.))))))))))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L19886866625.5900000PS3sp04SPlo5fdata3msp3tsp2Ln1a2Ha". (* [comment removed for export] *)
  Lemma outside_tcell_compl : forall a, 0 <= a < 2^64 -> outside tcell_compl a <-> tcell a.
  Proof. intros a Ha. unfold tcell_compl, tcell, drv_static. cbn. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L53024458802.70L56765666148.7000000O019S3sp05fdata3msp3tsp2Ln1a1n1j2HjS3sp04SPlo5fdata3msp3tsp2Ln1a1n2Ha2Hn1j2Hj". (* [comment removed for export] *)
  Lemma rdn_agree_staticZ : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PP,P,$7.SpPm,Px,(2.&40.)(3.(2.&8.))Pm',Px,(2.&40.)(3.(2.&8.))Pa,$7.Pn,$36.Pbs,(0.(2.&8.))P,Px,$7.P,A1.R7.R1.(>.(3.(2.&8.))A1.R6.(11.R2.)A1.R7.(11.R2.))P,Px,$7.P,(8.(9.R5.R1.)(:.R1.(1:.R5.(37.R4.))))A1.R9.R2.P,(9.=R5.)P,(9.(1:.R6.(37.R5.))(;.+2.+40.))P,(>.(3.(0.(2.&8.)))(38.$5.R9.(17.&40.R7.)R6.)(39.(0.(2.&8.))R5.))(>.(3.(0.(2.&8.)))(38.$5.R9.(17.&40.R8.)R7.)(39.(0.(2.&8.))R6.))")
(* [comment removed for export] *).
  Proof.
    intros P m m' a n bs AG DS Ha Hn H. rewrite <- H. symmetry. apply rdn_agree. intros j Hj. rewrite unsigned_lit by lia.
    symmetry. change (Z_to_bv 64 (a + Z.of_nat j)) with (wa (a + Z.of_nat j)). apply AG. apply DS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0?L10406873899.64L13259230457.75L14611293452.75L16047649081.75L16736775289.75L16968114859.75L20621833868.75L22338733305.75L2574614028.75 L25785764473.75L28403215219.64L32670817676.75L37328845689.75L38336654841.75L46369464697.75L48212680332.75L4830460492.75 L50718165516.75L5199478649.75 L53226144140.75L57910941305.75L59253461772.75L59624745264.75L6075849740.75 L61394514425.75L62758662412.75L66549718394.63L66551810193.66L66551810193.7700000K00f01A01\02702R02m03H03c04>04^05905T05o06J06e07@07[08608Q08l09G09b0:=0:X0;30;N0<20<QS3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp04SPlo5fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1k2K3S3sp05fdata3msp3tsp2Ln1a2HaS3sp04SPlo5fdata3msp3tsp2Ln1k2K31x1HS3sp05fdata3msp3tsp2Ln1k2K31x1H". (* [comment removed for export] *)
  Lemma out_state_agree : forall d m m',
    (forall x, tcell x -> m' (wa x) = m (wa x)) -> out_state d m -> out_state d m'.
  Proof.
    intros [|k] m m' AG OS; cbn in *.
    - intros a Ha. change (Z_to_bv 64 a) with (wa a). rewrite AG by (unfold tcell, drv_static; lia). apply OS. exact Ha.
    - destruct OS as (SB & RD & K3). split; [| split; [| exact K3]].
      + destruct SB; split; (eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | cbn; lia | assumption]).
      + eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | lia | exact RD].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0?L11564578883.86L14499217681.86L16737410102.86L18374770230.88L18482938710.82L27045534584.83L27600830787.86L28787061046.86L29762617489.86L30411838262.88L3113916227.88 L35633778371.86L36287218902.82L36433118902.88L36641843011.86L38256400014.70L38725004483.88L40579273489.86L44353465482.86L44715633782.88L4701636406.86 L48620104469.70L50560457987.88L51249963587.88L53129492106.86L54496988470.88L55369052342.86L56359739233.86L58561136906.86L58685671818.86L60337411194.86L61566265873.86L62791332163.88L6338123523.86 L63639758454.86L65551847173.85L6636908630.82 L66549718394.87L66551810193.72L66551810193.88L66551810193.90L67196195854.8200000F00\01201H01^02802N02d03:03P03f04<04R04h05>05T05j06@06V06l07B07X07n08D08Z09009F09\0:20:H0:^0;40;J0;`0<60<Y0<o0=W0>10>K0>e0?;S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1x1HS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1A2cs2DSS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1A2cs2DS1a2HaS3sp05fdata3msp3tsp2Ln1x1HS3sp05fdata3msp3tsp2Ln1x1HS3sp05fdata3msp3tsp2Ln1x1HS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma tmem_agree : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Pm,P,(2.&40.)(3.(2.&8.))Pm',Px,(2.&40.)(3.(2.&8.))Ph',(3:.$5.VR,VHIA,)PLB',(0.$3;.)PLF,(0.$3;.)P,(3<.R6.R5.)P,Px,$7.P,(3=.R1.)(>.(3.(2.&8.))A1.R7.(11.R2.)A1.R8.(11.R2.))P,Pa,$7.P,(3=.R1.)P,(<.(>.(3.(2.&8.))(3>.$5.R9.(11.R2.))(27.(2.&8.))))(<.(>.(3.(2.&8.))(3>.$5.R9.(11.R3.))(27.(2.&8.))))P,(3?.$5.VR,VHIA,R6.R5.R4.R7.)P,(4.$5.R8.)(3<.R;.R9.)")
(* [comment removed for export] *).
  Proof.
    intros d m m' h' LB' LF [XM CAN OS] AG WV HH MI. split.
    - destruct XM as [MI0 TID LOCK MTID NL COMP RTC MAPPED GLOB FIN ERR].
      assert (MU : munch tcell_compl m m').
      { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
        apply AG. apply (proj1 (outside_tcell_compl (bv_unsigned x) ltac:(lia))). exact Hx. }
      assert (WM : forall A cs, rw_cells asegs m A cs ->
                   (0x0fa460 <= A /\ A + Z.of_nat (cells_size cs) <= 0x0fa780) \/ (A = 0x106390 /\ cells_size cs = 1%nat) \/ (0x63c180 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c9ec)
                   \/ (0x63cae8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cae0) \/ (0x65cc10 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cd50) ->
                   rw_cells asegs m' A cs).
      { intros A cs H DS. eapply rw_cells_transport_w; [exact H | exact MU | intros a Ha; apply WV; unfold tcell, drv_static; lia |].
        unfold tcell_compl. cbn [disjoint_from fst snd]. lia. }
      split.
      + exact MI.
      + exact TID.
      + apply WM; [exact LOCK | cbn; lia].
      + apply WM; [exact MTID | cbn; lia].
      + eapply ro_cells_transport; [exact NL | exact MU |]. unfold tcell_compl. cbn [disjoint_from fst snd cells_size csize]. lia.
      + apply WM; [exact COMP | cbn; lia].
      + apply (hd_rtc _ _ _ HID). eapply (hm_rtc _ _ HIA). exact HH.
      + eapply (hd_lowsh _ _ _ HID). exact HH.
      + destruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
        repeat split; (eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | cbn; lia | assumption]).
      + destruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
        repeat split; (eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | cbn; lia | assumption]).
      + destruct ERR as (wp2 & rp2 & Q1 & Q2 & Q3 & Q4 & Q5). exists wp2, rp2. unfold file_clean.
        repeat split; (eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | cbn; lia | assumption]).
    - eapply (rdn_agree_staticZ tcell); [exact AG | unfold tcell, drv_static; intros; lia | lia | cbn; lia | exact CAN].
    - eapply out_state_agree; [exact AG | exact OS].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56765667309.7500000PS3sp04SPlo5fdata3msp3tsp2Ln1a2Ha". (* [comment removed for export] *)
  Lemma tmem_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Ph',(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLB',(0.$3;.)PLF,(0.$3;.)PSP,$7.PSSP,$7.PSTKHI',$7.PW,(0.$1.)P,(3<.R;.R:.)P,(40.$5.VR,R8.R6.R5.R4.R3.R2.R;.R:.)P,Pa,$7.P,(41.R1.)(=.R5.R2.)P,(3?.$5.VR,VHIA,R;.R9.R8.R<.)P,(4.$5.R=.)(3<.R10.R>.)")
(* [comment removed for export] *).
  Proof.
    intros * TX [HP _] HW HH MI.
    eapply tmem_agree; [exact TX | | | exact HH | exact MI].
    - intros a [Ha _]. apply (proj1 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) (HW a Ha))).
    - intros a [Ha _]. apply (proj2 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) (HW a Ha))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56765667309.7200000PS3sp04SPlo5fdata3msp3tsp2Ln1a2Ha". (* [comment removed for export] *)
  Lemma tmem_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Ph',(3:.$5.VR,VHIA,)PLB',(0.$3;.)PLF,(0.$3;.)PW,(0.$1.)P,(3<.R7.R6.)P,(6.R2.R7.R6.)P,(2:.$5.R8.R7.)P,Pa,$7.P,(3=.R1.)(=.R6.R2.)P,(3?.$5.VR,VHIA,R8.R7.R6.R9.)P,(4.$5.R:.)(3<.R=.R;.)")
(* [comment removed for export] *).
  Proof.
    intros * TX MU WM HW HH MI.
    eapply tmem_agree; [exact TX | | | exact HH | exact MI].
    - intros a Ha. apply MU. rewrite wa_unsigned by (unfold tcell, drv_static in Ha; lia). exact (HW a Ha).
    - intros a Ha W0. apply WM. exact W0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L10572854214.66L24928566088.66L25272235902.67L32604509895.67L61028779120.66L61029216989.67L6379126650.66 00000N00d01:01R01h02>02\S3sp05fdata3msp3tsp2Ln2lo1A2H1S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1AS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2hi1A2H2". (* [comment removed for export] *)
  Lemma sshad_rdn8 : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Plo,$7.Phi,$7.PA,$7.P,(42.$5.VAL,R4.R3.R2.)P,(9.R4.(43.+8.(1>.R2.+7???8000.)))P,(9.(1:.(43.+8.(1>.R3.+7???8000.))+40.)R4.)P,(9.+7???8000.R4.)P,(9.(1:.R5.+8.)(;.+2.+40.))(>.(3.(0.(2.&8.)))(38.$5.R9.(17.&40.R6.)#8.)(39.(0.(2.&8.))(44.#8.(17.&40.=))))")
(* [comment removed for export] *).
  Proof.
    intros m lo hi A SS H1 H2 H3 H4.
    pose proof (sshad_chunk asegs AL m lo hi 7 (8 * (A - 0x7fff8000)) SS ltac:(lia) ltac:(lia) ltac:(rewrite Z.mul_comm, Z.mod_mul; lia)) as RW.
    replace (shadow_of AL (8 * (A - 0x7fff8000))) with A in RW.
    2:{ unfold shadow_of. change (al_sb AL) with (al_sb (arl_AL R)). fold AL. rewrite ASB. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    pose proof (bytes_at_rdn asegs m A _ 0 8 (rw_cells_bytes_at _ _ _ _ RW) ltac:(cbn; lia)) as RD.
    rewrite Z.add_0_r in RD. unfold wa in RD. rewrite RD. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L15032289737.61L22860122646.59L25271973500.60L42734876087.63L55686439908.63L56082919523.62L61028943863.63L6675703693.59 00000K00a01701R01m02H02c039S3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma img_shadow_bufword : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))P,(45.$5.VAL,R1.)(>.(3.(0.(2.&8.)))(38.$5.R2.(17.&40.+800<3:30.)#8.)(39.(0.(2.&8.))(44.#8.(17.&40.=))))")
(* [comment removed for export] *).
  Proof.
    intros m ISH.
    assert (BY : bytes_at asegs m 0x800c3a30 (repeat (Z_to_bv 8 0) 8)).
    { split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      assert (Z0 : img_shadow0 (0xcba30 + Z.of_nat i) = true).
      { assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%nat as C by lia.
        destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity. }
      pose proof (img_shadow_ok_zero asegs AL m (0xcba30 + Z.of_nat i) ISH ltac:(unfold IMG_GLO, IMG_GHI; lia) Z0) as B1.
      replace (shadow_of AL (8 * (0xcba30 + Z.of_nat i))) with (0x800c3a30 + Z.of_nat i) in B1.
      2:{ unfold shadow_of. change (al_sb AL) with (al_sb (arl_AL R)). fold AL. rewrite ASB. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
      destruct B1 as (_ & _ & B1). specialize (B1 0%nat ltac:(cbn; lia)). cbn [nth_error] in B1. rewrite Z.add_0_r in B1.
      rewrite B1. symmetry. apply nth_error_repeat. exact Hi. }
    pose proof (bytes_at_rdn asegs m 0x800c3a30 _ 0 8 BY ltac:(cbn; lia)) as RD.
    rewrite Z.add_0_r in RD. unfold wa in RD. rewrite RD. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition incbA (m : mem) (v : byte) : Prop := rw_cells asegs m 0x63c054 [C1 v].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L19392081570.0 Q11668531018.86Q17758594599.89Q37215584081.86Q4893521969.87 00000100C00d01601KSS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2HB5Ha_st5Hl_stS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2HB". (* [comment removed for export] *)
  Lemma L1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pv,(2.&8.)Pplen,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))P,(46.R1.R4.)P,(30.R19.+63<054.+1.)P,(4.$5.R3.)(34.$5.VAL,R1;.Lms',$22.(23.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(8.(>.$22.R2.(24.(47.(17.&40.+9747<.)R1;.R1:.R19.R<.(17.&40.R8.)R16.R15.R14.R13.R12.R11.(17.&40.=)(17.&40.-2.)R10.R?.R>.R=.R8.R<.R;.R:.R7.)(26.&5.(2.&40.))(17.&40.$48.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))(8.(6.(13.(20.$7.$7.)(21.$7.$7.+63<054.+63<055.)(1;.(20.$7.$7.)))R6.R1.)(8.(2:.$5.R6.R1.)(8.(4.$5.R1.)(46.R1.(17.&8.+1.)))))))(24.(47.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.(17.&40.=)(17.&40.-2.)R>.R=.R<.R;.R6.R:.R9.R8.R5.)(26.&5.(2.&40.))(17.&40.+97468.)(17.&20.=)(27.(2.&40.))R4.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * IC ICS MI. unfold TREGS, incbA in *. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(0x63c054, 0x63c055)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.                        (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ 0x63c054 _ |- _ => rewrite ?(u_small 1) in H by lia end.
    zstep. zstep. zstep.                            (* [comment removed for export] *)
    finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L19392081570.0 Q11668531018.84Q17758594599.87Q37215584081.84Q4893521969.85 00000100C00d01601KSS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2HB5Ha_st5Hl_stS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2HB". (* [comment removed for export] *)
  Lemma L2_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pv,(2.&8.)Pplen,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))P,(46.R1.R4.)P,(30.R17.+63<054.+1.)P,(4.$5.R3.)(34.$5.VAL,R19.Lms',$22.(23.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(8.(>.$22.R2.(24.(47.(17.&40.+9748<.)R1:.R19.R18.(17.&40.=)(17.&40.=)R16.R15.R14.R13.R12.R11.(17.&40.=)(17.&40.-2.)R10.R?.R>.R=.R8.R<.R;.(17.&40.=)R7.)(26.&5.(2.&40.))(17.&40.+97538.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))(8.(6.(13.(20.$7.$7.)(21.$7.$7.+63<054.+63<055.)(1;.(20.$7.$7.)))R6.R1.)(8.(2:.$5.R6.R1.)(8.(4.$5.R1.)(46.R1.(17.&8.=)))))))(24.(47.(17.&40.+9747<.)R18.R17.R16.(17.&40.=)R15.R14.R13.R12.R11.R10.R?.(17.&40.=)(17.&40.-2.)R>.R=.R<.R;.R6.R:.R9.R8.R5.)(26.&5.(2.&40.))(17.&40.+9747<.)(17.&20.=)(27.(2.&40.))R4.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * IC ICS MI. unfold TREGS, incbA in *. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(0x63c054, 0x63c055)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.                        (* [comment removed for export] *)
    lazymatch goal with H : rw_cells _ _ 0x63c054 _ |- _ => rewrite ?(u_small 0) in H by lia end.
    zstep. zstep.                                   (* [comment removed for export] *)
    finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L1950623412.80 L2169817893.80 L23970616829.80L29023184571.79L2971973454.80 L53519004689.80L65221224721.79L780929237.80  00000J00d01;01E01_02102H02bS3sp05fdata3msp2Ln1r2Hr2R1S3sp05fdata3msp2Ln1r2Hr2R1S3sp05fdata3msp2Ln1r2HrS3sp01r2HrS3sp05fdata3msp2Ln1r2Hr2R1S3sp05fdata3msp2LnS3sp05fdata3msp2Ln1r2HrS3sp05fdata3msp2Ln1r2Hr2R1". (* [comment removed for export] *)
  Lemma L3_steps : forall (CS : Z -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1 s2 : word) (plen r : Z) m,
    1 <= r <= 4 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (TREGS (Z_to_bv 64 0x09748c) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 LS6 LS7 t3 t4 t5 t6 plen s1 s2 (Z_to_bv 64 (-1)) (r - 1))
                           bvmap_empty (Z_to_bv 64 (if r =? 1 then 0x0974a0 else 0x097468)) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (TREGS (Z_to_bv 64 0x09748c) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 LS6 LS7 t3 t4 t5 t6 plen s1 s2 (Z_to_bv 64 0) r)
          bvmap_empty (Z_to_bv 64 0x09748c) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hr. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep.                                          (* [comment removed for export] *)
    zstep. try ifc true.                            (* [comment removed for export] *)
    zstep. rewrite ?swrap32_id by lia. zstep.       (* [comment removed for export] *)
    destruct (Z.eq_dec r 1) as [R1|R1].
    - ifc false. replace (r =? 1) with true by (symmetry; apply Z.eqb_eq; lia). done_regs.
    - ifc true. replace (r =? 1) with false by (symmetry; apply Z.eqb_neq; lia). done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma L4_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pplen,$7.Pm,P,(2.&40.)(3.(2.&8.))(34.$5.VAL,R15.Lms',$22.(>.$22.R1.(24.(47.(17.&40.+974:8.)R15.R14.R13.R5.R11.R10.R?.R>.R=.R<.R;.(17.&40.=)(17.&40.-2.)R:.R9.R8.R7.R3.R6.R5.R4.=)(26.&5.(2.&40.))(17.&40.+6947<.)(17.&20.=)(27.(2.&40.))R2.(28.$5.)))(24.(47.(17.&40.+9748<.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.(17.&40.=)(17.&40.-2.)R9.R8.R7.R6.R2.R5.R4.R3.=)(26.&5.(2.&40.))(17.&40.+974:0.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros *. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Definition RREGS (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (rv buf cl plen : Z) (b1 : byte) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(25.(17.&40.+97254.)(17.&40.Vmsp,)(17.&40.+10800.)(17.&40.+63<:90.)O14.O13.O12.(17.&40.(1:.O4.+2.))(17.&40.O4.)(17.&40.O5.)O11.O10.O?.O>.O=.O<.O;.(17.&40.O3.)(17.&40.(1:.(1:.(1:.O4.+2.)O3.)+4.))(17.&40.O2.)(19.O1.)(17.&40.$18.)O:.(17.&40.=)(17.&40.=)(17.&40.=)(17.&40.=)O9.O8.O7.O6.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0?L13309229874.85L14981969176.85L21971292696.85L22120147736.85L30021243613.84L31722891288.85L34234375064.85L36667852792.0 L51126253464.85L52071667727.84L53506590987.84L56498182552.85L6274867352.85 L67856165528.85Q12872860869.84Q15304725424.84Q16156991457.84Q18894481989.84Q18994824390.84Q20351153222.84Q21338652976.84Q23962701510.84Q24216750433.84Q24930197445.84Q27357656752.84Q31136645702.84Q33360389168.84Q3427631174.84 Q35722900577.84Q36949832389.84Q39381486000.84Q39988450118.84Q40243683937.84Q41276410182.84Q43614680518.84Q44904801222.84Q45400751920.84Q4652940513.84 Q51434941616.84Q51496327493.84Q51785118561.84Q57453875760.84Q57517674181.84Q59807448801.84Q60827833697.84Q63456610224.84Q63536675909.84Q6870390597.84 Q7116621281.84 Q853483973.84  00000>00L00Z00h01601D01R01S01a01b01g02502C02Q02_03203E03S03a03o04B04P04c05105D05R05e06306F06T06g07507H07V07d08208E08X08k09909L09_09m0:@0:S0:f0;40;B0;U0;cS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnSS3sp05fdata2LnFS3sp0S3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2Ln". (* [comment removed for export] *)
  Lemma L5_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pbuf,$7.Pcl,$7.Pplen,$7.Pb1,(2.&8.)Pjunk,(0.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(2<.$5.R1.Vtsp,(2=.R2.R>.R3.R4.(1:.(1:.(1:.R6.+2.)R5.)+4.)R5.R6.))P,(30.R1;.Vtsp,+50.)(34.$5.VAL,R1<.Lms',$22.(>.$22.R1.(24.(49.R1<.R1;.R1:.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.=R9.R8.R7.R6.)(26.&5.(2.&40.))(17.&40.+97254.)(17.&20.=)(27.(2.&40.))R4.(28.$5.)))(24.(47.(17.&40.+974:8.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.(17.&40.=)(17.&40.-2.)R?.R>.R=.R<.R6.R;.R:.R9.=)(26.&5.(2.&40.))(17.&40.+974:8.)(17.&20.=)(27.(2.&40.))R3.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * FR SCS. unfold TREGS, RREGS, TRFA in *. subst msp tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    replace (bv_unsigned sp0 - 208) with (bv_unsigned sp0 + -208) in * by lia.
    zstep. zstep. zstep.                            (* [comment removed for export] *)
    do 9 zstep.                                     (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L19815123762.83L29849367789.83L59315336847.83L59315369869.83L64599873339.8300000B00[01601Q01jS3sp05fdata3tsp2LnS3sp05fdata3tsp2Ln2b13RB1S3sp05fdata3tsp2Ln2b13NEG1lS3sp05fdata3tsp2Ln2b13POS1nS3sp05fdata3tsp2Ln2b13RB1". (* [comment removed for export] *)
  Lemma M1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prv,$7.Pbuf,$7.Pcl,$7.Pplen,$7.Pb1,(2.&8.)Pm,P,(2.&40.)(3.(2.&8.))P,(8.(9.=R6.)(9.R6.+2.))(34.$5.VAL,R17.Lms',$22.(23.(2.&40.)Lra',(2.&40.)(23.(2.&40.)La0',(2.&40.)(23.(2.&40.)La1',(2.&40.)(>.$22.R4.(24.(25.R3.(17.&40.Vmsp,)(17.&40.+10800.)(17.&40.+63<:90.)R1:.R19.R18.(17.&40.(4:.R;.R7.))(17.&40.R:.)R2.R1.R16.R15.R14.R13.R12.R11.(17.&40.R9.)(17.&40.(1:.(1:.(1:.R:.+2.)R9.)+4.))(17.&40.R8.)(19.R7.)(17.&40.$18.)R10.(17.&40.=)(17.&40.=)(17.&40.=)(17.&40.=)R?.R>.R=.R<.)(26.&5.(2.&40.))(17.&40.+972=4.)(17.&20.=)(27.(2.&40.))R6.(28.$5.))))))(24.(49.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(26.&5.(2.&40.))(17.&40.+97254.)(17.&20.=)(27.(2.&40.))R2.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * Hrv. unfold RREGS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 8 b1) as RB1. unfold bv_modulus in RB1. cbn in RB1.
    zstep.                                          (* [comment removed for export] *)
    unfold status. destruct (Z.leb_spec0 128 (bv_unsigned b1)) as [NEG|POS].
    - lazymatch goal with
      | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
          replace c with true; [cbv iota | symmetry; rewrite bv_lts_zero_r, sxb_unsigned; destruct (Z.ltb_spec0 (bv_unsigned b1) 128); [exfalso; lia | apply Z.leb_le; lia]]
      end.
      zstep. zstep. zstep.                          (* [comment removed for export] *)
      zstep. zstep. zstep.                          (* [comment removed for export] *)
      apply evtA_done. eexists _, _, _. unfold mkR. repeat (first [ reflexivity | lia | progress f_equal ]).
    - lazymatch goal with
      | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) =>
          replace c with false; [cbv iota | symmetry; rewrite bv_lts_zero_r, sxb_unsigned; destruct (Z.ltb_spec0 (bv_unsigned b1) 128); [apply Z.leb_gt; lia | exfalso; lia]]
      end.
      zstep. zstep.                                 (* [comment removed for export] *)
      apply evtA_done. eexists _, _, _. unfold mkR. repeat (first [ reflexivity | lia | progress f_equal ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L53024458802.70L56765666148.70L7985991406.70 00000O01901cS3sp05fdata3msp3tsp2Ln1a1n1j2HjS3sp04SPlo5fdata3msp3tsp2Ln1a1n2Ha2Hn1j2HjS3sp04SPlo5fdata3msp3tsp2Ln1a1n2Ha2Hn1j2Hj". (* [comment removed for export] *)
  Lemma rdn_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pa,$7.Pn,$36.Pbs,(0.(2.&8.))P,(6.R6.R5.R4.)P,(4;.R7.R4.(37.R3.))P,(9.=R5.)P,(9.(1:.R6.(37.R5.))(;.+2.+40.))P,(>.(3.(0.(2.&8.)))(38.$5.R9.(17.&40.R7.)R6.)(39.(0.(2.&8.))R5.))(>.(3.(0.(2.&8.)))(38.$5.R9.(17.&40.R8.)R7.)(39.(0.(2.&8.))R6.))")
(* [comment removed for export] *).
  Proof.
    intros W m m' a n bs MU DJ Ha Hn H. rewrite <- H. symmetry. apply rdn_agree. intros j Hj. rewrite unsigned_lit by lia.
    symmetry. apply MU. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact DJ | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition xmem_cells : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "(13.(20.$7.$7.)(21.$7.$7.+65<=00.+4.)(13.(20.$7.$7.)(21.$7.$7.+63<9>8.+4.)(13.(20.$7.$7.)(21.$7.$7.+65<=23.+1.)(13.(20.$7.$7.)(21.$7.$7.+106390.+1.)(13.(20.$7.$7.)(21.$7.$7.+65=188.+8.)(13.(20.$7.$7.)(21.$7.$7.+?:750.+8.)(13.(20.$7.$7.)(21.$7.$7.+?:660.+8.)(13.(20.$7.$7.)(21.$7.$7.+?:570.+8.)(13.(20.$7.$7.)(21.$7.$7.+?:668.+>8.)(13.(20.$7.$7.)(21.$7.$7.+?:488.+>8.)(13.(20.$7.$7.)(21.$7.$7.+65<:=0.+8.)(1;.(20.$7.$7.)))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac in_cells := solve [ unfold xmem_cells; cbn [In]; repeat (first [left; reflexivity | right]) ].
  Local Ltac2 Set LiaOrc.tbl := fun () => "00n0?L10214751138.88L11867564459.86L13494977998.13L14497203344.86L14881493323.88L14995579956.86L15161605707.86L16173312667.82L17815194018.88L18697922987.86L21833388971.86L24058980692.82L24058980692.86L26015535182.86L26358007860.86L27198444875.86L27667345201.82L2845637195.88 L29590517008.88L29760472336.86L3014991566.86 L32946052811.88L33670937502.82L3379418731.82 L34216847787.82L37049136462.86L37154567220.82L37394724916.82L37953385232.86L38430668907.82L38973098827.88L39414722126.82L40577259152.86L42726357387.88L42791503924.82L43164157474.88L44052137058.88L44603334818.86L45262037707.86L45648188962.86L46034424226.86L47299478434.86L47418779810.88L47848537294.88L48618024080.82L48925198434.86L51272814411.86L51796692231.82L51941590606.86L54785334836.82L55043374475.86L55711655988.86L56361753312.86L61124435438.86L61564252048.86L62937724468.86L64945935787.86L65352685275.82L65352685275.86L65400351438.86L68057139237.82L8952318364.82 00000F00\01401J01`02602L02b03803N03d04:04P04f05<05R06;06Q06g07=07S07i08?08U08k09A09W09m0:C0:Y0:o0;E0;[0<10<G0<]0=30=I0=_0>50>K0>a0?70?M0?c0@90@O0A60AL0Ab0B80BN0Bd0C:0CP0Cf0D<0DR0Dh0E>0ET0ElS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS2lo2hi1a1n1k1j2H12H22X1S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1a1n1k1j2H22H4S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1a1k1j2H12H3S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1j". (* [comment removed for export] *)
  Lemma xmem_munchW : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Ph',(3:.$5.VR,VHIA,)PLB',(0.$3;.)PLF,(0.$3;.)P,(4<.(1>.(1?.&40.Vsp0,)+30.)R5.Vtid,Vwp0,Vrp0,)P,(>.(3.(0.(2.&8.)))(38.$5.R6.(17.&40.+65<:=0.)#8.)(39.(0.(2.&8.))(44.#8.Vcan,)))P,(6.R8.R7.R6.)P,(2:.$5.R8.R7.)P,(3?.$5.VR,VHIA,R7.R6.R5.R8.)P,(4.$5.R9.)P,Pa,$7.Pn,$7.P,(4=.(20.$7.$7.)(21.$7.$7.R2.R1.)$4>.)(4;.R?.R3.R2.)(8.(4<.(1>.(1?.&40.Vsp0,)+30.)R;.Vtid,Vwp0,Vrp0,)(>.(3.(0.(2.&8.)))(38.$5.R;.(17.&40.+65<:=0.)#8.)(39.(0.(2.&8.))(44.#8.Vcan,))))")
(* [comment removed for export] *).
  Proof.
    intros W m m' h' LB' LF XM CAN MU WM HH MI DJ.
    assert (D : forall a n k j, In (a, n) xmem_cells -> a <= k -> k + j <= a + n -> 0 <= j -> disjoint_from W k j).
    { intros a n k j Hin H1 H2 H3. pose proof (DJ a n Hin) as X. clear -X H1 H2 H3.
      induction W as [|[lo hi] W IH]; cbn in *; [exact I|]. destruct X as [X1 X2]. split; [lia | apply IH; exact X2]. }
    assert (RDN : forall a n k (j : nat) bs, In (a, n) xmem_cells -> a <= k -> k + Z.of_nat j <= a + n -> 0 <= a -> a + n <= 2^64 ->
                  rdn asegs m (Z_to_bv 64 k) j = Some bs -> rdn asegs m' (Z_to_bv 64 k) j = Some bs).
    { intros a n k j bs Hin H1 H2 H3 H4 H. eapply rdn_munch; [exact MU | eapply D; [exact Hin | exact H1 | exact H2 | lia] | lia | lia | exact H]. }
    destruct XM as [MI0 TID LOCK MTID NL COMP RTC MAPPED GLOB FIN ERR].
    split; [split|].
    - exact MI.
    - exact TID.
    - eapply rw_cells_transport; [exact LOCK | exact MU | exact WM | apply (D 0x65cd00 4); [in_cells | lia | cbn; lia | cbn; lia]].
    - eapply rw_cells_transport; [exact MTID | exact MU | exact WM | apply (D 0x63c9e8 4); [in_cells | lia | cbn; lia | cbn; lia]].
    - eapply ro_cells_transport; [exact NL | exact MU | apply (D 0x65cd23 1); [in_cells | lia | cbn; lia | cbn; lia]].
    - eapply rw_cells_transport; [exact COMP | exact MU | exact WM | apply (D 0x106390 1); [in_cells | lia | cbn; lia | cbn; lia]].
    - apply (hd_rtc _ _ _ HID). eapply (hm_rtc _ _ HIA). exact HH.
    - eapply (hd_lowsh _ _ _ HID). exact HH.
    - destruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
      split; [refine (RDN 0x65cd23 1 _ _ _ _ _ _ _ _ Q1); [in_cells | lia | cbn; lia | lia | lia] |].
      split; [refine (RDN 0x65d188 8 _ _ _ _ _ _ _ _ Q2); [in_cells | lia | cbn; lia | lia | lia] |].
      split; [refine (RDN 0x0fa750 8 _ _ _ _ _ _ _ _ Q3); [in_cells | lia | cbn; lia | lia | lia] |].
      split; [refine (RDN 0x0fa660 8 _ _ _ _ _ _ _ _ Q4); [in_cells | lia | cbn; lia | lia | lia] |].
      refine (RDN 0x0fa570 8 _ _ _ _ _ _ _ _ Q5); [in_cells | lia | cbn; lia | lia | lia].
    - destruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; [refine (RDN 0x0fa668 232 _ _ _ _ _ _ _ _ Q1) | refine (RDN 0x0fa668 232 _ _ _ _ _ _ _ _ Q2) | refine (RDN 0x0fa668 232 _ _ _ _ _ _ _ _ Q3)
                   | refine (RDN 0x0fa668 232 _ _ _ _ _ _ _ _ Q4) | refine (RDN 0x0fa668 232 _ _ _ _ _ _ _ _ Q5)];
        first [in_cells | cbn; lia | lia].
    - destruct ERR as (wp2 & rp2 & Q1 & Q2 & Q3 & Q4 & Q5). exists wp2, rp2. unfold file_clean.
      repeat split; [refine (RDN 0x0fa488 232 _ _ _ _ _ _ _ _ Q1) | refine (RDN 0x0fa488 232 _ _ _ _ _ _ _ _ Q2) | refine (RDN 0x0fa488 232 _ _ _ _ _ _ _ _ Q3)
                   | refine (RDN 0x0fa488 232 _ _ _ _ _ _ _ _ Q4) | refine (RDN 0x0fa488 232 _ _ _ _ _ _ _ _ Q5)];
        first [in_cells | cbn; lia | lia].
    - refine (RDN 0x65cad0 8 _ _ _ _ _ _ _ _ CAN); [in_cells | lia | cbn; lia | lia | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma wseg_638840 : wseg_ok asegs (Z_to_bv 64 0x63c340) 139136%nat = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L48958127933.60L55686714054.61L58116899626.60L60071012102.6000000K00a01<01RS3sp05fdata3msp3tsp2Ln1a2HaS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1a2HaS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma wview_6d5 : forall m (a : word), 0x63c340 <= bv_unsigned a < 0x65e2c0 -> wview asegs m a <> None.
  Proof.
    intros m a Ha.
    pose proof (store_ok_window asegs m (Z_to_bv 64 0x63c340) a 139136%nat 1%nat 0x63c340 0x65e2c0
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) wseg_638840 ltac:(lia) ltac:(cbn; lia)) as SO.
    pose proof (store_ok_wview asegs m a 1%nat 0%nat SO ltac:(lia)) as WV.
    rewrite Z.add_0_r in WV. unfold wa in WV. rewrite Z_to_bv_bv_unsigned in WV. exact WV.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L15930908145.61L17562664839.64L17562664839.65L27606809322.61L28910316598.61L3877452529.61 L46015156202.61L46952822506.61L53506590998.61L54554161777.61L56765666148.64L56765666148.65L59711116138.61L60083429610.61L60575246321.61L64334991665.6100000F00n01V01l02B02X02n03D03Z04004S05605L05b06806NS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1a2H12H21j2HjS3sp04SPlo5fdata3msp3tsp2Ln1a2H12H21j2HjS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1a2H12H21j2HjS3sp05fdata3msp3tsp2Ln1a2H12H21j2HjS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma stdout_pristine_clean : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,Px,(2.&40.)(3.(2.&8.))P,Pa,$7.P,(8.(9.+?:578.R1.)(:.R1.+?:660.))(>.(3.(2.&8.))A1.R3.(17.&40.R2.)(27.(2.&8.)))(4?.R2.+?:578.(17.&40.=)(17.&40.=))")
(* [comment removed for export] *).
  Proof.
    intros m PR.
    assert (IMG8 : forall a, 0x0fa578 <= a -> a + 8 <= 0x0fa660 -> rdn asegs m (Z_to_bv 64 a) 8 = rdn asegs (fun _ => None) (Z_to_bv 64 a) 8).
    { intros a H1 H2. apply rdn_agree. intros j Hj. rewrite unsigned_lit by lia. apply PR. lia. }
    assert (IMG4 : forall a, 0x0fa578 <= a -> a + 4 <= 0x0fa660 -> rdn asegs m (Z_to_bv 64 a) 4 = rdn asegs (fun _ => None) (Z_to_bv 64 a) 4).
    { intros a H1 H2. apply rdn_agree. intros j Hj. rewrite unsigned_lit by lia. apply PR. lia. }
    unfold file_clean. rewrite IMG4, !IMG8 by lia. unfold word_to_le_bytes. rewrite !unsigned_lit by lia. repeat split; rdn_img_lit.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L24034688355.63L41954788037.63L43665194877.63L57217654605.63L61028791263.62L63368327942.61L9148458690.73 00000R01401V02802P02h03US3sp04SPlo4SPal5fdata3msp3tsp2Ln1XS3sp04SPlo4SPal5fdata3msp3tsp2Ln1XS3sp04SPlo4SPal5fdata3msp3tsp2Ln1XS3sp04SPlo4SPhi5fdata3msp3tsp2Ln1XS3sp05fdata3msp3tsp2Ln1XS3sp05fdata3msp3tsp2Ln1XS3sp02r04SPal5fdata3msp3tsp2Ln1q1r1H2H02q02H4". (* [comment removed for export] *)
  Lemma ssw_zero : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))P,(42.$5.VAL,R1.(1=.VR,)Vmsp,)(>.(3.(0.(2.&8.)))(38.$5.R2.(17.&40.(1>.(1:.(50.(1>.Vtsp,+390.)+8.)+7???8000.)(51.(1:.(50.(1>.Vtsp,+390.)+8.)+7???8000.)+8.)))#8.)(39.(0.(2.&8.))(44.#8.(17.&40.=))))")
(* [comment removed for export] *).
  Proof.
    intros m SSH. cbv delta [tsp msp] in *.
    set (X := (bv_unsigned sp0 - 192 - 912) / 8).
    assert (HX : 8 * X <= bv_unsigned sp0 - 192 - 912 < 8 * X + 8) by (subst X; Z.div_mod_to_equations; lia).
    pose proof (Z.mod_pos_bound (X + 0x7fff8000) 8 ltac:(lia)) as HY.
    pose proof (Z.div_mod (X + 0x7fff8000) 8 ltac:(lia)) as HZ.
    eapply sshad_rdn8; [exact SSH | rewrite STKLO; lia | lia | lia | lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac rtc_fld RTC := first [ apply (rtc_rdn1 _ _ _ RTC); rtc_in | apply (rtc_rdn8 _ _ _ RTC); rtc_in ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926387083.71L21307703404.73L35432951903.71L39428219559.71L58748631727.71L62856262335.71L8299480064.73 00000F00a01701W01m02C02kS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1a2HaS3sp05fdata3msp3tsp2LnS3sp04SPlo4SPhi5fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln1a2Ha". (* [comment removed for export] *)
  Lemma pf_of_tmem : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Ph,(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLF,(0.$3;.)P,(3<.#0.R4.)P,(3?.$5.VR,VHIA,R4.R3.R2.R5.)P,(2;.$5.R6.(1=.VR,)Vtsp,)P,(42.$5.VAL,R7.(1=.VR,)Vmsp,)(52.(17.&40.Vtsp,)R8.Vcan,)")
(* [comment removed for export] *).
  Proof.
    intros m h LB LF [XM CAN OS] HH ST SSH. cbn in OS.
    pose proof (hd_rtc _ _ _ HID m (hm_rtc _ _ HIA _ _ _ _ HH)) as RTC.
    pose proof (A_main_loop.HM_ZIMG R HIA ASB h LB LF m HH) as ZI.
    pose proof (img_shadow_bufword m (hm_img_shadow _ _ HIA h LB LF m HH)) as SHB.
    pose proof (ssw_zero m SSH) as SHS.
    split; rewrite ?unsigned_lit by (cbv delta [tsp]; lia).
    all: first [ exact OS | exact CAN | exact SHB | exact SHS
               | rtc_fld RTC
               | (intros a Ha; apply (mem_inv_text_noneA m a (xm_mi _ _ _ _ _ XM) Ha))
               | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia)
               | (intros a Ha; apply wview_6d5; lia)
               | (intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (proj1 (proj2 (proj2 ST) (bv_unsigned a) ltac:(cbv delta [tsp] in Ha; lia))))
               | match goal with |- ?g => idtac "PFREM" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac pn_of_tmem_tac :=
    intros m h LB LF [XM CAN OS] HH ST SSH; cbn [out_state] in OS; destruct OS as (SB & RD & K3);
    pose proof (hd_rtc _ _ _ HID m (hm_rtc _ _ HIA _ _ _ _ HH)) as RTC;
    pose proof (A_main_loop.HM_ZIMG R HIA ASB h LB LF m HH) as ZI;
    pose proof (img_shadow_bufword m (hm_img_shadow _ _ HIA h LB LF m HH)) as SHB;
    pose proof (ssw_zero m SSH) as SHS;
    destruct SB as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11];
    split; rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
    first [ exact CAN | exact SHB | exact SHS | assumption
          | rtc_fld RTC
          | (intros a Ha; apply (mem_inv_text_noneA m a (xm_mi _ _ _ _ _ XM) Ha))
          | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia)
          | (intros a Ha; apply wview_6d5; lia)
          | (intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply (proj1 (proj2 (proj2 ST) (bv_unsigned a) ltac:(cbv delta [tsp] in Ha; lia))))
          | match goal with |- ?g => idtac "PNREM" g end ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926387083.84L21307703404.86L35432951903.84L39428219559.84L58748631727.84L62856262335.84L8299480064.86 00000I00g01@01c02<02U03@S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K31a2HaS3sp05fdata3msp3tsp2Ln2K3S3sp04SPlo4SPhi5fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln2K31a2Ha". (* [comment removed for export] *)
  Lemma pn0_of_tmem : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Ph,(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLF,(0.$3;.)P,(3<.#1.R4.)P,(3?.$5.VR,VHIA,R4.R3.R2.R5.)P,(2;.$5.R6.(1=.VR,)Vtsp,)P,(42.$5.VAL,R7.(1=.VR,)Vmsp,)(53.(17.&40.Vtsp,)$54.R8.Vcan,)")
(* [comment removed for export] *).
  Proof. pn_of_tmem_tac. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926387083.84L21307703404.86L35432951903.84L39428219559.84L58748631727.84L62856262335.84L8299480064.86 00000I00g01@01c02<02U03@S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K31a2HaS3sp05fdata3msp3tsp2Ln2K3S3sp04SPlo4SPhi5fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln2K31a2Ha". (* [comment removed for export] *)
  Lemma pn2_of_tmem : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Ph,(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLF,(0.$3;.)P,(3<.#2.R4.)P,(3?.$5.VR,VHIA,R4.R3.R2.R5.)P,(2;.$5.R6.(1=.VR,)Vtsp,)P,(42.$5.VAL,R7.(1=.VR,)Vmsp,)(55.(17.&40.Vtsp,)$56.R8.Vcan,)")
(* [comment removed for export] *).
  Proof. pn_of_tmem_tac. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926387083.84L21307703404.86L35432951903.84L39428219559.84L58748631727.84L62856262335.84L8299480064.86 00000I00g01@01c02<02U03@S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K31a2HaS3sp05fdata3msp3tsp2Ln2K3S3sp04SPlo4SPhi5fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S3sp05fdata3msp3tsp2Ln2K3S1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln2K31a2Ha". (* [comment removed for export] *)
  Lemma pn4_of_tmem : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Ph,(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLF,(0.$3;.)P,(3<.#3.R4.)P,(3?.$5.VR,VHIA,R4.R3.R2.R5.)P,(2;.$5.R6.(1=.VR,)Vtsp,)P,(42.$5.VAL,R7.(1=.VR,)Vmsp,)(57.(17.&40.Vtsp,)$58.R8.Vcan,)")
(* [comment removed for export] *).
  Proof. pn_of_tmem_tac. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11452209111.83L18668317360.83L29406145770.83L49825971688.83L52483706608.7100000T01801W02;02YS3sp04SPlo5fdata3msp3tsp2Ln2k'2K32HdS3sp04SPlo5fdata3msp3tsp2Ln2k'2K32HdS3sp05fdata3msp3tsp2Ln2k'2K32HdS3sp04SPlo5fdata3msp3tsp2Ln2k'2K32HdS3sp05fdata3msp3tsp2Ln2Hd1a2Ha". (* [comment removed for export] *)
  Lemma xout_of_tmem : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)PLB,(0.$3;.)PLF,(0.$3;.)P,(3<.R6.R5.)P,(5:.R7.#4.)P,(>.(3.$5;.)(5<.(5=.R6.)(17.&40.+1.))(39.$5;.(5>.(17.&40.+1.))))P,(3?.$5.VR,VHIA,R6.R5.R4.R8.)(5?.R9.R8.(60.(61.R:.#1.)))")
(* [comment removed for export] *).
  Proof.
    intros d m mo h LB LF [XM CAN OS] Hd FD1 HH.
    pose proof (hd_rtc _ _ _ HID m (hm_rtc _ _ HIA _ _ _ _ HH)) as RTC.
    destruct d as [|k]; cbn [out_state] in OS.
    - left. split; [reflexivity|]. exists (Z_to_bv 64 0), (Z_to_bv 64 0). apply stdout_pristine_clean. intros a Ha. apply OS. lia.
    - destruct OS as (SB & RD & K3). destruct k as [|k'].
      + left. split; [reflexivity|]. exists (Z_to_bv 64 0x65d1a0), (Z_to_bv 64 0). destruct SB. unfold file_clean.
        change (0x65d1a0 + 2 * Z.of_nat 0) with 0x65d1a0 in *. repeat split; assumption.
      + right. exists 0x65d1a0, (0x65d1a0 + 2 * Z.of_nat (S k')), (Z_to_bv 64 0x65d1a0), (Z_to_bv 64 1024), (Z_to_bv 64 0), can.
        split; [| exact FD1]. destruct SB. replace (S (S k') - 1)%nat with (S k') by lia. split; try assumption.
        * lia.
        * rewrite zero_lines_length. lia.
        * rewrite zero_lines_length. unfold rw_bytes_max. lia.
        * rewrite zero_lines_length. exact RD.
        * split; [rtc_fld RTC | exact CAN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L37672473263.66L40694246611.65L58734992898.6400000Y01601SS3sp04SPlo5fdata3msp3tsp2Ln1A1n1H1u1v1U1VS3sp05fdata3msp3tsp2Ln1u1v2WFS3sp05fdata3msp3tsp2Ln1u1v2WF". (* [comment removed for export] *)
  Lemma sifp_disjoint : forall A n, (A + n <= 0x63c0a0 \/ 0x63c180 <= A) -> disjoint_from (si_fp SI) A n.
  Proof.
    intros A n H. apply (si_fp_disjoint_gen (arl_L R) SI). intros u v Hin.
    pose proof (proj1 (Forall_forall _ _) (si_wf SI) _ Hin) as WF. simpl in WF.
    pose proof (SIFP u (in_window_not_outside _ u v u Hin ltac:(lia))) as U.
    pose proof (SIFP (v - 1) (in_window_not_outside _ u v (v - 1) Hin ltac:(lia))) as V. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59314873579.6100000MS3sp05fdata3msp3tsp2Ln1a2Ha1H". (* [comment removed for export] *)
  Lemma sifp_static : forall a, drv_static a -> outside (si_fp SI) a.
  Proof.
    intros a Ha. destruct (outside_dec (si_fp SI) a) as [O|NO]; [exact O|]. pose proof (SIFP a NO). unfold drv_static in Ha. exfalso. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma sifp_cstatic : forall a, ~ outside (si_fp SI) a -> cstatic R a.
  Proof. intros a NO. destruct (si_data SI a NO) as (D & _ & NS). split; [exact D | exact NS]. Qed.

  (* [comment removed for export] *)
  Fixpoint rsum (r : nat) : Z := match r with O => 0 | S k => FPHI + rsum k end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15043033658.58L60128343076.60L66477854252.5700000F01201HS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln1H1r3IHrS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma rsum_nonneg : forall r, 0 <= rsum r.
  Proof. pose proof (PHI_max 0 ltac:(lia)). induction r; cbn [rsum]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12206939378.59L22115751310.59L31138525880.59L31138525880.60L34368415526.59L66477854252.5700000Y01B01k02K03403JS3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln1H2HrS3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln1H2HrS3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln1H2HrS3sp05fdata4FPHI3msp3tsp2Ln1r2HrS3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln1H2HrS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma rsum_le4 : forall r, (r <= 4)%nat -> rsum r <= 4 * FPHI.
  Proof.
    pose proof (PHI_max 0 ltac:(lia)). intros r Hr.
    destruct r as [|[|[|[|[|r]]]]]; cbn [rsum]; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint fsum (r : nat) : Z := match r with O => 0 | S k => FFFR + fsum k end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15043033658.58L60392593019.60L66477854252.5700000F01201HS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln1H1r3IHrS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma fsum_nonneg : forall r, 0 <= fsum r.
  Proof. pose proof (FFR_max 0 ltac:(lia)). induction r; cbn [fsum]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L117632477.59  L5669888055.59 L61582053961.59L61582053961.60L66477854252.57L68629857646.5900000Y01B01k02K02a03JS3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln1H2HrS3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln1H2HrS3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln1H2HrS3sp05fdata4FFFR3msp3tsp2Ln1r2HrS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln1H2Hr". (* [comment removed for export] *)
  Lemma fsum_le4 : forall r, (r <= 4)%nat -> fsum r <= 4 * FFFR.
  Proof.
    pose proof (FFR_max 0 ltac:(lia)). intros r Hr.
    destruct r as [|[|[|[|[|r]]]]]; cbn [fsum]; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Fixpoint csum (q : Z) (r : nat) : Z := match r with O => 0 | S k => (1 + 2 * q) + csum q k end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15045126081.59L63232787460.6100000F00lS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln1q1r2Hq3IHr". (* [comment removed for export] *)
  Lemma csum_nonneg : forall q r, 0 <= q -> 0 <= csum q r.
  Proof. intros q r Hq. induction r; cbn [csum]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15959842002.60L19636589881.60L19636589881.61L36896474230.60L64032622029.6000000S01601S02602YS3sp04SPlo5fdata3msp3tsp2Ln1q2Hq2HrS3sp04SPlo5fdata3msp3tsp2Ln1q2Hq2HrS3sp05fdata3msp3tsp2Ln1q1r2HrS3sp04SPlo5fdata3msp3tsp2Ln1q2Hq2HrS3sp04SPlo5fdata3msp3tsp2Ln1q2Hq2Hr". (* [comment removed for export] *)
  Lemma csum_le4 : forall q r, 0 <= q -> (r <= 4)%nat -> csum q r <= 4 * (1 + 2 * q).
  Proof. intros q r Hq Hr. destruct r as [|[|[|[|[|r]]]]]; cbn [csum]; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section PLoopA.
    Variables (buf cap cl plen DATA owned : Z) (junk : list byte) (x7 : word).   (* [comment removed for export] *)
    Hypothesis Hcl : 0 <= cl.
    Hypothesis Hplen : 0 <= plen.
    Hypothesis HL : cl + 6 + plen = Ln.
    Hypothesis COK : cap_ok cap.
    Hypothesis LCAP : Ln < cap.
    Hypothesis BRANGE : 0 < buf /\ (buf + cap <= arl_stklo R \/ STKHI <= buf) /\ buf + cap <= alloc_ceiling.
    Hypothesis BLO : 0x65f000 <= buf.
    Let b1 : byte := nth 1 fdata (Z_to_bv 8 0).
    Let PAY : Z := buf + 2 + cl + 4.
    Let pay : list byte := skipn (Z.to_nat (cl + 6)) fdata.
    Let TRFm : list cell := TRFA junk x7 b1 plen PAY cl buf.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40665719618.7500000hS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen3Hcl5Hplen2HL3PAY". (* [comment removed for export] *)
    Lemma pay_len : Z.of_nat (length pay) = plen.
    Proof. subst pay. rewrite length_skipn. cbv delta [Ln] in HL. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Ltac uwc0 := apply uwc_data; [lia | rewrite STKLO; pose proof (cap_ok_bounds sp0 cap COK); rewrite ?unsigned_lit by (cbv delta [Ln] in *; lia); cbv delta [Ln] in *; lia].

    (* [comment removed for export] *)
    Record PLA (d : nat) (icb : byte) (LB : list blk) (m : mem) (mo : Model) (h : HST asegs R HIA) : Prop := MKPLA {
      pa_hm : HM asegs R HIA h LB [] m;
      pa_hk : HK asegs R HIA h mo;
      pa_htop : htop asegs R HIA h = TOP;
      pa_hstkhi : hstkhi asegs R HIA h = STKHI;
      pa_buf : In (buf, cap) LB;
      pa_owned : (owned = 0 /\ DATA = 0x63c060 /\ plen = 0)
                 \/ (owned = DATA /\ In (DATA, plen) LB /\ DATA <> buf /\ 0 < plen /\ 0x65f000 <= DATA /\ (DATA + plen <= arl_stklo R \/ STKHI <= DATA));
      pa_tx : TMEM d m;
      pa_si : si_P SI m;
      pa_stk : stk asegs m (arl_stklo R) tsp;
      pa_sshad : sshad asegs AL m (arl_stklo R) msp;
      pa_trf : rw_cells asegs m tsp TRFm;
      pa_frame : rw_cells asegs m msp (A_main_loop.FRAMEA sp0 pad);
      pa_fs : m_fs mo = fs0;
      pa_fds : m_fds mo = FDS2;
      pa_data : bytes_at asegs m DATA pay;
      pa_atx : exists (b : bool) (jp jq jf : list byte), atexit_cells b m (Z_to_bv 8 0) jp jq jf;   (* [comment removed for export] *)
      pa_incb : incbA m icb                                                                     (* [comment removed for export] *)
    }.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L11556280553.122L13178042328.122L1808768547.122 L24824263852.126L31907629586.127L33668808604.122L33668808604.126L34034126860.120L36220967052.127L37265361884.127L40836481488.122L47486133700.127L51433590761.122L53753218194.122L56303887148.122L56672648374.122L59276408844.122L62069740404.124L62069740404.128L67811799308.120L68059204647.12200000_01L02102V03E03j04O05405^06N07@08308a09P0:50:Z0;?0;i0<S0=80=]S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3pay4TRFmS1R3sp05STKLO5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4DATA3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA3PAY3pay3DLOS3sp04SPlo5fdata3pad3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a2HaS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a2HaS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay". (* [comment removed for export] *)
    Lemma PLA_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Picb,(2.&8.)PLB,(0.$3;.)PLB',(0.$3;.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pmo,$59.Pmo',$59.Ph,(3:.$5.VR,VHIA,)Ph',(3:.$5.VR,VHIA,)PW,(0.$1.)PSSP,$7.P,(62.R<.R;.R:.R8.R6.R4.)P,(40.$5.VR,R;.(1;.$3;.)Vtsp,R2.VSTKHI,R3.R9.R8.)P,(1<.(>.(0.$1.)R4.(1;.$1.))(>.(0.$1.)R4.(63.(64.VR,)VSI,)))P,(1<.(>.$7.R4.(1=.VR,))(>.$7.R4.Vtsp,))P,(3?.$5.VR,VHIA,R7.R=.(1;.$3;.)R;.)P,Pb,$3;.P,(4=.$3;.R1.R10.)(4=.$3;.R2.R10.)P,(65.$5.VR,VHIA,R9.R;.)P,(>.$7.(66.$5.VR,VHIA,R:.)VTOP,)P,(>.$7.(67.$5.VR,VHIA,R;.)VSTKHI,)P,(4.$5.R10.)P,(2;.$5.R11.(1=.VR,)Vtsp,)P,(42.$5.VAL,R12.(1=.VR,)Vtsp,)P,(68.(64.VR,)VSI,R13.)P,(>.$69.(6:.R12.)(6:.R13.))P,(>.(0.(20.(2.&40.)$5;.))(5=.R13.)(5=.R14.))(62.R1;.R1:.R18.R16.R14.R12.)")
(* [comment removed for export] *).
    Proof.
      intros * P HP HW HSSP HH' SUB HKh' HT' HS' MI' ST' SSH' SI' FS' FDS'.
      destruct P as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      assert (DW : forall A n, 0 <= n -> (A + n <= 0x63c0a0 \/ 0x63c180 <= A) -> disjoint_from W A n).
      { intros A n Hn HA. destruct HW as [-> | ->]; [exact I | apply sifp_disjoint; exact HA]. }
      assert (OW : forall a, drv_static a -> outside W a).
      { intros a Ha. destruct HW as [-> | ->]; [exact I | apply sifp_static; exact Ha]. }
      pose proof pay_len as PL.
      split.
      - exact HH'.
      - exact HKh'.
      - exact HT'.
      - exact HS'.
      - apply SUB. exact IB.
      - destruct IO as [IO|(E1 & I2 & NE & PP & DLO & DHI)]; [left; exact IO | right]. repeat split; try assumption. apply SUB. exact I2.
      - eapply tmem_presA; [exact TX | exact HP | exact OW | exact HH' | exact MI'].
      - exact SI'.
      - exact ST'.
      - eapply sshad_merge with (mid := tsp); [exact SSH' | | cbv delta [tsp msp]; lia].
        eapply (presA_sshad asegs R); [exact HP | | destruct HSSP as [-> | ->]; [rewrite STKLO|]; cbv delta [tsp]; lia | cbv delta [msp]; lia].
        eapply (proj2 (sshad_split asegs AL m (arl_stklo R) tsp msp SSH ltac:(rewrite STKLO; cbv delta [tsp msp]; lia) ltac:(cbv delta [tsp]; lia))).
      - eapply (presA_rw_cells asegs R); [exact HP | exact TR | apply client_range_stack; lia | apply DW; [cbn; lia | cbv delta [tsp]; lia]].
      - eapply (presA_rw_cells asegs R); [exact HP | exact FR | apply client_range_stack; cbv delta [tsp msp]; lia | apply DW; [cbn; lia | cbv delta [msp]; lia]].
      - rewrite FS'. exact FS.
      - rewrite FDS'. exact FDS.
      - eapply (presA_bytes_at0 asegs R); [exact HP | exact BY |].
        destruct IO as [(E0 & ED & P0)|(E1 & I2 & NE & PP & DLO & DHI)].
        + left. apply Nat2Z.inj. rewrite PL, P0. reflexivity.
        + right. rewrite PL. split; [| apply DW; lia].
          eapply client_range_block; [apply in_app_iff; left; exact I2 | lia | lia].
      - destruct AX as (bb & jp & jq & jf & AT). exists bb, jp, jq, jf. unfold atexit_cells in *.
        eapply (presA_rw_cells asegs R); [exact HP | exact AT | | apply DW; cbn; lia].
        intros a Ha. right; left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. cbn in Ha. lia.
      - unfold incbA in *.
        eapply (presA_rw_cells asegs R); [exact HP | exact IC | | apply DW; cbn; lia].
        intros a Ha. right; left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. cbn in Ha. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01e0@L10628004972.118L1206758680.117 L12225543046.121L12225543046.124L12602198444.118L12846170758.121L12846170758.124L14062937730.121L14188274840.118L14283716567.118L14283716567.121L14497567600.118L1606732508.114 L1606732508.117 L16575326386.121L1853829068.117 L18817334409.121L19049459228.118L19096133232.118L19272480902.121L19272480902.124L20694033836.118L20700440712.124L2095639644.118 L21011301036.118L21547560088.118L21894298876.121L2295424837.121 L22961087404.118L24223726296.118L2480226220.118 L26644621732.124L26796267641.121L26796267641.124L27136647223.121L27318640032.122L27916485768.118L28652226200.118L29067581395.121L29067581395.124L2955598764.118 L29590676208.118L29760312048.118L30361372897.122L30392913836.118L30410317833.117L31565860720.118L3185220848.118 L33353266169.121L33353266169.124L33671248953.117L33671248953.121L33888846021.117L34181487708.118L34338576542.117L35717735916.118L37213846903.117L37263706233.122L3786729798.120 L3788567612.122 L37953479920.118L38198049944.118L39551380764.118L4002499824.118 L40576827760.118L40823179312.118L41167373682.124L42144144434.124L42874000286.117L43177478534.121L43177478534.124L43212770862.121L43212770862.124L4330372012.118 L44797254407.121L4520065196.118 L46830269592.118L47873876682.122L48617929584.118L50204620208.117L50682474156.118L50969839064.118L5108865519.121 L51437027308.118L51703474364.121L52463682185.121L53523280556.118L53761255088.117L53909669640.118L5409953996.117 L54597810860.118L55384519816.124L56361651456.118L59125168605.124L59315137787.122L60084165372.118L60397718152.121L60397718152.124L60555157513.117L61564352624.118L62022224981.117L62071574159.121L63370423024.118L64182550988.117L6427517080.118 L66032793580.118L66777190920.121L66777190920.124L67250057441.122L67446269592.118L6753814880.118 L67550707884.118L67739202252.117L68056928130.117L6966484972.118 L9925190316.118 L9965028060.124 00000\01P02502Z03?03d04I04n05X06D07007U08?09i0:N0;80;]0<B0<g0=L0>10>V0?@0?e0@J0A40A`0BJ0Bo0CY0D>0D?0D@0DA0Df0ET0F>0Fh0GM0H20HW0I<0Ia0JT0K90K^0LC0Lh0Li0Lj0MO0N40N^0OC0Om0PR0Q70Qg0RX0SL0T10T[0U@0Ue0VJ0Vo0WT0X90Xc0YH0Ym0Za0[U0\:0]i0^N0_80`d0aI0an0bS0c=0d>0dc0eO0f40fY0g>0gh0hR0i70ia0jF0k00k`0lL0m10mV0n;0n`0oG10010U11?11i12N13313X14K15515Z16?16i17N18318X19BS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H4S1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H2S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H2S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1x2NOS1R1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen3Hcl2HL4LCAP6BRANGE3PAY3pay1w2W12W21x2NOS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1w2W1S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payFFFS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4DATA3PAY3pay3DLOS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA3PAY3pay3DLOS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payFFS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3pay1x2Hx1XS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY3pay1x2HxS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY3payS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS1R1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen3Hcl2HL4LCAP6BRANGE3PAY3pay1w2W12W21A1n2H12H4S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS1R1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen4DATA3Hcl2HL4LCAP6BRANGE3PAY3pay2NE2PP3DHIS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS1R3sp04SPlo5STKLO5fdata3TOP6HTOPlo3msp3tsp2Ln3buf2cl3PAY3pay1a1XS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1w2W1S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1w2W1S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3pay1a1H1XS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n2H3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS1R3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a1XS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA3PAY3pay3DLOS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1w2W2". (* [comment removed for export] *)
    Lemma PLA_munch : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Pd',$36.Picb,(2.&8.)PLB,(0.$3;.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pmo,$59.Pmo',$59.Ph,(3:.$5.VR,VHIA,)PW,(0.$1.)P,(62.R:.R8.R7.R6.R4.R2.)P,(6.R2.R7.R6.)P,(2:.$5.R8.R7.)P,(6;.R9.R8.)P,(1<.(>.(0.$1.)R5.(13.(20.$7.$7.)(21.$7.$7.(1>.Vtsp,+1000.)Vtsp,)(13.(20.$7.$7.)(21.$7.$7.+?:578.+?:660.)(13.(20.$7.$7.)(21.$7.$7.+65=1:0.+65=1:1.)(1;.(20.$7.$7.))))))(23.$7.Lw,$7.(8.(9.+65=1:0.R1.)(8.(9.(1:.R1.+2.)+65=1:8.)(>.(0.$1.)R6.(13.(20.$7.$7.)(21.$7.$7.(1>.Vtsp,+1000.)Vtsp,)(13.(20.$7.$7.)(21.$7.$7.+?:578.+?:57<.)(13.(20.$7.$7.)(21.$7.$7.+?:5:0.+?:5:8.)(13.(20.$7.$7.)(21.$7.$7.R1.(1:.R1.+2.))(1;.(20.$7.$7.)))))))))))P,(6<.R>.R:.)P,(65.$5.VR,VHIA,R8.R9.)P,(>.$69.(6:.R:.)(6:.R;.))P,(>.(0.(20.(2.&40.)$5;.))(5=.R;.)(5=.R<.))(62.R12.R11.R10.R>.R<.R;.)")
(* [comment removed for export] *).
    Proof.
      intros * P MU WM GR HW OS' HKh' FS' FDS'.
      destruct P as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof pay_len as PL. pose proof (u64_range sp0) as SPR.
      assert (DJ : forall A n, 0 <= A -> 0 <= n -> (A + n <= tsp - 4096 \/ tsp <= A) -> (A + n <= 0x0fa578 \/ 0x0fa660 <= A) ->
                   (A + n <= 0x65d1a0 \/ 0x65d1a8 <= A) -> disjoint_from W A n).
      { intros A n H0 H1 H2 H3 H4. destruct HW as [-> | (w & W1 & W2 & ->)]; cbn; repeat split; lia. }
      assert (WIN : forall x, ~ outside W x -> (tsp - 4096 <= x < tsp) \/ (0x0fa578 <= x < 0x0fa660) \/ (0x65d1a0 <= x < 0x65d1a8)).
      { intros x NO. destruct HW as [-> | (w & W1 & W2 & ->)]; cbn in NO; lia. }
      assert (HH' : HM asegs R HIA h LB [] m').
      { eapply (hm_munch _ _ HIA); [exact HH | exact MU | exact WM |].
        apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha.
        destruct (WIN a (in_window_not_outside _ lo hi a Hin Ha)) as [X|[X|X]].
        - left. left. rewrite HT. cbv delta [tsp] in X. lia.
        - left. right. left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia.
        - left. right. left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      assert (MI' : mem_inv asegs m').
      { eapply mem_inv_munch; [exact (xm_mi _ _ _ _ _ (tx_x _ _ TX)) | exact MU |].
        intros x Hx NO. destruct (WIN x NO) as [X|[X|X]]; apply ro_addr_geA; cbv delta [tsp] in *; lia. }
      split.
      - exact HH'.
      - exact HKh'.
      - exact HT.
      - exact HS.
      - exact IB.
      - exact IO.
      - destruct (xmem_munchW W m m' h LB [] (tx_x _ _ TX) (tx_can _ _ TX) MU WM HH' MI') as [XM' CAN'].
        { intros a n Hin. unfold xmem_cells in Hin. cbn [In] in Hin.
          repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; apply DJ; cbv delta [tsp]; lia |]). destruct Hin. }
        split; [exact XM' | exact CAN' | exact OS'].
      - eapply (si_munch (arl_L R) SI); [exact SIm | exact MU |]. intros a NO. pose proof (SIFP a NO).
        destruct (outside_dec W a) as [O|NO']; [exact O|]. destruct (WIN a NO') as [X|[X|X]]; cbv delta [tsp] in *; exfalso; lia.
      - eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. right.
        destruct ST as (_ & _ & S3). destruct (S3 x Hx) as [_ (b & Hb)]. unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E0.
        + destruct (m' (wa x)) as [b2|] eqn:E1; [exists b2; reflexivity|]. exfalso. apply (GR (wa x)); [congruence | exact E1].
        + exfalso. pose proof (A_exit_lib.seg_rom_high x ltac:(unfold AIMG_HI; rewrite STKLO in Hx; cbv delta [tsp] in Hx; lia)) as SR. rewrite SR in Hb. discriminate.
      - eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [apply (hcs_ok _ _ HIA h) | | | exact MU | exact WM | exact SSH].
        + unfold w_client. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
          pose proof (hcs_img _ _ HIA h) as HCSI. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. destruct IMG' as (HGOT & HILO & HIHI & HGSB2).
          destruct HW as [-> | (w & W1 & W2 & ->)]; cbn in Hin;
            repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <- |]); try (destruct Hin; fail);
            first [ eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS; cbv delta [tsp]; lia]
                  | apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia ].
        + eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia].
      - eapply rw_cells_transport; [exact TR | exact MU | exact WM | apply DJ; cbv delta [tsp]; cbn; lia].
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM | apply DJ; cbv delta [tsp msp]; cbn; lia].
      - rewrite FS'. exact FS.
      - rewrite FDS'. exact FDS.
      - eapply bytes_at_transport0; [exact BY | exact MU |].
        destruct IO as [(E0 & ED & P0)|(E1 & I2 & NE & PP & DLO & DHI)].
        + left. apply Nat2Z.inj. rewrite PL, P0. reflexivity.
        + right. rewrite PL. apply DJ; first [lia | cbv delta [tsp] in *; rewrite STKLO in *; lia].
      - destruct AX as (bb & jp & jq & jf & AT). exists bb, jp, jq, jf. unfold atexit_cells in *.
        eapply rw_cells_transport; [exact AT | exact MU | exact WM | apply DJ; cbv delta [tsp]; cbn; lia].
      - unfold incbA in *.
        eapply rw_cells_transport; [exact IC | exact MU | exact WM | apply DJ; cbv delta [tsp]; cbn; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L1206709400.114 L14416692944.114L15954172057.118L1870712294.118 L1877007115.117 L23857495836.114L25745385367.116L27414129180.114L60027729699.114L62022307285.114L62069740404.115L64282238065.11900000d01O02402^03G04104`05J06406[07E088S1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1A1n1HS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a2HbS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a1HS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3pay1x2HxS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1x2HxS1R3sp05fdata3msp3tsp2Ln3buf2cl3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl3PAY3pay1a2HaS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA3PAY3pay3DLO". (* [comment removed for export] *)
    Lemma PLA_incb : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Picb,(2.&8.)PLB,(0.$3;.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pmo,$59.Pmo',$59.Ph,(3:.$5.VR,VHIA,)Pv,(2.&8.)P,(62.R9.R8.R7.R6.R4.R2.)P,(6.(13.(20.$7.$7.)(21.$7.$7.+63<054.+63<055.)(1;.(20.$7.$7.)))R7.R6.)P,(2:.$5.R8.R7.)P,(4.$5.R8.)P,(46.R9.R5.)P,(65.$5.VR,VHIA,R7.R8.)P,(>.$69.(6:.R9.)(6:.R:.))P,(>.(0.(20.(2.&40.)$5;.))(5=.R:.)(5=.R;.))(62.R11.R9.R?.R=.R;.R:.)")
(* [comment removed for export] *).
    Proof.
      intros * P MU WM MI' IC' HKh' FS' FDS'.
      destruct P as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof pay_len as PL. pose proof (u64_range sp0) as SPR.
      assert (DJ : forall A n, (A + n <= 0x63c054 \/ 0x63c055 <= A) -> disjoint_from [(0x63c054, 0x63c055)] A n).
      { intros A n H. cbn. split; [lia | exact I]. }
      assert (FCS : crange (hcs asegs R HIA h) 0x63c054 1).
      { intros x Hx. apply (hcs_static _ _ HIA h). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      assert (HH' : HM asegs R HIA h LB [] m').
      { eapply (hm_munch _ _ HIA); [exact HH | exact MU | exact WM |].
        constructor; [| constructor]. cbn [fst snd]. intros a Ha. left. right. left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      split.
      - exact HH'.
      - exact HKh'.
      - exact HT.
      - exact HS.
      - exact IB.
      - exact IO.
      - eapply tmem_munch; [exact TX | exact MU | exact WM | | exact HH' | exact MI'].
        intros a (Ha & Hb & Hc). cbn. split; [| exact I]. unfold drv_static in Ha. lia.
      - eapply (si_munch (arl_L R) SI); [exact SIm | exact MU |]. intros a NO. pose proof (SIFP a NO). cbn. split; [lia | exact I].
      - eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. left. cbn. split; [| exact I]. rewrite STKLO in Hx. cbv delta [tsp] in Hx. lia.
      - eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [apply (hcs_ok _ _ HIA h) | | | exact MU | exact WM | exact SSH].
        + unfold w_client. constructor; [cbn [fst snd]; exact FCS | constructor].
        + eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia].
      - eapply rw_cells_transport; [exact TR | exact MU | exact WM | apply DJ; cbv delta [tsp]; cbn; lia].
      - eapply rw_cells_transport; [exact FR | exact MU | exact WM | apply DJ; cbv delta [tsp msp]; cbn; lia].
      - rewrite FS'. exact FS.
      - rewrite FDS'. exact FDS.
      - eapply bytes_at_transport0; [exact BY | exact MU |].
        destruct IO as [(E0 & ED & P0)|(E1 & I2 & NE & PP & DLO & DHI)].
        + left. apply Nat2Z.inj. rewrite PL, P0. reflexivity.
        + right. rewrite PL. apply DJ. cbv delta [tsp] in *; rewrite STKLO in *; lia.
      - destruct AX as (bb & jp & jq & jf & AT). exists bb, jp, jq, jf. unfold atexit_cells in *.
        eapply rw_cells_transport; [exact AT | exact MU | exact WM | apply DJ; cbn; lia].
      - exact IC'.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L15047374368.124L1540133238.124 L1705593193.125 L1810845757.124 L21170156300.124L27318997019.124L31909676044.124L34049303407.124L36218918546.124L39428222624.124L39443160219.157L45098317904.124L47406669953.124L48978835966.125L53751171724.124L54158214119.127L57428283056.124L5973000491.157 L62022713838.124L62200254563.124L68247433648.124L8913396782.124 00000`01P02W03G04A05B06707J08?0990:30;;0<60=;0>50?<0@D0A40Af0C60D60DkS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY3pay1HS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3pay2D03DLOS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3payS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3pay3DHIS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3payS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY3pay2CBS3sp05fdata3TOP6HTOPlo3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS1R3HIA3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3pay1m1h2P02HnS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS1R3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen4DATA5Hplen3PAY3pay2LB2P01a2HaS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY3pay2CBS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS1R3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen4DATA3Hcl5Hplen2HL4LCAP3PAY3pay2D02CBS3sp05fdata4FSTK:FSTK_range3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3payS3sp04SPhi5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY3pay". (* [comment removed for export] *)
    Lemma fuzz_callA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Picb,(2.&8.)PLB,(0.$3;.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3,(2.&40.)Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)PT,$6=.P,(62.R16.R15.R14.R4.R3.R2.)P,(9.(1:.(6>.$5.VR,VHIA,R3.)A1.VPHI,Vplen,)$6?.)P,(9.(1:.(70.$5.VR,VHIA,R4.)A1.VFFR,Vplen,)$71.)P,(9.(1:.(1:.(1:.(72.R17.)+1.)(43.+2.(50.Vplen,+1701.)))VC24f,)$73.)P,A1.R5.(1;.$74.)P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)Pm',P,(2.&40.)(3.(2.&8.))Pmo',$59.Ph',(3:.$5.VR,VHIA,)PLBx,(0.$3;.)P,(62.R2=.R2<.(75.$3;.R1.R2;.)R4.R3.R2.)P,(9.(6>.$5.VR,VHIA,R3.)(1:.(6>.$5.VR,VHIA,R1:.)A1.VPHI,Vplen,))P,(9.(70.$5.VR,VHIA,R4.)(1:.(70.$5.VR,VHIA,R1;.)A1.VFFR,Vplen,))P,(9.(72.(75.$3;.R4.R2>.))(1:.(1:.(72.R2>.)+1.)(43.+2.(50.Vplen,+1701.))))(76.$5.(77.(24.(47.(17.&40.+9747<.)R16.R15.R14.(17.&40.=)R13.R12.R11.R10.R?.R>.R=.(17.&40.=)(17.&40.-2.)R<.R;.R:.R9.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)R21.R20.)(26.&5.(2.&40.))(17.&40.+9747<.)(17.&20.=)(27.(2.&40.))R8.(28.$5.))R7.)R1<.)(76.$5.(77.(24.(47.(17.&40.+9747<.)R19.R18.R17.(17.&40.VDATA,)(17.&40.Vplen,)R16.R15.R14.R13.R12.R11.(17.&40.=)(17.&40.-2.)R10.R?.R>.R=.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)R<.R;.)(26.&5.(2.&40.))(17.&40.$48.)(17.&20.=)(27.(2.&40.))R:.(28.$5.))R9.)R7.)")
(* [comment removed for export] *).
    Proof.
      intros * P HV HFR HC24 Tnil HC. pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof pay_len as PL. pose proof (cap_ok_bounds sp0 cap COK) as CB. pose proof (u64_range sp0) as SPR.
      unfold TREGS.
      eapply srzJ_of_aevtS; [ | exact Tnil | ].
      { eapply (FUZZ h LB [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) m mo DATA plen (arl_stklo R) (arl_stklo R) pay);
          rewrite ?unsigned_lit by (cbv delta [tsp]; lia).
        - exact HH.
        - exact HKh.
        - exact BY.
        - exact PL.
        - cbv delta [Ln] in *. lia.
        - destruct IO as [(_ & D0 & _)|(_ & _ & _ & _ & DLO & _)]; lia.
        - destruct IO as [(_ & D0 & P0)|(_ & I2 & _ & _ & _ & _)]; [intros a Ha; lia |].
          eapply client_range_block; [apply in_app_iff; left; exact I2 | lia | lia].
        - intros Hn. destruct IO as [(_ & _ & P0)|(_ & I2 & _)]; [lia |]. eapply (hm_aobj_block _ _ HIA h); [exact HH | exact I2].
        - destruct IO as [(_ & D0 & _)|(_ & _ & _ & _ & _ & DHI)]; [left; rewrite STKLO; lia | ]. cbv delta [tsp]. rewrite STKLO in DHI. lia.
        - destruct IO as [(_ & _ & P0)|(_ & I2 & _)]; [left; exact P0|]. eapply (A_rt_facts.blk_top47_sub _ _ HIA h); [exact HH| exact I2| lia].
        - exact ST.
        - eapply (proj1 (sshad_split asegs AL m (arl_stklo R) tsp msp SSH ltac:(rewrite STKLO; cbv delta [tsp msp]; lia) ltac:(cbv delta [tsp]; lia))).
        - lia.
        - lia.
        - rewrite STKLO. cbv delta [tsp]. lia.
        - rewrite HT. cbv delta [tsp]. lia.
        - cbv delta [tsp]. lia.
        - cbv delta [tsp]. lia.
        - exact (xm_mi _ _ _ _ _ (tx_x _ _ TX)).
        - rewrite HTP. reflexivity.
        - exact SIm.
        - exact HV.
        - uwc0.   (* [comment removed for export] *)
        - exact HFR.
        - exact HC24.
        - cbn. lia.
        - reflexivity.
        - reflexivity. }
      intros c (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mo' & h' & LBx & -> & MI' & ST' & SSH' & MF & HP & HT' & HS' & HF' & HKh' & HCS' & HV' & HFR' & HH' & SI' & C24').
      reg_lit 0x09747c. rewrite ?unsigned_lit in ST', SSH', HP by (cbv delta [tsp]; lia).
      apply (HC _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' h' LBx); [| exact HV' | exact HFR' | exact C24'].
      eapply (PLA_presA d icb LB (LBx ++ LB) m m' mo mo' h h' (si_fp SI) tsp P); try eassumption.
      - rewrite <- HS. exact HP.
      - right. reflexivity.
      - right. reflexivity.
      - intros b Hb. apply in_app_iff. right. exact Hb.
      - rewrite HT'. exact HT.
      - rewrite HS'. exact HS.
      - apply (A_main_fin.mo_frame_fs _ _ MF).
      - apply (A_main_fin.mo_frame_fds _ _ MF).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L11646182908.123L1540038358.147 L1563080444.123 L17141005533.123L17425310856.123L21157130668.123L29067581395.123L33124412637.123L35142027400.123L36289747910.123L39428382976.147L39440886784.123L42684309056.147L50454542171.123L53948502780.123L57404987900.123L9054834425.123 00000Q01201S02402U03@03a04B04c05I06406_07@08008Q09209XS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAYS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAYS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp05fdata3msp3tsp2Ln3buf2cl3PAYS3sp04SPhi5fdata3msp3tsp2Ln3buf2cl3PAY". (* [comment removed for export] *)
    Lemma printf1_callA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Picb,(2.&8.)PLB,(0.$3;.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)PT,$6=.P,(62.#0.R15.R14.R4.R3.R2.)P,A1.R2.(1;.$74.)P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa0',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)Pm',P,(2.&40.)(3.(2.&8.))Pmo',$59.P,(62.#1.R28.R27.R2.R1.R15.)(76.$5.(77.(24.(47.(17.&40.+9748<.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.(17.&40.=)(17.&40.-2.)R7.R6.R5.R4.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)(17.&40.=)R19.)(26.&5.(2.&40.))(17.&40.+9748<.)(17.&20.=)(27.(2.&40.))R3.(28.$5.))R2.)R15.)(76.$5.(77.(24.(47.(17.&40.+9748<.)R16.R15.R14.R13.(17.&40.=)R12.R11.R10.R?.R>.R=.(17.&40.=)(17.&40.-2.)R<.R;.R:.R9.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)(17.&40.=)R8.)(26.&5.(2.&40.))(17.&40.+97538.)(17.&20.=)(27.(2.&40.))R7.(28.$5.))R6.)(78.(79.+1.(60.#1.))R4.))")
(* [comment removed for export] *).
    Proof.
      intros * P Tnil HC. pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof (u64_range sp0) as SPR. pose proof (hcs_img _ _ HIA h) as HCSI.
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. destruct IMG' as (HGOT & HILO & HIHI & HGSB2).
      unfold TREGS. change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
      eapply (printf1A AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h) (Z_to_bv 64 tsp) mo);
        rewrite ?unsigned_lit by (cbv delta [tsp]; lia).
      - cbv delta [tsp]. lia.
      - cbv delta [tsp]. lia.
      - cbv delta [tsp]. lia.
      - exact HKh.
      - rewrite FDS. reflexivity.
      - eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS; cbv delta [tsp]; lia].
      - apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia.
      - apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - eapply pf_of_tmem; [exact TX | exact HH | exact ST | exact SSH].
      - exact Tnil.
      - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 PP HK2 MM2.
        unfold mkR. norm_getr. fold mkR.
        apply (HC t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2).
        destruct PP as [AG MU GR WM SOB]. rewrite ?unsigned_lit in MU, AG by (cbv delta [tsp]; lia).
        eapply (PLA_munch 0 1 icb LB m m2 mo mo2 h _ P MU WM GR).
        + left. reflexivity.
        + cbn [out_state]. split; [| split; [reflexivity | lia]]. replace (0x65d1a0 + 2 * Z.of_nat 0) with 0x65d1a0 by lia. exact SOB.
        + exact HK2.
        + apply (mo_mat_fs _ _ MM2).
        + apply (A_main_fin.mo_mat_fds _ _ MM2).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0100@L10406873899.159L10547991579.171L11658948059.125L12512416027.171L13982118556.159L14521258047.159L14801818406.159L1575845595.125 L1610387797.171 L16369078365.171L16545862365.171L17136710906.126L17421216943.126L1897397915.171 L20102498269.171L20169984883.159L21157523859.127L2303432736.154 L23549655718.177L23562828701.171L26981515745.177L27225304192.155L27684404864.154L27943126933.171L28403215219.159L29067581395.124L33128293626.125L33496824795.171L33888933260.171L35138240687.125L36290141177.127L37674684739.128L38281479133.171L38961105429.171L39043373723.171L39428382976.154L39440755775.127L39966973077.171L41011730331.171L42100783131.171L42684309056.154L44382264686.159L48149747674.159L49643842843.171L50454542171.124L52019902869.171L52056694683.171L52684048477.171L53944474331.126L56238079325.171L5700204893.171 L57371911963.171L57400693211.126L58022570773.171L60004920541.171L60546936981.171L60742066177.155L64376901173.159L66031090011.177L66566382101.171L67098810077.171L7379809173.171 L9054703302.127 L9870753557.171 00000Y01B01h02Q03:03c04L05205[06D06m07S08908b09K0:>0:l0;P0=C0=l0>\0?L0@00@Y0AG0Am0BS0C<0Co0DU0E>0Fh0GQ0H:0Hc0IQ0J?0Jh0KQ0L:0L^0MQ0ND0Nm0Ob0PK0Q40Q]0RC0Rl0SU0T>0Td0UM0V60V_0WO0XB0Y20Y[0ZD0Zm0[V0\?S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2Hw2K3S3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY2HkS1R1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen3Hcl2HL4LCAP6BRANGE3PAY1k2Hk1w2Hw2K31a1n2H12H22H3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K31a1n2H1S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2HwS3sp05fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2Hw2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp05fdata3msp3tsp2Ln3buf2cl4plen4DATA5owned3PAY2k'2t02t12t22a02a22a32a42a52a62a72t32t42t52t61r1m2mo1T2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2Hw2K3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2Hw2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2HwS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk1w2Hw2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K31a1n2H2S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3S3sp04SPhi5fdata3msp3tsp2Ln3buf2cl3PAY2HkS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1k2Hk2K3". (* [comment removed for export] *)
    Lemma printfN_callA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pk,$36.Picb,(2.&8.)PLB,(0.$3;.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)PT,$6=.P,(62.(7:.R16.)R15.R14.R4.R3.R2.)P,(5:.R17.#2.)P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa0',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)Pm',P,(2.&40.)(3.(2.&8.))Pmo',$59.P,(62.(7:.(7:.R29.))R28.R27.R2.R1.R15.)(76.$5.(77.(24.(47.(17.&40.+9748<.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.(17.&40.=)(17.&40.-2.)R7.R6.R5.R4.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)(17.&40.=)R19.)(26.&5.(2.&40.))(17.&40.+9748<.)(17.&20.=)(27.(2.&40.))R3.(28.$5.))R2.)R15.)(76.$5.(77.(24.(47.(17.&40.+9748<.)R16.R15.R14.R13.(17.&40.=)R12.R11.R10.R?.R>.R=.(17.&40.=)(17.&40.-2.)R<.R;.R:.R9.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)(17.&40.=)R8.)(26.&5.(2.&40.))(17.&40.+97538.)(17.&20.=)(27.(2.&40.))R7.(28.$5.))R6.)R4.)")
(* [comment removed for export] *).
    Proof.
      intros * P Hk HC. pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof (u64_range sp0) as SPR. pose proof (hcs_img _ _ HIA h) as HCSI.
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. destruct IMG' as (HGOT & HILO & HIHI & HGSB2).
      assert (WCS : crange (hcs asegs R HIA h) (tsp - 4096) 4096).
      { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS; cbv delta [tsp]; lia]. }
      assert (FCS : crange (hcs asegs R HIA h) 0x156c0 64) by (apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia).
      assert (BCS : crange (hcs asegs R HIA h) 0x65d180 128) by (apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia).
      unfold TREGS. change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
      assert (POSTK : forall (w : Z) m2 mo2 (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        w = 0x65d1a0 + 2 * Z.of_nat k ->
        munch [(tsp - 4096, tsp); (0x0fa578, 0x0fa57c); (0x0fa5a0, 0x0fa5a8); (w, w + 2)] m m2 -> mem_grows m m2 -> wmono asegs m m2 ->
        rdn asegs m2 (Z_to_bv 64 0x0fa578) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5)) ->
        rdn asegs m2 (Z_to_bv 64 0x0fa5a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (w + 2))) ->
        rdn asegs m2 (Z_to_bv 64 w) 1 = Some [Z_to_bv 8 48] -> rdn asegs m2 (Z_to_bv 64 (w + 1)) 1 = Some [Z_to_bv 8 10] ->
        HK asegs R HIA h mo2 -> mo_mat mo mo2 ->
        srealizesJ asegs (mkCfg (MS (mkR (Z_to_bv 64 0x09748c) (Z_to_bv 64 tsp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0' t1' t2'
                                          (Z_to_bv 64 plen) (Z_to_bv 64 DATA) a0' a1' a2' a3' a4' a5' a6' a7'
                                          (Z_to_bv 64 owned) (Z_to_bv 64 0) (Z_to_bv 64 0x63c050) (Z_to_bv 64 r) LS6 LS7
                                          (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3' t4' t5' t6')
                                   bvmap_empty (Z_to_bv 64 0x09748c) (Z_to_bv 32 0) None m2 (seg_rom asegs)) mo2) T).
      { intros w m2 mo2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hw MU GR WM FL WP NB0 NB1 HK2 MM2.
        assert (NB : rdn asegs m2 (Z_to_bv 64 w) 2 = Some [Z_to_bv 8 48; Z_to_bv 8 10]).
        { change 2%nat with (1 + 1)%nat. change [Z_to_bv 8 48; Z_to_bv 8 10] with ([Z_to_bv 8 48] ++ [Z_to_bv 8 10]).
          apply rdn_app_Z; [exact NB0 | exact NB1 | lia | lia]. }
        apply (HC t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2).
        pose proof (tx_out _ _ TX) as OS. cbn [out_state] in OS. destruct OS as (SB & RD & K3).
        eapply (PLA_munch (S k) (S (S k)) icb LB m m2 mo mo2 h _ P MU WM GR).
        - right. exists w. split; [lia|]. split; [lia|]. reflexivity.
        - cbn [out_state]. split; [| split; [| lia]].
          + destruct SB as [F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11].
            assert (KEEP : forall (a : Z) n bs, 0x0fa57c <= a -> a + Z.of_nat n <= 0x0fa660 -> (a + Z.of_nat n <= 0x0fa5a0 \/ 0x0fa5a8 <= a) ->
                      rdn asegs m (Z_to_bv 64 a) n = Some bs -> rdn asegs m2 (Z_to_bv 64 a) n = Some bs).
            { intros a n bs H1 H2 H3 H. eapply rdn_munch; [exact MU | cbn; cbv delta [tsp]; lia | lia | lia | exact H]. }
            split; first [ exact FL
                         | replace (0x65d1a0 + 2 * Z.of_nat (S k)) with (w + 2) by lia; exact WP
                         | (eapply KEEP; [cbn; lia | cbn; lia | cbn; lia | eassumption]) ].
          + replace (2 * S k)%nat with (2 * k + 2)%nat by lia.
            replace (zero_lines (S k)) with (zero_lines k ++ [Z_to_bv 8 48; Z_to_bv 8 10]).
            2:{ change [Z_to_bv 8 48; Z_to_bv 8 10] with (zero_lines 1). rewrite <- zero_lines_app. f_equal. lia. }
            apply rdn_app_Z; [| replace (0x65d1a0 + Z.of_nat (2 * k)) with w by lia; exact NB | lia | lia].
            eapply rdn_munch; [exact MU | cbn; cbv delta [tsp]; lia | lia | lia | exact RD].
        - exact HK2.
        - apply (mo_mat_fs _ _ MM2).
        - apply (A_main_fin.mo_mat_fds _ _ MM2). }
      destruct k as [|[|[|k']]]; [ | | | lia].
      - eapply (A_printfN0.printfNA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (Z_to_bv 64 tsp) mo);
          rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
          [ cbv delta [tsp]; lia | cbv delta [tsp]; lia | cbv delta [tsp]; lia
          | exact HKh | exact WCS | exact FCS | exact BCS
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | eapply pn0_of_tmem; [exact TX | exact HH | exact ST | exact SSH] | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 PP HK2 MM2. unfold mkR. norm_getr. fold mkR.
        destruct PP as [AG MU GR WM FL WP NB0 NB1]. unfold A_printfN0.WP in *. rewrite ?unsigned_lit in MU by (cbv delta [tsp]; lia).
        eapply (POSTK 0x65d1a0); [cbn; lia | exact MU | exact GR | exact WM | exact FL | exact WP | exact NB0 | exact NB1 | exact HK2 | exact MM2].
      - eapply (A_printfN2.printfNA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (Z_to_bv 64 tsp) mo);
          rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
          [ cbv delta [tsp]; lia | cbv delta [tsp]; lia | cbv delta [tsp]; lia
          | exact HKh | exact WCS | exact FCS | exact BCS
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | eapply pn2_of_tmem; [exact TX | exact HH | exact ST | exact SSH] | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 PP HK2 MM2. unfold mkR. norm_getr. fold mkR.
        destruct PP as [AG MU GR WM FL WP NB0 NB1]. unfold A_printfN2.WP in *. rewrite ?unsigned_lit in MU by (cbv delta [tsp]; lia).
        eapply (POSTK 0x65d1a2); [cbn; lia | exact MU | exact GR | exact WM | exact FL | exact WP | exact NB0 | exact NB1 | exact HK2 | exact MM2].
      - eapply (A_printfN4.printfNA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (Z_to_bv 64 tsp) mo);
          rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
          [ cbv delta [tsp]; lia | cbv delta [tsp]; lia | cbv delta [tsp]; lia
          | exact HKh | exact WCS | exact FCS | exact BCS
          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | eapply pn4_of_tmem; [exact TX | exact HH | exact ST | exact SSH] | ].
        intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 PP HK2 MM2. unfold mkR. norm_getr. fold mkR.
        destruct PP as [AG MU GR WM FL WP NB0 NB1]. unfold A_printfN4.WP in *. rewrite ?unsigned_lit in MU by (cbv delta [tsp]; lia).
        eapply (POSTK 0x65d1a4); [cbn; lia | exact MU | exact GR | exact WM | exact FL | exact WP | exact NB0 | exact NB1 | exact HK2 | exact MM2].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L13298636584.117L4728183951.111 L62516623220.11700000V01H02:S3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1d2rv2Hd3HrvS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1d2rv2Hd3Hrv". (* [comment removed for export] *)
    Lemma ret_finA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.Prv,$7.PLB,(0.$3;.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)P,(5:.R14.#4.)P,(1<.(>.$7.R14.=)(>.$7.R14.+2.))P,(3?.$5.VR,VHIA,R3.R14.(1;.$3;.)R5.)P,(4=.(20.$7.$7.)(21.$7.$7.Vbuf,Vcap,)R15.)P,(65.$5.VR,VHIA,R5.R6.)P,(>.$7.(66.$5.VR,VHIA,R6.)VTOP,)P,(>.$7.(67.$5.VR,VHIA,R7.)VSTKHI,)P,(9.(1:.(6>.$5.VR,VHIA,R8.)$7;.)$6?.)P,(9.(1:.(70.$5.VR,VHIA,R9.)(7<.=))$71.)P,(>.$69.(6:.R;.)Vfs0,)P,(>.(0.(20.(2.&40.)$5;.))(5=.R<.)$7=.)P,(3<.R1?.R>.)P,(7>.R?.)P,(2<.$5.R10.Vmsp,(7?.Vsp0,Vpad,))P,(2;.$5.R11.(1=.VR,)Vmsp,)(76.$5.(77.(24.(49.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.Vx7,R16.R15.R14.R13.R22.Vbuf,Vcl,Vplen,Vb1,)(26.&5.(2.&40.))(17.&40.+97254.)(17.&20.=)(27.(2.&40.))R12.(28.$5.))R11.)(78.(79.+1.(60.(61.R23.#1.)))(80.(81.(4:.R22.Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      intros * Hd Hrv HH IB HKh HT HS HV HFR FS FDS TX ATX FR ST.
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKh | apply (M1_steps (hcs asegs R HIA h)); lia |].
      cbn beta. intros ms1 mo1 (ra' & a0' & a1' & ->) HK1 MM1.
      eapply (finA R HIA HID IMG ASB HFREE HTP HIMGCS sp0 SPlo SPhi SPal STKLO fs0 tid wp0 rp0 TOP STKHI HTOPlo HSTKHI pad
                (status rv b1) (zero_lines (d - 1)) buf cap LB);
        [ exact HH | exact IB | exact HK1 | exact HT | exact HS | exact HV | exact HFR
        | rewrite (mo_mat_fs _ _ MM1); exact FS
        | exact (tx_x _ _ TX)
        | eapply (xout_of_tmem d m mo1 h LB []); [exact TX | exact Hd | rewrite (A_main_fin.mo_mat_fds _ _ MM1), FDS; reflexivity | exact HH]
        | exact ATX
        | exact FR | exact ST
        | unfold status; destruct (128 <=? bv_unsigned b1); lia ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L43985082463.8300000dS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1A1B1k1r3Hne1e". (* [comment removed for export] *)
    Lemma in_lb_remove : forall (A B k : Z) (LB : list blk), In (B, k) LB -> B <> A -> In (B, k) (lb_remove A LB).
    Proof.
      intros A B k LB. induction LB as [|b r IH]; intros HIn Hne; [destruct HIn|].
      cbn [lb_remove]. destruct HIn as [->|HIn].
      - cbn [fst]. destruct (Z.eqb_spec B A); [lia|]. left. reflexivity.
      - destruct (Z.eqb_spec (fst b) A); [exact HIn | right; apply IH; assumption].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L15034842047.131L15486030912.162L1705593193.132 L21157592723.128L21157592723.131L2402105605.131 L2414492218.161 L32227596763.159L34035782069.162L34036210738.159L39414171869.161L39418301410.131L39428301440.162L39428382976.160L39440819007.128L39440819007.131L46954932887.162L47402560798.128L47402560798.131L49846022755.128L49846022755.131L52920302833.163L56670682120.161L56670682760.162L57415811887.131L57423741610.132L59273918642.161L59273919026.162L60143321393.162L62010051697.128L62010051697.131L7835904048.160 L7835954096.162 00000V01U02W03G04704i05[06P07607\08M09>09n0:^0;N0<>0=;0=l0>]0?S0@I0@o0AU0B;0B<0CD0Cj0DP0E60E^0FF0Fl0GRS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3HIA3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd3HFR2h24HFR2S3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl2HL4LCAP3PAY1d2Hd1HS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp04SPlo4SPal5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3HIA3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd3HFRS1R3HIA3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd3HFRS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3HIA3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd2HVS1R3HIA3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd2HVS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp04SPlo4SPhi5fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3HIA3sp04SPlo5fdata3msp3tsp2Ln3buf2cl3PAY1d1h2Hd2HV2h23HV2S3sp05fdata3TOP6HTOPlo3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3TOP6HTOPlo3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln3buf2cl3PAY1d2Hd2NFS1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln3buf2cl3PAY1d2Hd2NFS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdFS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY1d2Hd1HS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS1R3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2HdS3sp05fdata3msp3tsp2Ln3buf2cl3PAY1d2Hd". (* [comment removed for export] *)
    Lemma last_freeA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pd,$36.PLB,(0.$3;.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)P,(8.(5:.#1.R14.)(5:.R14.#4.))P,(62.R15.(17.&8.=)R14.R4.R3.R2.)P,(9.(1:.(6>.$5.VR,VHIA,R3.)(43.+2.$7;.))$6?.)P,(9.(1:.(70.$5.VR,VHIA,R4.)(43.+2.(7<.=)))$71.)(76.$5.(77.(24.(47.(17.&40.+9748<.)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.=)(17.&40.-2.)R;.R:.R9.R8.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)(17.&40.-1.)=)(26.&5.(2.&40.))(17.&40.+974:0.)(17.&20.=)(27.(2.&40.))R7.(28.$5.))R6.)(78.(79.+1.(60.(61.R18.#1.)))(80.(81.(4:.=Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      intros * Hd P HV HFR. pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof (hd_needs _ _ _ HID) as (NM & NF & NA). pose proof (u64_range sp0) as SPR.
      pose proof (@A_main_fin.atx_presA R HIA HID sp0 SPlo) as ATXP.
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKh | apply (L4_steps (hcs asegs R HIA h)) |].
      cbn beta. intros ms1 mo1 -> HK1 MM1. unfold TREGS. rewrite <- HFREE.
      assert (TAILK : forall m2 mo2 h2 LB2 (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        HM asegs R HIA h2 LB2 [] m2 -> In (buf, cap) LB2 -> HK asegs R HIA h2 mo2 ->
        htop asegs R HIA h2 = TOP -> hstkhi asegs R HIA h2 = STKHI -> havol asegs R HIA h2 + AVOL_CALL <= AVOL_MAX ->
        hfr asegs R HIA h2 + fr_charge 0 <= FR_MAX ->
        m_fs mo2 = fs0 -> m_fds mo2 = FDS2 -> TMEM d m2 -> mem_inv asegs m2 -> A_main_fin.atx_clause m2 ->
        rw_cells asegs m2 tsp TRFm -> rw_cells asegs m2 msp (A_main_loop.FRAMEA sp0 pad) -> stk asegs m2 (arl_stklo R) tsp ->
        srealizesJ asegs (mkCfg (MS (mkR (Z_to_bv 64 0x0974a8) (Z_to_bv 64 tsp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0' t1' t2'
                                          (Z_to_bv 64 plen) (Z_to_bv 64 DATA) a0' a1' a2' a3' a4' a5' a6' a7'
                                          (Z_to_bv 64 owned) (Z_to_bv 64 (-1)) (Z_to_bv 64 0x63c050) (Z_to_bv 64 0) LS6 LS7
                                          (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3' t4' t5' t6')
                                   bvmap_empty (Z_to_bv 64 0x0974a8) (Z_to_bv 32 0) None m2 (seg_rom asegs)) mo2)
          (t_emit (W 1 (zero_lines (d - 1))) (t_exit (exit_code (status 0 b1)) fs0))).
      { intros * HH2 IB2 HK2 HT2 HS2 HV2 HFR2 FS2 FDS2' TX2 MI2 ATX2 TR2 FR2 ST2.
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2));
          [exact HK2 | eapply (L5_steps (hcs asegs R HIA h2)); [exact TR2 | eapply crange_sub; [apply (hcs_stack _ _ HIA h2) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS2; cbv delta [tsp]; lia]] |].
        cbn beta. intros ms3 mo3 -> HK3 MM3.
        eapply (ret_finA d 0 LB2); [lia | left; reflexivity | exact HH2 | exact IB2 | exact HK3 | exact HT2 | exact HS2 | exact HV2 | exact HFR2
          | rewrite (mo_mat_fs _ _ MM3); exact FS2 | rewrite (A_main_fin.mo_mat_fds _ _ MM3); exact FDS2' | exact TX2 | exact ATX2 | exact FR2 |].
        pose proof (stk_release asegs m2 (arl_stklo R) tsp _ ST2 TR2 ltac:(rewrite STKLO; cbv delta [tsp]; lia)) as ST2'.
        unfold TRFm, TRFA in ST2'. cbn [cells_size csize Nat.add] in ST2'. replace (tsp + Z.of_nat 80) with msp in ST2' by (cbv delta [tsp msp]; lia). exact ST2'. }
      destruct IO as [(O0 & D0 & P0) | (OD & ID & NE & PP & DLO & DHI)].
      - (* [comment removed for export] *)
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h)); [exact HK1 | |].
        { eapply (heapA_free_null _ _ HIA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) m h LB [] (arl_stklo R));
            rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
            [ exact HH | exact ST | lia | cbv delta [tsp]; lia | rewrite HT; cbv delta [tsp]; lia | cbv delta [tsp]; lia
            | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX)) | rewrite HTP; reflexivity | rewrite O0; reflexivity ]. }
        cbn beta. intros ms2 mo2 P2 HK2' MM2.
        destruct P2 as (u0 & u1 & u2 & r2 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m2 & -> & MI2 & ST2 & WM2 & HP2 & h2 & HCS2 & HT2 & HS2 & HF2 & HV2 & HFR2 & HKiff & HH2).
        rewrite ?unsigned_lit in ST2, HP2 by (cbv delta [tsp]; lia). reg_lit 0x0974a8.
        assert (HK2 : HK asegs R HIA h2 mo2) by (apply (proj2 (HKiff mo2)); exact HK2').
        eapply (TAILK m2 mo2 h2 LB); try eassumption.
        + rewrite HT2. exact HT.
        + rewrite HS2. exact HS.
        + rewrite HV2. unfold AVOL_CALL in *. lia.
        + rewrite HFR2. unfold fr_charge in *. lia.
        + rewrite (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM1). exact FS.
        + rewrite (A_main_fin.mo_mat_fds _ _ MM2), (A_main_fin.mo_mat_fds _ _ MM1). exact FDS.
        + eapply tmem_presA; [exact TX | exact HP2 | intros a Ha; exact I | exact HH2 | exact MI2].
        + eapply ATXP; [| exact HP2 | intros a Ha; exact I].
          destruct AX as (bb & jp & jq & jf & AT). exists bb, (Z_to_bv 8 0), jp, jq, jf. split; [exact AT | intros _; exact IC].
        + eapply (presA_rw_cells asegs R); [exact HP2 | exact TR | apply client_range_stack; lia | exact I].
        + eapply (presA_rw_cells asegs R); [exact HP2 | exact FR | apply client_range_stack; cbv delta [tsp msp]; lia | exact I].
      - (* [comment removed for export] *)
        eapply srzJ_of_aevtS; [ | apply t_emit_has_nil | ].
        { eapply (heapA_freeD _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   bvmap_empty (Z_to_bv 32 0) m mo1 h LB [] DATA plen (arl_stklo R) 0);
            rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
            [ exact HH | exact HK1 | exact ID | exact ST | lia | cbv delta [tsp]; lia
            | rewrite HT; cbv delta [tsp]; lia | cbv delta [tsp]; lia
            | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX)) | rewrite HTP; reflexivity | rewrite OD; reflexivity | unfold AVOL_CALL in *; lia
            | uwc0
            | unfold fr_charge in *; lia ]. }
        intros c2 (ms2 & mo2 & -> & P2).
        destruct P2 as (u0 & u1 & u2 & r2 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m2 & -> & MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HFRESH2 & HH2).
        rewrite ?unsigned_lit in ST2, HP2 by (cbv delta [tsp]; lia). reg_lit 0x0974a8.
        eapply (TAILK m2 mo2 h2 (lb_remove DATA LB)); try eassumption.
        + apply in_lb_remove; [exact IB | intros E; apply NE; symmetry; exact E].
        + rewrite HT2. exact HT.
        + rewrite HS2. exact HS.
        + unfold AVOL_CALL in *. lia.
        + unfold fr_charge in *. lia.
        + rewrite (A_main_fin.mo_frame_fs _ _ MF2), (mo_mat_fs _ _ MM1). exact FS.
        + rewrite (A_main_fin.mo_frame_fds _ _ MF2), (A_main_fin.mo_mat_fds _ _ MM1). exact FDS.
        + eapply tmem_presA; [exact TX | exact HP2 | intros a Ha; exact I | exact HH2 | exact MI2].
        + eapply ATXP; [| exact HP2 | intros a Ha; exact I].
          destruct AX as (bb & jp & jq & jf & AT). exists bb, (Z_to_bv 8 0), jp, jq, jf. split; [exact AT | intros _; exact IC].
        + eapply (presA_rw_cells asegs R); [exact HP2 | exact TR | apply client_range_stack; lia | exact I].
        + eapply (presA_rw_cells asegs R); [exact HP2 | exact FR | apply client_range_stack; cbv delta [tsp msp]; lia | exact I].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L19324082503.172L20570979214.196L21046246212.195L22609511833.197L24875814373.197L28491474389.195L30043403411.195L32487010370.196L40206808597.140L41606015376.196L44968825303.196L45102888010.128L45102888010.139L47716378138.106L4819972543.195 L51927619311.193L5400083613.196 L54089392246.140L59992366529.173L60027729699.130L60027729699.169L63883216425.195L65119284975.196L65548430650.7  L65548543238.6  L7263800832.108 00002503003m05K06k08F09c0:^0<60=10=l0?=0@N0BP0CH0DG0EB0F[0GZ0HY0IX0JP0KP0Km0LE0M?S3sp03fs05fdata3msp3tsp2Ln3buf2cl4plen4DATA5owned5Hplen2b13PAY1r2Hr2Hd3Hdr3t0'3t1'3t2'3a2'3a3'3a4'3a5'3a6'3a7'3t3'3t4'3t5'3t6'3mo32m3S3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1k2Hr2Hd3HdrS1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k1h2Hr2Hd3Hdr2HV2PB2h23HV2S1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k1h2Hr2Hd3Hdr3HFR2FB2h24HFR2S1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1k1h2Hr2Hd3Hdr2HV2PB2h23HV2S1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1k1h2Hr2Hd3Hdr3HFR2FB2h24HFR2S3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1d1h2Hr2Hd3Hdr2HV2PB1HS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY1r1d2Hr2Hd3Hdr1HS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY1r1d2Hr2Hd3Hdr1HS3sp03fs05fdata3msp3tsp2Ln3buf2cl4plen4DATA5owned5Hplen2b13PAY1d2ra2t02t12t22a02a12a22a32a42a52a62a72t32t42t52t62s31m2mo2Hr2Hd3HdrS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1k2Hr2Hd3HdrS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1k2Hr2Hd3HdrS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1d1h2Hr2Hd3Hdr3HFR2FB1HS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1k2Hr2Hd3HdrS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1d2Hr2Hd3Hdr1x2HxS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1d2Hr2Hd3Hdr1x2HxS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1k2Hr2Hd3HdrS3sp04SPlo5fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2r'1k2Hr2Hd3HdrS4C24f4plen2r'2LB3HCN3LBx3HC2S4C24f4plen1r2LB3HCN3CSNS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1r1d2Hr2Hd3Hdr". (* [comment removed for export] *)
    Lemma ploopA : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pr,$36.Pd,$36.PLB,(0.$3;.)Picb,(2.&8.)Pra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3,(2.&40.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)P,(5:.#1.R18.)P,(5:.#1.R18.)P,(5:.(82.R19.R1:.)#4.)P,(62.R1:.R18.R19.R6.R5.R4.)P,(9.(1:.(1:.(6>.$5.VR,VHIA,R5.)(83.R1<.))(43.+2.$7;.))$6?.)P,(9.(1:.(1:.(70.$5.VR,VHIA,R6.)(84.R1=.))(43.+2.(7<.=)))$71.)P,(9.(1:.(1:.(72.R1<.)(85.(50.Vplen,+1701.)R1>.))VC24f,)$73.)(76.$5.(77.(24.(47.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.(17.&40.=)(17.&40.-2.)R?.R>.R=.R<.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)R;.(37.R1?.))(26.&5.(2.&40.))(17.&40.+97468.)(17.&20.=)(27.(2.&40.))R:.(28.$5.))R9.)(78.(79.+1.(60.(82.(61.R1>.#1.)R1?.)))(80.(81.(4:.=Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      induction r as [|r IH]; intros d LB icb ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3 m mo h Hr Hd Hdr P HV HFR HCN; [lia|].
      pose proof (Z.div_pos plen 5889 Hplen ltac:(lia)) as QP. pose proof (csum_nonneg (plen / 5889) r QP) as CSN. cbn [csum] in HCN.
      pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof (PHI_max plen ltac:(cbv delta [Ln] in *; pose proof (cap_ok_bounds sp0 cap COK); lia)) as PB.
      (* [comment removed for export] *)
      assert (FCS : crange (hcs asegs R HIA h) 0x63c054 1).
      { intros x Hx. apply (hcs_static _ _ HIA h). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKh | eapply (L1_steps (hcs asegs R HIA h)); [exact IC | exact FCS | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX))] |].
      cbn beta. intros ms1 mo1 (m1 & -> & MU1 & WM1 & MI1 & IC1) HK1 MM1.
      assert (P1 : PLA d (Z_to_bv 8 1) LB m1 mo1 h).
      { eapply (PLA_incb d icb LB m m1 mo mo1 h); [exact P | exact MU1 | exact WM1 | exact MI1 | exact IC1 | exact HK1 | apply (mo_mat_fs _ _ MM1) | apply (A_main_fin.mo_mat_fds _ _ MM1)]. }
      pose proof (FFR_max plen ltac:(cbv delta [Ln] in *; pose proof (cap_ok_bounds sp0 cap COK); lia)) as FB.
      eapply (fuzz_callA d (Z_to_bv 8 1) LB) with (h := h); [ exact P1 | cbn [rsum] in HV; pose proof (rsum_nonneg r); unfold AVOL_CALL in *; lia
                                              | cbn [fsum] in HFR; pose proof (fsum_nonneg r); unfold fr_charge in *; lia
                                              | clear - HCN CSN; lia | apply t_emit_has_nil |].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 h2 LBx P2 HV2 HFR2 HC2.
      pose proof P2 as P2'. destruct P2' as [HH2 HK2 HT2 HS2 _ _ TX2 _ _ _ _ _ _ _ _ _ IC2].
      (* [comment removed for export] *)
      assert (FCS2 : crange (hcs asegs R HIA h2) 0x63c054 1).
      { intros x Hx. apply (hcs_static _ _ HIA h2). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2));
        [exact HK2 | eapply (L2_steps (hcs asegs R HIA h2)); [exact IC2 | exact FCS2 | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX2))] |].
      cbn beta. intros ms3 mo3 (m3 & -> & MU3 & WM3 & MI3 & IC3) HK3 MM3.
      assert (P3 : PLA d (Z_to_bv 8 0) (LBx ++ LB) m3 mo3 h2).
      { eapply (PLA_incb d (Z_to_bv 8 1) (LBx ++ LB) m2 m3 mo2 mo3 h2); [exact P2 | exact MU3 | exact WM3 | exact MI3 | exact IC3 | exact HK3 | apply (mo_mat_fs _ _ MM3) | apply (A_main_fin.mo_mat_fds _ _ MM3)]. }
      clear P2 HH2 TX2 IC2.
      destruct d as [|k]; [lia|].
      eapply (printfN_callA k (Z_to_bv 8 0) (LBx ++ LB)) with (h := h2); [exact P3 | lia |].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 P4.
      pose proof P4 as P4'. destruct P4' as [HH4 HK4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2));
        [exact HK4 | apply (L3_steps (hcs asegs R HIA h2)); lia |].
      cbn beta. intros ms5 mo5 -> HK5 MM5.
      destruct r as [|r'].
      - (* [comment removed for export] *)
        replace (Z.of_nat 1 =? 1) with true by reflexivity. replace (Z.of_nat 1 - 1) with 0 by lia.
        replace (S k - 1 + 1)%nat with (S (S k) - 1)%nat by lia.
        eapply (last_freeA (S (S k)) (LBx ++ LB)) with (h := h2); [lia | | cbn [rsum] in HV; unfold AVOL_CALL in *; lia | cbn [fsum] in HFR; unfold fr_charge in *; lia].
        destruct P4; split; try assumption. all: rewrite ?(A_main_fin.mo_mat_fds _ _ MM5), ?(mo_mat_fs _ _ MM5); assumption.
      - replace (Z.of_nat (S (S r')) =? 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (Z.of_nat (S (S r')) - 1) with (Z.of_nat (S r')) by lia.
        replace (S k - 1 + S (S r'))%nat with (S (S k) - 1 + S r')%nat by lia.
        eapply (IH (S (S k)) (LBx ++ LB) (Z_to_bv 8 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 mo5 h2); [lia | lia | lia | | cbn [rsum] in *; pose proof (rsum_nonneg r'); unfold AVOL_CALL in *; lia
          | cbn [fsum] in *; pose proof (fsum_nonneg r'); unfold fr_charge in *; lia
          | clear - HCN HC2; lia].
        destruct P4; split; try assumption. all: rewrite ?(A_main_fin.mo_mat_fds _ _ MM5), ?(mo_mat_fs _ _ MM5); assumption.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L13785505604.194L20570979214.194L22609511833.195L24875814373.195L28491474389.193L30043403411.193L40213220270.137L43572747969.193L45102888010.124L45102888010.126L47716378138.103L51927619311.191L53174411120.194L54083231181.137L60027729699.129L60027729699.167L61435218698.194L63883216425.193L65548430650.7  L65548543238.6  L6693015536.194 L7263800832.104 00000b01T02i04@05U06m08>08m0:60;?0=80=j0>\0?o0@f0A]0BO0C>0C[0D40Df0EXS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c22HcS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c22HcS1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c21h2Hc2HV2PB2h23HV2S1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c21h2Hc3HFR2FB2h24HFR2S1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1h2Hc2HV2PB2RS2h23HV2S1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY1h2Hc3HFR2FB3FS'2h24HFR2S1R3HIA3sp04SPlo5fdata3PHI4FPHI3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c11h2Hc2HV2PB2RSS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2HcS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY2c12Hc1HS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl5Hplen2HL4LCAP3PAY2c12Hc1HS3sp03fs05fdata3msp3tsp2Ln3buf2cl4plen4DATA5owned5Hplen2b13PAY2ra2t02t12t22a02a12a22a32a42a52a62a72t32t42t52t62s31m2mo2HcS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c12HcS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c22HcS1R3HIA3sp04SPlo5fdata3FFR4FFFR3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c11h2Hc3HFR2FB3FS'S3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c12Hc1x2HxS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c12Hc1x2HxS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c22HcS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2HcS4C24f4plen2c22LB3HCN3LBx3HC2S4C24f4plen2c12LB3HCN3CSNS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c22HcS3sp05fdata3msp3tsp2Ln3buf2cl4plen5Hplen3PAY2c12Hc". (* [comment removed for export] *)
    Lemma piter1A : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pcalls,$36.PLB,(0.$3;.)Picb,(2.&8.)Pra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3,(2.&40.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$59.Ph,(3:.$5.VR,VHIA,)P,(8.(5:.#1.R17.)(5:.R17.#4.))P,(62.#0.R16.R17.R4.R3.R2.)P,(9.(1:.(1:.(6>.$5.VR,VHIA,R3.)(83.R19.))(43.+2.$7;.))$6?.)P,(9.(1:.(1:.(70.$5.VR,VHIA,R4.)(84.R1:.))(43.+2.(7<.=)))$71.)P,(9.(1:.(1:.(72.R1:.)(85.(50.Vplen,+1701.)R1;.))VC24f,)$73.)(76.$5.(77.(24.(47.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.(17.&40.=)(17.&40.-2.)R=.R<.R;.R:.Vplen,(17.&40.VDATA,)(17.&40.Vowned,)R9.(37.R1<.))(26.&5.(2.&40.))(17.&40.+97468.)(17.&20.=)(27.(2.&40.))R8.(28.$5.))R7.)(78.(79.+1.(60.R1<.))(80.(81.(4:.=Vb1,))Vfs0,)))")
(* [comment removed for export] *).
    Proof.
      intros * Hc P HV HFR HCN. destruct calls as [|c1]; [lia|].
      pose proof (Z.div_pos plen 5889 Hplen ltac:(lia)) as QP. pose proof (csum_nonneg (plen / 5889) c1 QP) as CSN. cbn [csum] in HCN.
      pose proof P as P'. destruct P' as [HH HKh HT HS IB IO TX SIm ST SSH TR FR FS FDS BY AX IC].
      pose proof (PHI_max plen ltac:(cbv delta [Ln] in *; pose proof (cap_ok_bounds sp0 cap COK); lia)) as PB.
      pose proof (rsum_nonneg c1) as RS. cbn [rsum] in HV.
      pose proof (FFR_max plen ltac:(cbv delta [Ln] in *; pose proof (cap_ok_bounds sp0 cap COK); lia)) as FB.
      pose proof (fsum_nonneg c1) as FS'. cbn [fsum] in HFR.
      (* [comment removed for export] *)
      assert (FCS : crange (hcs asegs R HIA h) 0x63c054 1).
      { intros x Hx. apply (hcs_static _ _ HIA h). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKh | eapply (L1_steps (hcs asegs R HIA h)); [exact IC | exact FCS | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX))] |].
      cbn beta. intros ms1 mo1 (m1 & -> & MU1 & WM1 & MI1 & IC1) HK1 MM1.
      assert (P1 : PLA 0%nat (Z_to_bv 8 1) LB m1 mo1 h).
      { eapply (PLA_incb 0%nat icb LB m m1 mo mo1 h); [exact P | exact MU1 | exact WM1 | exact MI1 | exact IC1 | exact HK1 | apply (mo_mat_fs _ _ MM1) | apply (A_main_fin.mo_mat_fds _ _ MM1)]. }
      eapply (fuzz_callA 0 (Z_to_bv 8 1) LB) with (h := h); [ exact P1 | unfold AVOL_CALL in *; lia | unfold fr_charge in *; lia | clear - HCN CSN; lia | apply t_emit_has_nil |].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 h2 LBx P2 HV2 HFR2 HC2.
      pose proof P2 as P2'. destruct P2' as [HH2 HK2 HT2 HS2 _ _ TX2 _ _ _ _ _ _ _ _ _ IC2].
      (* [comment removed for export] *)
      assert (FCS2 : crange (hcs asegs R HIA h2) 0x63c054 1).
      { intros x Hx. apply (hcs_static _ _ HIA h2). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2));
        [exact HK2 | eapply (L2_steps (hcs asegs R HIA h2)); [exact IC2 | exact FCS2 | exact (xm_mi _ _ _ _ _ (tx_x _ _ TX2))] |].
      cbn beta. intros ms3 mo3 (m3 & -> & MU3 & WM3 & MI3 & IC3) HK3 MM3.
      assert (P3 : PLA 0%nat (Z_to_bv 8 0) (LBx ++ LB) m3 mo3 h2).
      { eapply (PLA_incb 0%nat (Z_to_bv 8 1) (LBx ++ LB) m2 m3 mo2 mo3 h2); [exact P2 | exact MU3 | exact WM3 | exact MI3 | exact IC3 | exact HK3 | apply (mo_mat_fs _ _ MM3) | apply (A_main_fin.mo_mat_fds _ _ MM3)]. }
      clear P2 HH2 TX2 IC2.
      change (zero_lines (S c1)) with (zero_lines 1 ++ zero_lines c1).
      eapply srzJ_conseq; [ | apply (t_emit_W_app 1) ].
      eapply (printf1_callA (Z_to_bv 8 0) (LBx ++ LB)) with (h := h2); [exact P3 | apply t_emit_has_nil |].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 P4.
      pose proof P4 as P4'. destruct P4' as [HH4 HK4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2));
        [exact HK4 | apply (L3_steps (hcs asegs R HIA h2)); lia |].
      cbn beta. intros ms5 mo5 -> HK5 MM5.
      destruct c1 as [|c2].
      - replace (Z.of_nat 1 =? 1) with true by reflexivity. replace (Z.of_nat 1 - 1) with 0 by lia.
        change (zero_lines 0) with (zero_lines (1 - 1)).
        eapply (last_freeA 1 (LBx ++ LB)) with (h := h2); [lia | | unfold AVOL_CALL in *; lia | unfold fr_charge in *; lia].
        destruct P4; split; try assumption. all: rewrite ?(A_main_fin.mo_mat_fds _ _ MM5), ?(mo_mat_fs _ _ MM5); assumption.
      - replace (Z.of_nat (S (S c2)) =? 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (Z.of_nat (S (S c2)) - 1) with (Z.of_nat (S c2)) by lia.
        change (zero_lines (S c2)) with (zero_lines (1 - 1 + S c2)).
        eapply (ploopA (S c2) 1 (LBx ++ LB) (Z_to_bv 8 0)) with (h := h2); [lia | lia | lia | | cbn [rsum] in *; pose proof (rsum_nonneg c2); unfold AVOL_CALL in *; lia
          | cbn [fsum] in *; pose proof (fsum_nonneg c2); unfold fr_charge in *; lia
          | clear - HCN HC2; lia].
        destruct P4; split; try assumption. all: rewrite ?(A_main_fin.mo_mat_fds _ _ MM5), ?(mo_mat_fs _ _ MM5); assumption.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End PLoopA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L14664342920.59L14670927129.61L14670927129.62L16222032411.59L39096254020.63L39096254020.64L40011237873.61L53299372405.58L55687794104.58L56288820006.59L56572483714.61L56572483714.62L57168869077.5800000F00\01201H01c02>02Y02o03E03[04104G04]S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma flag_cell : forall m, exists v : byte, rw_cells asegs m 0x63c050 [C1 v].
  Proof.
    intros m.
    assert (WV : wview asegs m (wa 0x63c050) <> None).
    { pose proof (store_ok_wview asegs m (Z_to_bv 64 0x63c050) 1%nat 0%nat (store_ok_6d4 m 0x63c050 1%nat ltac:(lia) ltac:(cbn; lia)) ltac:(lia)) as W.
      rewrite unsigned_lit in W by lia. rewrite Z.add_0_r in W. exact W. }
    assert (WR : wr_at asegs m 0x63c050 1).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (0x63c050 + i) with 0x63c050 by lia. exact WV. }
    destruct (m (wa 0x63c050)) as [b|] eqn:E.
    - exists b. split; [split; [cbn; tauto |] | exact WR].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. unfold mrd. rewrite E. reflexivity.
    - exists (Z_to_bv 8 0). split; [split; [cbn; tauto |] | exact WR].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. unfold mrd. rewrite E. vm_compute. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L11661943618.61L11661943618.62L14928457969.61L34622810133.58L37215581128.59L37217909593.61L37217909593.62L39096254020.63L39096254020.64L40973748661.58L41654481638.59L54060502939.59L55687794104.5800000F00\01701M01c02902O02j03E03[04104G04]S3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2Ln1i2HiS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln". (* [comment removed for export] *)
  Lemma incb_cell_any : forall m, exists v : byte, incbA m v.
  Proof.
    intros m. unfold incbA.
    assert (WV : wview asegs m (wa 0x63c054) <> None).
    { pose proof (store_ok_wview asegs m (Z_to_bv 64 0x63c054) 1%nat 0%nat (store_ok_6d4 m 0x63c054 1%nat ltac:(lia) ltac:(cbn; lia)) ltac:(lia)) as W.
      rewrite unsigned_lit in W by lia. rewrite Z.add_0_r in W. exact W. }
    assert (WR : wr_at asegs m 0x63c054 1).
    { split; [lia|]. split; [lia|]. intros i Hi. replace (0x63c054 + i) with 0x63c054 by lia. exact WV. }
    destruct (m (wa 0x63c054)) as [b|] eqn:E.
    - exists b. split; [split; [cbn; tauto |] | exact WR].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. unfold mrd. rewrite E. reflexivity.
    - exists (Z_to_bv 8 0). split; [split; [cbn; tauto |] | exact WR].
      split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. unfold mrd. rewrite E. vm_compute. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma T3e_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pplen,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))(34.$5.VAL,R18.Lms',$22.(>.$22.R1.(24.(47.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(17.&40.=)(17.&40.-2.)R;.R:.R9.R8.R4.(17.&40.+63<060.)(17.&40.=)R5.R3.)(26.&5.(2.&40.))(17.&40.+97468.)(17.&20.=)(27.(2.&40.))R2.(28.$5.)))(24.(47.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.$18.)R;.R:.R9.R8.R7.R3.R6.R5.R4.R2.)(26.&5.(2.&40.))(17.&40.+97458.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros *. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. zstep. zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Lemma T3m_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pplen,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))(34.$5.VAL,R18.Lms',$22.(>.$22.R1.(24.(47.(17.&40.+97414.)R17.R16.R15.(17.&40.R4.)R13.R12.R11.R10.R?.R>.R=.(17.&40.$18.)R<.R;.R:.R9.R8.R4.R7.R6.R5.R3.)(26.&5.(2.&40.))(17.&40.+69480.)(17.&20.=)(27.(2.&40.))R2.(28.$5.)))(24.(47.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.$18.)R;.R:.R9.R8.R7.R3.R6.R5.R4.R2.)(26.&5.(2.&40.))(17.&40.+9740<.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros *. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L47902356289.82L53506590987.82L8544643339.82 00000G00Y010S3sp05fdata3msp2Ln1D2HDS3sp05fdata3msp2LnS3sp05fdata3msp2Ln1D2HD". (* [comment removed for export] *)
  Lemma T4_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pplen,$7.PD,$7.PPAY,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))P,(8.(:.=R4.)(:.R4.(;.+2.+2?.)))P,(8.(9.=R4.)(:.R4.(;.+2.+40.)))(34.$5.VAL,R19.Lms',$22.(>.$22.R1.(24.(47.(17.&40.+97428.)R19.R18.R17.(17.&40.R7.)(17.&40.R6.)(17.&40.R8.)R14.R13.R12.R11.R10.(17.&40.$18.)R?.R>.R=.R<.R;.R8.(17.&40.R6.)(17.&40.R7.)R9.R5.)(26.&5.(2.&40.))(17.&40.+67=;8.)(17.&20.=)(27.(2.&40.))R4.(28.$5.)))(24.(47.(17.&40.+97414.)R18.R17.R16.(17.&40.R6.)R15.R14.R13.R12.R11.R10.R?.(17.&40.$18.)R>.R=.R<.R;.R:.R7.(17.&40.R5.)R9.R8.R4.)(26.&5.(2.&40.))(17.&40.+97414.)(17.&20.=)(27.(2.&40.))R3.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * HD HP. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. ifc false. zstep. zstep. zstep. zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma T5_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps3,(2.&40.)Pplen,$7.PD,$7.Pr,$7.Pm,P,(2.&40.)(3.(2.&8.))(34.$5.VAL,R17.Lms',$22.(>.$22.R1.(24.(47.(17.&40.+97428.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(17.&40.=)(17.&40.-2.)R;.R:.R9.R8.R5.(17.&40.R4.)(17.&40.R4.)R6.R3.)(26.&5.(2.&40.))(17.&40.+97468.)(17.&20.=)(27.(2.&40.))R2.(28.$5.)))(24.(47.(17.&40.+97428.)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.(17.&40.$18.)R;.R:.R9.R8.R7.R4.R6.(17.&40.R3.)R5.R2.)(26.&5.(2.&40.))(17.&40.+97428.)(17.&20.=)(27.(2.&40.))R1.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros *. unfold TREGS. subst tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. zstep. zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L13309229874.85L14981969176.85L21971292696.85L22120147736.85L30021243613.84L31722891288.85L34234375064.85L36667852792.0 L51126253464.85L56498182552.85L6274867352.85 L67856165528.85Q12872860869.84Q15304725424.84Q16156991457.84Q18894481989.84Q18994824390.84Q20351153222.84Q21338652976.84Q23962701510.84Q24216750433.84Q24930197445.84Q27357656752.84Q31136645702.84Q33360389168.84Q3427631174.84 Q35722900577.84Q36949832389.84Q39381486000.84Q39988450118.84Q40243683937.84Q41276410182.84Q43614680518.84Q44904801222.84Q45400751920.84Q4652940513.84 Q51434941616.84Q51496327493.84Q51785118561.84Q57453875760.84Q57517674181.84Q59807448801.84Q60827833697.84Q63456610224.84Q63536675909.84Q6870390597.84 Q7116621281.84 Q853483973.84  00000>00L00Z00h01601D01R01S01a01o02=02K02Y02l03?03M03[03i04<04J04]04k05>05L05_05m06@06N06a06o07B07P07^07l08?08R08e09309F09Y09g0::0:M0:`0:n0;<0;O0;]S3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnSS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPlo5fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp04SPhi5fdata2LnS3sp04SPlo5fdata2LnS3sp05fdata2LnS3sp05fdata2LnS3sp04SPhi5fdata2LnS3sp05fdata2Ln". (* [comment removed for export] *)
  Lemma L5n_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "PCS,P,$7.SpPt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Pr,$7.Pbuf,$7.Pcl,$7.Pplen,$7.Pb1,(2.&8.)Pjunk,(0.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(2<.$5.R1.Vtsp,(2=.R2.R?.R3.R4.(1:.(1:.(1:.R6.+2.)R5.)+4.)R5.R6.))P,(30.R1;.Vtsp,+50.)(34.$5.VAL,R1<.Lms',$22.(>.$22.R1.(24.(49.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.+2.R9.R8.R7.R6.)(26.&5.(2.&40.))(17.&40.+97254.)(17.&20.=)(27.(2.&40.))R4.(28.$5.)))(24.(47.(17.&40.+97414.)R1;.R1:.R19.(17.&40.=)R18.R17.R16.R15.R14.R13.R12.(17.&40.$18.)R11.R10.R?.R>.R=.R6.R<.R;.R:.R9.)(26.&5.(2.&40.))(17.&40.+97414.)(17.&20.=)(27.(2.&40.))R3.(28.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros * FR SCS. unfold TREGS, RREGS, TRFA in *. subst msp tsp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    replace (bv_unsigned sp0 - 208) with (bv_unsigned sp0 + -208) in * by lia.
    zstep. try ifc true.                            (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    do 9 zstep.                                     (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18362652261.6300000SS3sp04SPlo5fdata3msp3tsp2Ln2bs1k2LE". (* [comment removed for export] *)
  Lemma bytes_at_skipn : ltac2:(CDefT.buildp (gd_tbl_A_main_target ()) "Pm,P,(2.&40.)(3.(2.&8.))Pa,$7.Pbs,(0.(2.&8.))Pk,$36.P,(86.$5.R4.R3.R2.)P,(5:.R2.(87.(2.&8.)R3.))(86.$5.R6.(1:.R5.(37.R3.))(88.(2.&8.)R3.R4.))")
(* [comment removed for export] *).
  Proof.
    intros m a bs k BY LE.
    rewrite <- (firstn_skipn k bs) in BY. apply (proj1 (bytes_at_app _ _ _ _ _)) in BY. destruct BY as [_ B2].
    rewrite firstn_length in B2. replace (Nat.min k (length bs)) with k in B2 by lia. exact B2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "02G0@L10333729495.163L10770895180.224L10949882775.199L10953994280.198L11148492598.194L11148916662.200L11153685762.256L1204523653.224 L1206641794.144 L1206779827.116 L12566903814.224L1423829364.226 L14390665410.252L15047276935.163L1540038355.198 L15425241144.160L15730465884.198L15734579171.199L15842111232.198L1709705940.163 L17377105029.163L17678791660.199L19574577830.216L20279677568.217L20814097441.218L21169798315.163L21530852239.145L21704603700.248L22609511833.164L22609511833.252L23503075856.151L2410297472.164 L24227077183.252L24875814373.164L24875814373.252L25064775520.151L25819418591.163L26833293852.219L27193321446.160L27195758691.163L27415653979.224L27901296685.163L29108126117.145L31083085908.145L31254589524.145L32227711709.195L32409989873.145L34035782071.198L34036162356.195L35911969340.219L36647774536.11 L36647774536.12 L37278223966.164L37278223966.252L37278349049.252L3767899476.159 L39428382980.248L39428382983.163L39430347910.224L39447730772.145L39600575525.145L39823570202.198L40665656729.218L40825674972.158L40849210613.252L41944582785.225L43035330635.167L43035330635.255L43570698356.158L4455481414.152 L44774073073.145L44839198817.199L44843312094.198L44923132891.199L44927408228.198L45111114475.157L45246675210.151L45335624142.224L45879207211.252L46741096805.115L47404667559.224L47407165222.163L47788488016.151L47965744677.145L48458956325.145L48756710214.216L48786278267.198L48821187741.198L49858457691.163L49860677082.224L50970842096.224L5115413524.145 L52191170596.165L52523326688.163L52579485648.145L52920303601.199L53700087601.224L54055120434.252L54179188776.148L55258109492.198L56532565042.252L56670682766.194L56670748337.212L56730697831.224L57427984663.163L57622410744.255L57628697365.256L57628700040.254L57750011036.151L58243753146.198L58247898885.199L58375304701.252L592074626.198  L59274000823.198L59274377012.213L59314873579.167L59976436350.146L60027729699.119L60027729699.120L60877502257.145L61905504811.163L62011830997.252L62022225481.163L62022246142.116L62022632911.144L62024725448.224L62069740404.145L62069740404.217L62069740404.220L62411857322.224L62749270687.226L63327169650.145L65108326814.224L65325083322.199L65329228037.198L65403709119.164L66216646405.163L66216646409.251L66219071648.165L66219071648.253L66475777781.198L66475777783.163L67372331299.224L67679842163.225L67783293542.198L7249202944.164 L7249202944.252 L7263880762.166 L7263880762.254 L8800126135.150 L8806421082.147 00000o01`01a01b02>02\03N04F04k05P06907I08;08W09309]09^09_09`0:Y0;j0=30=^0>U0?70?]0@30@\0AW0C=0C_0D`0EM0FJ0G`0H\0I80J50J_0KI0LK0M;0M<0MR0Mh0NS0Ni0OE0Oa0Pl0Q]0RP0SD0T@0U20UO0VB0Vh0W[0X10X20Xk0Yb0Z80Zn0\@0]70^H0^^0_N0_d0_e0_f0_g0_h0`d0aB0b90ch0dW0eK0f20fO0fP0fQ0g30g40gk0hW0iT0j=0k00kT0l00lK0lg0mU0oO0oj10F11E11a12?13D14C15=17217k18Z18[18\19E19F19b1:@1;:1<A1<\1=71=M1=i1>T1?21?J1?b1@M1@h1AK1An1B[1Cf1DK1FT1FU1FV1G;1GW1H@1I41In1JJ1Jf1K[1LU1N91Nb1OX1PL1QF1Qe1RKS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl5Hplen2HL4LCAP2CB2CRS3sp05fdata3msp3tsp2Ln3buf2cl4plen3Hcl2CR1D2jD2LJFFS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CR1DS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen2CR1D2jD3DLO2LJS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2LnS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen4Hcl22HL4LCAP3BR22CB2CR1D2jD3AB12LJS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen2CR1D2jD3DLO2LJS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl4plen5Hplen2CR2PnFFFS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl2HL4LCAP2CB2CRS1R3HIA3sp04SPlo5fdata2V04HV0M3msp3tsp2Ln3cap2cl4plen1h3Hcl2HL3VOL4LCAP2CB2CR3HV0S1R3HIA3sp04SPlo5fdata3FFR4FFFR3FR04HFRF3msp3tsp2Ln2cl1h3FRB2CR2h44HFR41HS3sp05fdata3msp3tsp2Ln3buf3cap2cl4LCAP2CR1DS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen3Hcl2HL2CR1D3AB13AB2S3sp05fdata3msp3tsp2Ln2cl3Hcl2CR1DS3sp04SPlo4SPal5fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3HIA3sp04SPlo5fdata2V04FPHI3HVF3msp3tsp2Ln2cl1h3VOL2CR1HS1R3HIA3sp04SPlo5fdata2V04FPHI3HVF3msp3tsp2Ln3cap2cl4plen1h3Hcl2HL3VOL4LCAP2CB2CR2h41D2jD3HV43AB12LJ1HS3sp05fdata3msp3tsp2Ln2cl3Hcl4Hcl2S1R3HIA3sp04SPlo5fdata3FFR4FFFR3FR04HFRF3msp3tsp2Ln2cl1h3FRB2CR1HS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD3DLO2LJS1R3HIA3sp04SPlo5fdata4FFFR3FR04HFRF3msp3tsp2Ln2cl1h3FRB2CR1HS1R3HIA3sp04SPlo5fdata4FFFR3FR04HFRF3msp3tsp2Ln2cl4plen1h3FRB2CR2h41D2jD4HFR43AB12LJ1HS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl5Hplen2HL4LCAP2CBS3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp04SPlo5fdata3msp3tsp2Ln2cl4plen5HCEIL2CR1D3AB13DCE4PLENS3sp05fdata3msp3tsp2Ln2cl4plen5Hplen2CR2P0S3sp05fdata3msp3tsp2Ln2cl4plen5Hplen2CR2P0S3sp04SPlo5fdata5STKHI6HSTKHI3msp3tsp2Ln2cl4plen2CR1D2jD2DK3AB12LJS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen3Hcl2HL2CR2P0FS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2LnS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl3Hcl4Hcl22CB3BLO3BCE5HCEIL2CR1D3AB1S5fdata4C24f8C24F_max3buf3cap2cl4plen4CLEN3CS42QBS5fdata4C24f8C24F_max3buf3cap2cl4plen1D4CLEN3CS42QBS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen5Hplen2CR4CLENS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen5Hplen2CR1D2jD2LJ4CLENS3sp05fdata3msp3tsp2Ln2cl4plen5Hplen2CR2Pn1D2jD2LJS3sp04SPlo5fdata3msp3tsp2Ln1HS3sp04SPlo4SPhi5fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS3sp04SPlo4SPhi5fdata3msp3tsp2Ln2cl2CRS3sp04SPlo4SPhi5fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS3sp05fdata3msp3tsp2LnFS1R3HIA3sp04SPlo5fdata5STKHI3msp3tsp2Ln2cl1h2HS2CR2h43HS4S3sp04SPlo5fdata3msp3tsp2Ln2cl4plen3Hcl2HL2CR1D3AB13AB2S3sp05fdata3msp3tsp2LnS3sp05fdata5STKHI6HSTKHI3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen4Hcl22HL4LCAP2CB3BCE2CR1D2jD3AB12LJ1HS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen5Hplen2CR2P04CLENS3sp04SPlo5fdata3msp3tsp2Ln3buf3cap2cl4plen3Hcl2HL4LCAP2CR1D2jD3AB13AB22LJ4CLEN1HS3sp05fdata3msp3tsp2LnS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen3Hcl5Hplen2HLS3sp05fdata3msp3tsp2LnFFFFS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl5Hplen2HL4LCAP2CBS3sp05fdata3msp3tsp2Ln3buf3BLOS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen2CR1D2jD3AB14PLEN2LJS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen5Hplen2BR2CB3BHI2CR2Pn1D2jD4DBLK3AB13FA43DHI2LJS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen2HL4LCAPS3sp05fdata3TOP6HTOPlo3msp3tsp2Ln2cl4plen2CR1D2jD2LJS3sp05fdata3TOP6HTOPlo3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln3cap2CBFFS3sp05fdata3msp3tsp2Ln3buf2cl2CR1DFS1R3HIA3sp04SPlo5fdata3TOP3msp3tsp2Ln2cl1h2HT2CR2h43HT4S1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln2cl2NM2CRS1R3sp04SPlo5STKLO5fdata3msp3tsp2Ln2cl4plen2NA2CR1D2jD3AB12LJS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3sp04SPlo5STKLO5fdata3TOP6HTOPlo3msp3tsp2Ln1a2HaS3sp05fdata3msp3tsp2Ln2cl2m12CR1i2HiS3sp05fdata3msp3tsp2Ln2cl2CRS3sp04SPlo5fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2DK2LJS1R3HIA3sp04SPlo4SPal5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen1h5Hplen2HS2BR2CB2CR2Pn1D2jD4AL164DBLK3AB13FA42LJS3sp04SPlo5fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp05fdata5STKHI3msp3tsp2Ln2cl4plen5Hplen2CR2Pn1D2jD4DBLK2LJS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CR1DS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl2HL4LCAP2CB2CR1D2jD3AB12LJS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen3Hcl5Hplen2HL4LCAP2CB2CRS3sp04SPlo5fdata3msp3tsp2Ln2cl4plen2CR1D2jD3AB13DLO2LJ1a1HS1R3HIA3sp04SPlo5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen1h5Hplen2HS2CB3BLO3BHI2CR2Pn1D2jD3AB13DLO2LJ1a2Ha2Hb2HcS1R3sp05fdata3msp3tsp2Ln2cl4plen5Hplen2CR2Pn1D2jD2LJ1x2HxS1R3sp04SPlo5fdata3msp3tsp2Ln3buf3cap3BCE5HCEILFFS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJFS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CR1DS3sp04SPlo5fdata3msp3tsp2Ln3cap2cl4plen4Hcl22HL2C12C22CR1HS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap4LCAP2BR2CB3BLOS3sp05fdata3msp3tsp2Ln1x2HxS3sp05fdata3msp3tsp2Ln1x2HxS3sp05fdata3msp3tsp2LnS3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS1R3sp05fdata3msp3tsp2Ln2cl2CRS1R3sp05fdata3msp3tsp2LnS1R3sp05fdata3msp3tsp2LnS1R3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS3sp05fdata3msp3tsp2Ln1a2HaS3sp05fdata3msp3tsp2Ln2cl2CR1D1a2HaS3sp05fdata3msp3tsp2Ln2cl2CR1D1a2HaS3sp05fdata3msp3tsp2Ln3buf2cl4plen2CR1D2jD2LJS3sp04SPlo5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf2cl4plen3Hcl3BR22CR1D2jD3AB12LJS1R3sp05fdata5STKHI6HSTKHI3msp3tsp2LnS1R3HIA3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3tsp2Ln3buf3cap2cl4plen1h3Hcl4Hcl25Hplen2HL2HS4LCAP2BR2CB3BHI2CR2Pn1D2jD4DBLK3AB13FA43DHI2LJFFS3sp05fdata3msp3tsp2Ln2cl4plen2CR3BIGS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl4plen2CR1D2jD2LJS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen5Hplen2CR4CLENS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen2CR1D2jD3AB22LJ4CLENS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln2cl2CRS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen3LnB2CR1D2jD2LJS1R3sp04SPlo5fdata3msp3tsp2Ln2cl4plen2CR1D2jD3AB13DCE2LJ1HS1R3HIA3sp04SPlo5fdata2V04HV0M3PHI4FPHI3HVF3msp3tsp2Ln3cap2cl4plen1h3Hcl2HL3VOL4LCAP2CB2PB2CR2h43HV4S3sp05fdata3msp3tsp2Ln3buf3cap2cl2CR4CLENS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen2CR1D2jD2LJ4CLENS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen5Hplen2CR4CLENS3sp05fdata3msp3tsp2Ln3buf3cap2cl4plen2CR1D2jD3AB22LJ4CLENS3sp04SPlo5fdata3msp3tsp2Ln1a1HS3sp04SPlo5fdata3msp3tsp2Ln1a2Ha2Hb2Hc". (* [comment removed for export] *)
  Theorem target_phaseA : target_stmtA R HIA HID SI sp0 fs0 fdata can tid wp0 rp0 wp1 rp1 TOP STKHI V0 FR0 pad.
  Proof.
    intros buf cap cl plen t0 t1 t2 a4 a5 a6 a7 x7 t3 t4 t5 t6 m mo h TI [Hcl Hcl2] Hplen HL.
    pose proof TI as TI'. destruct TI' as [HH HKmo HT HS VOL FRB TM FI SSH SIm ST FR FS FDSq BY WR LCAP COK BR FRSH FRSH0].
    pose proof (cap_ok_bounds sp0 cap COK) as CB. pose proof (u64_range sp0) as SPR.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
    pose proof (hd_blk_band _ _ _ HID h _ _ m buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
    pose proof (hd_ceil _ _ _ HID) as HCEIL. pose proof (hd_needs _ _ _ HID) as (NM & NF & NA).
    pose proof (hcs_block _ _ HIA h _ _ m buf cap HH ltac:(left; reflexivity)) as CRB.
    pose proof (hd_rtc _ _ _ HID m (hm_rtc _ _ HIA _ _ _ _ HH)) as RTC.
    assert (LnB : cl + 6 + plen < cap) by (cbv delta [Ln] in *; lia).
    assert (SCS : crange (hcs asegs R HIA h) (arl_stklo R) (msp - arl_stklo R)).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia]. }
    assert (FCS1 : crange (hcs asegs R HIA h) 0x63c050 1).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
    assert (ACS : crange (hcs asegs R HIA h) 0x65cae0 304).
    { intros x Hx. apply (hcs_static _ _ HIA h). apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
    destruct (flag_cell m) as [fv FL]. pose proof (tm_incb _ _ _ _ _ _ _ _ TM : incbA m (Z_to_bv 8 0)) as IC0.
    destruct (tm_atexit _ _ _ _ _ _ _ _ TM) as (jp & jq & jf & AT0).
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | eapply (T1_steps (hcs asegs R HIA h)); [exact ST | exact (tm_mi _ _ _ _ _ _ _ _ TM) | exact SCS | exact FL | exact FCS1 | exact RTC
                                                          | exact AT0 | exact ACS | exact (tm_nl _ _ _ _ _ _ _ _ TM)] |].
    cbn beta. intros ms1 mo1 P1 HK1 MM1. destruct P1 as (ra' & a0' & a1' & a2' & a3' & junk & m1 & -> & MU1 & WM1 & MI1 & ST1 & TR1 & AT1).
    (* [comment removed for export] *)
    assert (HH1 : HM asegs R HIA h [(buf, cap)] [] m1).
    { eapply (hm_munch _ _ HIA); [exact HH | exact MU1 | exact WM1 |]. unfold T1W.
      apply Forall_forall. intros [lo hi] Hin a Ha. cbn [fst snd] in Ha. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <- |]); try (destruct Hin; fail);
        first [ left; left; rewrite HT; cbv delta [tsp msp] in Ha; lia
              | left; right; left; apply (hd_static _ _ _ HID); unfold ARtDrv.drv_static; lia ]. }
    assert (TX1 : TMEM 0 m1).
    { eapply tmem_munch; [apply (tmem_of_tail m TM FI) | exact MU1 | exact WM1 | | exact HH1 | exact MI1].
      intros a (Ha & Hb & Hc). unfold drv_static in Ha. unfold T1W. cbn. cbv delta [tsp msp]. lia. }
    assert (SSH1 : sshad asegs AL m1 (arl_stklo R) msp).
    { eapply (sshad_munch asegs AL (hcs asegs R HIA h)); [exact CSOK | | | exact MU1 | exact WM1 | exact SSH].
      - unfold w_client, T1W. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd]. cbn [In] in Hin.
        repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <- |]); try (destruct Hin; fail);
          first [ eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS; cbv delta [tsp msp]; lia]
                | exact FCS1
                | eapply crange_sub; [exact ACS | lia | lia] ].
      - eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia]. }
    assert (FR1 : rw_cells asegs m1 msp (A_main_loop.FRAMEA sp0 pad)).
    { eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |]. unfold T1W. cbn [cells_size csize A_main_loop.FRAMEA Nat.add disjoint_from fst snd]. cbv delta [tsp msp]. lia. }
    assert (BY1 : bytes_at asegs m1 buf fdata).
    { eapply bytes_at_transport; [exact BY | exact MU1 |]. unfold T1W. cbn [disjoint_from fst snd]. cbv delta [tsp msp Ln] in *. lia. }
    assert (SI1 : si_P SI m1).
    { eapply si_munch; [exact SIm | exact MU1 |]. intros a NO. pose proof (SIFP a NO). unfold T1W. cbn. cbv delta [tsp msp]. lia. }
    assert (IC1 : incbA m1 (Z_to_bv 8 0)).
    { unfold incbA in *. eapply rw_cells_transport; [exact IC0 | exact MU1 | exact WM1 |]. unfold T1W. cbn. cbv delta [tsp msp]. lia. }
    assert (AX1 : exists (b : bool) (jp jq jf : list byte), atexit_cells b m1 (Z_to_bv 8 0) jp jq jf) by (eexists _, _, _, _; exact AT1).
    (* [comment removed for export] *)
    set (b2 := nth 2 fdata (Z_to_bv 8 0)).
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HK1 | eapply (T2_steps (hcs asegs R HIA h) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ buf cap cl plen (buf + 2 + cl + 4) b2 m1);
                   [cbv delta [Ln] in *; lia | cbv delta [Ln] in *; lia | lia | lia | lia | | exact CRB | reflexivity] |].
    { intros CL0. exact (nth_byte_readA m1 buf fdata 2 BY1 ltac:(cbv delta [Ln] in *; lia)). }
    cbn beta. intros ms2 mo2 (a0'' & ->) HK2 MM2.
    assert (FS2 : m_fs mo2 = fs0) by (rewrite (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM1); exact FS).
    assert (FDS2' : m_fds mo2 = FDS2) by (rewrite (A_main_fin.mo_mat_fds _ _ MM2), (A_main_fin.mo_mat_fds _ _ MM1); exact FDSq).
    assert (PB : 0 <= PHI plen <= FPHI) by (apply PHI_max; cbv delta [Ln] in *; lia).
    assert (CR : (1 <= CALLS fdata cl <= 4)%nat).
    { unfold CALLS. destruct (cl =? 0); [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 fdata (Z_to_bv 8 0))) 4 ltac:(lia)). lia. }
    unfold TAIL. destruct (Z.eq_dec plen 0) as [P0|Pn].
    - (* [comment removed for export] *)
      replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HK2 | apply (T3e_steps (hcs asegs R HIA h)) |].
      cbn beta. intros ms3 mo3 -> HK3 MM3.
      unfold SUCC. replace (exit_code 0) with (exit_code (status 0 (nth 1 fdata (Z_to_bv 8 0)))) by (rewrite status0; reflexivity).
      eapply (piter1A buf cap cl plen 0x63c060 0 junk x7) with (h := h) (LB := [(buf, cap)]) (icb := Z_to_bv 8 0) (calls := CALLS fdata cl).
      all: lazymatch goal with
           | |- havol _ _ _ _ + _ + _ <= _ => pose proof (rsum_le4 (CALLS fdata cl) ltac:(lia)); unfold AVOL_CALL in *; lia
           | |- hfr _ _ _ _ + _ + _ <= _ => pose proof (fsum_le4 (CALLS fdata cl) ltac:(lia)); unfold fr_charge in *; lia
           | |- cnt24 ?lb + _ + _ <= _ =>   (* [comment removed for export] *)
               pose proof (cnt24_le_length lb) as CLEN; cbn [length] in CLEN;
               pose proof (Z.div_pos plen 5889 ltac:(lia) ltac:(lia)) as QP;
               pose proof (csum_le4 (plen / 5889) (CALLS fdata cl) QP ltac:(lia)) as CS4;
               assert (QB : plen / 5889 <= 11396) by (apply Z.div_le_upper_bound; [lia|]; pose proof (cap_ok_bounds sp0 cap COK); cbv delta [Ln] in *; lia);
               unfold C24MAX; clear - CLEN CS4 QB QP C24F_max; lia
           | |- _ => try first [exact Hcl | exact Hplen | exact HL | exact COK | exact LCAP | exact BR | exact BLO | exact CR]
           end.
      split; try assumption.
      + left. reflexivity.
      + left. repeat split; lia.
      + rewrite (mo_mat_fs _ _ MM3). exact FS2.
      + rewrite (A_main_fin.mo_mat_fds _ _ MM3). exact FDS2'.
      + (* [comment removed for export] *) replace (skipn (Z.to_nat (cl + 6)) fdata) with (@nil byte).
        2:{ symmetry. apply skipn_all2. cbv delta [Ln] in *. lia. }
        split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - (* [comment removed for export] *)
      replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HK2 | apply (T3m_steps (hcs asegs R HIA h)) |].
      cbn beta. intros ms3 mo3 -> HK3 MM3. unfold TREGS. rewrite <- HMALLOC.
      eapply (heapA_malloc_split _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                bvmap_empty (Z_to_bv 32 0) m1 mo3 h [(buf, cap)] [] plen (arl_stklo R) 0);
        rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
        [ exact HH1 | exact HK3 | exact ST1 | lia | cbv delta [tsp]; lia | rewrite HT; cbv delta [tsp]; lia | cbv delta [tsp]; lia
        | exact MI1 | rewrite HTP; reflexivity | reflexivity | unfold AMAX; cbv delta [Ln] in *; lia
        | (* [comment removed for export] *)
          destruct (Z_lt_le_dec plen AMAX_SEC) as [SMALL|BIG]; [right | left; lia];
          destruct FRSH0 as [[C1 C2] | ALL]; [| apply ALL];
          apply FRSH; intros E; pose proof (hd_pclass_batch _ _ _ HID plen E); cbv delta [Ln] in *; lia
        | unfold AVOL_CALL in *; lia
        | unfold AVOL_CALL in *; cbv delta [Ln] in *; lia   (* [comment removed for export] *)
        | apply uwc_data; [lia | rewrite STKLO; cbv delta [Ln] in *; lia]   (* [comment removed for export] *)
        | pose proof (FFR_max 0 ltac:(lia)); unfold fr_charge; lia
        | intros _; eapply Z.le_lt_trans; [apply cnt24_le_length| cbn [length]; unfold C24MAX; lia]   (* [comment removed for export] *)
        | apply t_emit_has_nil | unfold SUCC; apply t_emit_has_nil | | ].
      + (* [comment removed for export] *)
        intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo4 h4 MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HFRESH4 HH4.
        reg_lit 0x097414.
        assert (TR4 : rw_cells asegs m4 tsp (TRFA junk x7 (nth 1 fdata (Z_to_bv 8 0)) plen (buf + 2 + cl + 4) cl buf)).
        { eapply (presA_rw_cells asegs R); [exact HP4 | exact TR1 | apply client_range_stack; lia | exact I]. }
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
          [exact HK4 | eapply (L5n_steps (hcs asegs R HIA h4)); [exact TR4 | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | rewrite STKLO; cbv delta [tsp]; lia | rewrite HS4, HS; cbv delta [tsp]; lia]] |].
        cbn beta. intros ms5 mo5 -> HK5 MM5.
        change (t_emit (W 1 []) (t_exit (exit_code (status 2 (nth 1 fdata (Z_to_bv 8 0)))) fs0))
          with (t_emit (W 1 (zero_lines (0 - 1))) (t_exit (exit_code (status 2 (nth 1 fdata (Z_to_bv 8 0)))) fs0)).
        eapply (ret_finA buf cap cl plen x7 0 2 [(buf, cap)]); first
          [ lia | right; reflexivity | exact HH4 | left; reflexivity | exact HK5
          | rewrite HT4; exact HT | rewrite HS4; exact HS | unfold AVOL_CALL in *; lia | pose proof (FFR_max 0 ltac:(lia)); unfold fr_charge in *; lia
          | rewrite (mo_mat_fs _ _ MM5), (A_main_fin.mo_frame_fs _ _ MF4), (mo_mat_fs _ _ MM3); exact FS2
          | rewrite (A_main_fin.mo_mat_fds _ _ MM5), (A_main_fin.mo_frame_fds _ _ MF4), (A_main_fin.mo_mat_fds _ _ MM3); exact FDS2'
          | eapply tmem_presA; [exact TX1 | exact HP4 | intros a Ha; exact I | exact HH4 | exact MI4]
          | (eapply (@A_main_fin.atx_presA R HIA HID sp0 SPlo); [ | exact HP4 | intros a Ha; exact I ];
             exists (bv_unsigned fv =? 0), (Z_to_bv 8 0), jp, jq, jf; split; [exact AT1 | intros _; exact IC1])
          | eapply (presA_rw_cells asegs R); [exact HP4 | exact FR1 | apply client_range_stack; cbv delta [tsp msp]; lia | exact I]
          | idtac ].
        pose proof (stk_release asegs m4 (arl_stklo R) tsp _ ST4 TR4 ltac:(rewrite STKLO; cbv delta [tsp]; lia)) as ST4'.
        unfold TRFA in ST4'. cbn [cells_size csize Nat.add] in ST4'. replace (tsp + Z.of_nat 80) with msp in ST4' by (cbv delta [tsp msp]; lia). exact ST4'.
      + (* [comment removed for export] *)
        intros t0' t1' t2' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' m4 mo4 h4 D jD MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HFRESH4 AL16 FRESH DBLK HH4 RW4.
        reg_lit 0x097414.
        destruct (hm_apart _ _ HIA h4 _ _ m4 HH4) as [HBLKS _]. pose proof (Forall_inv HBLKS) as AB. cbn [fst snd app] in AB. destruct AB as (AB1 & AB2 & AB3 & AB4).
        pose proof FRESH as FRESH'. destruct FRESH' as (FA1 & FA2 & FA3 & FA4). specialize (FA4 buf cap ltac:(cbn; left; reflexivity)).
        pose proof (hd_blk_band _ _ _ HID h4 _ _ m4 D plen HH4 ltac:(left; reflexivity)) as (DLO & DCE & DHI).
        assert (TR4 : rw_cells asegs m4 tsp (TRFA junk x7 (nth 1 fdata (Z_to_bv 8 0)) plen (buf + 2 + cl + 4) cl buf)).
        { eapply (presA_rw_cells asegs R); [exact HP4 | exact TR1 | apply client_range_stack; lia | exact I]. }
        assert (FR4 : rw_cells asegs m4 msp (A_main_loop.FRAMEA sp0 pad)).
        { eapply (presA_rw_cells asegs R); [exact HP4 | exact FR1 | apply client_range_stack; cbv delta [tsp msp]; lia | exact I]. }
        assert (AX4 : exists (b : bool) (jp jq jf : list byte), atexit_cells b m4 (Z_to_bv 8 0) jp jq jf).
        { destruct AX1 as (bb & jp' & jq' & jf' & AT4). exists bb, jp', jq', jf'. unfold atexit_cells in *.
          eapply (presA_rw_cells asegs R); [exact HP4 | exact AT4 | | exact I].
          intros a Ha. right; left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. cbn in Ha. lia. }
        assert (IC4 : incbA m4 (Z_to_bv 8 0)).
        { unfold incbA in *. eapply (presA_rw_cells asegs R); [exact HP4 | exact IC1 | | exact I].
          intros a Ha. right; left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. cbn in Ha. lia. }
        assert (BY4 : bytes_at asegs m4 buf fdata).
        { eapply (presA_bytes_at asegs R); [exact HP4 | exact BY1 | | cbn; exact I].
          eapply client_range_block; [apply in_app_iff; left; left; reflexivity | lia | cbv delta [Ln] in *; lia]. }
        pose proof (bytes_at_skipn m4 buf fdata (Z.to_nat (cl + 6)) BY4 ltac:(cbv delta [Ln] in *; lia)) as PAY4. rewrite Z2Nat.id in PAY4 by lia.
        assert (PLEN : Z.of_nat (length (skipn (Z.to_nat (cl + 6)) fdata)) = plen) by (rewrite length_skipn; cbv delta [Ln] in *; lia).
        (* [comment removed for export] *)
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
          [exact HK4 | apply (T4_steps (hcs asegs R HIA h4)); lia |].
        cbn beta. intros ms5 mo5 -> HK5 MM5. unfold TREGS. rewrite <- HMEMCPY.
        pose proof RW4 as RW4'. destruct RW4' as [[WF4 _] _]. cbn in WF4. destruct WF4 as [LJ _].
        pose proof (u8arr_of_rw_cells asegs m4 D _ jD RW4) as U4.
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4)); [exact HK5 | |].
        { eapply (artA_amemcpy _ _ HIA (arl_memcpy_i R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   bvmap_empty (Z_to_bv 32 0) m4 h4 ((D, plen) :: [(buf, cap)]) [] D (buf + (cl + 6)) plen (arl_stklo R));
            rewrite ?unsigned_lit by (cbv delta [tsp]; lia);
            [ right; left; reflexivity | exact HH4 | exact U4 | exact PAY4 | rewrite LJ; lia | exact PLEN
            | eapply aobj_sub; [eapply (hm_aobj_block _ _ HIA h4); [exact HH4 | left; reflexivity] | lia | lia]
            | eapply aobj_sub; [eapply (hm_aobj_block _ _ HIA h4); [exact HH4 | right; left; reflexivity] | lia | lia]
            | right; lia
            | exact ST4 | lia | cbv delta [tsp]; lia
            | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | lia | rewrite HS4, HS; cbv delta [tsp]; lia]
            | exact MI4
            | rewrite HS in DBLK; destruct DBLK as [DK|DK]; [left; lia | right; cbv delta [tsp]; lia]
            | destruct BR as (BR1 & [BR2|BR2] & BR3); [left; cbv delta [Ln] in *; lia | right; cbv delta [tsp]; lia]
            | right; pose proof HCEIL; lia
            | right; pose proof HCEIL; cbv delta [Ln] in *; lia
            | lia
            | eapply client_wrange_block; [apply in_app_iff; left; left; reflexivity | lia | lia]
            | rewrite HT4, HT; cbv delta [tsp]; lia
            | reflexivity | f_equal; lia | reflexivity ]. }
        cbn beta. intros ms6 mo6 P6 HK6 MM6. destruct P6 as (u0 & u1 & u2 & r6 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m6 & -> & MU6 & WM6 & MI6 & -> & U6 & ST6 & HH6).
        rewrite ?unsigned_lit in MU6, ST6 by (cbv delta [tsp]; lia). reg_lit 0x097428.
        (* [comment removed for export] *)
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
          [exact HK6 | apply (T5_steps (hcs asegs R HIA h4)) |].
        cbn beta. intros ms7 mo7 -> HK7 MM7.
        unfold SUCC. replace (exit_code 0) with (exit_code (status 0 (nth 1 fdata (Z_to_bv 8 0)))) by (rewrite status0; reflexivity).
        eapply (piter1A buf cap cl plen D D junk x7) with (h := h4) (LB := (D, plen) :: [(buf, cap)]) (icb := Z_to_bv 8 0) (calls := CALLS fdata cl).
        all: lazymatch goal with
             | |- havol _ _ _ _ + _ + _ <= _ => pose proof (rsum_le4 (CALLS fdata cl) ltac:(lia)); unfold AVOL_CALL in *; lia
             | |- hfr _ _ _ _ + _ + _ <= _ => pose proof (fsum_le4 (CALLS fdata cl) ltac:(lia)); unfold fr_charge in *; lia
             | |- cnt24 ?lb + _ + _ <= _ =>   (* [comment removed for export] *)
                 pose proof (cnt24_le_length lb) as CLEN; cbn [length] in CLEN;
                 pose proof (Z.div_pos plen 5889 ltac:(lia) ltac:(lia)) as QP;
                 pose proof (csum_le4 (plen / 5889) (CALLS fdata cl) QP ltac:(lia)) as CS4;
                 assert (QB : plen / 5889 <= 11396) by (apply Z.div_le_upper_bound; [lia|]; pose proof (cap_ok_bounds sp0 cap COK); cbv delta [Ln] in *; lia);
                 unfold C24MAX; clear - CLEN CS4 QB QP C24F_max; lia
             | |- _ => try first [exact Hcl | exact Hplen | exact HL | exact COK | exact LCAP | exact BR | exact BLO | exact CR]
             end.
        assert (HH6' : HM asegs R HIA h4 ((D, plen) :: [(buf, cap)]) [] m6) by exact HH6.
        split.
        * exact HH6.
        * exact HK7.
        * rewrite HT4. exact HT.
        * rewrite HS4. exact HS.
        * right. left. reflexivity.
        * right. rewrite HS in DBLK. repeat split; first [reflexivity | left; reflexivity | lia | exact DBLK].
        * eapply tmem_munch; [| exact MU6 | exact WM6 | | exact HH6 | exact MI6].
          { eapply tmem_presA; [exact TX1 | exact HP4 | intros a Ha; exact I | exact HH4 | exact MI4]. }
          intros a (Ha & Hb & Hc). unfold drv_static in Ha. cbn. rewrite STKLO. cbv delta [tsp]. lia.
        * eapply si_munch; [| exact MU6 | intros a NO; pose proof (SIFP a NO); cbn; rewrite STKLO; cbv delta [tsp]; lia].
          eapply si_heap_presx; [exact SI1 | eapply presA_presx; exact HP4 | intros; exact I].
        * exact ST6.
        * eapply (sshad_keep_munch R HIA h4 _ _ m4 m6 D (D + plen) msp); [exact HH4 | | | exact WM6 | | rewrite HS4, HS; cbv delta [msp]; lia].
          -- eapply (presA_sshad asegs R); [exact HP4 | exact SSH1 | lia | rewrite HS; cbv delta [msp]; lia].
          -- eapply munch_weaken; [| exact MU6]. unfold sub_fp; cbn [outside]; intros x Hx; cbv delta [tsp msp] in *; lia.
          -- replace (D + plen - D) with plen by lia. eapply (hcs_block _ _ HIA h4); [exact HH4 | left; reflexivity].
        * eapply rw_cells_transport; [exact TR4 | exact MU6 | exact WM6 | cbn [cells_size csize TRFA Nat.add disjoint_from fst snd]; rewrite STKLO; cbv delta [tsp]; lia].
        * eapply rw_cells_transport; [exact FR4 | exact MU6 | exact WM6 | cbn [cells_size csize A_main_loop.FRAMEA Nat.add disjoint_from fst snd]; rewrite STKLO; cbv delta [tsp msp]; lia].
        * rewrite (mo_mat_fs _ _ MM7), (mo_mat_fs _ _ MM6), (mo_mat_fs _ _ MM5), (A_main_fin.mo_frame_fs _ _ MF4), (mo_mat_fs _ _ MM3). exact FS2.
        * rewrite (A_main_fin.mo_mat_fds _ _ MM7), (A_main_fin.mo_mat_fds _ _ MM6), (A_main_fin.mo_mat_fds _ _ MM5), (A_main_fin.mo_frame_fds _ _ MF4), (A_main_fin.mo_mat_fds _ _ MM3). exact FDS2'.
        * destruct U6 as [BY6 _]. exact BY6.
        * destruct AX4 as (bb & jp' & jq' & jf' & AT4). exists bb, jp', jq', jf'. unfold atexit_cells in *.
          eapply rw_cells_transport; [exact AT4 | exact MU6 | exact WM6 | cbn [cells_size csize Nat.add disjoint_from fst snd]; rewrite STKLO; cbv delta [tsp]; lia].
        * unfold incbA in *. eapply rw_cells_transport; [exact IC4 | exact MU6 | exact WM6 | cbn [cells_size csize Nat.add disjoint_from fst snd]; rewrite STKLO; cbv delta [tsp]; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Target.
