(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_read_binary P_rsa_parse_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_stmtA A_asn1_get_tag_stmt A_mpi_read_binary_stmt A_mpi_read_binary A_mpi_bitlen A_rsa_check_context A_rsa_check_pubkey A_rsa_complete.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00ffce20fcf3c0ae 0 6 0 1 46 1 47 1 48 1 56 1 57 1P0113d07910327600 0 4 0 1 44 1 56 1 57 1P01b32399993a7132 0 4 0 1 68 1 69 1 70 1P01b5de3abbf7e4cf 0 7 0 1 37 1 68 1 69 1 70 1 78 1 79 1P035673dec9f684e9 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P037f17669870b403 0 5 0 1 46 1 48 1 56 1 57 1P04082291d321663b 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P04fe25bcc04c6c00 1 1 16 3 0 1 80 1 81 1 8 43 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P0620a8898ab9a1f1 0 6 0 1 46 1 47 1 48 1 56 1 57 1P07815a1fdf4d0844 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P079d7ec2cb907d6d 0 6 0 1 46 1 47 1 48 1 56 1 57 1P07ed482d63f59502 1 2 32 3 1 1 79 1 82 1 32 8 38 1 43 1 66 1 69 1 70 1 71 1 80 1 81 1 2 83 1 84 1P084d0d4d7db92b7e 0 3 0 1 39 1 43 1P086f7e9413fd72ec 0 5 0 1 46 1 48 1 56 1 57 1P08a8cc42a39cfdee 0 4 0 1 44 1 56 1 57 1P08c59b05e4a62fbf 0 5 0 1 46 1 48 1 56 1 57 1P097c5198ffacc79f 0 4 0 1 44 1 56 1 57 1P0a4d25f10cb977ad 0 4 0 1 44 1 56 1 57 1P0a69769380f20d94 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P0adc9533d751a292 0 4 0 1 68 1 69 1 70 1P0b295a20d0c98d2a 0 4 0 1 68 1 69 1 70 1P0b335afe05568a82 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P0c59c8f424decec6 1 1 16 3 0 1 79 1 80 1 8 42 4 65 4 68 4 69 4 70 4 78 4 81 4 82 64P0cd74251c1771e55 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P0cf6d2623c9bda5f 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P0d419e01a038302d 0 3 0 1 37 1 67 1P0d58be71dff7359c 1 1 16 3 0 1 80 1 81 1 8 43 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P0d869e67ffe6cbcd 0 4 0 1 56 1 57 1 58 1P0d9813c168fc518c 0 6 0 1 46 1 47 1 48 1 56 1 57 1P0df3dc2e65528d8a 1 1 64 2 9 1 78 1 3 0 1 79 1 80 64P0e21c55b11617b00 0 5 0 1 46 1 48 1 56 1 57 1P0e3678095a1ea474 1 1 16 2 26 1 56 1 3 0 1 57 1 58 16P0e6ebd5fc01a3225 0 3 0 1 37 1 67 1P0eac2702b6ff7a64 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P0ed1487427541971 0 3 0 1 37 1 67 1P0f034378d2482e2d 0 3 0 1 37 1 67 1P0f92af0d5b079bdb 0 6 0 1 46 1 47 1 48 1 56 1 57 1P101d10e11153c660 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P104375b696a77495 0 4 0 1 44 1 56 1 57 1P10b29c9744466cdf 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1120eb49f424076a 0 3 0 1 36 1 38 1P114a32ebd74f14cb 0 4 0 1 68 1 69 1 70 1P1169cf4666a7871d 0 5 0 1 46 1 48 1 56 1 57 1P1223831e459658b4 0 4 0 1 44 1 56 1 57 1P1236e256d9b5e06c 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P123bd1b1670661aa 0 4 0 1 68 1 69 1 70 1P1289cd7ca899e930 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P130cb42cd50229f2 0 5 0 1 46 1 48 1 56 1 57 1P13723e5adfa872c6 1 1 16 3 0 1 80 1 81 1 8 43 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P13ee1b15630308c4 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P13f6c665a57e397a 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P14025ec87e750287 1 2 32 3 0 1 62 1 65 1 32 3 1 1 63 1 64 1 2 66 2 67 2P1445282cbd49bad5 0 4 0 1 44 1 56 1 57 1P1570751869d70bc9 0 3 0 1 37 1 67 1P157deef46fbaede8 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P158bbe49e3df087b 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P16d39271a6e0dcfe 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P16ee4211f94cacca 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P16f11d9c9c1dd729 0 5 0 1 46 1 48 1 56 1 57 1P172973134c20219f 0 4 0 1 68 1 69 1 70 1P174dda29a17a3b61 1 1 16 3 0 1 80 1 81 1 8 43 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P17e164bf371acbc5 0 6 0 1 53 1 56 1 66 1 78 1 79 1P17f91bb35250d730 0 4 0 1 44 1 56 1 57 1P18a44275550428d1 0 4 0 1 44 1 56 1 57 1P18f6b4052c0ea21a 0 6 0 1 46 1 47 1 48 1 56 1 57 1P19ec7663583d424f 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P19f746dbf2c326eb 0 4 0 1 44 1 56 1 57 1P1a7f34eee3c33213 0 4 0 1 68 1 69 1 70 1P1a9e936fe2000fbc 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1b0e6e5216255304 0 3 0 1 37 1 67 1P1b395057cfdb3bd8 0 5 0 1 46 1 48 1 56 1 57 1P1bc446f2dfa5cd3c 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1bd7111e6549312b 1 1 16 2 1 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1d3c07786bca2a21 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1e3790f90bb10e5e 0 6 0 1 46 1 47 1 48 1 56 1 57 1P1e7464746839adbd 0 4 0 1 44 1 56 1 57 1P1e957a676fbacf84 0 7 0 1 26 1 56 1 57 1 58 1 61 1 62 1P1ef96de6d630f6fd 0 6 0 1 46 1 47 1 48 1 56 1 57 1P1efe9b45eeeefa9f 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P1f04a7b465467f4f 0 6 0 1 25 1 37 1 55 1 61 1 62 1P1f3e19a7792f1839 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P1f58c8868e56bce0 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P201be874837d6ffd 0 4 0 1 25 1 73 1 74 1P20267d8ed5d82810 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P20606abe7e0b57cc 0 5 0 1 46 1 48 1 56 1 57 1P215cd5c77c53472e 0 4 0 1 25 1 73 1 74 1P21947cd0177124db 1 2 32 3 0 1 79 1 82 1 32 3 1 1 80 1 81 1 2 83 2 84 2P21cd97752ae09abc 0 3 0 1 37 1 67 1P222f04e0668ccdee 0 4 0 1 44 1 56 1 57 1P22a83283d82b8195 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P22c812322cd5f369 0 3 0 1 37 1 67 1P238335d9708aef1c 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P23db1037fc508e11 0 4 0 1 68 1 69 1 70 1P24848501471224ee 0 6 0 1 26 1 68 1 70 1 73 1 74 1P25483cd88d8fc428 0 6 0 1 46 1 47 1 48 1 56 1 57 1P260d70dae1e6e428 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2663f21a6e5db1c3 1 2 32 3 0 1 79 1 82 1 32 8 38 1 43 1 66 1 69 1 70 1 71 1 80 1 81 1 2 83 1 84 1P27a291d8c8e60fc8 0 5 0 1 46 1 48 1 56 1 57 1P282d708dc28a45e6 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P29cf43638c5fd68f 0 4 0 1 44 1 56 1 57 1P2a2fcf3d0e987b41 0 5 0 1 46 1 48 1 56 1 57 1P2a90d84ace5bf3cc 1 1 64 2 47 1 62 1 3 0 1 61 1 63 64P2adb6beee39e98ee 1 1 64 2 0 1 61 1 3 2 1 62 1 63 64P2b5297319bfc4807 1 2 32 3 0 1 79 1 82 1 32 3 1 1 80 1 81 1 2 83 2 84 2P2b84d262643c4fbe 0 6 0 1 46 1 47 1 48 1 56 1 57 1P2bc59d1bde01ed0b 0 4 0 1 25 1 73 1 74 1P2c19213bf468d1e1 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P2c4c4862a9db77b2 0 5 0 1 46 1 48 1 56 1 57 1P2c73343f4373fce6 0 5 0 1 46 1 48 1 56 1 57 1P2c9345e074ecae7e 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2c977c9846035ba5 0 3 0 1 37 1 55 1P2d410a302dd3a1a7 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P2e78d6db06ce925a 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P2ea244eeaf3015be 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P2f2fc0e4d9f4c6dc 1 1 64 2 1 1 61 1 3 0 1 62 1 63 64P2fef525590471d4b 0 8 0 1 47 1 51 1 57 1 58 1 59 1 62 1 63 1P30033cfb8ac5521c 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P3079e4dce8bfbf8d 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P30d7051a986e9f49 0 3 0 1 37 1 67 1P30d7b2c78a33aac3 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P310693bd3ee4493d 0 6 0 1 46 1 47 1 48 1 56 1 57 1P31cbe6086801184b 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P321162cf289d2f58 0 4 0 1 68 1 69 1 70 1P324bcd915e43f23f 1 1 64 2 0 1 78 1 3 6 1 79 1 80 64P32d2850ea60e3405 0 4 0 1 68 1 69 1 70 1P333590fd26c8f99e 0 5 0 1 68 1 70 1 78 1 79 1P33435d4ae8cc25d3 0 4 0 1 25 1 73 1 74 1P33ffddb9930960f9 0 4 0 1 68 1 69 1 70 1P358bc8b9ee905a9e 1 2 32 3 0 1 79 1 82 1 32 3 1 1 80 1 81 1 2 83 2 84 2P35a97c720c08c867 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P368f12406b007e52 0 3 0 1 37 1 67 1P36bfe06b1e6415f7 1 2 16 3 0 1 32 1 58 1 16 3 1 1 31 1 57 1 2 59 1 60 1P36e22e87aee09d1a 0 6 0 1 46 1 47 1 48 1 56 1 57 1P36feed8bc26d549b 0 6 0 1 46 1 47 1 48 1 56 1 57 1P377b3b94043d8e9e 0 6 0 1 37 1 68 1 70 1 78 1 79 1P3783c87d513e1152 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P3807446843a801c0 0 3 0 1 37 1 67 1P3828a53b1e3a485a 1 2 32 3 0 1 78 1 81 1 32 8 37 1 42 1 65 1 68 1 69 1 70 1 79 1 80 1 2 82 1 83 1P3a1fff78ce39f65e 1 2 32 3 0 1 78 1 81 1 32 8 37 1 42 1 65 1 68 1 69 1 70 1 79 1 80 1 2 82 1 83 1P3bdba9613db966ac 0 4 0 1 68 1 69 1 70 1P3c199b34fb42e507 1 1 16 3 1 1 31 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P3c6459dc2feff384 0 4 0 1 68 1 69 1 70 1P3c6473b8a6e9dc39 0 3 0 1 37 1 67 1P3d8023c0e22aa6a7 1 1 16 2 0 1 56 1 3 4 1 57 1 58 16P3df019975d32c85b 0 3 0 1 37 1 67 1P3df7c6080fbb6e55 0 4 0 1 44 1 56 1 57 1P3e3fca3fc4ee65b9 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16P3f1d68224d8b6a0a 0 6 0 1 46 1 47 1 48 1 56 1 57 1P3f3cde76e7f2d67e 0 5 0 1 46 1 48 1 56 1 57 1P3fabcee4fce8e887 1 1 16 4 1 1 33 1 35 1 57 1 7 38 1 44 1 47 1 48 1 49 1 58 1 59 16N00eec77663c50993N015a3852778b9b07N017f3ed77744ab29N0285f5e686e65d6cN03b8cd67e2d13418N0409ac4ca12b5367N04b16e3d9fb8641cN05e8b859ea4fbd9dN0667d10198296bf5N0691ee3327c1b45dN08dab2c0adb2b87cN0ac4295ab024587dN0b1da67b42e2e931N0d58fa05a920b82dN0db0ef27b7e1e10eN0e05dd9bfba53267N0e5a497e8867133fN0e6bc1b5dfd4d341N0f03d1e0d13dda77N1029cf6f894fd45fN10caa5561714f7cdN1185a203856d040fN11d7467fa94ce4bcN1214fa94f3d783a7N122ad93b3080c783N12b246960aadc551N131c0ac7857e9fceN13d888aca1ded139N141548199bf89aa8N1450b8321f3fcee8N148ce028455e7689N1511e26b49784441N155538c3517882e2N183e46dad4edccddN1af6ca8920e52109N1bbf21da7c2a0d51N1cae24ce8f1a586bN1d4091ae0a647a0fN1dea978c1d17200fN211af21e6a2e7124N2338b9c802ac13a6N2387eff2896d9b16N24f80d9d0bd3a6a8N26f06af7d473ea1bN279f2660a3b94471N27a7e9a3700d5f7cN285181cf38737f0dN29cc86d41b0c8258N2b7330af9f1e7a22N2c830cbd87d297b1N2ca1408676487e47N2d4e1e28069ada6bN2dc5df4f4b9f2cd3N301ac5c40af2b1f5N32509d35ca727bc6N32ea6dd64b464d99N339c7c83c393b6c0N357beb2c4ab57e4aN39459cc3ad926af7N3984e65eb4a3aa1aN3b11963a1e03cd3dN3b30d6457d7b4147N3edafd51f45755afN3f767d04def91156"%lxh.
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
Ltac2 gd_tbl_A_rsa_parse_pubkey () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RSA_PP_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RSA_PP_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_limb_blocks"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "C24_RSA_PP"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "rsa_parse_pubkey_postA"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.mkRSA"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkRP.Call.S1P"; "A_RSA_PARSE_PUBKEY"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "WalkRP.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "WalkRP.Call.EPIQ"; "WalkRP.Call.CALLQ"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.asn1_get_tag_stmtA"; "A_ASN1_GET_TAG_RP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.mpi_size_stmtA"; "A_MPI_SIZE_RP"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_complete.rsa_complete_stmtA"; "A_RSA_COMPLETE_RP"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_check_pubkey.rsa_check_pubkey_stmtA"; "A_RSA_CHECK_PUBKEY_RP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary.mpi_read_binary_stmtA_r"; "rsa_parse_pubkey_stmtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "A_UAR_GOT_RP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "A_SMALLOC_1_RP"].


Definition A_RSA_PARSE_PUBKEY : Z := 0x0b28e4.      (* [comment removed for export] *)
Definition A_SMALLOC_1_RP : Z := 0x5306c.            (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_RP : Z := 0x0f5ea8.             (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASN1_GET_TAG_RP : Z := 0x09990c.        (* [comment removed for export] *)
Definition A_MPI_SIZE_RP : Z := 0x09c91c.            (* [comment removed for export] *)
Definition A_RSA_COMPLETE_RP : Z := 0x0b2404.        (* [comment removed for export] *)
Definition A_RSA_CHECK_PUBKEY_RP : Z := 0x0b26e0.    (* [comment removed for export] *)

(* [comment removed for export] *)
Notation RSA_PARSE_PUBKEY_STACK_A := 528 (only parsing).
(* [comment removed for export] *)
Definition RSA_PP_PHI (len : Z) : Z := 2 * MPI_RB_PHI len.
Definition RSA_PP_FR : Z := 2 * MPI_RB_FR 28.
(* [comment removed for export] *)
Definition C24_RSA_PP : Z := 2.

Definition rsa_parse_pubkey_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C LEN lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1=.O1<.O1;.)Lh',(5.O1=.O1<.O1;.)(1.(6.$7.)LLB',(6.$7.)(1.$8.Lr',$8.(9.(:.$0.R15.(;.(<.(=.O17.O16.O15.O14.R14.R13.R12.O13.O12.R11.R10.R?.R>.R=.R<.R;.R:.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R9.R8.R7.R6.)O7.(>.O17.)O6.(?.(2.&40.))R5.(10.O1=.))R4.))(9.(11.O1=.R5.)(9.(12.O1=.R5.O3.(13.&40.O16.))(9.(14.O1.R4.)(9.(15.O1=.O1<.O19.O18.(13.&40.O16.)(16.O1<.)(17.O1=.O1<.O1;.O1:.)(18.(19.$1:.$1:.)(1;.$1:.$1:.O5.(1<.O5.$1=.))(1>.(19.$1:.$1:.)))O2.R5.)(9.(:.$1:.(1?.O1=.O1<.O1;.R3.)(1?.O1=.O1<.O1;.O1:.))(9.(:.$1:.(17.O1=.O1<.O1;.R3.)(17.O1=.O1<.O1;.O1:.))(9.(:.$1:.(20.O1=.O1<.O1;.R3.)(20.O1=.O1<.O1;.O1:.))(9.(21.O1=.O1<.O1;.R3.R4.)(9.Px,$1:.P,(22.O1=.O1<.O1;.O1:.R1.)(22.O1=.O1<.O1;.R5.R2.)(9.(23.(24.O1=.O1<.O1;.R3.)(1<.(24.O1=.O1<.O1;.O1:.)(25.O4.)))(9.(23.(26.O1=.O1<.O1;.R3.)(1<.(26.O1=.O1<.O1;.O1:.)$27.))(9.(28.O1=.O1<.O1;.R3.R2.O18.R5.)(9.(29.O1=.R5.R2.O5.R1.)(9.Pb,$7.P,(2:.$7.R1.R3.)(2;.(2:.$7.R2.O19.)(2:.$7.R2.(2<.R3.)))(9.Pb,$7.P,(2:.$7.R1.O19.)(2:.$7.R2.R4.)(9.Pb,$7.P,(2:.$7.R1.(2<.R2.))(2=.(2:.$7.R2.O19.))Pb,$7.P,(2:.$7.R1.(2<.R2.))(2>.O1<.O19.O18.(2?.$1:.$1:.R2.)(30.$1:.$1:.R2.)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_parse_pubkey_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
  forall (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (C KEY : Z) (kbs : list byte) (lo slo : Z),
    HM segs R HIA h LB LF m ->
    HK segs R HIA h mo ->
    (length LF < 511)%nat ->
    rsa_at segs m LB C (rsa_fresh C) ->
    bytes_at segs m KEY kbs ->
    0 < KEY ->
    KEY + Z.of_nat (length kbs) + 8 <= 2^47 ->
    client_range (arl_L R) (LB ++ fdata LF) lo KEY (Z.of_nat (length kbs)) ->
    (KEY + Z.of_nat (length kbs) <= C \/ C + RSA_CTX_SIZE <= KEY) ->
    (KEY + Z.of_nat (length kbs) <= lo \/ bv_unsigned sp <= KEY) ->
    stk segs m lo (bv_unsigned sp) ->
    arl_stklo R <= lo ->
    lo <= bv_unsigned sp - RSA_PARSE_PUBKEY_STACK_A - arl_need_rt R ->
    lo <= bv_unsigned sp - 448 - arl_need_smalloc R ->
    bv_unsigned sp <= htop segs R HIA h ->
    bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 (arl_tp R) ->
    sshad segs (arl_AL R) m slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= bv_unsigned sp - 432 ->
    mem_inv segs m ->
    bv_unsigned ra mod 2 = 0 ->
    aobj segs (arl_AL R) (hcs segs R HIA h) m KEY (Z.of_nat (length kbs)) ->
    havol segs R HIA h + RSA_PP_PHI (Z.of_nat (length kbs)) <= AVOL_MAX ->
    hfr segs R HIA h + RSA_PP_FR <= FR_MAX ->
    cnt24 LB + C24_RSA_PP <= C24MAX ->
    a0 = Z_to_bv 64 C ->
    a1 = Z_to_bv 64 KEY ->
    a2 = Z_to_bv 64 (Z.of_nat (length kbs)) ->
    aevtS segs (rsa_parse_pubkey_postA segs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                  C (Z.of_nat (length kbs)) lo m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo)
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L14676016731.40L15382381096.44L19269540527.40L21811129065.44L23141643611.40L24940377400.40L27000635790.40L27822296331.44L28650195958.44L38887430997.40L39036920974.40L63109766798.40L63400080262.40L6426834318.40 00000300;00>00F00I00L00O00W00_00b00e00h00k00nS1CS1C1d2A2S1CS1C1d2A1S1CS1CS1CS1C1d2A2S1C1d2A1S1CS1CS1CS1CS1C". (* [comment removed for export] *)
Lemma rsa_at_presx_len : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Psegs,(6.$4<.)PL,$4=.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PLBp,(6.$7.)PSP,$1:.PX,(6.$4>.)PC,$1:.Pr,$8.Plen',$1:.P,(29.R;.R9.R7.R3.R2.)P,(4?.R<.R;.R7.R6.R5.R:.R9.)P,(11.R=.R;.)P,(11.R>.R;.)P,(50.R?.R<.R7.(18.$51.(52.(41.&40.=))(18.$51.(52.(41.&40.=))(18.$51.(53.(41.&40.R5.))(1>.$51.)))))P,(9.(23.=R6.)(36.R6.(38.+2.+40.)))P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R9.+>8.)R<.)P,Pb,$7.P,(2:.$7.R1.(2<.R:.))(2:.$7.R2.R?.)P,(54.R<.(1<.R;.+10.)+=8.)P,Pb,$7.P,(2:.$7.R1.(2<.R<.))(54.R?.(2?.$1:.$1:.R2.)(30.$1:.$1:.R2.))(29.R15.R12.R11.R=.(55.R;.(56.R<.)(57.R<.)))")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBp SP X C r len' RAT PX MI MI' HD' LB' CINp SUBL DX DL.
  flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
  pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
  assert (CR : forall a n, C <= a -> a + n <= C + 232 -> client_range L LBp SP a n)
    by (intros a n H1 H2; eapply client_range_blk; [exact CINp| exact H1| exact H2]).
  assert (FLD : forall d, mpdr_at segs m LB d -> C + 16 <= md_addr d -> md_addr d + 16 <= C + 232 ->
                          (forall b, In b (mpd_blk d) -> In b LBp /\ disjoint_from X (fst b) (snd b)) -> mpdr_at segs m' LB d).
  { intros d Hd A1 A2 HB.
    eapply (relb segs m' LBp LB d).
    - eapply mpdr_at_presx; [exact Hd| exact PX| exact MI| exact MI'| apply CR; lia| eapply disjoint_from_sub; [exact DX| lia| lia]|].
      intros HO. destruct (HB (md_p d, 4 * md_n d)) as [B1 B2]; [unfold mpd_blk; rewrite HO; left; reflexivity|]. split; [exact B1| exact B2].
    - intros HO. flat constr:(Hd) 6%nat. flclear Hd. intros _ _ _ _ _ OW. rewrite HO in OW. exact (proj1 (proj2 OW)). }
  split; [exact HD'|].
  split. { eapply heap_presx_rw_cells; [exact PX| exact HT| apply CR; cbn; lia| eapply disjoint_from_sub; [exact DX| cbn; lia| cbn; lia]]. }
  cbn [r_N r_E r_len].
  split; [exact AN|]. split; [exact AE|]. split; [exact OKN|]. split; [exact OKE|]. split; [exact LB'|].
  split.
  { unfold rsa_mpds. cbn [r_N r_E]. constructor; [| constructor].
    - apply FLD; [exact MN| rewrite AN; lia| rewrite AN; lia|].
      intros b Hb. split; [apply SUBL| apply DL]; unfold rsa_limb_blocks; apply in_or_app; left; exact Hb.
    - apply FLD; [exact ME| rewrite AE; lia| rewrite AE; lia|].
      intros b Hb. split; [apply SUBL| apply DL]; unfold rsa_limb_blocks; apply in_or_app; right; exact Hb.
    - eapply (zeros_relb segs C m' LBp LB). eapply (zeros_presx segs L); [exact ZS| exact PX| exact MI| exact MI'| exact CINp| eapply disjoint_from_sub; [exact DX| lia| lia]]. }
  split; [exact CAL'|]. split; [exact C0'|]. split; [exact CB|]. split; [exact CINq|].
  split; [exact PN|]. split; [exact PE| exact PNE].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L23346303057.20L27805029925.20L6445878994.20 L7319009201.20 00000300600900<S1CS1CS1CS1C". (* [comment removed for export] *)
Lemma rsa_at_presx : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Psegs,(6.$4<.)PL,$4=.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PLBp,(6.$7.)PSP,$1:.PX,(6.$4>.)PC,$1:.Pr,$8.P,(29.R:.R8.R6.R2.R1.)P,(4?.R;.R:.R6.R5.R4.R9.R8.)P,(11.R<.R:.)P,(11.R=.R:.)P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R6.+>8.)R9.)P,Pb,$7.P,(2:.$7.R1.(2<.R7.))(2:.$7.R2.R<.)P,(54.R9.R8.+>8.)P,Pb,$7.P,(2:.$7.R1.(2<.R9.))(54.R<.(2?.$1:.$1:.R2.)(30.$1:.$1:.R2.))(29.R12.R?.R>.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LBp SP X C r RAT PX MI MI' CINp SUBL DX DL.
  flat constr:(RAT) 8%nat. intros HD _ _ _ _ _ LEN _.
  replace r with (mkRSA (r_len r) (r_N r) (r_E r)) by (destruct r; reflexivity).
  eapply rsa_at_presx_len; [exact RAT| exact PX| exact MI| exact MI'| | exact LEN| exact CINp| exact SUBL| eapply disjoint_from_sub; [exact DX| lia| lia]| exact DL].
  eapply heap_presx_rw_cells; [exact PX| exact HD| eapply client_range_blk; [exact CINp| lia| cbn; lia]| eapply disjoint_from_sub; [exact DX| cbn; lia| cbn; lia]].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma rsa_limb_blocks_in : forall segs m LB C r b, rsa_at segs m LB C r -> In b (rsa_limb_blocks r) -> In b LB.
Proof.
  intros segs m LB C r b (_ & _ & _ & _ & _ & _ & _ & ALL & _) Hb.
  pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME.
  unfold rsa_limb_blocks in Hb. apply in_app_or in Hb.
  assert (K : forall d, mpdr_at segs m LB d -> In b (mpd_blk d) -> In b LB).
  { intros d (_ & _ & _ & _ & _ & OW) Hd. unfold mpd_blk in Hd. destruct (md_own d); [destruct Hd| | destruct Hd].
    destruct Hd as [<-|[]]. exact (proj1 (proj2 OW)). }
  destruct Hb as [Hb|Hb]; [exact (K _ MN Hb)| exact (K _ ME Hb)].
Qed.

Lemma rsa_limb_apart : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Psegs,(6.$4<.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PLBx,(6.$7.)PC,$1:.Pr,$8.Pb,$7.P,(29.R7.R6.R5.R3.R2.)P,(58.(3;.$7.R6.R5.))P,(2:.$7.R3.(2<.R4.))(2;.(23.(1<.(2?.$1:.$1:.R4.)(30.$1:.$1:.R4.))R6.)(23.(1<.R6.+>8.)(2?.$1:.$1:.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs m LB LBx C r [B k] RAT BA Hb. pose proof (rsa_limb_blocks_in segs m LB C r _ RAT Hb) as HIN.
  flat constr:(RAT) 15%nat. flclear RAT. intros _ _ _ _ _ _ _ _ _ _ _ CIN PN PE _. unfold RSA_CTX_SIZE in CIN.
  assert (NE : B <> C).
  { unfold rsa_limb_blocks in Hb. apply in_app_or in Hb.
    destruct Hb as [Hb|Hb]; unfold mpd_blk in Hb.
    - destruct (md_own (r_N r)) eqn:EO; try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as <- <-. exact (PN eq_refl).
    - destruct (md_own (r_E r)) eqn:EO; try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as <- <-. exact (PE eq_refl). }
  cbn [fst snd]. eapply (blocks_apart_in2 (LB ++ LBx)); [exact BA| apply in_app_iff; left; exact HIN| apply in_app_iff; left; exact CIN| exact NE].
Qed.


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11805470595.44L14678192461.44L19271554489.44L39839201721.44L41670513248.44L63398034576.44L6443992142.44 L7316765997.44 00000300600900<00?00B00E00HS1CS1CS1CS1CS1CS1CS1CS1C". (* [comment removed for export] *)
Lemma rsa_at_importN : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Psegs,(6.$4<.)PL,$4=.Pmq,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PLBq,(6.$7.)PLB2,(6.$7.)PLBp,(6.$7.)PSP,$1:.PC,$1:.Pr,$8.PdN',$59.P,(29.R;.R9.R7.R3.R2.)P,(:.$5:.(5;.(56.R3.))$5<.)P,(:.$5:.(5;.(57.R4.))$5<.)P,(5=.R>.R;.R9.R4.)P,(5>.R;.(56.R6.)R:.R5.)P,(4?.R10.R?.R:.R9.(18.(19.$1:.$1:.)(1;.$1:.$1:.(1<.R8.+10.)(1<.(1<.R8.+10.)+10.))(1>.(19.$1:.$1:.)))R>.R=.)P,(11.R11.R?.)P,(11.R12.R?.)P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R;.+>8.)R=.)P,P,(:.$5:.(5;.R:.)$5?.)(2=.(:.$1:.(60.R;.)R=.))(29.R15.R12.R10.R=.(55.(61.R<.)R;.(57.R<.)))")
(* [comment removed for export] *).
Proof.
  intros segs L mq m2 LBq LB2 LBp SP C r dN' RAT ON OE MN2 OUT PX MI MI2 CINp PNC.
  flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
  pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
  assert (BLKN : mpd_blk (r_N r) = []) by (unfold mpd_blk; rewrite ON; reflexivity).
  flat constr:(OUT) 5%nat. flclear OUT. intros AN2 NST2 O1 O2 O3. rewrite BLKN in O2. rewrite AN in AN2.
  assert (SUB : forall b, In b LBq -> In b LB2) by (intros b Hb; apply O2; [exact Hb| intros []]).
  assert (CR : forall a n, C <= a -> a + n <= C + 232 -> client_range L LBp SP a n)
    by (intros a n H1 H2; eapply client_range_blk; [exact CINp| exact H1| exact H2]).
  split. { eapply heap_presx_rw_cells; [exact PX| exact HD| apply CR; cbn; lia| cbn; lia]. }
  split. { eapply heap_presx_rw_cells; [exact PX| exact HT| apply CR; cbn; lia| cbn; lia]. }
  cbn [r_N r_E r_len].
  split; [exact AN2|]. split; [exact AE|].
  split. { split; [exact NST2|]. right. exact (proj2 MN2). }
  split; [exact OKE|]. split; [exact LEN|].
  split.
  { unfold rsa_mpds. cbn [r_N r_E]. constructor; [exact (proj1 MN2)|]. constructor.
    - eapply (null_relb segs m2 LBp LB2); [| exact OE].
      eapply mpdr_at_presx; [exact ME| exact PX| exact MI| exact MI2| rewrite AE; apply CR; lia| rewrite AE; cbn; lia| rewrite OE; intros; discriminate].
    - eapply (zeros_relb segs C m2 LBp LB2). eapply (zeros_presx segs L); [exact ZS| exact PX| exact MI| exact MI2| exact CINp| cbn; lia]. }
  split; [exact CAL'|]. split; [exact C0'|]. split; [exact CB|]. split; [apply SUB; exact CINq|].
  split; [exact PNC|].
  split; [rewrite OE; intros; discriminate|]. rewrite OE. intros _ X; discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11805470595.46L19271554489.46L23143660109.46L27806981305.46L41670513248.46L60601565920.48L63398034576.46L6443992142.46 L7316765997.46 00000300600900<00?00F00I00L00OS1CS1CS1CS1CS1CS1C1r1KS1CS1CS1C". (* [comment removed for export] *)
Lemma rsa_at_importE : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Psegs,(6.$4<.)PL,$4=.Pmq,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PLBq,(6.$7.)PLB2,(6.$7.)PLBp,(6.$7.)PSP,$1:.PC,$1:.Pr,$8.PdE',$59.P,(29.R;.R9.R7.R3.R2.)P,(:.$5:.(5;.(57.R3.))$5<.)P,(5=.R=.R:.R8.R3.)P,(5>.R:.(57.R5.)R9.R4.)P,(4?.R?.R>.R9.R8.(18.(19.$1:.$1:.)(1;.$1:.$1:.(1<.R7.+20.)(1<.(1<.R7.+20.)+10.))(1>.(19.$1:.$1:.)))R=.R<.)P,(11.R10.R>.)P,(11.R11.R>.)P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R:.+>8.)R<.)P,P,(:.$5:.(5;.(56.R:.))$5?.)(2:.(19.$1:.$1:.)(1;.$1:.$1:.(60.(56.R;.))(62.+4.(63.(56.R;.))))R>.)P,P,(:.$5:.(5;.(56.R;.))$5?.)(2;.(23.(1<.(60.(56.R<.))(62.+4.(63.(56.R<.))))R=.)(23.(1<.R=.+>8.)(60.(56.R<.))))P,P,(:.$5:.(5;.R;.)$5?.)(2=.(:.$1:.(60.R<.)R>.))P,P,(:.$5:.(5;.(56.R=.))$5?.)P,(:.$5:.(5;.R=.)$5?.)(2=.(:.$1:.(60.(56.R?.))(60.R>.)))(29.R17.R14.R12.R?.(55.(61.R>.)(56.R>.)R=.))")
(* [comment removed for export] *).
Proof.
  intros segs L mq m2 LBq LB2 LBp SP C r dE' RAT OE ME2 OUT PX MI MI2 CINp NINp NAP PEC PNE2.
  flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
  pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
  assert (BLKE : mpd_blk (r_E r) = []) by (unfold mpd_blk; rewrite OE; reflexivity).
  flat constr:(OUT) 5%nat. flclear OUT. intros AE2 NST2 O1 O2 O3. rewrite BLKE in O2. rewrite AE in AE2.
  assert (SUB : forall b, In b LBq -> In b LB2) by (intros b Hb; apply O2; [exact Hb| intros []]).
  assert (CR : forall a n, C <= a -> a + n <= C + 232 -> client_range L LBp SP a n)
    by (intros a n H1 H2; eapply client_range_blk; [exact CINp| exact H1| exact H2]).
  split. { eapply heap_presx_rw_cells; [exact PX| exact HD| apply CR; cbn; lia| cbn; lia]. }
  split. { eapply heap_presx_rw_cells; [exact PX| exact HT| apply CR; cbn; lia| cbn; lia]. }
  cbn [r_N r_E r_len].
  split; [exact AN|]. split; [exact AE2|]. split; [exact OKN|].
  split. { split; [exact NST2|]. right. exact (proj2 ME2). }
  split; [exact LEN|].
  split.
  { unfold rsa_mpds. cbn [r_N r_E]. constructor; [| constructor; [exact (proj1 ME2)|]].
    - eapply (relb segs m2 LBp LB2).
      + eapply mpdr_at_presx; [exact MN| exact PX| exact MI| exact MI2| rewrite AN; apply CR; lia| rewrite AN; cbn; lia|].
        intros HO. split; [exact (NINp HO)|]. cbn [disjoint_from]. split; [| exact I]. destruct (NAP HO) as [K|K]; lia.
      + intros HO. flat constr:(MN) 6%nat. intros _ _ _ _ _ OW. rewrite HO in OW. flat constr:(OW) 3%nat. flclear OW. intros _ NIN _. apply SUB. exact NIN.
    - eapply (zeros_relb segs C m2 LBp LB2). eapply (zeros_presx segs L); [exact ZS| exact PX| exact MI| exact MI2| exact CINp| cbn; lia]. }
  split; [exact CAL'|]. split; [exact C0'|]. split; [exact CB|]. split; [apply SUB; exact CINq|].
  split; [exact PN|]. split; [exact PEC| exact PNE2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59314923118.900000:S1N1k2Hk1K". (* [comment removed for export] *)
Lemma fresh_apart_notin : forall R LB LF N k, fresh_apart R LB LF N k -> 0 < k -> ~ In (N, k) LB.
Proof.
  intros R LB LF N k (_ & _ & _ & F3) Hk HIn. destruct (F3 N k ltac:(apply in_app_iff; left; exact HIn)) as [K|K]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59314923118.1100000?S1N1k2Hk1K1j2Hj". (* [comment removed for export] *)
Lemma fresh_apart_ne : forall R LB LF N k B j, fresh_apart R LB LF N k -> In (B, j) LB -> 0 < k -> 0 < j -> N <> B.
Proof.
  intros R LB LF N k B j (_ & _ & _ & F3) HIn Hk Hj E. subst B. destruct (F3 N j ltac:(apply in_app_iff; left; exact HIn)) as [K|K]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma fresh_apart_frames_mono : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "PR,$64.PLB,(6.$7.)PLF,(6.$7.)PLF',(6.$7.)PN,$1:.Pk,$1:.P,(2>.R6.R5.R3.R2.R1.)P,Pb,$7.P,(2:.$7.R1.(3<.R6.))(2:.$7.R2.(3<.R6.))(2>.R8.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R LB LF LF' N k (F0 & F1 & F2 & F3) HI. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros B j Hb. apply F3. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply HI, Hb].
Qed.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56669685265.1900000<S2FB1n1B1j1X". (* [comment removed for export] *)
Lemma fresh_apart_relist_rp : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "PR,$64.PHIA,(65.$66.R1.)Ph3,(5.$66.R2.R1.)PLB,(6.$7.)PLB',(6.$7.)PLF,(6.$7.)Pm3,P,(2.&40.)(3.(2.&8.))PFB,$1:.Pn,$1:.P,(2>.R9.R6.R4.R2.R1.)P,(28.$66.R:.R9.R8.R6.(18.(19.$1:.$1:.)(1;.$1:.$1:.R3.R2.)R5.)R4.)(2>.R;.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros R HIA h3 LB LB' LF m3 FB n (F0 & F1 & F2 & F3) HH. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
  flat constr:((hm_apart asegs R HIA h3 _ _ _ HH)) 2%nat. intros _ BA.
  pose proof (blocks_apart_app2 LB' ((FB, n) :: LF) (B, j) (FB, n) BA Hb ltac:(left; reflexivity)) as X. cbn [fst snd] in X. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
Local Ltac zchk_fails ::= constr:([0x0b2ca4]).
Local Ltac zchk_new ::= constr:([0x0b29f0; 0x0b2a04; 0x0b2a08; 0x0b2a0c; 0x0b2a10; 0x0b2a14; 0x0b2a18; 0x0b2a1c; 0x0b2a4c; 0x0b2a50; 0x0b2a54; 0x0b2a58; 0x0b2a60; 0x0b2a90; 0x0b2a94; 0x0b2a98; 0x0b2aac; 0x0b2ab0; 0x0b2abc; 0x0b2ac0; 0x0b2ac8; 0x0b2af8; 0x0b2afc; 0x0b2b00; 0x0b2b04; 0x0b2b08; 0x0b2b30; 0x0b2b34; 0x0b2b38; 0x0b2b48; 0x0b2b4c; 0x0b2b58; 0x0b2b5c; 0x0b2b70; 0x0b2b74; 0x0b2b78; 0x0b2b7c; 0x0b2b80]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.
Section WalkRP.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_RP.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_RP.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (C KEY : Z) (kbs : list byte) (lo : Z).
  Local Notation LEN := (Z.of_nat (length kbs)).
  Local Notation END := (KEY + Z.of_nat (length kbs)).
  Hypothesis K0 : 0 < KEY.
  Hypothesis KB : KEY + Z.of_nat (length kbs) + 8 <= 2^47.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 528 - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 448 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 511)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_RP in UARG; unfold A_SMALLOC_1_RP in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Lms,$67.(1.$1:.LFB,$1:.(1.$1:.Lsp1,$1:.(1.(5.$66.VR,VHIA,)Lh1,(5.$66.VR,VHIA,)(1.P,(2.&40.)(3.(2.&8.))Lm1,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)Lw0,(2.&40.)(1.(2.&40.)Lw1,(2.&40.)(1.(2.&40.)Lw2,(2.&40.)(1.(2.&40.)Llenj,(2.&40.)(9.(:.$67.R18.(<.(=.(41.&40.+;2958.)(41.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(41.&40.R16.)R10.R?.R>.R=.R<.R;.R:.R9.(41.&40.R17.)(41.&40.VC,)(41.&40.(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))(41.&40.(1<.R17.+20.))(41.&40.(1<.R17.+40.))Vs7,(41.&40.(1<.(68.R17.+3.)(69.(44.VR,))))(41.&40.R17.)(41.&40.(69.(44.VR,)))Vs11,R8.R7.R6.R5.)VF,(41.&40.+;2:28.)Vfc,(?.(2.&40.))R14.(10.$66.)))(9.(9.(23.(3=.(13.&40.Vsp,)+90.)R16.)(23.R16.(3=.(13.&40.Vsp,)+80.)))(9.(:.$1:.(40.R16.+20.)=)(9.(28.$66.VR,VHIA,R15.VLB,(18.(19.$1:.$1:.)(1;.$1:.$1:.R17.+80.)VLF,)R14.)(9.(:.P,$1:.Sp(22.$66.VR,VHIA,R15.)(22.$66.VR,VHIA,Vh,))(9.(:.$1:.(1?.$66.VR,VHIA,R15.)(1?.$66.VR,VHIA,Vh,))(9.(:.$1:.(17.$66.VR,VHIA,R15.)(17.$66.VR,VHIA,Vh,))(9.(:.$1:.(20.$66.VR,VHIA,R15.)(20.$66.VR,VHIA,Vh,))(9.(:.$1:.(24.$66.VR,VHIA,R15.)(24.$66.VR,VHIA,Vh,))(9.(:.$1:.(26.$66.VR,VHIA,R15.)(26.$66.VR,VHIA,Vh,))(9.Pmo,$4.(6:.(21.$66.VR,VHIA,R16.R1.)(21.$66.VR,VHIA,Vh,R1.))(9.(:.$1:.(40.R17.+40.)=)(9.(2>.VR,VLB,VLF,R17.+80.)(9.(50.$66.R14.R17.(18.$51.(53.R4.)(18.$51.(53.R3.)(18.$51.(53.R2.)(1>.$51.)))))(9.(50.$66.R14.(1<.R17.+20.)(18.$51.(53.(41.&40.VKEY,))(1>.$51.)))(9.(50.$66.R14.(1<.R17.+40.)(18.$51.(53.R1.)(1>.$51.)))(9.(50.$66.R14.(1<.(68.R17.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))(9.(50.$66.R14.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))(9.(50.$66.R14.(1<.R16.+18.)(18.$51.(53.(41.&40.R17.))(1>.$51.)))(9.(12.$66.R14.R16.(1<.R16.+18.))(9.(12.$66.R14.(1<.R16.+20.)(1<.(13.&40.Vsp,)-60.))(9.(12.$66.R14.Vlo,R16.)(9.(11.$66.R14.)(6<.$66.VR,VHIA,Vh,VLB,VLF,(13.&40.Vsp,)(16.VR,)(1>.$4>.)Vm,R14.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 kbs; try lx_pin1 mo0.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@D18607476203.109D2457697676.139 D29569067328.139D32458983511.139D32604263317.140D3375410824.138 D45716866873.138D50254960491.110D558665111.79   D62009822325.79 D62011770190.140D6395731754.110 D68407129291.138D6911780558.138 L10330779775.1  L10646859417.10 L10989370580.7  L12595714138.78 L13424450160.124L15629616632.10 L19546883925.124L19980016842.10 L2275137097.0   L24131365019.119L25233394630.3  L27188209011.143L29738741675.1  L32463525127.1  L33473079733.79 L33483560980.11 L33485826452.1  L38996969702.76 L3983061409.0   L40278113038.147L43061657906.74 L47230721790.119L48117620902.120L48117620911.69 L55351494680.11 L57355539152.120L58790154276.10 L59308677456.12 L59922446343.1  L60534120280.1  L62018535662.1  L6395777846.134 L6912107244.119 L7040749983.79  L7422344154.133 L9356559645.11  Q10533598597.81 Q10592386206.144Q1530342990.110 Q23937998252.81 Q24131365019.145Q24137657765.143Q30223088059.144Q32440833928.143Q35653441506.69 Q40271359350.110Q47241206720.81 Q48117620904.144Q48132302231.143Q56531220660.144Q59310664043.143Q59310664043.81 Q59321150548.144Q60109315147.69 Q6192914196.108 Q62012212072.110Q62022254708.81 Q6897428434.143 Q6912107244.145 Q9356560156.91  00000100200H00^01=01>01T01U01h02502M02d02e03;03@03A03[04B04b04c05C05[05\05g06306N06R06V06W06X06Y06h06i07G07i08708Y09;09K09L09b09l0:00:50:80:R0:]0;80;N0<90<F0<Q0<d0=@0=K0=V0=a0=b0>E0>U0>c0?E0?g0?h0?i0?j0?k0@@0@L0@V0@`0@k0A60AJFFS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBS1R3HIA2LF2sp3LFB3sp13H152h12FBFS2LF2sp3LFB3sp13H152FBFS1R3HIA1h2LF2sp3LFBS1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H133H15FS2LF2sp3LFB3sp13H152FBS3sp1SS1R3NS12sp2lo4SLOS3sp13SP1S2LF2sp3SPA3LFB3SPR3sp13H113H123H133H15S2LF2sp3LFB3SPR3sp13H152FB2F02F8SS2LF2sp3LFB3SPR3sp13H152FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1SS2LF3LFB2FBS2sp3sp13SP1S2LF2sp3LFB3sp13H152FB1c2HcS2FBS2FBFFFS2LF2sp3kbs3LFBSS2LF2sp3KEY3kbs3LFB3sp13H152FBS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3SPRS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R3ACV2FB2F02F1FS1R2sp2lo4SLOS3sp13SP1S2FB2Kb2F0S2spS3sp1S1RS2LF2sp3LFB3sp13H133H152FBS2LF3LFB2FBS2LF2sp3LFB3SPR3sp13H113H15S2LF2sp3LFB3sp13H152FBS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp13H13S1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS1R3HIA1h2LF2sp3kbs2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS1R2LF3kbs2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp13H143H15". (* [comment removed for export] *)
  #[using="LFB TPV SPA TOP SLOS SLO LOS NEEDR NS1 SM1 UARG IMG K0 KB"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(28.$66.VR,VHIA,Vh,VLB,VLF,Vm,)P,(12.$66.Vm,Vlo,(13.&40.Vsp,))P,(11.$66.Vm,)(6=.$66.(44.VR,)(22.$66.VR,VHIA,Vh,)$6>.(<.(=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(41.&40.VC,)(41.&40.VKEY,)(41.&40.(37.(33.(2.&8.)Vkbs,)))R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(41.&40.$6?.)Vfc,(?.(2.&40.))Vm,(10.$66.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST MI.
  unfold A_RSA_PARSE_PUBKEY.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
  flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
  carve_frame 128%nat ST.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 230%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -128) ST ltac:(first [ clear - SP1 SLOS NS1; lia | lx_side_lia ])) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340076) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | (clear - LFB; lia) | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLOS SP1 TOP NS1; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. flat constr:(FRSH) 3%nat. flclear FRSH. intros F0 F1 _.
          try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
      pose proof (art_stk_high asegs R HIA) as STKH.
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -128 + 32) with (bv_unsigned sp + -96) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -128) |- _ => release_frame FRa STx (bv_unsigned sp + -96); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 32) (bv_unsigned sp + -96) STJ ltac:(first [ clear - SP1; lia | lx_side_lia ])) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 32) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
      replace (sp1 + 32 - Z.of_nat 8) with (sp1 + 24) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
      cb8_to_c8 SLOT (@nil cell).
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 24; 8; 56]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat PSL FRM3. chunk_split FRM3 1%nat RZC FRM4. chunk_split FRM4 1%nat LSL FREST.
      lazymatch type of PSL with rw_cells _ _ ?a _ => replace a with (FB + 32) in PSL by (clear; lia) end.
      lazymatch type of LSL with rw_cells _ _ ?a _ => replace a with (FB + 64) in LSL by (clear; lia) end.
      clear FLNK FREST RZC.
      cb8_to_c8 FHD (@nil cell). cb8_to_c8 LSL (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xb2a28; 0xb2ca4] [(0xb2a0c, DSplit); (0xb2a10, DSplit)] 230%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  all: lxu_chk_leaves 0xb2ca4.
  all: try (exfalso; lxu_contra).
  lxr_leaf. lx_carry.
  try (match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end).
  try (match goal with H : rw_cells _ _ (Z.shiftr _ 3 + al_sb _) _ |- _ => rename H into FSHX end).
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      do 15 eexists. exists (Z_to_bv 64 1102416563), (Z_to_bv 64 128969), (Z_to_bv 64 731364). eexists.
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact PSL|]. split; [exact LSL|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|].
      exact PRES.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Lms,$67.(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(5.$66.VR,VHIA,)Lh4,(5.$66.VR,VHIA,)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(9.(:.$67.R12.(<.(=.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,R<.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(>.Vra,)Vfc,(?.(2.&40.))R11.(10.$66.)))(9.(11.$66.R11.)(9.(12.$66.R11.Vlo,(13.&40.Vsp,))(9.(6<.$66.VR,VHIA,O7.O6.VLF,(13.&40.Vsp,)(16.VR,)O2.O4.R11.)(9.(6<.$66.VR,VHIA,O7.O5.VLF,(13.&40.Vsp,)(16.VR,)O1.O3.R11.)(9.(:.P,$1:.Sp(22.$66.VR,VHIA,R10.)(22.$66.VR,VHIA,O7.))(9.(:.$1:.(1?.$66.VR,VHIA,R10.)(1?.$66.VR,VHIA,O7.))(9.(:.$1:.(17.$66.VR,VHIA,R10.)(17.$66.VR,VHIA,O7.))(9.(:.$1:.(20.$66.VR,VHIA,R10.)(20.$66.VR,VHIA,O7.))(9.(:.$1:.(24.$66.VR,VHIA,R10.)(24.$66.VR,VHIA,O7.))(9.(:.$1:.(26.$66.VR,VHIA,R10.)(26.$66.VR,VHIA,O7.))(9.Pmo,$4.(6:.(21.$66.VR,VHIA,R11.R1.)(21.$66.VR,VHIA,O7.R1.))(28.$66.VR,VHIA,R10.O5.VLF,R11.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 KB; try lx_pin1 K0; try lx_pin1 KEY; try lx_pin1 C; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 LB; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@D10777814275.118D2459793318.118 D32452690557.118D3385958441.117 D43016287773.119D45702252952.117D62011770188.119D68409162346.117D6897035375.117 L13312155929.147L13424450162.102L13424450175.106L16057223713.8  L19546883927.102L19546883930.106L2275137097.0   L24131365012.103L24131365017.99 L27188209011.122L30443457480.6  L35655538631.9  L38077847203.1  L39332637397.0  L39540652971.1  L39844638933.0  L42411609006.0  L47230721777.103L47230721788.99 L48117620903.104L48117620904.100L50790580594.6  L5162232212.2   L52237888267.158L54922193708.156L60098763854.3  L61387209310.157L61956910058.155L62018535662.1  L6912107235.103 L6912107246.99  L8247844460.152 L9356559676.11  P5152549648.152 Q10592386204.123Q10592386207.127Q21721340005.124Q21721340008.128Q22358563588.126Q24131365012.128Q24131365017.124Q24137657765.122Q24137657789.126Q30147450662.124Q30223088057.123Q30223088058.127Q30871588746.150Q31314676345.122Q34796740410.127Q4125667684.149 Q4279611329.151 Q48117620905.127Q48117620906.123Q48132302223.126Q48132302231.122Q52741535643.150Q5935758158.151 Q59668625896.128Q60382659730.128Q60382659743.124Q64133651577.150Q67397950268.123Q6897428426.126 Q6897428434.122 Q6912107235.128 Q6912107246.124 Q7917062807.128 Q7917062810.124 00000?00@00O00P00h01701H01I01X01l02F02`03?03T03i03j04504@04T04k05D05H05I05M05N05O05]05k06M06o07F07G08208_08i09V0:?0:B0:M0:X0:g0;R0;S0;^0;i0;j0;k0;l0<70<B0<M0<X0<Y0<d0<o0=?0=@0=A0=N0=[0>=0>_0?A0?c0@30@@0@A0@B0@C0@P0@Q0@\0@g0A20A=0AQ0AeS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1FS1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S2LF3LFB2FB3sp11p2PBS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0SS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB3sp11c2HcS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1h2sp2lo3TOP5HTOP3S2spSS2FBSSS1R2LF3LFB3ALOS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2sp2lo3LOS3SLOFS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP12F02H7S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S1R2lo3LOSS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14SP1R2F0S1RS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS2LF3LFB2FBS2LF3LFB2FBFFFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB1p2PBFFS2LF3LFB1p2PBS2LF3LFB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2LF3LFB2FB1p2PBS2LF3LFB1p2PBFFFS2LF3LFB1p2PBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LFB TOP SLO LOS kbs NEEDR IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Ph3,(5.$66.VR,VHIA,)PLBa,(6.$7.)PLBb,(6.$7.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(6.$4>.)PWB,(6.$4>.)PFB,$1:.Psp1,$1:.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Ps11v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)P,(28.$66.VR,VHIA,R23.R21.(18.(19.$1:.$1:.)(1;.$1:.$1:.R1;.+80.)VLF,)R1>.)P,Px,$1:.P,(22.$66.VR,VHIA,Vh,R1.)(22.$66.VR,VHIA,R26.R2.)P,(:.$1:.(1?.$66.VR,VHIA,R25.)(1?.$66.VR,VHIA,Vh,))P,(:.$1:.(17.$66.VR,VHIA,R26.)(17.$66.VR,VHIA,Vh,))P,(9.(23.(3=.(13.&40.Vsp,)+90.)R1>.)(23.R1>.(3=.(13.&40.Vsp,)+80.)))P,(:.$1:.(40.R1?.+20.)=)P,(:.$1:.(40.R21.+40.)=)P,(2>.VR,R29.VLF,R22.+80.)P,(2>.VR,R29.VLF,R23.+80.)P,(70.(22.$66.VR,VHIA,Vh,)R24.+80.)P,PB,$1:.Pj,$1:.P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R2.R1.)VLF,)(2;.(23.(1<.R28.+80.)R3.)(23.(1<.R3.R2.)R28.))P,Pb',$7.P,(2:.$7.R1.R2>.)(2:.$7.R2.R2>.)P,(50.$66.R2:.R27.(18.$51.(53.R?.)(18.$51.(53.R>.)(18.$51.(53.R=.)(1>.$51.)))))P,(50.$66.R2;.(1<.(68.R28.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))P,(50.$66.R2<.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))P,(50.$66.R2=.(1<.R29.+18.)(18.$51.(53.(41.&40.R2:.))(1>.$51.)))P,(12.$66.R2>.R2:.(1<.R2:.+18.))P,(12.$66.R2?.(1<.R2;.+20.)(1<.(13.&40.Vsp,)-60.))P,(12.$66.R30.Vlo,R2<.)P,(11.$66.R31.)P,(6<.$66.VR,VHIA,R37.R36.VLF,(13.&40.Vsp,)(16.VR,)R31.R34.R32.)P,(6<.$66.VR,VHIA,R38.R36.VLF,(13.&40.Vsp,)(16.VR,)R31.R34.R33.)(6=.$66.(44.VR,)(22.$66.VR,VHIA,R39.)(71.R39.R38.R37.R36.R35.R33.R32.)(<.(=.R2?.(41.&40.R30.)Vgp,Vtp,R2>.R2=.R2<.Vsp,(41.&40.R30.)R2;.R2:.R29.R28.R27.R26.R25.R24.(41.&40.R31.)R1?.R1>.R1=.R1<.R1;.(41.&40.(1<.(68.R31.+3.)(69.(44.VR,))))(41.&40.R31.)R1:.Vs11,R23.R22.R21.R20.)VF,(41.&40.+;2;<<.)Vfc,(?.(2.&40.))R34.(10.$66.)))")
(* [comment removed for export] *).
  Proof.
  intros until w2.
  intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT ST16 SThi STlo MI PRES PRES2.
  rt_facts.
  pose proof (hcs_ok asegs R HIA h3) as CSOK3.
  pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3.
  rewrite ET3, ES3 in HTOP3.
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia | lx_side_lia ]).
  assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NEEDR TOP HTOP3; lia | lx_side_lia ]]).
  assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
  assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
  destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
  as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS).
  change (128 / 8) with 16 in SBND, APS.
  pose proof FRSH as FRSH'.
  unfold fresh_apart in FRSH'.
  flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
  pose proof (art_stk_high asegs R HIA) as STKH.
  pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
  (* [comment removed for export] *)
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xb2c2c] [] 230%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try (lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => try match goal with MUx : munch _ _ mx |- _ => clear MUx end; try match goal with WMx : wmono _ _ mx |- _ => clear WMx end end).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
  (* [comment removed for export] *)
  match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
  destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
  as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
  replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
  pose proof (rw_cells_bound _ _ _ _ Hold) as PB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
  pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp.
  clear Hold.
  assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
  { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right]. eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
  assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
  assert (NP5 : bv_unsigned sp + -96 + 96 <= p \/ p + 1 <= bv_unsigned sp + -96).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (NP6 : sp1 + 24 + 8 <= p \/ p + 1 <= sp1 + 24).
  { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; first [ clear - SLO LOS SP1 NEEDR; lia | lx_side_lia ]| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
  assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| first [ clear - LOS SLO NEEDR; lia | lx_side_lia ]]).
  clear HHe NCp NSp FHD.
  repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H| H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
  zstep.
  zstep.
  fake_free_done p HSp.
  (* [comment removed for export] *)
  lx_mkR. lx_pre. lx_run_tac (PLAN [] [] 40%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f). subst lxm.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
  cbn [lb_remove fst Z.eqb] in HM4.
  rewrite Z.eqb_refl in HM4.
  apply evtA_done.
  unfold EPOST.
  exists mf, h4.
  do 15 eexists.
  split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ].
  split; [assumption|].
  split.
  {
  first [ assumption | (
  chunk_to_stk SLOT;
  chunk_to_stk SAVE;
  lazymatch goal with ST0 : stk _ mf lo sp1, STA : stk _ mf sp1 (sp1 + 24), STB : stk _ mf (sp1 + 32) _ |- _ =>
          stk_merge_into ST0 STA; stk_merge_into ST0 SLOT; stk_merge_into ST0 STB; stk_merge_into ST0 SAVE;
          replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) in ST0 by (clear; lia); exact ST0 end) ].
  }
  split; [exact PRES|].
  split; [exact PRES2|].
  split; [rewrite E4cs; reflexivity|].
  split; [exact E4top|].
  split; [exact E4stk|].
  split; [exact E4flag|].
  split; [exact E4vol|].
  split; [exact E4fr|].
  split; [exact HKI4|].
  exact HM4.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_RP.

  Definition EPIQ (hq hp : HST asegs R HIA) (LBa LBq : list blk) (m0 : mem) (WA : list ivl) (FB sp1 : Z) (w0 w1 w2 : word)
      (XQ : mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Lms,$67.(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lxra,(2.&40.)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)Ls3v,(2.&40.)(1.(2.&40.)Ls4v,(2.&40.)(1.(2.&40.)Ls5v,(2.&40.)(1.(2.&40.)Ls6v,(2.&40.)(1.(2.&40.)Ls7v,(2.&40.)(1.(2.&40.)Ls11v,(2.&40.)(9.(:.$67.R18.(<.(=.R16.(41.&40.O5.)Vgp,Vtp,R15.R14.R13.Vsp,(41.&40.O5.)R12.R11.R10.R?.R>.R=.R<.R;.(41.&40.O6.)R6.R5.R4.R3.R2.(41.&40.(1<.(68.O6.+3.)(69.(44.VR,))))(41.&40.O6.)R1.Vs11,R:.R9.R8.R7.)VF,(41.&40.+;2;<<.)Vfc,(?.(2.&40.))R17.(10.$66.)))(9.(28.$66.VR,VHIA,O<.O9.(18.(19.$1:.$1:.)(1;.$1:.$1:.O6.+80.)VLF,)R17.)(9.(50.$66.R17.O6.(18.$51.(53.O4.)(18.$51.(53.O3.)(18.$51.(53.O2.)(1>.$51.)))))(9.(50.$66.R17.(1<.(68.O6.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))(9.(50.$66.R17.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))(9.(50.$66.R17.(1<.O5.+18.)(18.$51.(53.(41.&40.O6.))(1>.$51.)))(9.(12.$66.R17.O5.(1<.O5.+18.))(9.(12.$66.R17.(1<.O5.+20.)(1<.(13.&40.Vsp,)-60.))(9.(12.$66.R17.Vlo,O5.)(9.(11.$66.R17.)(9.(6<.$66.VR,VHIA,O;.O:.VLF,(13.&40.Vsp,)(16.VR,)O7.O8.R17.)A1.O1.R17.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition CALLQ (RA XA : Z) (hq hp : HST asegs R HIA) (LBa LBq : list blk) (m0 : mem) (WA : list ivl) (FB sp1 : Z) (w0 w1 w2 : word)
      (XQ : mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Lms,$67.(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.$1:.Lp2,$1:.(1.(2.&40.)Llenw,(2.&40.)(9.(:.$67.R10.(<.(=.(41.&40.O>.)(41.&40.O5.)Vgp,Vtp,R>.R=.R<.Vsp,(41.&40.O5.)(41.&40.O=.)(41.&40.R2.)R1.R;.R:.R9.R8.R7.(41.&40.O6.)(41.&40.VC,)(41.&40.(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))(41.&40.(1<.O6.+20.))(41.&40.(1<.O6.+40.))(41.&40.(1<.VC,+10.))(41.&40.(1<.(68.O6.+3.)(69.(44.VR,))))(41.&40.O6.)(41.&40.(69.(44.VR,)))Vs11,R6.R5.R4.R3.)VF,(41.&40.$72.)Vfc,(?.(2.&40.))R?.(10.$66.)))(9.(28.$66.VR,VHIA,O<.O9.(18.(19.$1:.$1:.)(1;.$1:.$1:.O6.+80.)VLF,)R?.)(9.(50.$66.R?.O6.(18.$51.(53.O4.)(18.$51.(53.O3.)(18.$51.(53.O2.)(1>.$51.)))))(9.(50.$66.R?.(1<.O6.+20.)(18.$51.(53.(41.&40.R2.))(1>.$51.)))(9.(50.$66.R?.(1<.O6.+40.)(18.$51.(53.R1.)(1>.$51.)))(9.(50.$66.R?.(1<.(68.O6.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))(9.(50.$66.R?.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))(9.(50.$66.R?.(1<.O5.+18.)(18.$51.(53.(41.&40.O6.))(1>.$51.)))(9.(12.$66.R?.O5.(1<.O5.+18.))(9.(12.$66.R?.(1<.O5.+20.)(1<.(13.&40.Vsp,)-60.))(9.(12.$66.R?.Vlo,O5.)(9.(11.$66.R?.)(9.(6<.$66.VR,VHIA,O;.O:.VLF,(13.&40.Vsp,)(16.VR,)O7.O8.R?.)(9.(35.$66.R?.VKEY,Vkbs,)(9.(43.$66.(44.VR,)(22.$66.VR,VHIA,O<.)R?.VKEY,(37.(33.(2.&8.)Vkbs,)))(9.(23.(1<.VKEY,+2.)R2.)(9.(23.(1<.R2.(13.&40.R1.))(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))A1.O1.R?.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac fin_epiq :=
    apply evtA_done; left; unfold EPIQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- HM _ _ _ _ _ _ _ => eassumption
    | |- _ => idtac
    end.
  Ltac fin_callq :=
    apply evtA_done; right; unfold CALLQ;
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end;
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|];
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- HM _ _ _ _ _ _ _ => eassumption
    | |- _ => idtac
    end.
  Ltac kz K := try (change 18446744073709551615 with (Z.ones 64) in K); rewrite ?Z.land_ones in K by (clear; lia); rewrite ?unsigned_lit in K by lia.

  (* [comment removed for export] *)
  Ltac xq_presx RAT0 MIB CINl :=
    lazymatch goal with
    | |- rsa_at _ ?mm ?LBx _ _ =>
      lazymatch goal with PB : presW _ _ _ _ LBx LF _ _ [] _ mm, MIx : mem_inv _ mm |- _ =>
        eapply (rsa_at_presx asegs L _ mm LBx (LBx ++ fdata LF) (bv_unsigned sp) []);
          [exact RAT0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ LF _ _ _ _ _ PB))| exact (proj1 MIB)| exact MIx
          | apply in_app_iff; left; exact CINl| intros b Hb; apply in_app_iff; left; exact (rsa_limb_blocks_in asegs _ _ _ _ b RAT0 Hb)| exact I| intros; exact I]
      end end.

  Lemma EPIQ_ex : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Phq,(5.$66.VR,VHIA,)Php,(5.$66.VR,VHIA,)PLBa,(6.$7.)PLBq,(6.$7.)Pm0,P,(2.&40.)(3.(2.&8.))PWA,(6.$4>.)PFB,$1:.Psp1,$1:.Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)PT,StPXQ,P,R1.P,P,(2.&40.)(3.(2.&8.))SpPms,$67.P,(73.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.Lmm,P,(2.&40.)(3.(2.&8.))(1.R4.Lt,R4.A2.R4.R1.R2.)R1.)(1.R4.Lt,R4.(73.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.A1.R4.R1.R3.))")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros (mm & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & s3v & s4v & s5v & s6v & s7v & s11v
                             & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & [t HX]).
    exists t. unfold EPIQ. exists mm, xra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, s3v, s4v, s5v, s6v, s7v, s11v.
    repeat (split; [assumption|]). exact HX.
  Qed.


  Local Ltac2 Set LiaOrc.tbl := fun () => "03Q0@C23920765559.172C23922862675.150C60407910007.171C60410007123.149D10780387598.150D10782484778.172D16069757090.172D16071854214.150D2455419791.172 D2457516971.150 D32456773204.172D32458870384.150D46113380110.150D46115477290.172D56536395888.150D56538493012.172D5982099855.172 D5984197035.150 D68221095944.150D68223193132.172K34017150414.172K34019247594.150K34019247594.152K65868372942.172K65870470122.152L10912730231.1  L1107921052.164 L13340048728.1  L13511390815.22 L13513313310.28 L1384220064.164 L13951498865.3  L16720171459.142L17609328382.22 L17611537599.28 L19698471166.22 L19700476607.28 L21644325741.3  L21654730866.2  L22070304172.28 L2275137097.0   L24206288344.2  L24817214193.2  L2621559066.1   L27832436138.124L27832436139.147L27938633021.22 L27940753276.28 L29731203473.22 L29733262288.28 L31473906376.3  L33312312071.22 L33314451782.28 L34014826108.3  L34521824657.28 L3482443989.28  L3484572308.22  L35653441506.9  L38235734261.1  L39650474714.3  L41251426164.1  L41663468825.142L41663468825.164L42488948659.2  L47870616696.2  L48067958343.28 L48069962758.22 L48455046775.1  L49233373885.2  L49354241059.142L49858401057.0  L5021251703.1   L53527181501.2  L5491309809.2   L55180610054.22 L55182815303.28 L57387012359.22 L57389345606.28 L576250137.142  L576250137.164  L58786296421.22 L59308586248.2  L59308632045.10 L59427880762.142L59726336417.0  L60098763854.3  L60448817524.1  L6058464020.22  L6060730709.28  L62275882349.3  L63344940145.3  L64526681523.2  L65882689660.3  L66298372189.2  L66572625893.3  L66584664650.28 L66586861579.22 L66925227178.125L66925227178.148L68526664119.7  L8163705040.8   L8163714305.5   L881835912.0    L9080220944.4   L9356559676.11  O14785264606.147O14787361786.169O19173376225.172O19175473349.152O21228041722.169O21230138846.147O30010457231.150O30012554411.170O3076189820.169 O3078286936.147 O33647379806.150O33649476986.170O40095405918.150O40097503098.170O424351700.148  O426448880.170  O44938202843.148O44940300031.170O49699726460.169O49701823576.147O55209884805.148O55211981985.170O55516142064.170O55518239188.148O63649880056.152O63651977180.172O64471909102.170O64474006218.150O67168963243.170O67171060367.150O7437325788.172 O7439422968.150 O7439422968.152 P13947775218.169P13949872342.147P21647862485.148P21649959665.170P21656429038.170P21658526154.148P24827162710.150P24829259890.170P34019247594.150P39654189145.172P39656286333.152P42484919333.150P42487016449.170P47874275067.170P47876372191.148P49228642366.169P49230739482.147P53529750042.147P53531847230.169P5494959730.170 P5497056854.150 P62260666314.148P62262763502.170P63339218646.147P63341315826.169P64538971685.150P64541068801.170P66292560634.150P66294657758.170Q10592398491.167Q10592533181.150Q10594630297.172Q10598576410.124Q10598576411.147Q10598692432.145Q11133374175.150Q11135471355.172Q19561565648.125Q19561565648.148Q19561597648.124Q19561597649.147Q21765573510.172Q21767670690.150Q27942454161.150Q27944551349.172Q2803826605.150 Q2805923721.172 Q29720193674.167Q29722292289.145Q29775981542.150Q29778078658.172Q30220517308.172Q30222614424.150Q32435106995.172Q32437204119.150Q33228598872.147Q33228598873.124Q34667424921.172Q34669132443.167Q34669522109.150Q34671222864.145Q34671239194.125Q34671239194.148Q3477426724.150 Q3479523840.172 Q35333702489.125Q35333702489.148Q41412201211.172Q41414298335.150Q48118064779.150Q48120161967.172Q51218566552.150Q51220663740.172Q55202266689.145Q55208551562.167Q56530976407.150Q56533073587.172Q59321559671.150Q59323656787.172Q9356756743.127 Q9356888860.149 Q9633850158.147 Q9633850159.124 Q9634014255.125 Q9634014255.148 Q9644583048.150 Q9646680236.172 00000400800<00@00V00l01e02^02_02`03603L03b04804N04d04e04f05a06\07e07f08]09f0:]0:^0;^0;c0<60<I0<J0<K0=I0>B0?;0@40@m0@n0@o0AF0AG0AO0AP0AU0Ak0BA0C20Cc0D70DK0DW0Df0E50E60EM0FC0G90GQ0GU0GV0GZ0H00HF0HG0HH0I<0J00J40J50Jm0Jn0Jo0K00K10Ke0LY0Lh0M70MM0Mc0N30N90NW0NX0NY0Nc0Ng0Oh0Q50Q60Q70Q80Q90Q:0QE0QQ0Q]0R30RI0Rb0Rc0S80S90SH0T30T40T50T60T70T80T90T:0T;0T<0T=0T>0T?0T@0TA0TB0TC0TD0TE0TF0TG0TH0TI0TJ0TK0TL0TM0TN0TO0TP0TQ0TR0TS0TT0UB0V00V10V20VM0Vh0WV0XD0XE0Yh0[A0[m0\Y0]G0^50^c0_Q0`?0`m0a[0bI0bd0c?0cm0d[0eG0f30fJ0fa0g00g?0gN0g]0gl0h;0hJ0hY0i90iY0j90jY0kG0l50l[0mA0mQ0ma0n00n?0nV0nm0o<0oK0oL0oM0o\0ok10:10I10X10g11611E11X11k12:12I12X12g13M14314B14Q14`14o15015115215315H15]15o16A16S16e17717IS2FBS2FBS2FBS2FBS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3sp13SP13SPR4SP1R2F0S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3sp13SP13SPR4SP1R2F0FFS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1FFS1R3HIA1h2LF2sp3kbs3TOP3LFB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S1R3HIA1h2LF2sp3kbs3TOP3LFB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S2LF3KEY3kbs2lo3LFB2FB3sp13x283APK2p12Lw2LR4Hp1a2KE3x163x293x303x315POST0FS2LF3KEY2lo1l2KB3LFB2FB3sp13x143APK2x23x153x163x174POSTS2LF3KEY3kbs2lo3LFB2FB3sp13x283APK2p12Lw2LR4Hp1a2KE3x163x293x303x315POST0S2LF3KEY2lo1l2KB3LFB2FB3sp13x143APK2x23x153x163x174POSTFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p14Hp1a2p23Hp24Hp2aS3sp1S3KEY3kbs2KB2FB3sp1S3KEY3kbs2KB2FB3sp1FFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p12Lw2LR4Hp1a3HLwS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FFS3KEY3kbs2FB3sp12p13Hp1SS2sp3sp1FS3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S3KEY3kbs2FB3sp13APKS3KEY3kbs2FB3sp13APKS2r23RR23KT2S3kbs2FB3sp12F0S3kbs2FB3sp12F0FS3KEY3kbs2FB3sp12p13Hp1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R3HIA1h2sp2lo3TOP4HTOPS2loFS2FBS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1FFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S2FBFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p13Hp14Hp1aSFFFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S3kbs2FB3sp12F0S3kbs2FB3sp12F0S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S3KEY3kbs2FB3sp1S1i2HiS3KEY3kbs2K02p13Hp12p24Hp2a2KNFSS1R2lo3LOSS2FBS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3DKS3ALO3ACP2F02F1S1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3DKS3ALO3ACP2F02F12p13Hp14Hp1aFFFFFS2r13RR12KTS3kbs2FB3sp1S3kbs2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S3KEY3kbs2p14Hp1a2p24Hp2aFS3KEY3kbs2p23Lw24HLw2SS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOFFS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOFS1R5NEEDR2LF2sp3KEY3kbs2lo3LOS3SLO3LFB2FB3sp13SP13x283DKS3ALO2F14FBLO2p14Hp1a3x163x293x303x315POST0S1R5NEEDR2LF2sp3KEY2lo1l2KB3LOS3SLO3LFB2FB3sp13SP13x143APK3DKS3ALO2F12x23x153x163x174POSTS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S2LF2sp3kbs3LFB3sp13SP1S2LF2sp3kbs3LFB3sp13SP1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP13ALOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP13ALOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1S1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1S2LF3kbs3LFB3sp1S2LF3kbs3LFB3sp1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF2sp3kbs3LFB3sp13SP1S2LF2sp3kbs3LFB3sp13SP1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBFFS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs2lo3LFB3sp1S2LF3kbs2lo3LFB3sp1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3ALOS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBFFFFS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0". (* [comment removed for export] *)
  Lemma seg_A : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "PFB,$1:.Psp1,$1:.Ph1,(5.$66.VR,VHIA,)Pm1,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Plenj,(2.&40.)P,(9.(23.(3=.(13.&40.Vsp,)+90.)R17.)(23.R17.(3=.(13.&40.Vsp,)+80.)))P,(:.$1:.(40.R18.+20.)=)P,(28.$66.VR,VHIA,R18.VLB,(18.(19.$1:.$1:.)(1;.$1:.$1:.R1:.+80.)VLF,)R17.)P,(:.P,$1:.Sp(22.$66.VR,VHIA,R19.)(22.$66.VR,VHIA,Vh,))P,(:.$1:.(1?.$66.VR,VHIA,R1:.)(1?.$66.VR,VHIA,Vh,))P,(:.$1:.(17.$66.VR,VHIA,R1;.)(17.$66.VR,VHIA,Vh,))P,(:.$1:.(40.R1>.+40.)=)P,(2>.VR,VLB,VLF,R1?.+80.)P,(50.$66.R1=.R20.(18.$51.(53.R<.)(18.$51.(53.R;.)(18.$51.(53.R:.)(1>.$51.)))))P,(50.$66.R1>.(1<.R21.+20.)(18.$51.(53.(41.&40.VKEY,))(1>.$51.)))P,(50.$66.R1?.(1<.R22.+40.)(18.$51.(53.R;.)(1>.$51.)))P,(50.$66.R20.(1<.(68.R23.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))P,(50.$66.R21.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))P,(50.$66.R22.(1<.R24.+18.)(18.$51.(53.(41.&40.R25.))(1>.$51.)))P,(12.$66.R23.R25.(1<.R25.+18.))P,(12.$66.R24.(1<.R26.+20.)(1<.(13.&40.Vsp,)-60.))P,(12.$66.R25.Vlo,R27.)P,(11.$66.R26.)P,(6<.$66.VR,VHIA,Vh,VLB,VLF,(13.&40.Vsp,)(16.VR,)(1>.$4>.)Vm,R27.)P,(35.$66.R28.VKEY,Vkbs,)P,(43.$66.(44.VR,)(22.$66.VR,VHIA,Vh,)R29.VKEY,(37.(33.(2.&8.)Vkbs,)))P,(2;.(:.$1:.(37.(33.(2.&8.)Vkbs,))=)(2;.(23.(1<.R2=.+80.)VKEY,)(23.(1<.VKEY,(37.(33.(2.&8.)Vkbs,)))R2=.)))P,(2;.(23.(1<.VKEY,(37.(33.(2.&8.)Vkbs,)))Vlo,)(23.(13.&40.Vsp,)VKEY,))P,(11.$66.Vm,)P,(29.$66.Vm,VLB,VC,(34.VC,))(6=.$66.(44.VR,)(22.$66.VR,VHIA,Vh,)Lms,$67.(2;.(73.R30.Vh,VLB,VLB,Vm,(1>.$4>.)R32.R31.R1>.R1=.R1<.Lmm,P,(2.&40.)(3.(2.&8.))(29.$66.R1.VLB,VC,(34.VC,))R1.)(74.+;2::<.(1<.VC,+10.)R30.Vh,VLB,VLB,Vm,(1>.$4>.)R32.R31.R1>.R1=.R1<.Lmm,P,(2.&40.)(3.(2.&8.))(29.$66.R1.VLB,VC,(34.VC,))R1.))(<.(=.R2=.(41.&40.R30.)Vgp,Vtp,R2<.R2;.R2:.Vsp,(41.&40.R30.)R29.R28.R27.R26.R25.R24.R23.R22.(41.&40.R31.)(41.&40.VC,)(41.&40.(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))(41.&40.(1<.R31.+20.))(41.&40.(1<.R31.+40.))Vs7,(41.&40.(1<.(68.R31.+3.)(69.(44.VR,))))(41.&40.R31.)(41.&40.(69.(44.VR,)))Vs11,R21.R20.R1?.R1>.)VF,(41.&40.+;2:28.)Vfc,(?.(2.&40.))R2>.(10.$66.)))")
(* [comment removed for export] *).
  Proof.
    intros until lenj. intros SP1 SP1M HH1 Ehcs Ehtop Estk F64 FRSH FHD PSL LSL FSHX SAVE SLOT ST16 SThi STlo MI1 PRES HKY OKEY APK DKS MI0 RAT0.
    pose proof (conj MI0 I) as MI0box. flat constr:(RAT0) 13%nat. intros _ _ _ _ _ _ _ _ CAL0 CPOS0 CHI0 CIN0 _. unfold RSA_CTX_SIZE in CIN0, CHI0.
    rt_facts.
    pose proof (hm_top asegs R HIA h1 LB _ _ HH1) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP; lia]).
    assert (SCS1 : crange CS lo (sp1 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia]).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    assert (WL : wlow R LB LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    pose proof (hm_abase asegs R HIA h1 LB _ m1 HH1) as AB1.
    frame_aobj FSHX (FB + 32) 1%nat as OL1. frame_aobj FSHX (FB + 64) 1%nat as OL2.
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_RP in GT'.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    callxA_sp sp1 (eapply GT' with (CS := CS) (PP := FB + 32) (LENP := FB + 64) (P := KEY) (END := KEY + LEN) (BUF := KEY) (bs := kbs) (tag := 48) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NEEDR F0 F1 F8 F64 ALO LOS ACP K0 KB APK DKS; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "TAG1-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "TAG1-LEFT:" g end.
    clear OL1 OL2 AB1.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : rw_cells _ m2 (FB + 64) [C8 ?lw] |- _ => rename H into HL1; rename lw into Lw end.
    match goal with H : rw_cells _ m2 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP2; rename qq into p1 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into HOK1 end.
    match goal with H : _ < r1 <= 0 |- _ => rename H into RR1 end.
    match goal with H : KEY <= p1 <= _ |- _ => rename H into Hp1 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn [Z.pow Z.of_N Pos.pow] in LR.
    (* [comment removed for export] *)
    zstep. if_cases KT; zify_cond KT.
    { fin_epiq; first [ eassumption | xq_presx RAT0 MI0box CIN0 | match goal with |- ?g => idtac "EPIQ1-LEFT:" g end ]. }
    kz KT. assert (R10 : r1 = 0) by (clear - KT RR1; lia). subst r1. flat constr:((HOK1 eq_refl)) 2%nat. intros Hp1a HLw. clear HOK1. try clear KT.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep.
      fin_epiq; first [ eassumption | xq_presx RAT0 MI0box CIN0 | match goal with |- ?g => idtac "EPIQ2-LEFT:" g end ]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with HHc : HM _ _ _ h1 _ _ mx |- _ => pose proof (hm_abase asegs R HIA h1 LB _ mx HHc) as AB2 end end.
    match goal with H : rw_cells _ m2 (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH2 end.
    frame_aobj FSH2 (FB + 32) 1%nat as OL1. frame_aobj FSH2 (FB + 64) 1%nat as OL2.
    callxA_sp sp1 (eapply GT' with (CS := CS) (PP := FB + 32) (LENP := FB + 64) (P := p1) (END := KEY + LEN) (BUF := KEY) (bs := kbs) (tag := 2) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NEEDR F0 F1 F8 F64 ALO LOS ACP K0 KB APK DKS Hp1 Hp1a HLw LR; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "TAG2-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "TAG2-LEFT:" g end.
    clear OL1 OL2 AB2.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : rw_cells _ m3 (FB + 64) [C8 ?lw] |- _ => rename H into HL2; rename lw into Lw2 end.
    match goal with H : rw_cells _ m3 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP3; rename qq into p2 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r2 end.
    match goal with H : r2 = 0 -> _ |- _ => rename H into HOK2 end.
    match goal with H : _ < r2 <= 0 |- _ => rename H into RR2 end.
    match goal with H : p1 <= p2 <= _ |- _ => rename H into Hp2 end.
    pose proof (bv_unsigned_in_range 64 Lw2) as LR2. unfold bv_modulus in LR2. cbn [Z.pow Z.of_N Pos.pow] in LR2.
    (* [comment removed for export] *)
    zstep. if_cases KT2; zify_cond KT2.
    { fin_epiq; first [ eassumption | xq_presx RAT0 MI0box CIN0 | match goal with |- ?g => idtac "EPIQ3-LEFT:" g end ]. }
    kz KT2. assert (R20 : r2 = 0) by (clear - KT2 RR2; lia). subst r2. flat constr:((HOK2 eq_refl)) 2%nat. intros Hp2a HLw2. clear HOK2. try clear KT2.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. kz KN. clear - KN Hp2a Hp1 K0 KB Hp2. lia. }
    clear KN.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    fin_callq; first [ eassumption | xq_presx RAT0 MI0box CIN0 | (rewrite Ehcs; eassumption) | clear - Hp2a Hp1 Hp1a; lia | clear - HLw2; lia | match goal with |- ?g => idtac "CALLQ1-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis MPISIZE : mpi_size_stmtA asegs AL A_MPI_SIZE_RP.

  (* [comment removed for export] *)
  Ltac xq_presx_len RAT0 MIB CINl LENB BAx :=
    lazymatch goal with
    | |- rsa_at _ ?mm ?LBx _ _ =>
      lazymatch goal with PB : presW _ _ _ _ LBx LF _ _ [(C + 8, C + 16)] _ mm, MIx : mem_inv _ mm, HDx : rw_cells _ mm C _ |- _ =>
        eapply (rsa_at_presx_len asegs L _ mm LBx (LBx ++ fdata LF) (bv_unsigned sp) [(C + 8, C + 16)]);
          [exact RAT0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ LF _ _ _ _ _ PB))| exact (proj1 MIB)| exact MIx
          | exact HDx| exact LENB
          | apply in_app_iff; left; exact CINl| intros b Hb; apply in_app_iff; left; exact (rsa_limb_blocks_in asegs _ _ _ _ b RAT0 Hb)
          | cbn [disjoint_from]; split; [clear; lia| exact I]
          | intros b Hb; cbn [disjoint_from]; split; [| exact I]; destruct (rsa_limb_apart asegs _ _ _ _ _ b RAT0 BAx Hb) as [K|K]; clear - K; lia ]
      end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "04I0@C17025492443.191C23922862675.214C60410007123.215D10780387598.215D1310172651.193 D16071854214.215D2302662246.191 D2457516971.215 D27413640265.193D32312377831.193D32458870384.215D37764614195.191D43080244883.191D46113380110.215D56536395888.215D59521016234.191D5984197035.215 D60109196847.193D60109446735.191D66149944741.193D67928118627.215D68669309656.193K19417199362.214K20197146615.193K21212095580.191K34019247594.215K37211889074.191K40320258448.193K41580779312.191K54254745587.191K54254745587.193K55088519473.191K56742996226.214K65614493584.193K65870470122.215L10278198556.27 L10470256643.203L10912730231.1  L11266288813.9  L11269007652.4  L11377594986.2  L13176305223.2  L13340048728.1  L13513376638.27 L13951498865.3  L14405467828.2  L15445091466.181L15822417165.1  L15904255106.18 L16215250139.3  L1685717371.0   L17611600863.27 L19421690004.2  L19700409823.27 L20184474625.2  L21218866939.2  L21644325741.3  L21654730866.2  L21866712442.1  L2275137097.0   L23137366490.1  L24206288344.2  L24817214193.2  L2545017055.180 L25784868313.1  L2621559066.1   L27758563447.2  L27800688430.1  L27832436140.189L27940814876.27 L28604189903.3  L29311557968.152L29311558097.152L29428292188.18 L29733199024.27 L32027975233.0  L32675610705.18 L33314520614.27 L34014826108.3  L3482382261.27  L3482526763.18  L35653441506.9  L37224515140.2  L38146119331.3  L38235734261.1  L38350716672.3  L39650474714.3  L40324500070.2  L41251426164.1  L41409160545.3  L41582364055.4  L41663468825.180L41663468825.203L42488948659.2  L43445289383.1  L44163628344.203L44182274304.3  L46533908870.3  L47870616696.2  L48068024615.27 L48455046775.1  L49233373885.2  L5021251703.1   L52941874306.3  L53527181501.2  L54232767084.7  L54242110469.3  L54244916338.3  L54716365463.3  L5491309809.2   L55085943702.3  L55182884647.27 L56755282580.2  L56775193499.11 L57389278246.27 L576250137.180  L576250137.203  L58451400700.3  L59308586248.2  L59308628304.1  L59308632045.12 L59308873939.4  L60056205954.3  L60098763854.3  L60448817524.1  L6060664373.27  L61603606271.2  L62275882349.3  L62584254982.3  L63344940145.3  L63505931041.0  L64526681523.2  L64903376861.3  L65258828961.0  L65601858662.2  L65698399962.1  L65882689660.3  L66298372189.2  L66584597802.27 L66925227178.190L7049614941.2   L7738195705.2   L8122120014.3   L881835912.0    L9080220944.4   L9356559676.11  L9365803230.9   L9365812872.5   L9744944814.1   O14785264606.212O1478916974.191 O15410436215.191O15806046987.214O17025492443.191O19175473349.215O21230138846.212O29029543562.214O30010457231.214O3078286936.212 O33647379806.214O33934863603.191O35530008476.214O38903829125.214O40095405918.214O424351700.213  O44938202843.213O49701823576.212O50702732434.191O54941931932.214O55209884805.213O55518239188.213O56414299794.191O59625529265.191O61363827850.214O63649880056.215O64474006218.214O67171060367.214O7439422968.215 O8932501257.191 P11263960254.191P11387568333.214P13949872342.212P14399962227.193P16213722748.191P21212095580.191P21647862485.213P21658526154.213P24827162710.214P27752269830.193P38141074233.214P38338851482.214P39656286333.215P41419110342.191P42484919333.214P44186274970.214P47876372191.213P49230739482.212P52940256805.191P53529750042.212P54719981421.193P5497056854.214 P60050384933.191P61592333368.191P62260666314.213P63339218646.212P64538971685.214P66292560634.214P7750690063.191 P8134093492.191 Q10103930589.191Q10592398492.210Q10592533181.215Q10598576412.189Q10598691372.187Q10750552072.189Q11133374175.215Q11801279589.191Q11801586693.215Q13762724344.191Q14946898661.191Q15766564435.191Q15825002892.190Q16071854214.215Q17139219548.215Q19469071352.215Q19561565648.190Q19561597654.189Q19750898618.189Q21538057956.190Q21540267236.191Q21767670690.215Q23236331406.191Q24064611734.191Q25158727472.191Q25160678704.190Q27880293120.192Q2803826605.215 Q29720193677.210Q29722293309.187Q29775981542.215Q30222614424.215Q30802955094.188Q32312377831.193Q32437204119.215Q33228598879.189Q34669132444.210Q34669522109.215Q34671223852.187Q34671239194.190Q34964382778.191Q35333702489.190Q37527221250.215Q41414298335.215Q41602360616.191Q45248764730.191Q45629188794.190Q48117823211.191Q48118064779.215Q48360113622.191Q49698585326.189Q51218566552.215Q52590069023.190Q53647085228.192Q55202265661.187Q55208551565.210Q56530976407.215Q57828105177.215Q61820201889.215Q64193412887.190Q64709088086.215Q65210003448.215Q65314376097.215Q66149944741.193Q67259744550.191Q9356756743.192 Q9356855175.171 Q9633850153.189 Q9634014255.190 Q9644583048.191 Q9644583048.215 Q9740947091.189 00000100500900T00U01Y02K02L02M03:03U04^05P05k06F06G06H07>07b08O09U09V0:Z0;D0;E0<S0=B0=l0>Q0?B0?m0@J0AN0B80CF0DK0DL0DM0Df0Dg0Dh0E00E50EH0EI0EJ0FA0FE0Fl0Fm0Fn0Gg0Gh0Ha0Hb0Hc0Hd0He0Hi0Hj0Hm0I50I60IQ0IT0IY0IZ0I]0J80Ji0K00K10K20KY0Km0Kn0L[0Lj0Lk0Ma0NM0Ne0Nf0Ng0Nk0Nl0Nm0Nn0O20O30O40OO0Oj0Ok0On0QA0QB0QJ0QK0R?0RC0RD0RE0RF0RG0Rd0Re0Rf0Rg0Rh0Ri0S]0S^0T30TB0T]0U80UB0UH0UL0V30V=0V>0VH0VL0Wa0Wb0Wc0Wo0X00X10X20X=0X>0X?0XB0XC0XD0XP0Xk0Y30Y40Y50Y60YE0Z00Z10ZF0ZI0ZJ0ZK0ZL0ZM0ZN0ZO0ZP0ZQ0ZR0ZS0ZT0ZU0ZV0ZW0ZX0ZY0ZZ0Z[0Z\0Z]0Z^0Z_0Z`0Za0Zb0Zc0Zd0Ze0Zf0Zg0[P0\G0]80^A0^g0^h0^i0_G0`80a90b30c:0dh0eF0f50g<0gm0h^0i<0im0jS0kD0kb0lj0mH0n90nh0oB10H11:11\11n12@12R12d13513G13H13I13J13d14@14Q15>16516616^17F17W18@18i19Z19[19\1:E1:n1;Q1;d1<61<H1<b1=41=L1=o1>01>B1>T1>f1?81?J1@31@E1@F1@X1@Y1@Z1@k1An1BW1C41CO1Ca1DU1E81EJ1E\1E]1FH1FI1F`1Fa1Fb1Fc1GF1GG1G_1H71HL1Ha1I61IK1I\FS2FBS2FBS2LF2sp1C3kbs3LFB2FB3sp12dNFS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB2FB3sp13SP12dN3SPR4SP1R2F02C02N0S2LF2sp1C3kbs3LFB2FB3sp14lenw2p22dN2HB5Ha_st5Hl_stFFS2LF2sp1C3kbs3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS2LF2sp1C3kbs3LFB2FB3sp12dNS1R3HIA1h2LF2sp1C3kbs2lo3TOP3LFB2h22FB3sp13SP15Ehtop2dN3SPR4SP1R2F02C02N0S2LF2sp1C3kbs3LFB2FB3sp14lenw2p22dN2HB5Ha_st5Hl_stS2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNFFS1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1C3kbs3TOP3LFB2h22FB3sp13SP15Ehtop2dN3SPR4SP1R2F02C02N0FS2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN3APC3x163x293x303x314POSTS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stFS2LF3KEY3kbs2lo3LFB2FB3sp14lenw2p23x283KP23KL23APK2dN3LRW3x163x293x303x314POSTS2LF1C3kbs3LFB2FB4lenw2p22dN3APC2HB5Ha_st5Hl_stS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stS2LF2sp3KEY3kbs2lo3LFB3sp13SP13DKS2dNS2LF3KEY3kbs3LFB2FB4lenw2p23APK2dN2HB5Ha_st5Hl_stS2LF1C3KEY3kbs3LFB3DKC2dN2sz2HB5Ha_st5Hl_stS2LF2sp3kbs2lo3LFB3sp13SP12dNS2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN3APC3x163x293x303x314POSTS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stS2LF3KEY3kbs2lo3LFB2FB3sp14lenw2p23x283KP23KL23APK2dN3LRW3x163x293x303x314POSTS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp14lenw2p23SP13KP23ALO3ACP2F03LRWFFS1R2lo3LOS3sp12dN3ALO3NCEFFS2lo3sp1S3sp1S3KEY3kbs2KB2FB3sp1FFS1R2LF2sp1C3kbs3LFB2FB3sp12dN3ACV3SPR4SP1R2F02C03CCE2N0S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVFSS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FFFFS2FBSS1CS2sp3sp1FS2LF2sp1C3kbs3LFB2FB3sp12dNS1CS3sp1FS1CS2LF2sp1C3kbs3LFB2FB3sp12dNS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S1C1b1KFFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVS3KEY3kbs2FB3sp13APKSS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV3CCES3kbs2FB3sp12F0FS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACVS1R3HIA1h2sp2lo3TOP4HTOPFFS2loFFFS2FBFFS2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNFS1CS2LF2sp1C3KEY3kbs2K02KB3LFB2FB3sp14lenw2p23KP22dN3SPR4SP1R2F02C02N03LRW2p33Hp34Hp3aFS2dN3NRNFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S2FBFFFFS3KEY4lenw2p23KP23LRW2p34Hp3aFFFFFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1FS2dN3NRN3CBR1q1r1H2H0S3kbs2FB3sp12F0S2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNS2rv2RV2K2S1i2HiS2K1S3KEY3kbs2K04lenw2p23KP23LRW2p34Hp3a2KNS2dN2N12Z0FS1R2lo3LOSS2FBS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp14lenw2p23SP14SP1M3KP23KL23DKS3ALO3ACP2F02F13LRWFFS2r33RR33KT3FSFS2sp2lo3sp1SFS1CFFS3kbs2FB3sp1S2LF2sp1C3kbs3LFB2FB3sp12dNS2lo3sp1FFSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS3KEY3kbs2p33Lw34HLw3S1CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF1C3kbs2lo3LOS3LFB3sp12dN2AN3ALO3CCES1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALO3CCES1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12sz2dN3ALO3CCE2HB5Ha_st5Hl_stS1R2LF1C3kbs2lo3LOS3LFB3sp12dN3ALO3CCEFFS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB2sz2dN3ALO3CCE2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN2AN3ALO3CCES2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN2AN3APC3x163x293x303x314POSTS1R5NEEDR2LF2sp1C3KEY3kbs2lo3LOS3SLO3LFB2FB3sp14lenw2p23SP13x283KP23DKS2dN3ALO2F13CCE3LRW3x163x293x303x314POSTS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB2dN3ALO2F1S2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN2AN3APC3x163x293x303x314POSTS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF1C3kbs3LFB2sz2dN2AN2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp14lenw2p23SP12dN4FBLO2HB5Ha_st5Hl_stS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB2dN3ALO2F1S2LF2sp3kbs3LFB3sp13SP12dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p22dN3ALO2F12HB5Ha_st5Hl_stS2LF1C3kbs3LFB2FB4lenw2p22dN2AN3APC2HB5Ha_st5Hl_stS1R2LF1C3kbs2lo3LOS3LFB2dN3ALO3CCES2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF1C3kbs3LFB2dNS2LF3kbs3LFB2FB2dNFFFS2LF1C3kbs3LFB2dN2HB5Ha_stS1R2LF3kbs2lo3LOS3LFB2dN3ALOS2LF1C3kbs3LFB2dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP12dNS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALO3CCEFS2LF2sp1C3kbs3LFB2FB3sp12dN3SPR2F02F82C0S2LF2sp1C3kbs3LFB2FB3sp12dN3SPR2F02F82C0S2LF1C3kbs3LFB2dNS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALOFFS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF1C3kbs3LFB2dN2sz2HB5Ha_st5Hl_stS2LF3kbs3LFB3sp12dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF2sp3kbs3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dN2F02HBS2LF1C3kbs3LFB2sz2dN2HB5Ha_st5Hl_stFS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dNFS2LF3kbs3LFB2FB2dNFFS2LF1C3kbs3LFB2dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p22dN3ALO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2dN3ALOS2LF2sp3kbs2lo3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dN2HB5Ha_stS2LF3kbs3LFB2FB2dNS2LF2sp1C3kbs3LFB2FB3sp12dN2AN3SPR4SP1R2F02C03NAL2N0S2LF1C3kbs3LFB2dN2sz2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNFS1R3HIA1h2LF2sp3kbs3TOP3LFB3sp13SP12dN4HTOPFS2LF1C3kbs3LFB2dN2C02HBFFFS2LF1C3kbs3LFB2sz2dN2HB5Ha_st5Hl_stFS2LF3kbs3LFB3sp12dN4SP1RS2LF3kbs3LFB3sp12dN4SP1RS2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF1C3kbs3LFB2dN". (* [comment removed for export] *)
  Lemma seg_B : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Ph2,(5.$66.VR,VHIA,)PLBa,(6.$7.)PLB2,(6.$7.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2,P,(2.&40.)(3.(2.&8.))PWA,(6.$4>.)PFB,$1:.Psp1,$1:.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Plenw,(2.&40.)Pp2,$1:.Prv,$1:.Pr2,$8.P,(9.(23.(3=.(13.&40.Vsp,)+90.)R16.)(23.R16.(3=.(13.&40.Vsp,)+80.)))P,(:.$1:.(40.R17.+20.)=)P,(28.$66.VR,VHIA,R1?.R1=.(18.(19.$1:.$1:.)(1;.$1:.$1:.R19.+80.)VLF,)R1;.)P,Px,$1:.P,(22.$66.VR,VHIA,Vh,R1.)(22.$66.VR,VHIA,R22.R2.)P,(:.$1:.(1?.$66.VR,VHIA,R21.)(1?.$66.VR,VHIA,Vh,))P,(:.$1:.(17.$66.VR,VHIA,R22.)(17.$66.VR,VHIA,Vh,))P,(:.$1:.(40.R1=.+40.)=)P,(2>.VR,R22.VLF,R1>.+80.)P,(50.$66.R21.R1?.(18.$51.(53.R?.)(18.$51.(53.R>.)(18.$51.(53.R=.)(1>.$51.)))))P,(50.$66.R22.(1<.R20.+20.)(18.$51.(53.(41.&40.R<.))(1>.$51.)))P,(50.$66.R23.(1<.R21.+40.)(18.$51.(53.R>.)(1>.$51.)))P,(50.$66.R24.(1<.(68.R22.+3.)(69.(44.VR,)))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.+?1.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.+?2.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.+?3.))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(18.$51.(6;.(41.&8.=))(1>.$51.))))))))))))))))))P,(50.$66.R25.(1<.(13.&40.Vsp,)-60.)(18.$51.(53.Vs10,)(18.$51.(53.Vs9,)(18.$51.(53.Vs8,)(18.$51.(53.Vs7,)(18.$51.(53.Vs6,)(18.$51.(53.Vs5,)(18.$51.(53.Vs4,)(18.$51.(53.Vs3,)(18.$51.(53.Vs2,)(18.$51.(53.Vs1,)(18.$51.(53.Vs0,)(18.$51.(53.Vra,)(1>.$51.))))))))))))))P,(50.$66.R26.(1<.R23.+18.)(18.$51.(53.(41.&40.R24.))(1>.$51.)))P,(12.$66.R27.R24.(1<.R24.+18.))P,(12.$66.R28.(1<.R25.+20.)(1<.(13.&40.Vsp,)-60.))P,(12.$66.R29.Vlo,R26.)P,(11.$66.R2:.)P,(6<.$66.VR,VHIA,R2?.R2>.VLF,(13.&40.Vsp,)(16.VR,)R2:.R2<.R2;.)P,(6<.$66.VR,VHIA,R30.R2>.VLF,(13.&40.Vsp,)(16.VR,)(18.(19.$1:.$1:.)(1;.$1:.$1:.(1<.VC,+8.)(1<.VC,+10.))(1>.(19.$1:.$1:.)))R2<.R2<.)P,(75.VR,R30.VLF,(13.&40.Vsp,)R2<.(1<.VC,+8.)+8.)P,Pb,$7.P,(2:.$7.R1.R32.)(2:.$7.R2.R32.)P,(35.$66.R2?.VKEY,Vkbs,)P,(43.$66.(44.VR,)(22.$66.VR,VHIA,R34.)R30.VKEY,(37.(33.(2.&8.)Vkbs,)))P,(23.(1<.VKEY,+2.)R1;.)P,(23.(1<.R1<.(13.&40.R1=.))(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))P,(2;.(:.$1:.(37.(33.(2.&8.)Vkbs,))=)(2;.(23.(1<.R31.+80.)VKEY,)(23.(1<.VKEY,(37.(33.(2.&8.)Vkbs,)))R31.)))P,(2;.(23.(1<.VKEY,(37.(33.(2.&8.)Vkbs,)))Vlo,)(23.(13.&40.Vsp,)VKEY,))P,(2;.(23.(1<.VKEY,(37.(33.(2.&8.)Vkbs,)))VC,)(23.(1<.VC,+>8.)VKEY,))P,(29.$66.R36.R38.VC,R1>.)P,(:.$1:.(61.R1?.)=)P,P,(:.$1:.R21.=)(:.$1:.(76.(56.R21.))+1.)P,(2;.(:.$1:.R22.=)(:.$1:.R22.$77.))(6=.$66.(44.VR,)(22.$66.VR,VHIA,R3>.)Lms,$67.(2;.(73.R3?.R3?.R3>.R3=.R3<.R3:.R39.R38.R29.R28.R27.Lmm,P,(2.&40.)(3.(2.&8.))(1.$1:.Llenv,$1:.(29.$66.R2.R3?.VC,(55.R1.(56.R25.)(57.R25.))))R1.)(74.+;2;48.(1<.VC,+20.)R3?.R3?.R3>.R3=.R3<.R3:.R39.R38.R29.R28.R27.Lmm,P,(2.&40.)(3.(2.&8.))(1.$1:.Llenv,$1:.(9.(29.$66.R2.R3?.VC,(55.R1.(56.R25.)(57.R25.)))(:.$1:.(76.(56.R25.))+1.)))R1.))(<.(=.(41.&40.+;2::<.)(41.&40.R37.)Vgp,Vtp,R36.R35.R34.Vsp,(41.&40.R37.)(41.&40.R23.)R33.R32.R31.R30.R2?.R2>.R2=.(41.&40.R38.)(41.&40.VC,)(41.&40.(1<.VKEY,(37.(33.(2.&8.)Vkbs,))))(41.&40.(1<.R38.+20.))(41.&40.(1<.R38.+40.))(41.&40.(1<.VC,+10.))(41.&40.(1<.(68.R38.+3.)(69.(44.VR,))))(41.&40.R38.)(41.&40.(69.(44.VR,)))Vs11,R2<.R2;.R2:.R29.)VF,(41.&40.+;2::<.)Vfc,(?.(2.&40.))R3:.(10.$66.)))")
(* [comment removed for export] *).
  Proof.
    intros until r2. intros SP1 SP1M HH2 HCS2 Ehtop Estk F64 FRSH FHD PSL LSL FSHX SAVE SLOT ST16 SThi STlo MI2 PRESa PRESb WCa SUBa HKY OKEY KP2 KL2 APK DKS DKC RAT2 LEN0 SGN RV.
    pose proof (conj MI2 I) as MI2box.
    assert (Z0B : 0 <= 0 < 2^64) by (clear; lia).
    flat constr:(RAT2) 13%nat. intros HDC _ AN _ OKN _ _ ALL2 CAL _ _ CIN _. unfold RSA_CTX_SIZE in CIN.
    unfold rsa_head_cells in HDC. rewrite LEN0 in HDC. pose proof (proj1 OKN) as NST.
    pose proof (Forall_inv ALL2) as MNr. set (dN := r_N r2) in *.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h2) as CSOK2.
    pose proof (hm_top asegs R HIA h2 LB2 _ _ HH2) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP; lia]).
    assert (SCS2 : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS2| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA h2) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS2| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA h2) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS2| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 LB2 LF m2 FB 128 lo HH2 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof (fresh_apart_blocks_mono R LB2 LBa LF FB 128 FRSH SUBa) as FRSHa.
    assert (WLa : wlow R LBa LF) by (split; [exact (proj2 (proj2 (proj2 PRESa)))| apply (art_data_lo asegs R HIA)]).
    assert (WLb : wlow R LB2 LF) by (split; [exact (proj2 (proj2 (proj2 PRESb)))| apply (art_data_lo asegs R HIA)]).
    assert (WCb : wcover R LB2 LF (bv_unsigned sp) [(C + 8, C + 16)] (C + 8) 8) by (apply wcover_inside; cbn [inside]; left; clear; lia).
    (* [comment removed for export] *)
    flat constr:((hm_apart asegs R HIA h2 LB2 _ m2 HH2)) 2%nat. intros HBR BA2. rewrite Forall_forall in HBR.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact CIN)) as (C0 & _ & CCE & _). cbn [fst snd] in C0, CCE.
    assert (APC : FB + 128 <= C \/ C + 232 <= FB) by (apply F3; apply in_app_iff; left; exact CIN).
    assert (CWC : client_wrange L (LB2 ++ fdata ((FB, 128) :: LF)) lo (htop asegs R HIA h) (C + 8) 8).
    { eapply client_wrange_block; [apply in_app_iff; left; exact CIN| clear; lia| clear; lia]. }
    unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in RV.
    (* [comment removed for export] *)
    zpre. if_cases K2; zify_cond K2.
    2:{ kz K2. assert (RVF : rv = -16) by (clear - K2 RV; lia). subst rv.
      zstep. zstep. zstep. try (if_cases K3; zify_cond K3; [ | exfalso; clear - K3; first [ vm_compute in K3; discriminate | vm_compute in K3; lia | lia ] ]).
    (* [comment removed for export] *)
      fin_epiq; first [ eassumption | (exists 0; xq_presx_len RAT2 MI2box CIN Z0B BA2) | match goal with |- ?g => idtac "EPIQB1-LEFT:" g end ]. }
    kz K2. assert (RV0 : rv = 0) by (clear - K2 RV; lia). subst rv. pose proof (conj MNr (or_introl (SGN eq_refl)) : mpd_at asegs m2 LB2 dN) as MN. try clear K2.
    (* [comment removed for export] *)
    flat constr:(MN) 2%nat. intros FLt1 SGN1. flat constr:(FLt1) 6%nat. flclear FLt1. intros CN0 NAL N0 LENN NRN OWNN.
    assert (NPOS : md_own dN = LHeap -> 0 < md_p dN /\ md_p dN + 4 * md_n dN <= alloc_ceiling /\ In (md_p dN, 4 * md_n dN) LB2).
    { intros EO. rewrite EO in OWNN. flat constr:(OWNN) 3%nat. flclear OWNN. intros _ NIN _. destruct (HBR _ ltac:(apply in_app_iff; left; exact NIN)) as (P0 & _ & PCE & _). cbn [fst snd] in P0, PCE. split; [exact P0|]. split; [exact PCE| exact NIN]. }
    assert (NN1 : 1 <= md_n dN -> md_own dN = LHeap).
    { intros N1. destruct (md_own dN) eqn:EO; [exfalso; (flat constr:(OWNN) 2%nat; flclear OWNN; intros _ Z0); clear - Z0 N1; lia| reflexivity| exfalso; apply NST; reflexivity]. }
    pose proof (hm_aobj_block asegs R HIA h2 LB2 _ m2 C 232 HH2 CIN) as OC.
    pose proof (hm_abase asegs R HIA h2 LB2 _ m2 HH2) as AB1.
    assert (ONL : 1 <= md_n dN -> aobj asegs AL (hcs asegs R HIA h2) m2 (md_p dN) (4 * md_n dN)).
    { intros N1. flat constr:((NPOS (NN1 N1))) 3%nat. intros _ _ NIN. exact (hm_aobj_block asegs R HIA h2 LB2 _ m2 _ _ HH2 NIN). }
    pose proof MPISIZE as MS'. unfold mpi_size_stmtA, mpi_query_stmtA, A_MPI_SIZE_RP in MS'.
    zstep. zstep.
    callxA_sp sp1 (eapply MS' with (CS := hcs asegs R HIA h2) (LB := LB2) (dX := dN) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?AN; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | exact I
                         | (symmetry; apply definitions.Z_to_bv_bv_unsigned)
                         | (intros EO; exact (proj1 (NPOS EO)))
                         | (eapply aobj_sub; [exact OC| clear; lia| clear; lia])
                         | (intros N1; (flat constr:((NPOS (NN1 N1))) 3%nat; intros _ NCE _); clear - NCE ACV ALO LOS; lia)
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NEEDR F0 F1 ALO LOS ACP ACV C0 CCE; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "SIZE-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SIZE-LEFT:" g end.
    clear AB1.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : ?x = (core_bitlen _ _ + 7) / 8 |- _ => rename H into ESZ; rename x into sz end.
    assert (SZB : 0 <= sz < 2^64).
    { pose proof (core_bitlen_range (md_limbs dN) (md_n dN) ltac:(clear - NRN; lia)) as CBR. unfold MPI_MAX_LIMBS in NRN. clear - ESZ CBR NRN. subst sz. Z.div_mod_to_equations. lia. }
    clear ESZ.
    (* [comment removed for export] *)
    lazymatch goal with HHc : HM _ _ _ h2 _ _ m3 |- _ => pose proof (hm_abase asegs R HIA h2 LB2 _ m3 HHc) as AB2 end.
    lazymatch goal with OCc : aobj _ _ _ m3 C 232 |- _ => assert (OC8 : aobj asegs AL (hcs asegs R HIA h2) m3 (C + 8) 8) by (eapply aobj_sub; [exact OCc| clear; lia| clear; lia]) end.
    zstep. zstep. zstep. zstep. zstep.
    zstep.
    clear AB2 OC8.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 lenw) as LRW. unfold bv_modulus in LRW. cbn [Z.pow Z.of_N Pos.pow] in LRW.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with HHc : HM _ _ _ h2 _ _ m4 |- _ => pose proof (hm_abase asegs R HIA h2 LB2 _ m4 HHc) as AB3 end.
    match goal with H : rw_cells _ m4 (Z.shiftr FB 3 + al_sb AL) _ |- _ => rename H into FSH4 end.
    frame_aobj FSH4 (FB + 32) 1%nat as OL1. frame_aobj FSH4 (FB + 64) 1%nat as OL2.
    try (match goal with H : rw_cells _ m4 (FB + 32) [C8 (Z_to_bv 64 (bv_unsigned lenw + p2))] |- _ => rewrite (Z.add_comm (bv_unsigned lenw) p2) in H end).
    pose proof GETTAG as GT'. unfold asn1_get_tag_stmtA, A_ASN1_GET_TAG_RP in GT'.
    callxA_sp sp1 (eapply GT' with (CS := hcs asegs R HIA h2) (PP := FB + 32) (LENP := FB + 64) (P := p2 + bv_unsigned lenw) (END := KEY + LEN) (BUF := KEY) (bs := kbs) (tag := 2) (lo := lo);
                   rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
                   try (exact (art_alwf asegs R HIA));
                   first [ solve_crange
                         | lazymatch goal with
                           | |- _ => clear - SP1 SP1M SLO NEEDR F0 F1 F8 F64 ALO LOS ACP K0 KB APK DKS KP2 KL2 LRW; first [lia | Z.div_mod_to_equations; lia]
                           end
                         | match goal with |- ?g => idtac "TAG3-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "TAG3-LEFT:" g end.
    clear OL1 OL2 AB3.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : rw_cells _ m5 (FB + 64) [C8 ?lw] |- _ => rename H into HL3; rename lw into Lw3 end.
    match goal with H : rw_cells _ m5 (FB + 32) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into HPP3; rename qq into p3 end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r3 end.
    match goal with H : r3 = 0 -> _ |- _ => rename H into HOK3 end.
    match goal with H : _ < r3 <= 0 |- _ => rename H into RR3 end.
    match goal with H : _ <= p3 <= _ |- _ => rename H into Hp3 end.
    pose proof (bv_unsigned_in_range 64 Lw3) as LR3. unfold bv_modulus in LR3. cbn [Z.pow Z.of_N Pos.pow] in LR3.
    (* [comment removed for export] *)
    zstep. if_cases KT3; zify_cond KT3.
    { fin_epiq; first [ eassumption | (exists sz; xq_presx_len RAT2 MI2box CIN SZB BA2) | match goal with |- ?g => idtac "EPIQB2-LEFT:" g end ]. }
    kz KT3. assert (R30 : r3 = 0) by (clear - KT3 RR3; lia). subst r3. flat constr:((HOK3 eq_refl)) 2%nat. intros Hp3a HLw3. clear HOK3. try clear KT3.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KN; zify_cond KN.
    { exfalso. kz KN. clear - KN Hp3a Hp3 K0 KB KP2 LRW. lia. }
    clear KN.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    fin_callq; first [ eassumption | (exists sz; split; [xq_presx_len RAT2 MI2box CIN SZB BA2| exact (SGN eq_refl)]) | clear - Hp3a KP2 LRW; lia | clear - HLw3; lia | match goal with |- ?g => idtac "CALLQ2-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis RSACOMPLETE : rsa_complete_stmtA asegs R HIA A_RSA_COMPLETE_RP.
  Hypothesis RSACKPUB : rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY_RP.

  Definition EPIQH (h3 : HST asegs R HIA) (LBa LBq : list blk) (m0 : mem) (WA : list ivl) (FB sp1 : Z) (w0 w1 w2 : word)
      (XQ : mem -> Prop) : machine_state -> Prop := fun ms =>
    exists hq : HST asegs R HIA,
      hcs asegs R HIA hq = hcs asegs R HIA h3 /\ htop asegs R HIA hq = htop asegs R HIA h3
      /\ hstkhi asegs R HIA hq = hstkhi asegs R HIA h3 /\ hflag asegs R HIA hq = hflag asegs R HIA h3
      /\ havol asegs R HIA hq = havol asegs R HIA h3 /\ hfr asegs R HIA hq = hfr asegs R HIA h3
      /\ (forall mo, HK asegs R HIA hq mo <-> HK asegs R HIA h3 mo)
      /\ EPIQ hq h3 LBa LBq m0 WA FB sp1 w0 w1 w2 XQ ms.

  Lemma aevtA_KF_swap : forall (hq hq' : HST asegs R HIA) mo1 (Q : config -> Prop) ms,
    (forall mo, HK asegs R HIA hq' mo <-> HK asegs R HIA hq mo) ->
    aevtA asegs (KF asegs R HIA hq' mo1) Q ms -> aevtA asegs (KF asegs R HIA hq mo1) Q ms.
  Proof.
    unfold aevtA. intros hq hq' mo1 Q ms HKE A mo [HKm MFm].
    apply A. split; [apply (proj2 (HKE mo)); exact HKm| exact MFm].
  Qed.

  Ltac epiqh hx :=
    apply evtA_done; unfold EPIQH; exists hx;
    do 6 (split; [first [reflexivity | assumption]|]); split; [first [exact (fun mo => iff_refl _) | assumption]|];
    unfold EPIQ.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01^0@C17025492443.180C17027589631.201D2302662246.158 D31425002750.180D31427099866.202D43080244883.158D59521016234.158D60109446735.180D60111543915.202L13176305223.2  L15822417165.1  L16217372253.4  L1685717371.0   L21218866939.2  L21662875031.20 L21866712442.1  L2275137097.0   L23277816457.20 L2545017055.152 L29311557968.153L29311558097.153L29428292188.18 L29428292188.20 L3482526763.18  L3482526763.20  L35653441506.9  L38235734261.1  L41409160545.3  L41663468825.152L48495615874.18 L4855685921.0   L49347771668.187L52069193238.187L52941874306.3  L53024297377.0  L54445792399.1  L55085943702.3  L55726875008.187L576250137.152  L576250137.188  L58451400700.3  L59308628304.1  L59308873939.3  L60056205954.3  L60098763854.3  L61603606271.2  L6450286553.1   L64903376861.3  L66795766807.18 L67060177655.8  L7049614941.2   L7368832898.20  L7738195705.2   L881835912.0    L9080220944.4   L9356559676.11  O1476819786.201 O1478916974.180 O17025492443.180O17027589631.201O33932766423.202O50702732434.180O50704829622.201O56414299794.180O56416396982.201O59623432085.201O59625529265.180P16211625560.202P21212095580.180P21214192760.201P41419110342.180P41421207522.201P52938159617.201P52940256805.180P55088519473.180P55090616597.201P60050384933.180P60052482049.201P61592333368.158P7750690063.158 Q10588152145.154Q10594630297.190Q15766564435.180Q15768661623.202Q21538057956.157Q21540267236.158Q23234234282.202Q23236331406.180Q24064611734.158Q25158727472.158Q25160678704.157Q29716080448.154Q29717707912.190Q30802955094.155Q34664986449.154Q34964382778.180Q34966479902.202Q45248764730.158Q48117823211.158Q48358016498.202Q48360113622.180Q49698585326.156Q55212697920.154Q59321350679.158Q59321559671.180Q59323656787.202Q9356545927.160 Q9356823431.182 Q9644583048.180 Q9646680236.202 00000100200a01d02g03V03W04804Y04a04e04f04g04h05X05\05]06R06j06k06l07S08?08k09\0:40:80:90:Q0;80;90;j0;k0;l0;m0<00<10<l0=D0=\0=f0=j0>30>40>>0>?0>B0>M0?:0?S0?[0@G0@H0@I0@X0AC0AD0AE0AF0AG0AH0AI0AJ0AK0AL0AM0AN0AO0AP0AQ0Al0BG0Bb0C=0CW0D10DL0Dg0El0Fo0G>0GM0Gf0H?0He0IK0IL0IM0IN0J40JZ0Ji0K80KM0K\0LB0Lh0Li0Mi0NC0N]0O50OD0OE0OF0OG0O\0P10PC0PUFFS2LF2sp1C3kbs3LFB2FB3sp14lenw2p32HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1C3kbs2lo3TOP3LFB2h32FB3sp13SP15Ehtop3SPR4SP1R2F02C0S1R3HIA1h2LF2sp1C3kbs2lo3TOP3LFB2h32FB3sp13SP15Ehtop3SPR4SP1R2F02C0S2LF2sp1C3kbs3LFB2FB3sp14lenw2p32HB5Ha_st5Hl_stFS1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp1S1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp1S2lo3sp1S2FBFSFS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV2C03CCES2FBSS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP14SP1M3ALO3ACV3CAL2C0S2LF2sp1C3kbs3LFB2FB3sp1FFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV2C0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACVS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP14SP1M3ALO3ACV2C0S1R3HIA1h2sp2lo3TOP4HTOPS2loFS2LF2sp1C3kbs3LFB2FB3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVSS2LF2sp1C3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02C0FFSS1CFS2LF2sp1C3kbs3LFB2FB3sp14lenw2p33P303P3L3SPR4SP1R2F02C03LRWS2LF2sp1C3kbs3LFB2FB3sp1S2LF2sp1C3kbs3LFB2FB3sp1S2rv2RV2K2S2K1S1d2N12Z0FS1R2lo3LOSFS1CS2sp2lo3sp1S1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV3CCES1R2lo3LOS3sp12r33ALO3NCES2lo3sp1S1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV2C0FSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF2sp3kbs2lo3LFB3sp13SP1S2LF2sp3kbs2lo3LFB3sp13SP1S2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp14lenw2p33SP14FBLO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p33ALO2F12HB5Ha_st5Hl_stS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS1R2LF3kbs2lo3LOS3LFB3ALOS1R2LF3kbs2lo3LOS3LFB3ALOS2LF3kbs3LFB2FB4lenw2p32HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p32HB5Ha_st5Hl_stFFFS2LF3kbs3LFB2FB4lenw2p32HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p32HB5Ha_st5Hl_stS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FB2F02HBS2LF3kbs3LFB2FBS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1S1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1FS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p33ALO2HB5Ha_st5Hl_stS2LF2sp3kbs2lo3LFB3sp13SP1S2LF2sp3kbs2lo3LFB3sp13SP1S2LF3kbs3LFB2FB2HB5Ha_stS2LF3kbs3LFB2FBFFFS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0". (* [comment removed for export] *)
  Lemma seg_C : forall (h3 : HST asegs R HIA) (LBa LB3 : list blk) (m0 m3 : mem) (WA : list ivl) (FB sp1 : Z)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s7v w0 w1 w2 lenw : word) (p3 rv slo : Z) (r3 : rsa_st),
    bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 ->
    sp1 mod 32 = 0 ->
    HM asegs R HIA h3 LB3 ((FB, 128) :: LF) m3 ->
    (forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) ->
    htop asegs R HIA h3 = htop asegs R HIA h ->
    hstkhi asegs R HIA h3 = hstkhi asegs R HIA h ->
    FB mod 64 = 0 ->
    fresh_apart R LB3 LF FB 128 ->
    rw_cells asegs m3 FB [C8 w0; C8 w1; C8 w2] ->
    rw_cells asegs m3 (FB + 32) [C8 (Z_to_bv 64 p3)] ->
    rw_cells asegs m3 (FB + 64) [C8 lenw] ->
    rw_cells asegs m3 (Z.shiftr FB 3 + al_sb AL)
      [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0);
       C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0);
       C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0);
       C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m3 (bv_unsigned sp + -96)
      [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 (sp1 + 24) [C8 (Z_to_bv 64 FB)] ->
    stk asegs m3 sp1 (sp1 + 24) ->
    stk asegs m3 (sp1 + 32) (bv_unsigned sp + -96) ->
    stk asegs m3 lo sp1 ->
    mem_inv asegs m3 ->
    presW asegs R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 m3 ->
    presW asegs R HIA h3 LB3 LF (bv_unsigned sp) (arl_stklo R) [] m3 m3 ->
    (forall b, In b LBa -> In b LB3) ->
    0 < p3 ->
    p3 + bv_unsigned lenw < 2^64 ->
    rsa_at asegs m3 LB3 C r3 ->
    md_sg (r_N r3) = 1 ->
    (rv = 0 -> md_sg (r_E r3) = 1) ->
    rv = 0 \/ rv = MBEDTLS_ERR_MPI_ALLOC_FAILED ->
    sshad asegs AL m3 slo (bv_unsigned sp) ->
    arl_stklo R <= slo ->
    slo <= bv_unsigned sp - 432 ->
    evtA asegs AL (hcs asegs R HIA h3)
      (EPIQH h3 LBa LB3 m0 WA FB sp1 w0 w1 w2 (fun mm => rsa_at asegs mm LB3 C r3))
      (MS (mkR (Z_to_bv 64 0xb2b48) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 rv)
               a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 FB) (Z_to_bv 64 C) (Z_to_bv 64 (KEY + Z.of_nat (length kbs)))
               (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 (FB + 64)) s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL))
               (Z_to_bv 64 FB) (Z_to_bv 64 (al_sb AL)) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb2b48) fc None m3 (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until r3. intros SP1 SP1M HH3 HCS3 Ehtop Estk F64 FRSH FHD PSL LSL FSHX SAVE SLOT ST16 SThi STlo MI3 PRESa PRESb SUBa P30 P3L RAT SGN SGE RV
      SS3 SSLO3 SSHI3.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 LB3 _ _ HH3) as HTOP. rewrite Ehtop, Estk in HTOP.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP; lia]).
    assert (SCS2 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS1 : crange (hcs asegs R HIA h3) lo (sp1 - lo)) by (eapply crange_sub; [exact SCS2| clear; lia| clear - SP1; lia]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LB3 LF m3 FB 128 lo HH3 eq_refl FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof (fresh_apart_blocks_mono R LB3 LBa LF FB 128 FRSH SUBa) as FRSHa.
    assert (WLa : wlow R LBa LF) by (split; [exact (proj2 (proj2 (proj2 PRESa)))| apply (art_data_lo asegs R HIA)]).
    assert (WLb : wlow R LB3 LF) by (split; [exact (proj2 (proj2 (proj2 PRESb)))| apply (art_data_lo asegs R HIA)]).
    (* [comment removed for export] *)
    flat constr:(RAT) 13%nat. intros _ _ AN AE OKN OKE _ ALL CAL C0 CB CIN _. unfold RSA_CTX_SIZE in CB, CIN.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME.
    flat constr:((hm_apart asegs R HIA h3 LB3 _ m3 HH3)) 2%nat. intros HBR _. rewrite Forall_forall in HBR.
    destruct (HBR _ ltac:(apply in_app_iff; left; exact CIN)) as (_ & _ & CCE & _). cbn [fst snd] in CCE.
    assert (DPOS : forall d, mpdr_at asegs m3 LB3 d -> md_own d = LHeap -> 0 < md_p d /\ md_p d + 4 * md_n d <= alloc_ceiling /\ In (md_p d, 4 * md_n d) LB3).
    { intros d (_ & _ & _ & _ & _ & OW) EO. rewrite EO in OW. flat constr:(OW) 3%nat. flclear OW. intros _ DIN _.
      destruct (HBR _ ltac:(apply in_app_iff; left; exact DIN)) as (P0 & _ & PCE & _). cbn [fst snd] in P0, PCE. split; [exact P0|]. split; [exact PCE| exact DIN]. }
    assert (DN1 : forall d, mpdr_at asegs m3 LB3 d -> md_own d <> LStatic -> 1 <= md_n d -> md_own d = LHeap).
    { intros d (_ & _ & _ & _ & _ & OW) NS N1. destruct (md_own d) eqn:EO; [exfalso; (flat constr:(OW) 2%nat; flclear OW; intros _ Z0); clear - Z0 N1; lia| reflexivity| exfalso; apply NS; reflexivity]. }
    pose proof (rsa_limb_blocks_in asegs m3 LB3 C r3) as LIMB.
    unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in RV.
    pose proof (bv_unsigned_in_range 64 lenw) as LRW. unfold bv_modulus in LRW. cbn [Z.pow Z.of_N Pos.pow] in LRW.
    pose proof (conj MI3 I) as MI3box.
    destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SS3 ltac:(clear - SP1 SSHI3; lia)
                ltac:(clear - SP1M; first [lia | Z.div_mod_to_equations; lia])) as [SS3a _].
    pose proof (conj SS3a I) as SS3box. clear SS3 SS3a.
    (* [comment removed for export] *)
    zpre. if_cases K2; zify_cond K2.
    2:{ kz K2. assert (RVF : rv = -16) by (clear - K2 RV; lia). subst rv.
      zstep. zstep. zstep. try (if_cases K3; zify_cond K3; [ | exfalso; clear - K3; first [ vm_compute in K3; discriminate | vm_compute in K3; lia | lia ] ]).
    (* [comment removed for export] *)
      epiqh h3. ex_state; first [ eassumption | xq_presx RAT MI3box CIN | match goal with |- ?g => idtac "EPIQC1-LEFT:" g end ]. }
    kz K2. assert (RV0 : rv = 0) by (clear - K2 RV; lia). subst rv. specialize (SGE eq_refl). try clear K2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with PB : presW _ _ _ _ _ _ _ _ [] m3 m4, MIx : mem_inv _ m4 |- _ =>
      assert (RAT4 : rsa_at asegs m4 LB3 C r3)
        by (eapply (rsa_at_presx asegs L m3 m4 LB3 (LB3 ++ fdata LF) (bv_unsigned sp) [] C r3);
            [exact RAT| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PB))| exact (proj1 MI3box)| exact MIx
            | apply in_app_iff; left; exact CIN| intros b Hb; apply in_app_iff; left; exact (LIMB b RAT Hb)| exact I| intros; exact I]) end.
    lazymatch goal with HHc : HM _ _ _ h3 _ _ m4 |- _ =>
      pose proof (hm_abase asegs R HIA h3 LB3 _ m4 HHc) as AB4;
      pose proof (hm_aobj_block asegs R HIA h3 LB3 _ m4 C 232 HHc CIN) as OC4;
      assert (OL4 : forall d, mpdr_at asegs m3 LB3 d -> md_own d <> LStatic -> 1 <= md_n d -> aobj asegs AL (hcs asegs R HIA h3) m4 (md_p d) (4 * md_n d))
        by (intros d Hd NS N1; (flat constr:((DPOS d Hd (DN1 d Hd NS N1))) 3%nat; intros _ _ DIN); exact (hm_aobj_block asegs R HIA h3 LB3 _ m4 _ _ HHc DIN))
    end.
    pose proof RSACOMPLETE as RC'. unfold rsa_complete_stmtA, A_RSA_COMPLETE_RP in RC'.
    lazymatch goal with PB : presW _ _ _ _ _ _ _ _ [] m3 m4 |- _ =>
      pose proof (presA_sshad asegs R _ _ _ _ _ _ m3 m4 slo sp1 (proj1 PB) (proj1 SS3box)
                    ltac:(clear - SSLO3; lia) ltac:(rewrite Estk; clear - SP1 TOP HTOP; lia)) as SS4 end.
    assert (CRC4 : client_range L (LB3 ++ fdata ((FB, 128) :: LF)) lo C RSA_CTX_SIZE)
      by (unfold RSA_CTX_SIZE; eapply client_range_block; [apply in_app_iff; left; exact CIN| clear; lia| clear; lia]).
    eapply evtA_cut.
    { eapply RC' with (h := h3) (LB := LB3) (LF := (FB, 128) :: LF) (C := C) (r := r3) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
        first [ (cbn [length]; clear - LFB; lia)
              | (intros EO; exact (proj1 (DPOS _ MN EO))) | (intros EO; exact (proj1 (DPOS _ ME EO)))
              | (intros N1; exact (OL4 _ MN (proj1 OKN) N1)) | (intros N1; exact (OL4 _ ME (proj1 OKE) N1))
              | (intros EO; (flat constr:((DPOS _ MN EO)) 3%nat; intros _ NCE _); clear - NCE ACV ALO LOS; lia)
              | (intros EO; (flat constr:((DPOS _ ME EO)) 3%nat; intros _ NCE _); clear - NCE ACV ALO LOS; lia)
              | (rewrite Ehtop; clear - SP1 TOP; lia)
              | (unfold RSA_CTX_SIZE; clear - SP1 SP1M SLO SLOS NEEDR NS1 SSLO3 SSHI3 F0 F1 ALO LOS ACP ACV C0 CCE;
                 first [lia | Z.div_mod_to_equations; lia])
              | match goal with |- ?g => idtac "CPL-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold rsa_ctxck_postA in PO.
    destruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4' & h4
                    & -> & MI4' & ST4' & HP4 & Ecs4 & Etop4 & Estk4 & Eflag4 & Evol4 & Efr4 & HKI4 & HH4).
    rewrite ?(unsigned_lit sp1) in ST4', HP4 by exact SP1R.
    try (lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end).
    clear AB4 OC4 OL4 RAT4 SS4 CRC4.
    lazymatch goal with H : HM _ _ _ h3 _ _ m4 |- _ => clear H end.
    pose proof (presW_call asegs R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 m4 m4' LB3 ((FB, 128) :: LF) sp1 (arl_stklo R)
                  (hstkhi asegs R HIA h3) [] PRESa HP4 SUBa ltac:(solve_incl) ltac:(clear - SP1; lia) ltac:(clear; lia) ltac:(clear; lia)
                  ltac:(solve_outside_incl)) as PRESa4.
    clear PRESa. rename PRESa4 into PRESa.
    presA_transport HP4. clear HP4.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases K3; zify_cond K3.
    { epiqh h4. ex_state; first [ eassumption | xq_presx RAT MI3box CIN | match goal with |- ?g => idtac "EPIQC2-LEFT:" g end ]. }
    clear K3.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch goal with PB : presW _ _ _ _ _ _ _ _ [] m3 m5, MIx : mem_inv _ m5 |- _ =>
      assert (RAT5 : rsa_at asegs m5 LB3 C r3)
        by (eapply (rsa_at_presx asegs L m3 m5 LB3 (LB3 ++ fdata LF) (bv_unsigned sp) [] C r3);
            [exact RAT| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PB))| exact (proj1 MI3box)| exact MIx
            | apply in_app_iff; left; exact CIN| intros b Hb; apply in_app_iff; left; exact (LIMB b RAT Hb)| exact I| intros; exact I]) end.
    flat constr:(RAT5) 9%nat. intros HD5 _ _ _ _ _ LEN5 ALL5 _.
    pose proof (Forall_inv ALL5) as MN5. pose proof (Forall_inv (Forall_inv_tail ALL5)) as ME5.
    lazymatch goal with HHc : HM _ _ _ h4 _ _ m5 |- _ =>
      pose proof (hm_aobj_block asegs R HIA h4 LB3 _ m5 C 232 HHc CIN) as OC5;
      assert (OL5 : forall d, mpdr_at asegs m3 LB3 d -> md_own d <> LStatic -> 1 <= md_n d -> aobj asegs AL (hcs asegs R HIA h4) m5 (md_p d) (4 * md_n d))
        by (intros d Hd NS N1; (flat constr:((DPOS d Hd (DN1 d Hd NS N1))) 3%nat; intros _ _ DIN); exact (hm_aobj_block asegs R HIA h4 LB3 _ m5 _ _ HHc DIN))
    end.
    lazymatch goal with PB : presW _ _ _ _ _ _ _ _ [] m3 m5 |- _ =>
      pose proof (presA_sshad asegs R _ _ _ _ _ _ m3 m5 slo sp1 (proj1 PB) (proj1 SS3box)
                    ltac:(clear - SSLO3; lia) ltac:(rewrite Estk; clear - SP1 TOP HTOP; lia)) as SS5 end.
    assert (CRC5 : client_range L (LB3 ++ fdata ((FB, 128) :: LF)) lo C 48)
      by (eapply client_range_block; [apply in_app_iff; left; exact CIN| clear; lia| clear; lia]).
    pose proof RSACKPUB as CK'. unfold rsa_check_pubkey_stmtA, A_RSA_CHECK_PUBKEY_RP in CK'.
    rewrite <- Ecs4.
    eapply evtA_cut.
    { eapply CK' with (h := h4) (LB := LB3) (LF := (FB, 128) :: LF) (C := C) (r := r3) (lo := lo) (slo := slo);
        rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity;
        first [ (cbn [length]; clear - LFB; lia)
              | exact (conj MN5 (or_introl SGN)) | exact (conj ME5 (or_introl SGE))
              | exact (proj1 OKN) | exact (proj1 OKE)
              | (intros EO; exact (proj1 (DPOS _ MN EO))) | (intros EO; exact (proj1 (DPOS _ ME EO)))
              | (eapply aobj_sub; [exact OC5| clear; lia| clear; lia])
              | (intros N1; exact (OL5 _ MN (proj1 OKN) N1)) | (intros N1; exact (OL5 _ ME (proj1 OKE) N1))
              | (intros EO; (flat constr:((DPOS _ MN EO)) 3%nat; intros _ NCE _); clear - NCE ACV ALO LOS; lia)
              | (intros EO; (flat constr:((DPOS _ ME EO)) 3%nat; intros _ NCE _); clear - NCE ACV ALO LOS; lia)
              | (rewrite Etop4, Ehtop; clear - SP1 TOP; lia)
              | (unfold RSA_CTX_SIZE; clear - SP1 SP1M SLO SLOS NEEDR NS1 SSLO3 SSHI3 F0 F1 ALO LOS ACP ACV C0 CCE CAL CB;
                 first [lia | Z.div_mod_to_equations; lia])
              | match goal with |- ?g => idtac "CKP-PRE-LEFT:" g end ]. }
    intros ms' PO. unfold rsa_ctxck_postA in PO.
    destruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m5' & h5
                    & -> & MI5' & ST5' & HP5 & Ecs5 & Etop5 & Estk5 & Eflag5 & Evol5 & Efr5 & HKI5 & HH5).
    rewrite ?(unsigned_lit sp1) in ST5', HP5 by exact SP1R.
    try (lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end).
    rewrite Ecs4 in Ecs5 |- *. rewrite Etop4 in Etop5. rewrite Estk4 in Estk5. rewrite Eflag4 in Eflag5.
    rewrite Evol4 in Evol5. rewrite Efr4 in Efr5.
    assert (HKI5' : forall mo, HK asegs R HIA h5 mo <-> HK asegs R HIA h3 mo) by (intros mo; exact (iff_trans (HKI5 mo) (HKI4 mo))).
    clear HKI5.
    clear OC5 OL5 RAT5 ALL5 MN5 ME5 SS5 CRC5. try clear HD5.
    lazymatch goal with H : HM _ _ _ h4 _ _ m5 |- _ => clear H end.
    pose proof (presW_call asegs R HIA h3 LBa LF (bv_unsigned sp) (arl_stklo R) WA m0 m5 m5' LB3 ((FB, 128) :: LF) sp1 (arl_stklo R)
                  (hstkhi asegs R HIA h4) [] PRESa HP5 SUBa ltac:(solve_incl) ltac:(clear - SP1; lia) ltac:(clear; lia) ltac:(clear - Estk4; lia)
                  ltac:(solve_outside_incl)) as PRESa5.
    clear PRESa. rename PRESa5 into PRESa.
    presA_transport HP5. clear HP5.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases K4; zify_cond K4.
    { epiqh h5. ex_state; first [ eassumption | xq_presx RAT MI3box CIN | match goal with |- ?g => idtac "EPIQC3-LEFT:" g end ]. }
    clear K4.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    epiqh h5. ex_state; first [ eassumption | xq_presx RAT MI3box CIN | match goal with |- ?g => idtac "EPIQC4-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L26892418956.1L40281191306.3L62018535662.100000400=00@S2spS1R3HIA1hS1R". (* [comment removed for export] *)
  Lemma rp_fin : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Phq,(5.$66.VR,VHIA,)Php,(5.$66.VR,VHIA,)PLBq,(6.$7.)PWA,(6.$4>.)PFB,$1:.Psp1,$1:.Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Prq,$8.Pms,$67.P,(73.R;.R:.VLB,R9.Vm,R8.R7.R6.R5.R4.R3.Lmm,P,(2.&40.)(3.(2.&8.))(29.$66.R1.R:.VC,R3.)R1.)P,Px,$1:.P,(78.(18.(19.$1:.$1:.)(1;.$1:.$1:.VC,(1<.VC,+>8.))(1>.(19.$1:.$1:.)))R1.)(78.R;.R2.)P,Px,$1:.P,(22.$66.VR,VHIA,R=.R1.)(22.$66.VR,VHIA,R?.R2.)P,(:.$1:.(17.$66.VR,VHIA,R>.)(17.$66.VR,VHIA,R=.))P,(9.(23.(3=.(13.&40.Vsp,)+90.)R:.)(23.R:.(3=.(13.&40.Vsp,)+80.)))P,(:.$1:.(40.R;.+20.)=)P,(:.$1:.(40.R=.+40.)=)P,(2>.VR,VLB,VLF,R>.+80.)P,(2>.VR,R11.VLF,R?.+80.)P,(70.(22.$66.VR,VHIA,Vh,)R10.+80.)P,PB,$1:.Pj,$1:.P,(2:.(19.$1:.$1:.)(1;.$1:.$1:.R2.R1.)VLF,)(2;.(23.(1<.R14.+80.)R3.)(23.(1<.R3.R2.)R14.))P,Px,$1:.P,(22.$66.VR,VHIA,Vh,R1.)(22.$66.VR,VHIA,R18.R2.)P,(:.$1:.(1?.$66.VR,VHIA,R17.)(1?.$66.VR,VHIA,Vh,))P,(:.$1:.(17.$66.VR,VHIA,R18.)(17.$66.VR,VHIA,Vh,))P,(:.$1:.(20.$66.VR,VHIA,R19.)(20.$66.VR,VHIA,Vh,))P,(23.(24.$66.VR,VHIA,R1:.)(1<.(24.$66.VR,VHIA,Vh,)(25.(37.(33.(2.&8.)Vkbs,)))))P,(23.(26.$66.VR,VHIA,R1;.)(1<.(26.$66.VR,VHIA,Vh,)$27.))P,Pb,$7.P,(2:.$7.R1.R1;.)(2;.(2:.$7.R2.VLB,)(2:.$7.R2.(2<.R15.)))P,Pb,$7.P,(2:.$7.R1.VLB,)(2:.$7.R2.R1=.)P,Pb,$7.P,(2:.$7.R1.(2<.R16.))(2=.(2:.$7.R2.VLB,))P,Pb,$7.P,(2:.$7.R1.(2<.R17.))(2>.VR,VLB,VLF,(2?.$1:.$1:.R2.)(30.$1:.$1:.R2.))(79.$66.(7:.$66.VR,VHIA,R20.Vmo0,)(4;.$66.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VC,(37.(33.(2.&8.)Vkbs,))Vlo,Vm,Vmo0,)R16.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros EQ WSUB HCSp ESp SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq L1 L2 L3 L4.
    destruct EQ as (mm & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & s3v & s4v & s5v & s6v & s7v & s11v
                    & -> & HHq & FHD & FSHX & SAVE & SLOT & ST16 & SThi & STlo & MIq & PRESa & RATq).
    pose proof (presW_hmono R HIA hp hq LB LF _ _ _ m _ PRESa HCSp ESp) as PRESq.
    pose proof (presW_init_at R HIA hq _ _ LBq LF mm (bv_unsigned sp) (arl_stklo R) [] hq HHq
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBa := LB) (LBb := LBq);
        first [ exact HHq | exact HCSq | exact ETq | exact ESq | exact PRESq | exact PRES2 | exact FRSH | exact FRSHq | exact CFB | exact AP | exact L2
              | eassumption | reflexivity | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold rsa_parse_pubkey_postA.
    do 15 eexists. exists m9, mo9, h4, LBq, rq.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split.
    { pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES9) as HPF. rewrite ESq in HPF.
      eapply presA_weaken; [exact HPF| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact WSUB]. }
    split; [rewrite E4top; exact ETq|]. split; [rewrite E4stk; exact ESq|]. split; [rewrite E4flag; exact EFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; exact EVq|]. split; [rewrite E4fr; exact EFRq|].
    split; [exact HH4|].
    split.
    { flat constr:(RATq) 13%nat. intros _ _ _ _ _ _ _ _ _ _ _ CINq _. unfold RSA_CTX_SIZE in CINq.
      eapply (rsa_at_presx asegs L mm m9 LBq (LBq ++ fdata LF) (bv_unsigned sp) []);
        [exact RATq| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA _ _ LF _ _ _ _ _ PRES29))| exact MIq| exact MI9
        | apply in_app_iff; left; exact CINq| intros b Hb; apply in_app_iff; left; exact (rsa_limb_blocks_in asegs _ _ _ _ b RATq Hb)| exact I| intros; exact I]. }
    split; [exact L1|]. split; [exact L2|]. split; [exact L3| exact L4].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RB : mpi_read_binary_stmtA_r asegs R HIA A_MPI_READ_BINARY.
  Hypothesis RAT0 : rsa_at asegs m LB C (rsa_fresh C).
  Hypothesis HKY0 : bytes_at asegs m KEY kbs.
  Hypothesis CRK : client_range L (LB ++ fdata LF) lo KEY LEN.
  Hypothesis DKC : KEY + LEN <= C \/ C + 232 <= KEY.
  Hypothesis DKS : KEY + LEN <= lo \/ bv_unsigned sp <= KEY.
  Hypothesis BUD : havol asegs R HIA h + RSA_PP_PHI LEN <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + RSA_PP_FR <= FR_MAX.
  Variable slo : Z.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SSLO : arl_stklo R <= slo.
  Hypothesis SSHI : slo <= bv_unsigned sp - 432.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0?L10121468914.25L10127712114.4 L1044568644.12 L1045152775.11 L1045152775.12 L11585923358.11L11586385757.10L11586385757.11L12595682813.9 L12595843834.9 L12595843837.8 L13658852356.2 L14093053380.4 L14671903450.1 L1540877545.3  L16256253080.6 L16256414616.7 L16446017371.25L1741360775.7  L17565801997.5 L1820677675.25 L19959024712.1 L19964958796.25L19979640288.25L21179676237.3 L21193694771.25L21204179871.25L2164292835.4  L2275137097.0  L22923669014.9 L23137366490.1 L2397623502.7  L24128180555.1 L24926391073.0 L25985555144.1 L26892418956.1 L27188209011.3 L27356981623.3 L27800688430.1 L27884611213.1 L28390317327.1 L28762784221.6 L28762787805.5 L2953011965.10 L2975321653.25 L30417338446.25L31362055200.1 L3199309172.5  L32381825919.0 L32454903270.1 L32624459940.2 L33126711374.3 L33213852813.1 L33337549682.25L3480283673.25 L3482382261.25 L35653441506.9 L35666090444.8 L37156630869.0 L37622523289.3 L37796632789.0 L37814404089.2 L3789236036.8  L37898896573.25L38012506529.0 L38291272584.5 L38723264084.4 L38737777364.5 L39306246569.9 L39845491246.1 L40281191306.3 L46452926541.3 L48345000542.9 L50790580594.6 L51174981929.8 L52045659405.3 L52615975131.8 L52665112138.7 L52665116118.10L52680898955.25L52758365172.6 L53413695971.4 L55116274681.2 L56523586534.1 L5901681115.3  L59203503582.9 L59255599441.8 L59256028753.7 L59256028758.8 L59314923118.3 L59361649295.6 L60098763854.3 L60438662093.2 L60660409869.25L62018535662.1 L6203936179.1  L62672175878.25L627252352.12  L627704515.11  L627704515.12  L63158919349.6 L65566735028.9 L66557520514.1 L67028235242.8 L6899380056.1  L7034380190.8  L7034867865.8  L7034867870.7  L7546167771.7  L9356559645.11 L9631767084.2  L973128649.0   00000b01101201301401501601701801901:01?01N01Q01]02202L03D03E03W04M04R05G06<06F07107\07f07g08K08N08b08f08g08l09009909E09H09L09P09i09j0:L0;>0<>0<A0<V0<W0<[0<b0<l0=00=o0>_0?O0?g0@G0@H0@P0@Q0@]0A<0B<0B=0BS0B`0C20C30C60C?0CI0Ck0DB0E10E=0EW0F00FX0GW0H10H;0HE0HI0HU0I70I80I90I:0ID0I]0Ig0In0Ja0Jd0Ji0K[0K\0K]0K^0L40LV0L[0M:0M>0M?0M@0MA0M[0NF0NM0NNS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP12p33KP3S3KEY2K02p33KP3FFFFFFFFFS3kbsS1C3KEY3kbs3DKCS1CS2sp3sp13SP1S1R3HIA1h3FR02h24HFR2S1R3HIA1h3kbs4PHI02h24VOL2S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p35lenw33KL34LRW3FS1R3HIA1h4BUDF3FR0S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p24lenw3KL23LRWS3sp1S1R3HIA5NEEDR1h2sp1C3KEY3kbs2lo2K03SLO3TOP2C03sp13SP1S1R3HIA5NEEDR1h2sp1C3KEY3kbs2lo2K03SLO3TOP2C03sp13SP1S1C2FB3APCS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP1S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP1S1C1A1k2HASS1R3HIA1h3kbs3BUD2h24VOL25lenw34MONOS1CS1R1C2lo3LOS3ALO3CCES2FBSS3sp1S2spS2FB1c2HcS3KEY2p23KP2S1CS2FBS2FBS3KEY3kbs2KB2p35lenw33KL3FS2sp3KEY3kbs2lo3DKS3sp13SP11a2Ha1KS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP12p23KP2S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKC2C03sp13SP12p35lenw33KP33KL3S1CS3KEY3kbs2p24lenw3KL2SS2FBS2dN2N1S1C2FB3APCS2FBS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKC2C03sp13SP12p24lenw3KP23KL2S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP14SP1MS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP14SP1MS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h3kbs3BUD4PHI04lenw4MONOSS1C1x2HxSS5lenw34LRW3S1R3HIA1h3kbs4lenw2h24MONO4HV2'S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKS2C03sp13SP12p35lenw33KP33KL3SS3KEY3kbs2p35lenw33KL3S1R3HIA1h3FR0S1R3HIA1h3kbs4PHI0FS1CS1R3HIA1hS1C2FB3APCS1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCS1R5NEEDR2sp2lo3LOS3SLOS3KEY3kbs2p24lenw3KP23KL21a2Ha2p35lenw33KP33KL3S2sp3sp13SP1S2sp3KEY3kbs2lo3DKS1a2Ha1KS1R3HIA1h2h24HFR22h34HFR3S1R3HIA1h3kbs2h24VOL25lenw32h34MONO4HV3'S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKS2C03sp13SP12p24lenw3KP23KL2S3KEY3kbs2p35lenw33KP33KL3S1C1A1k2HAS4lenw3LRWS2FBS3KEY2p33KP3S1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCFFFS3kbs2NE1KS3KEY3kbs2p24lenw3KP23KL2S1R2lo3LOSS2dE2N1S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p35lenw33KL3S1RS3sp1S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p24lenw3KL2FFFS1R3HIA1h4BUDF2h24HFR2S1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCS3kbsS1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2FBFFFS1R5NEEDR2sp1C2lo3SLO4STKCS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S2FB2F0S". (* [comment removed for export] *)
  Lemma rp_main : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(28.$66.VR,VHIA,Vh,VLB,VLF,Vm,)P,(21.$66.VR,VHIA,Vh,Vmo0,)P,(12.$66.Vm,Vlo,(13.&40.Vsp,))P,(11.$66.Vm,)P,(43.$66.(44.VR,)(22.$66.VR,VHIA,Vh,)Vm,VKEY,(37.(33.(2.&8.)Vkbs,)))(4:.$66.(4;.$66.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VC,(37.(33.(2.&8.)Vkbs,))Vlo,Vm,Vmo0,)(;.(<.(=.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(41.&40.VC,)(41.&40.VKEY,)(41.&40.(37.(33.(2.&8.)Vkbs,)))R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(41.&40.$6?.)Vfc,(?.(2.&40.))Vm,(10.$66.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST MI OKEY0.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP; lia]).
    flat constr:(RAT0) 13%nat. intros _ _ _ _ _ _ _ _ CAL C0 CB CIN _. unfold RSA_CTX_SIZE in CB, CIN.
    assert (PHI0 : 0 <= MPI_RB_PHI LEN) by (unfold MPI_RB_PHI, AVOL_CALL; clear; lia).
    assert (FR0 : 0 <= MPI_RB_FR 28) by (unfold MPI_RB_FR, fr_charge; clear; lia).
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & lenj
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & PSL & LSL & FSHX
                   & SAVE & SLOT & ST16 & SThi & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (HCS1 : forall x, CS x -> hcs asegs R HIA h1 x) by (intros x Hx; rewrite Ehcs; exact Hx).
    (* [comment removed for export] *)
    assert (CRKs : client_range L (LB ++ fdata LF) (bv_unsigned sp) KEY LEN).
    { intros a Ha. destruct (CRK a Ha) as [K|[K|K]]; [| right; left; exact K| right; right; exact K]. left. clear - K Ha DKS. lia. }
    assert (HKY1 : bytes_at asegs m1 KEY kbs) by (eapply heap_presx_bytes_at; [exact HPX01| exact HKY0| exact CRKs| cbn; exact I]).
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (OKEY1 : aobj asegs AL CS m1 KEY LEN).
    { eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OKEY0| exact CRKs| clear - LOS SLO NEEDR; lia| exact TOPCS]. }
    assert (APK : LEN = 0 \/ FB + 128 <= KEY \/ KEY + LEN <= FB).
    { destruct (Z.eq_dec LEN 0) as [E0|NE]; [left; exact E0| right].
      destruct (frame_apart_obj0 R HIA LB LF lo KEY LEN FB 128 FRSH CRK ltac:(clear - NE; lia) ltac:(clear; lia) LOS) as [K|K]; [exfalso; clear - K NE; lia| exact K]. }
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply seg_A with (h1 := h1); first [ eassumption | reflexivity | match goal with |- ?g => idtac "SEGA-PRE-LEFT:" g end ]. }
    cbv beta. intros ms2 [EQ|CQ].
    { (* [comment removed for export] *)
      eapply aevtA_mono; [| intros c Hc; exact Hc].
      assert (KFE : forall Q ms', aevtA asegs (KF asegs R HIA h1 mo0) Q ms' -> aevtA asegs (KF asegs R HIA h mo0) Q ms').
      { intros Q ms' HA mo [HKm MFm]. apply HA. split; [apply (proj2 (HKI mo)); exact HKm| exact MFm]. }
      apply KFE.
      eapply rp_fin with (hq := h1) (hp := h) (LBq := LB) (rq := rsa_fresh C);
        first [ exact EQ | exact HCS1 | exact Estk | exact Ehtop | exact Eflag | exact FRSH | exact CFB | exact AP | eassumption
              | (intros x Hx; exact I)
              | (rewrite Evol; clear - PHI0; unfold RSA_PP_PHI; lia) | (rewrite Efr; clear - FR0; unfold RSA_PP_FR; lia)
              | (intros b Hb; left; exact Hb) | (intros b Hb; exact Hb) | (intros b []) 
              | match goal with |- ?g => idtac "FINA-LEFT:" g end ]. }

    (* [comment removed for export] *)
    destruct CQ as (mc & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & p2 & lenw
                    & -> & HHc & FHDc & PSLc & LSLc & FSHXc & SAVEc & SLOTc & ST16c & SThic & STloc & MIc & PRESc & HKYc & OKEYc & KP2 & KL2 & RATc).
    clear FHD PSL LSL FSHX SAVE SLOT ST16 SThi STlo HKY1 OKEY1 HH1 PRES0 HP01 HPX01.
    pose proof (bv_unsigned_in_range 64 lenw) as LRW. unfold bv_modulus in LRW. cbn [Z.pow Z.of_N Pos.pow] in LRW.
    destruct (sub_input asegs mc KEY kbs p2 (bv_unsigned lenw) HKYc ltac:(clear - KP2; lia) ltac:(clear - LRW; lia) KL2) as [HIB LENI].
    set (ibs := firstn (Z.to_nat (bv_unsigned lenw)) (skipn (Z.to_nat (p2 - KEY)) kbs)) in HIB, LENI.
    flat constr:(RATc) 9%nat. intros _ _ ANc _ OKNc _ _ ALLc _. cbn [rsa_fresh r_N r_E] in ANc, OKNc, ALLc.
    pose proof (Forall_inv ALLc) as MNc.
    pose proof (hm_aobj_block asegs R HIA h1 LB _ mc C 232 HHc CIN) as OCc.
    flat constr:((hm_apart asegs R HIA h1 LB _ mc HHc)) 2%nat. intros HBRc BAc. rewrite Forall_forall in HBRc.
    destruct (HBRc _ ltac:(apply in_app_iff; left; exact CIN)) as (_ & _ & CCE & _). cbn [fst snd] in CCE.
    assert (APC : FB + 128 <= C \/ C + 232 <= FB) by (apply F3; apply in_app_iff; left; exact CIN).
    pose proof RB as RB'. unfold mpi_read_binary_stmtA_r, A_MPI_READ_BINARY in RB'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply RB' with (h := h1) (LB := LB) (LF := (FB, 128) :: LF) (dX := mpd_z (C + 16)) (B := p2) (ibs := ibs) (lo := lo) (d := 28);
        cbn [mpd_z md_addr md_own md_p md_n];
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENI; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr;
        first [ exact HHc | exact MNc | exact HIB | exact STloc | exact LOS | exact MIc | exact TPV | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- LNull <> LStatic => discriminate
                | |- mpd_writableA _ _ _ _ _ _ =>
                    split; [cbn [md_addr mpd_z]; eapply client_wrange_block; [apply in_app_iff; left; exact CIN| clear; lia| clear; lia]
                           | cbn [md_own mpd_z]; intros EO; discriminate EO]
                | |- client_range _ _ _ p2 _ =>
                    intros a Ha; destruct (CRK a ltac:(clear - Ha KP2 KL2; lia)) as [K|[K|K]]; [left; exact K| right; left; exact K| right; right];
                    (flat constr:(K) 3%nat; flclear K; intros b Hb Rb); exists b; split; [apply fdata_cons_sub; exact Hb| exact Rb]
                | |- LNull = LHeap -> _ => intros EO; discriminate EO
                | |- aobj _ _ _ _ (C + 16) 16 => rewrite <- Ehcs; eapply aobj_sub; [exact OCc| clear; lia| clear; lia]
                | |- aobj _ _ _ _ p2 _ => rewrite <- Ehcs; eapply aobj_sub; [exact OKEYc| clear - KP2; lia| clear - KL2; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX =>
                    pose proof (MPI_RB_PHI_mono (bv_unsigned lenw) LEN ltac:(clear - KP2 KL2; lia)) as MONO; unfold RSA_PP_PHI in BUD; clear - BUD MONO PHI0; lia
                | |- uw_obj _ _ _ _ => right; clear; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold RSA_PP_FR in BUDF; clear - BUDF FR0; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ = Z_to_bv 64 _ => rewrite ?Z_to_bv_bv_unsigned; reflexivity
                | |- _ => clear - SP1 SP1M SLO NEEDR TOP KP2 KL2 K0 KB DKC DKS LRW C0 CB; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "CALL1-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & LB2 & dN & rv
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & RV & RV0 & FRS2).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xb2aac)) with (Z_to_bv 64 0xb2aac : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).

    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    rewrite Ehtop in HT2. rewrite Estk in HS2, HP2. rewrite Eflag in HF2. rewrite Evol in HV2. rewrite Efr in HFR2.
    unfold mpd_keep in HP2, FRS2. cbn [mpd_z md_own] in HP2, FRS2.
    assert (HCSh2 : forall x, CS x -> hcs asegs R HIA h2 x) by (intros x Hx; apply HCS2; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h2) as CSOK2.
    pose proof (fresh_apart_relist_rp R HIA h2 LB LB2 LF m2 FB 128 FRSH HH2) as FRSH2.
    flat constr:(OUT2) 5%nat. flclear OUT2. intros AN2 NST2 O1 O2 O3. cbn [mpd_z md_addr] in AN2.
    assert (SUB2 : forall b, In b LB -> In b LB2) by (intros b Hb; apply O2; [exact Hb| cbn; intros []]).
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(C + 16, C + 16 + 16)] mc m2).
    { eapply presA_weaken; [exact HP2| intros b' Hb; exact Hb| intros b' Hb; right; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    (* [comment removed for export] *)
    assert (PRESa2 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [(C, C + 232)] m m2).
    { flat constr:(PRESc) 4%nat. flclear PRESc. intros P0 C1 C2 C3. split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans.
      - eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I].
      - eapply presA_weaken; [exact HP2'| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
        intros x Hx. cbn [outside] in Hx |- *. split; [clear - Hx; lia| exact I]. }
    pose proof (presW_hmono R HIA h h2 LB LF _ _ _ m _ PRESa2 HCSh2 HS2) as PRESa2h.
    pose proof (presW_init_at R HIA h2 _ _ LB2 LF m2 (bv_unsigned sp) (arl_stklo R) [(C + 8, C + 16)] h2 HH2
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb2.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 128 -> cshd R LBq ((FB, 128) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJX : forall A k, (A + k <= C \/ C + 232 <= A) -> disjoint_from [(C + 16, C + 16 + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    assert (STKC : C + 232 <= lo) by (clear - CCE ACV ALO LOS; lia).
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) LB ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(C + 16, C + 16 + 16)] mc m2 FB _ CSOK) in FSHXc;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 FB _ HP2) in FHDc;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INH| clear; lia| clear; lia] | apply DJX; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in PSLc;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | apply DJX; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in LSLc;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact IND| clear; lia| clear; lia] | apply DJX; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SAVEc; [| apply client_range_stack; clear - SP1; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SLOTc; [| apply client_range_stack; clear; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in ST16c; [| clear; lia| apply DJX; clear - STKC SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m2 _ _ HP2) in SThic; [| clear; lia| apply DJX; clear - STKC SLO NEEDR SP1; lia].
    assert (CRK1 : client_range L (LB ++ fdata ((FB, 128) :: LF)) sp1 KEY LEN).
    { intros a Ha. destruct (CRK a Ha) as [K|[K|K]]; [left; clear - K Ha DKS SP1; lia| right; left; exact K| right; right].
      flat constr:(K) 3%nat. flclear K. intros b Hb Rb. exists b. split; [apply fdata_cons_sub; exact Hb| exact Rb]. }
    assert (HKY2 : bytes_at asegs m2 KEY kbs).
    { eapply heap_presx_bytes_at; [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| exact HKYc| exact CRK1| apply DJX; clear - DKC; lia]. }
    assert (OKEY2 : aobj asegs AL (hcs asegs R HIA h2) m2 KEY LEN).
    { eapply aobj_cs_mono; [exact HCS2|]. pose proof (hcs_ok asegs R HIA h1) as CSOK1.
      eapply (presA_aobj asegs R); [exact CSOK1| exact HP2| exact OKEYc| exact CRK1| clear - LOS SLO NEEDR SP1; lia|].
      rewrite Ehcs. exact TOPCS. }
    (* [comment removed for export] *)
    assert (RAT2 : rsa_at asegs m2 LB2 C (mkRSA 0 dN (mpd_z (C + 32)))).
    { change 0 with (r_len (rsa_fresh C)) at 1. change (mpd_z (C + 32)) with (r_E (rsa_fresh C)).
      eapply (rsa_at_importN asegs L mc m2 LB LB2 (LB ++ fdata ((FB, 128) :: LF)) sp1 C (rsa_fresh C) dN);
        [exact RATc| reflexivity| reflexivity| exact MX2| split; [exact AN2| split; [exact NST2| split; [exact O1| split; [exact O2| exact O3]]]]
        | exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP2)| exact MIc| exact MI2| apply in_app_iff; left; exact CIN|].
      intros EO. flat constr:((proj1 MX2)) 6%nat. intros _ _ _ _ _ OW. rewrite EO in OW. flat constr:(OW) 2%nat. flclear OW. intros N1 _.
      destruct (FRS2 (md_p dN, 4 * md_n dN) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [[]|FRN]. cbn [fst snd] in FRN.
      eapply (fresh_apart_ne R LB _ _ _ C 232); [exact FRN| exact CIN| clear - N1; lia| clear; lia]. }
    clear HP2 HP2' RATc MNc OCc HBRc BAc HHc MIc HKYc OKEYc PRESc PRESa2 STloc ALLc.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo0) _ _ _ (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    clear HK1 MF1 MF2 mo1.
    eapply (aevtA_cut_evtA_KF asegs R HIA h2 mo0).
    { eapply seg_B with (h2 := h2) (LBa := LB) (LB2 := LB2) (m0 := m) (WA := [(C, C + 232)]) (r2 := mkRSA 0 dN (mpd_z (C + 32))) (rv := rv);
        cbn [r_N r_E r_len];
        first [ exact HH2 | exact HCSh2 | exact HT2 | exact HS2 | exact FRSH2 | exact PRESa2h | exact PRESb2 | exact SUB2 | exact RAT2 | exact RV | exact HKY2 | exact OKEY2
              | eassumption | reflexivity
              | (apply wcover_inside; cbn [inside]; left; clear; lia)
              | (intros E0; exact (proj1 (RV0 E0)))
              | match goal with |- ?g => idtac "SEGB-PRE-LEFT:" g end ]. }

    assert (L3N : forall b, In b (mpd_blk dN) -> fresh_apart R LB LF (fst b) (snd b) /\ ~ In b LB).
    { intros [B k] Hb. destruct (FRS2 _ Hb) as [[]|FRN]. cbn [fst snd] in FRN |- *.
      assert (K0' : 0 < k).
      { unfold mpd_blk in Hb. destruct (md_own dN) eqn:EO; try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as <- <-.
        flat constr:((proj1 MX2)) 6%nat. intros _ _ _ _ _ OW. rewrite EO in OW. flat constr:(OW) 2%nat. flclear OW. intros N1 _. clear - N1. lia. }
      split; [eapply fresh_apart_frames_mono; [exact FRN| intros b' Hb'; eapply fdata_incl; [| exact Hb']; intros fb Hfb; right; exact Hfb]| eapply fresh_apart_notin; [exact FRN| exact K0']]. }
    assert (VOL2 : havol asegs R HIA h2 <= havol asegs R HIA h + MPI_RB_PHI LEN).
    { pose proof (MPI_RB_PHI_mono (bv_unsigned lenw) LEN ltac:(clear - KP2 KL2; lia)) as MONO. pose proof HV2 as HV2'. rewrite LENI in HV2'. clear - HV2' MONO. lia. }
    cbv beta. intros ms5 [EQ|CQ].
    { (* [comment removed for export] *)
      flat constr:((EPIQ_ex _ _ _ _ _ _ _ _ _ _ _ Z (fun lenv mm => rsa_at asegs mm LB2 C (mkRSA lenv dN (mpd_z (C + 32)))) ms5 EQ)) 2%nat. intros lenv EQl.
      eapply rp_fin with (hq := h2) (hp := h2) (LBq := LB2) (WA := [(C, C + 232)]) (rq := mkRSA lenv dN (mpd_z (C + 32)));
        first [ exact EQl | exact HCSh2 | exact HT2 | exact HS2 | exact HF2 | exact FRSH | exact FRSH2 | exact CFB | exact AP | exact SUB2 | reflexivity
              | (intros x Hx; exact Hx)
              | (unfold RSA_PP_PHI; clear - VOL2 PHI0; lia) | (unfold RSA_PP_FR; clear - HFR2 FR0; lia)
              | (intros b Hb; destruct (O1 b Hb) as [K|K]; [left; exact K| right; unfold rsa_limb_blocks; cbn [r_N r_E]; apply in_or_app; left; exact K])
              | (intros b Hb; unfold rsa_limb_blocks in Hb; cbn [r_N r_E mpd_z mpd_blk md_own] in Hb; rewrite app_nil_r in Hb; exact (proj2 (L3N b Hb)))
              | (intros b Hb; unfold rsa_limb_blocks in Hb; cbn [r_N r_E mpd_z mpd_blk md_own] in Hb; rewrite app_nil_r in Hb; exact (proj1 (L3N b Hb)))
              | eassumption
              | match goal with |- ?g => idtac "FINB-LEFT:" g end ]. }

    (* [comment removed for export] *)
    clear FHDc PSLc LSLc FSHXc SAVEc SLOTc ST16c SThic HKY2 OKEY2 PRESb2 PRESa2h RAT2 KP2 KL2 LRW.
    destruct CQ as (mc' & d0 & d1 & d2 & da3 & da4 & da5 & da6 & da7 & d3 & d4 & d5 & d6 & p3 & lenw3
                    & -> & HHd & FHDd & PSLd & LSLd & FSHXd & SAVEd & SLOTd & ST16d & SThid & STlod & MId & PRESd & HKYd & OKEYd & KP3 & KL3 & [lenv [RATd SGNN]]).
    cbn [r_N r_E] in RATd, SGNN.
    pose proof (bv_unsigned_in_range 64 lenw3) as LRW3. unfold bv_modulus in LRW3. cbn [Z.pow Z.of_N Pos.pow] in LRW3.
    destruct (sub_input asegs mc' KEY kbs p3 (bv_unsigned lenw3) HKYd ltac:(clear - KP3; lia) ltac:(clear - LRW3; lia) KL3) as [HIB3 LENI3].
    set (ibs3 := firstn (Z.to_nat (bv_unsigned lenw3)) (skipn (Z.to_nat (p3 - KEY)) kbs)) in HIB3, LENI3.
    flat constr:(RATd) 13%nat. intros _ _ _ _ _ _ _ ALLd _ _ _ CIN2 _. cbn [r_N r_E] in ALLd. unfold RSA_CTX_SIZE in CIN2.
    unfold rsa_mpds in ALLd. cbn [r_N r_E] in ALLd.
    pose proof (Forall_inv ALLd) as MNd. pose proof (Forall_inv (Forall_inv_tail ALLd)) as MEd.
    pose proof (hm_aobj_block asegs R HIA h2 LB2 _ mc' C 232 HHd CIN2) as OCd.
    flat constr:((hm_apart asegs R HIA h2 LB2 _ mc' HHd)) 2%nat. intros HBRd BAd.
    pose proof RB as RB2. unfold mpi_read_binary_stmtA_r, A_MPI_READ_BINARY in RB2.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply RB2 with (h := h2) (LB := LB2) (LF := (FB, 128) :: LF) (dX := mpd_z (C + 32)) (B := p3) (ibs := ibs3) (lo := lo) (d := 28);
        cbn [mpd_z md_addr md_own md_p md_n];
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?LENI3; rewrite ?HT2;
        first [ exact HHd | exact HK1 | exact MEd | exact HIB3 | exact STlod | exact LOS | exact MId | exact TPV | reflexivity
              | lazymatch goal with
                | |- LNull <> LStatic => discriminate
                | |- mpd_writableA _ _ _ _ _ _ =>
                    split; [cbn [md_addr mpd_z]; eapply client_wrange_block; [apply in_app_iff; left; exact CIN2| clear; lia| clear; lia]
                           | cbn [md_own mpd_z]; intros EO; discriminate EO]
                | |- client_range _ _ _ p3 _ =>
                    intros a Ha; destruct (CRK a ltac:(clear - Ha KP3 KL3; lia)) as [K|[K|K]]; [left; exact K| right; left; exact K| right; right];
                    (flat constr:(K) 3%nat; flclear K; intros b Hb Rb); exists b; split; [| exact Rb];
                    apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; apply SUB2; exact Hb| right; eapply fdata_incl; [| exact Hb]; intros fb Hfb; right; exact Hfb]
                | |- LNull = LHeap -> _ => intros EO; discriminate EO
                | |- aobj _ _ _ _ (C + 32) 16 => eapply aobj_sub; [exact OCd| clear; lia| clear; lia]
                | |- aobj _ _ _ _ p3 _ => eapply aobj_sub; [exact OKEYd| clear - KP3; lia| clear - KL3; lia]
                | |- havol _ _ _ _ + _ <= AVOL_MAX =>
                    pose proof (MPI_RB_PHI_mono (bv_unsigned lenw3) LEN ltac:(clear - KP3 KL3; lia)) as MONO; unfold RSA_PP_PHI in BUD; clear - BUD MONO VOL2; lia
                | |- uw_obj _ _ _ _ => right; clear; lia
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold RSA_PP_FR in BUDF; clear - BUDF HFR2; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- _ = Z_to_bv 64 _ => rewrite ?Z_to_bv_bv_unsigned; reflexivity
                | |- _ => clear - SP1 SP1M SLO NEEDR TOP KP3 KL3 K0 KB DKC DKS LRW3 C0 CB; first [lia | Z.div_mod_to_equations; lia]
                end
              | match goal with |- ?g => idtac "CALL2-PRE-LEFT:" g end ]. }
    cbv beta. intros ms6 mo6 (mo1 & [HK1 MF1] & PO).
    destruct PO as (e0 & e1 & e2 & ea1 & ea2 & ea3 & ea4 & ea5 & ea6 & ea7 & e3 & e4 & e5 & e6 & m3 & mo3 & h3 & LB3 & dE & rv3
                    & E6 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & RV3 & RV30 & FRS3).
    injection E6 as Ems Emo. subst ms6 mo6.
    replace (ret_pc (Z_to_bv 64 0xb2b48)) with (Z_to_bv 64 0xb2b48 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    pose proof HS3 as HS3raw. rewrite HT2 in HT3. rewrite HS2 in HS3, HP3. rewrite HF2 in HF3.
    unfold mpd_keep in HP3, FRS3. cbn [mpd_z md_own] in HP3, FRS3.
    assert (HCSh3 : forall x, CS x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; apply HCSh2; exact Hx).
    pose proof (fresh_apart_relist_rp R HIA h3 LB LB3 LF m3 FB 128 FRSH HH3) as FRSH3.
    flat constr:(OUT3) 5%nat. flclear OUT3. intros AE3 NST3 O1' O2' O3'. cbn [mpd_z md_addr] in AE3.
    assert (SUB3 : forall b, In b LB2 -> In b LB3) by (intros b Hb; apply O2'; [exact Hb| cbn; intros []]).
    assert (HP3' : presA asegs R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(C + 32, C + 32 + 16)] mc' m3).
    { eapply presA_weaken; [exact HP3| exact SUB2| intros b' Hb; right; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRESa3 : presW asegs R HIA h2 LB LF (bv_unsigned sp) (arl_stklo R) [(C, C + 232)] m m3).
    { flat constr:(PRESd) 4%nat. flclear PRESd. intros P0 C1 C2 C3. split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [exact P0|]. rewrite HS2.
      eapply presA_weaken; [exact HP3'| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia|].
      intros x Hx. cbn [outside] in Hx |- *. split; [clear - Hx; lia| exact I]. }
    pose proof (presW_hmono R HIA h2 h3 LB LF _ _ _ m _ PRESa3 HCS3 HS3raw) as PRESa3h.
    pose proof (presW_init_at R HIA h3 _ _ LB3 LF m3 (bv_unsigned sp) (arl_stklo R) [] h3 HH3
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) ltac:(intros x Hx; exact Hx) eq_refl ltac:(clear; lia)) as PRESb3.
    assert (DJX3 : forall A k, (A + k <= C \/ C + 232 <= A) -> disjoint_from [(C + 32, C + 32 + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    assert (CFB2 : crange (hcs asegs R HIA h2) FB 128) by (eapply crange_mono; [exact HCSh2| exact CFB]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h2) h2 LB2 LF mc' FB 128 lo HHd eq_refl FRSH2 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & _ & INHd & INDd & _ & _ & _ & _ & _ & _). change (128 - 40) with 88 in INDd.
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h2) LB2 ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(C + 32, C + 32 + 16)] mc' m3 FB _ CSOK2) in FSHXd;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB2| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP3 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc' m3 FB _ HP3) in FHDd;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INHd| clear; lia| clear; lia] | apply DJX3; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in PSLd;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INDd| clear; lia| clear; lia] | apply DJX3; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in LSLd;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [exact INDd| clear; lia| clear; lia] | apply DJX3; cbn [cells_size csize Nat.add]; clear - APC; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in SAVEd; [| apply client_range_stack; clear - SP1; lia| apply DJX3; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in SLOTd; [| apply client_range_stack; clear; lia| apply DJX3; cbn [cells_size csize Nat.add]; clear - STKC SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in ST16d; [| clear; lia| apply DJX3; clear - STKC SLO NEEDR SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc' m3 _ _ HP3) in SThid; [| clear; lia| apply DJX3; clear - STKC SLO NEEDR SP1; lia].
    (* [comment removed for export] *)
    assert (EK : forall b, In b (mpd_blk dE) -> fresh_apart R LB2 ((FB, 128) :: LF) (fst b) (snd b) /\ 0 < snd b).
    { intros [B k] Hb. destruct (FRS3 _ Hb) as [[]|FRE]. split; [exact FRE|]. cbn [snd].
      unfold mpd_blk in Hb. destruct (md_own dE) eqn:EO; try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as <- <-.
      flat constr:((proj1 MX3)) 6%nat. intros _ _ _ _ _ OW. rewrite EO in OW. flat constr:(OW) 2%nat. flclear OW. intros N1 _. clear - N1. lia. }
    assert (RAT3 : rsa_at asegs m3 LB3 C (mkRSA lenv dN dE)).
    { change lenv with (r_len (mkRSA lenv dN (mpd_z (C + 32)))) at 1. change dN with (r_N (mkRSA lenv dN (mpd_z (C + 32)))) at 1.
      eapply (rsa_at_importE asegs L mc' m3 LB2 LB3 (LB2 ++ fdata ((FB, 128) :: LF)) sp1 C (mkRSA lenv dN (mpd_z (C + 32))) dE);
        cbn [r_N r_E r_len];
        [exact RATd| reflexivity| exact MX3| split; [exact AE3| split; [exact NST3| split; [exact O1'| split; [exact O2'| exact O3']]]]
        | exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP3)| exact MId| exact MI3| apply in_app_iff; left; exact CIN2| | | |].
      - intros EO. apply in_app_iff. left. flat constr:(MNd) 6%nat. intros _ _ _ _ _ OW. rewrite EO in OW. exact (proj1 (proj2 OW)).
      - intros EO. exact (rsa_limb_apart asegs mc' LB2 ((FB, 128) :: LF) C _ (md_p dN, 4 * md_n dN) RATd BAd
                            ltac:(unfold rsa_limb_blocks, mpd_blk; cbn [r_N r_E]; rewrite EO; left; reflexivity)).
      - intros EO. destruct (EK (md_p dE, 4 * md_n dE) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [FRE KE]. cbn [fst snd] in FRE, KE.
        eapply (fresh_apart_ne R LB2 _ _ _ C 232); [exact FRE| exact CIN2| exact KE| clear; lia].
      - intros EN EO. destruct (EK (md_p dE, 4 * md_n dE) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [FRE KE]. cbn [fst snd] in FRE, KE.
        flat constr:(MNd) 6%nat. intros _ _ _ _ _ OW. rewrite EN in OW. flat constr:(OW) 3%nat. flclear OW. intros N1 NIN _.
        intros EQP. eapply (fresh_apart_ne R LB2 _ _ _ (md_p dN) (4 * md_n dN)); [exact FRE| exact NIN| exact KE| clear - N1; lia| symmetry; exact EQP]. }
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { assert (SS3m : sshad asegs AL m3 slo (bv_unsigned sp)).
      { eapply presA_sshad; [exact (proj1 PRESa3h)| exact SSH| exact SSLO|]. rewrite HS3. clear - TOP HTOP; lia. }
      eapply seg_C with (h3 := h3) (LBa := LB) (LB3 := LB3) (m0 := m) (WA := [(C, C + 232)]) (r3 := mkRSA lenv dN dE) (rv := rv3) (p3 := p3) (lenw := lenw3)
                        (slo := slo);
        cbn [r_N r_E r_len];
        first [ exact HH3 | exact HCSh3 | exact HT3 | exact HS3 | exact FRSH3 | exact PRESa3h | exact PRESb3 | exact RAT3 | exact RV3 | exact SGNN
              | exact SS3m | exact SSLO | exact SSHI
              | eassumption | reflexivity
              | (intros b Hb; apply SUB3; apply SUB2; exact Hb)
              | (intros E0; exact (proj1 (RV30 E0)))
              | (clear - KP3 K0; lia) | (clear - KL3 KB; lia)
              | match goal with |- ?g => idtac "SEGC-PRE-LEFT:" g end ]. }
    cbv beta. intros ms7 EQ.
    destruct EQ as (h7 & E7cs & E7top & E7stk & E7flag & E7vol & E7fr & HK7 & EQ).
    assert (VOL3 : havol asegs R HIA h3 <= havol asegs R HIA h + 2 * MPI_RB_PHI LEN).
    { pose proof (MPI_RB_PHI_mono (bv_unsigned lenw3) LEN ltac:(clear - KP3 KL3; lia)) as MONO. pose proof HV3 as HV3'. rewrite LENI3 in HV3'. clear - HV3' MONO VOL2. lia. }
    eapply (aevtA_KF_swap h3 h7 mo0); [exact HK7|].
    eapply rp_fin with (hq := h7) (hp := h3) (LBq := LB3) (WA := [(C, C + 232)]) (rq := mkRSA lenv dN dE);
      rewrite ?E7cs, ?E7top, ?E7stk, ?E7flag, ?E7vol, ?E7fr;
      first [ exact EQ | exact HCSh3 | exact HT3 | exact HS3 | exact HF3 | exact FRSH | exact FRSH3 | exact CFB | exact AP | reflexivity
            | (intros x Hx; exact Hx)
            | (unfold RSA_PP_PHI; exact VOL3) | (unfold RSA_PP_FR; clear - HFR3 HFR2; lia)
            | (intros b Hb; apply SUB3; apply SUB2; exact Hb)
            | (intros b Hb; unfold rsa_limb_blocks; cbn [r_N r_E]; destruct (O1' b Hb) as [K|K]; [destruct (O1 b K) as [K'|K']; [left; exact K'| right; apply in_or_app; left; exact K']| right; apply in_or_app; right; exact K])
            | (intros b Hb; unfold rsa_limb_blocks in Hb; cbn [r_N r_E] in Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (proj2 (L3N b Hb))|];
               (flat constr:((EK b Hb)) 2%nat; intros FRE KE); destruct b as [B k]; cbn [fst snd] in FRE, KE; intros HIn; exact (fresh_apart_notin R LB2 _ B k FRE KE (SUB2 _ HIn)))
            | (intros b Hb; unfold rsa_limb_blocks in Hb; cbn [r_N r_E] in Hb; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (proj1 (L3N b Hb))|];
               (flat constr:((EK b Hb)) 2%nat; intros FRE _); eapply fresh_apart_frames_mono; [eapply fresh_apart_blocks_mono; [exact FRE| exact SUB2]| intros b' Hb'; eapply fdata_incl; [| exact Hb']; intros fb Hfb; right; exact Hfb])
            | eassumption
            | match goal with |- ?g => idtac "FINC-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  Theorem A_rsa_parse_pubkey_spec_s :
    asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_RP -> mpi_size_stmtA asegs AL A_MPI_SIZE_RP ->
    rsa_complete_stmtA asegs R HIA A_RSA_COMPLETE_RP -> rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY_RP ->
    mpi_read_binary_stmtA_r asegs R HIA A_MPI_READ_BINARY -> rsa_parse_pubkey_stmtA asegs R HIA A_RSA_PARSE_PUBKEY
(* [comment removed for export] *).
  Proof.
    intros GT MSZ RC CK RB. unfold rsa_parse_pubkey_stmtA. intros until slo.
    intros HH HK LFB RAT HKY K0 KB CRK DKC DKS ST LOS SLO SLOS TOP SPA TPV SSH SSLO SSHI MI RAE OKEY BUD BUDF C24H -> -> ->.
    eapply rp_main; eassumption.
  Qed.
End WalkRP.

Theorem A_rsa_parse_pubkey_spec : forall (R : art_layout) (HIA : artA asegs R), asan_img_ok (arl_AL R) ->
    arl_uar_got R = A_UAR_GOT_RP -> arl_smalloc R 1 = A_SMALLOC_1_RP -> 0 <= arl_need_smalloc R -> 0 <= arl_need_rt R ->
    asn1_get_tag_stmtA asegs (arl_AL R) A_ASN1_GET_TAG_RP -> mpi_size_stmtA asegs (arl_AL R) A_MPI_SIZE_RP ->
    rsa_complete_stmtA asegs R HIA A_RSA_COMPLETE_RP -> rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY_RP ->
    mpi_read_binary_stmtA_r asegs R HIA A_MPI_READ_BINARY -> rsa_parse_pubkey_stmtA asegs R HIA A_RSA_PARSE_PUBKEY
(* [comment removed for export] *).
Proof. intros. apply A_rsa_parse_pubkey_spec_s; assumption. Qed.

(* [comment removed for export] *)
