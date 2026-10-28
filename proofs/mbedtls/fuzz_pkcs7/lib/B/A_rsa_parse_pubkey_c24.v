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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_read_binary_stmt_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_rsa_parse_pubkey.
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
Ltac2 gd_tbl_A_rsa_parse_pubkey_c24 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.w24"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_read_binary.chars_to_limbs"; "Stdlib.ZArith.BinInt.Z.div"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.RSA_PP_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_limb_blocks"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.C24_RSA_PP"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "rsa_parse_pubkey_postA_c"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "WalkRP.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_RSA_PARSE_PUBKEY"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "WalkRP.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.A_MPI_READ_BINARY"; "WalkRP.Call.EPIQ"; "WalkRP.Call.CALLQ"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.wcover"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.mkRSA"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_tag_stmt.asn1_get_tag_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_ASN1_GET_TAG_RP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.mpi_size_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_MPI_SIZE_RP"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_complete.rsa_complete_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_RSA_COMPLETE_RP"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_check_pubkey.rsa_check_pubkey_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_RSA_CHECK_PUBKEY_RP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt_c24.mpi_read_binary_stmtA_r_c"; "rsa_parse_pubkey_stmtA_c"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_UAR_GOT_RP"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey.A_SMALLOC_1_RP"].


(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L16587185911.6L17388578174.6L34772376590.7L7259787017.6 L7261736713.6 00000=00I00`00a00bS3LEN2lN2N01HS3LEN2lN1H1ES3LEN2lN1H2RG1E1D2N02NESS". (* [comment removed for export] *)
Lemma w24_one : forall LEN lN, 0 <= lN -> lN + 4 <= LEN -> w24 (4 * chars_to_limbs lN) <= LEN / 5889.
Proof.
  intros LEN lN N0 H. pose proof (w24_range (4 * chars_to_limbs lN)) as RG.
  destruct (Z.eq_dec (w24 (4 * chars_to_limbs lN)) 1) as [E|NE].
  - apply w24_ctl in E.
    assert (D : 1 <= LEN / 5889) by (apply Z.div_le_lower_bound; lia). lia.
  - assert (D : 0 <= LEN / 5889) by (apply Z.div_pos; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L16587185911.10L17382497993.11L42689759154.11L42689759154.12L42689759154.13L56662444218.12L7261713598.11 L7261713725.12 L7261736713.10 00000C00Y01801`02;02N02O02P02QS3LEN2lN2lE2N02E01HS3LEN2lN2lE2E01H2H02N0S3LEN2lN2lE2N02E01H2RN2RE2NN2NES3LEN2lN2lE2E01H2RE2EN2NE2H02N02RN2NN2EES3LEN2lN2lE1H2EN2EE2H02H11DS3LEN2lN2lE1H2H02H1SSS". (* [comment removed for export] *)
Lemma w24_two : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "PLEN,$0.PlN,$0.PlE,$0.P,(1.=R2.)P,(1.=R2.)P,(1.(2.(2.R4.R3.)+6.)R5.)(1.(2.(3.(4.+4.(5.R5.)))(3.(4.+4.(5.R4.))))(6.R6.+1701.))")
(* [comment removed for export] *).
Proof.
  intros LEN lN lE N0 E0 H. pose proof (w24_range (4 * chars_to_limbs lN)) as RN. pose proof (w24_range (4 * chars_to_limbs lE)) as RE.
  destruct (Z.eq_dec (w24 (4 * chars_to_limbs lN)) 1) as [EN|NN]; destruct (Z.eq_dec (w24 (4 * chars_to_limbs lE)) 1) as [EE|NE].
  - pose proof (w24_ctl _ EN). pose proof (w24_ctl _ EE). assert (D : 2 <= LEN / 5889) by (apply Z.div_le_lower_bound; lia). lia.
  - pose proof (w24_ctl _ EN). assert (D : 1 <= LEN / 5889) by (apply Z.div_le_lower_bound; lia). lia.
  - pose proof (w24_ctl _ EE). assert (D : 1 <= LEN / 5889) by (apply Z.div_le_lower_bound; lia). lia.
  - assert (D : 0 <= LEN / 5889) by (apply Z.div_pos; lia). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition rsa_parse_pubkey_postA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (C LEN lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Lc,$7.(8.(9.&40.)Lt0,(9.&40.)(8.(9.&40.)Lt1,(9.&40.)(8.(9.&40.)Lt2,(9.&40.)(8.(9.&40.)La0,(9.&40.)(8.(9.&40.)La1,(9.&40.)(8.(9.&40.)La2,(9.&40.)(8.(9.&40.)La3,(9.&40.)(8.(9.&40.)La4,(9.&40.)(8.(9.&40.)La5,(9.&40.)(8.(9.&40.)La6,(9.&40.)(8.(9.&40.)La7,(9.&40.)(8.(9.&40.)Lt3,(9.&40.)(8.(9.&40.)Lt4,(9.&40.)(8.(9.&40.)Lt5,(9.&40.)(8.(9.&40.)Lt6,(9.&40.)(8.P,(9.&40.)(:.(9.&8.))Lm',P,(9.&40.)(:.(9.&8.))(8.$;.Lmo',$;.(8.(<.O1=.O1<.O1;.)Lh',(<.O1=.O1<.O1;.)(8.(=.$>.)LLB',(=.$>.)(8.$?.Lr',$?.(10.(11.$7.R15.(12.(13.(14.O17.O16.O15.O14.R14.R13.R12.O13.O12.R11.R10.R?.R>.R=.R<.R;.R:.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R9.R8.R7.R6.)O7.(15.O17.)O6.(16.(9.&40.))R5.(17.O1=.))R4.))(10.(18.O1=.R5.)(10.(19.O1=.R5.O3.(1:.&40.O16.))(10.(1;.O1.R4.)(10.(1<.O1=.O1<.O19.O18.(1:.&40.O16.)(1=.O1<.)(1>.O1=.O1<.O1;.O1:.)(1?.(20.$0.$0.)(21.$0.$0.O5.(2.O5.$22.))(23.(20.$0.$0.)))O2.R5.)(10.(11.$0.(24.O1=.O1<.O1;.R3.)(24.O1=.O1<.O1;.O1:.))(10.(11.$0.(1>.O1=.O1<.O1;.R3.)(1>.O1=.O1<.O1;.O1:.))(10.(11.$0.(25.O1=.O1<.O1;.R3.)(25.O1=.O1<.O1;.O1:.))(10.(26.O1=.O1<.O1;.R3.R4.)(10.Px,$0.P,(27.O1=.O1<.O1;.O1:.R1.)(27.O1=.O1<.O1;.R5.R2.)(10.(1.(28.O1=.O1<.O1;.R3.)(2.(28.O1=.O1<.O1;.O1:.)(29.O4.)))(10.(1.(2:.O1=.O1<.O1;.R3.)(2.(2:.O1=.O1<.O1;.O1:.)$2;.))(10.(2<.O1=.O1<.O1;.R3.R2.O18.R5.)(10.(2=.O1=.R5.R2.O5.R1.)(10.Pb,$>.P,(2>.$>.R1.R3.)(2?.(2>.$>.R2.O19.)(2>.$>.R2.(30.R3.)))(10.Pb,$>.P,(2>.$>.R1.O19.)(2>.$>.R2.R4.)(10.Pb,$>.P,(2>.$>.R1.(30.R2.))(31.(2>.$>.R2.O19.))(10.Pb,$>.P,(2>.$>.R1.(30.R2.))(32.O1<.O19.O18.(33.$0.$0.R2.)(34.$0.$0.R2.))(1.(35.R2.)(2.(35.O19.)(6.O4.+1701.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Definition rsa_parse_pubkey_stmtA_c (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop :=
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
    aevtS segs (rsa_parse_pubkey_postA_c segs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                  C (Z.of_nat (length kbs)) lo m mo)
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)) mo)
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)





(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

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
  Hypothesis C24H : cnt24 LB + C24_RSA_PP <= C24MAX.     (* [comment removed for export] *)
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
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Lms,$50.(8.$0.LFB,$0.(8.$0.Lsp1,$0.(8.(<.$51.VR,VHIA,)Lh1,(<.$51.VR,VHIA,)(8.P,(9.&40.)(:.(9.&8.))Lm1,P,(9.&40.)(:.(9.&8.))(8.(9.&40.)Lt0,(9.&40.)(8.(9.&40.)Lt1,(9.&40.)(8.(9.&40.)Lt2,(9.&40.)(8.(9.&40.)La0,(9.&40.)(8.(9.&40.)La1,(9.&40.)(8.(9.&40.)La2,(9.&40.)(8.(9.&40.)La3,(9.&40.)(8.(9.&40.)La4,(9.&40.)(8.(9.&40.)La5,(9.&40.)(8.(9.&40.)La6,(9.&40.)(8.(9.&40.)La7,(9.&40.)(8.(9.&40.)Lt3,(9.&40.)(8.(9.&40.)Lt4,(9.&40.)(8.(9.&40.)Lt5,(9.&40.)(8.(9.&40.)Lt6,(9.&40.)(8.(9.&40.)Lw0,(9.&40.)(8.(9.&40.)Lw1,(9.&40.)(8.(9.&40.)Lw2,(9.&40.)(8.(9.&40.)Llenj,(9.&40.)(10.(11.$50.R18.(13.(14.(46.&40.+;2958.)(46.&40.R16.)Vgp,Vtp,R13.R12.R11.Vsp,(46.&40.R16.)R10.R?.R>.R=.R<.R;.R:.R9.(46.&40.R17.)(46.&40.VC,)(46.&40.(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))(46.&40.(2.R17.+20.))(46.&40.(2.R17.+40.))Vs7,(46.&40.(2.(52.R17.+3.)(53.(49.VR,))))(46.&40.R17.)(46.&40.(53.(49.VR,)))Vs11,R8.R7.R6.R5.)VF,(46.&40.+;2:28.)Vfc,(16.(9.&40.))R14.(17.$51.)))(10.(10.(1.(42.(1:.&40.Vsp,)+90.)R16.)(1.R16.(42.(1:.&40.Vsp,)+80.)))(10.(11.$0.(45.R16.+20.)=)(10.(2<.$51.VR,VHIA,R15.VLB,(1?.(20.$0.$0.)(21.$0.$0.R17.+80.)VLF,)R14.)(10.(11.P,$0.Sp(27.$51.VR,VHIA,R15.)(27.$51.VR,VHIA,Vh,))(10.(11.$0.(24.$51.VR,VHIA,R15.)(24.$51.VR,VHIA,Vh,))(10.(11.$0.(1>.$51.VR,VHIA,R15.)(1>.$51.VR,VHIA,Vh,))(10.(11.$0.(25.$51.VR,VHIA,R15.)(25.$51.VR,VHIA,Vh,))(10.(11.$0.(28.$51.VR,VHIA,R15.)(28.$51.VR,VHIA,Vh,))(10.(11.$0.(2:.$51.VR,VHIA,R15.)(2:.$51.VR,VHIA,Vh,))(10.Pmo,$;.(54.(26.$51.VR,VHIA,R16.R1.)(26.$51.VR,VHIA,Vh,R1.))(10.(11.$0.(45.R17.+40.)=)(10.(32.VR,VLB,VLF,R17.+80.)(10.(55.$51.R14.R17.(1?.$56.(57.R4.)(1?.$56.(57.R3.)(1?.$56.(57.R2.)(23.$56.)))))(10.(55.$51.R14.(2.R17.+20.)(1?.$56.(57.(46.&40.VKEY,))(23.$56.)))(10.(55.$51.R14.(2.R17.+40.)(1?.$56.(57.R1.)(23.$56.)))(10.(55.$51.R14.(2.(52.R17.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))(10.(55.$51.R14.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))(10.(55.$51.R14.(2.R16.+18.)(1?.$56.(57.(46.&40.R17.))(23.$56.)))(10.(19.$51.R14.R16.(2.R16.+18.))(10.(19.$51.R14.(2.R16.+20.)(2.(1:.&40.Vsp,)-60.))(10.(19.$51.R14.Vlo,R16.)(10.(18.$51.R14.)(59.$51.VR,VHIA,Vh,VLB,VLF,(1:.&40.Vsp,)(1=.VR,)(23.$5:.)Vm,R14.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 kbs; try lx_pin1 mo0.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01:0@D18607476203.109D2457697676.139 D29569067328.139D32458983511.139D32604263317.140D3375410824.138 D45716866873.138D50254960491.110D558665111.79   D62009822325.79 D62011770190.140D6395731754.110 D68407129291.138D6911780558.138 L10330779775.1  L10646859417.10 L10989370580.7  L12595714138.78 L13424450160.124L15629616632.10 L19546883925.124L19980016842.10 L2275137097.0   L24131365019.119L25233394630.3  L27188209011.143L29738741675.1  L32463525127.1  L33473079733.79 L33483560980.11 L33485826452.1  L38996969702.77 L3983061409.0   L40278113038.147L43061657906.75 L47230721790.119L48117620902.120L48117620911.69 L55351494680.11 L57355539152.120L58790154276.10 L59308677456.12 L59922446343.1  L60534120280.1  L62018535662.1  L6395777846.134 L6912107244.119 L7040749983.79  L7422344154.133 L9356559645.11  Q10533598597.81 Q10592386206.144Q1530342990.110 Q23937998252.81 Q24131365019.145Q24137657765.143Q30223088059.144Q32440833928.143Q35653441506.70 Q40271359350.110Q47241206720.81 Q48117620904.144Q48132302231.143Q56531220660.144Q59310664043.143Q59310664043.81 Q59321150548.144Q60109315147.70 Q6192914196.108 Q62012212072.110Q62022254708.81 Q6897428434.143 Q6912107244.145 Q9356560156.91  00000100200H00^01=01>01T01U01h02502M02d02e03;03@03A03[04B04b04c05C05[05\05g06306N06R06V06W06X06Y06h06i07G07i08708Y09;09K09L09b09l0:00:50:80:R0:]0;80;N0<90<F0<Q0<d0=@0=K0=V0=a0=b0>E0>U0>c0?E0?g0?h0?i0?j0?k0@@0@L0@V0@`0@k0A60AJFFS2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H152FBS1R3HIA2LF2sp3LFB3sp13H152h12FBFS2LF2sp3LFB3sp13H152FBFS1R3HIA1h2LF2sp3LFBS1R2LF2sp3LFBS1R2LF2sp3LFB3sp13H152FBS2LF2sp3LFB3sp13H133H15FS2LF2sp3LFB3sp13H152FBS3sp1SS1R3NS12sp2lo4SLOS3sp13SP1S2LF2sp3SPA3LFB3SPR3sp13H113H123H133H15S2LF2sp3LFB3SPR3sp13H152FB2F02F8SS2LF2sp3LFB3SPR3sp13H152FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1SS2LF3LFB2FBS2sp3sp13SP1S2LF2sp3LFB3sp13H152FB1c2HcS2FBS2FBFFFS2LF2sp3kbs3LFBSS2LF2sp3KEY3kbs3LFB3sp13H152FBS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3SPRS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R3ACV2FB2F02F1FS1R2sp2lo4SLOS3sp13SP1S2FB2Kb2F0S2spS3sp1S1RS2LF2sp3LFB3sp13H133H152FBS2LF3LFB2FBS2LF2sp3LFB3SPR3sp13H113H15S2LF2sp3LFB3sp13H152FBS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp13H13S1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS1R3HIA1h2LF2sp3kbs2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS1R2LF3kbs2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp13H143H15". (* [comment removed for export] *)
  #[using="LFB TPV SPA TOP SLOS SLO LOS NEEDR NS1 SM1 UARG IMG K0 KB C24H"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)P,(2<.$51.VR,VHIA,Vh,VLB,VLF,Vm,)P,(19.$51.Vm,Vlo,(1:.&40.Vsp,))P,(18.$51.Vm,)(5;.$51.(49.VR,)(27.$51.VR,VHIA,Vh,)$5<.(13.(14.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(46.&40.VC,)(46.&40.VKEY,)(46.&40.(3<.(38.(9.&8.)Vkbs,)))R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(46.&40.$5=.)Vfc,(16.(9.&40.))Vm,(17.$51.)))")
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
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Lms,$50.(8.P,(9.&40.)(:.(9.&8.))Lm',P,(9.&40.)(:.(9.&8.))(8.(<.$51.VR,VHIA,)Lh4,(<.$51.VR,VHIA,)(8.(9.&40.)Lt0,(9.&40.)(8.(9.&40.)Lt1,(9.&40.)(8.(9.&40.)Lt2,(9.&40.)(8.(9.&40.)La0,(9.&40.)(8.(9.&40.)La1,(9.&40.)(8.(9.&40.)La2,(9.&40.)(8.(9.&40.)La3,(9.&40.)(8.(9.&40.)La4,(9.&40.)(8.(9.&40.)La5,(9.&40.)(8.(9.&40.)La6,(9.&40.)(8.(9.&40.)La7,(9.&40.)(8.(9.&40.)Lt3,(9.&40.)(8.(9.&40.)Lt4,(9.&40.)(8.(9.&40.)Lt5,(9.&40.)(8.(9.&40.)Lt6,(9.&40.)(10.(11.$50.R12.(13.(14.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,R<.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(15.Vra,)Vfc,(16.(9.&40.))R11.(17.$51.)))(10.(18.$51.R11.)(10.(19.$51.R11.Vlo,(1:.&40.Vsp,))(10.(59.$51.VR,VHIA,O7.O6.VLF,(1:.&40.Vsp,)(1=.VR,)O2.O4.R11.)(10.(59.$51.VR,VHIA,O7.O5.VLF,(1:.&40.Vsp,)(1=.VR,)O1.O3.R11.)(10.(11.P,$0.Sp(27.$51.VR,VHIA,R10.)(27.$51.VR,VHIA,O7.))(10.(11.$0.(24.$51.VR,VHIA,R10.)(24.$51.VR,VHIA,O7.))(10.(11.$0.(1>.$51.VR,VHIA,R10.)(1>.$51.VR,VHIA,O7.))(10.(11.$0.(25.$51.VR,VHIA,R10.)(25.$51.VR,VHIA,O7.))(10.(11.$0.(28.$51.VR,VHIA,R10.)(28.$51.VR,VHIA,O7.))(10.(11.$0.(2:.$51.VR,VHIA,R10.)(2:.$51.VR,VHIA,O7.))(10.Pmo,$;.(54.(26.$51.VR,VHIA,R11.R1.)(26.$51.VR,VHIA,O7.R1.))(2<.$51.VR,VHIA,R10.O5.VLF,R11.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[local] Ltac lx_pins_hook ::= try lx_pin1 TPV; try lx_pin1 SPA; try lx_pin1 SLOS; try lx_pin1 KB; try lx_pin1 K0; try lx_pin1 KEY; try lx_pin1 C; try lx_pin1 mo0; try lx_pin1 m; try lx_pin1 s11; try lx_pin1 s10; try lx_pin1 s9; try lx_pin1 s8; try lx_pin1 s7; try lx_pin1 s6; try lx_pin1 s5; try lx_pin1 s4; try lx_pin1 s3; try lx_pin1 s2; try lx_pin1 s1; try lx_pin1 s0; try lx_pin1 ra; try lx_pin1 C24H; try lx_pin1 LB; try lx_pin1 NS1; try lx_pin1 SM1; try lx_pin1 UARG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01=0@D10777814275.118D2459793318.118 D32452690557.118D3385958441.117 D43016287773.119D45702252952.117D62011770188.119D68409162346.117D6897035375.117 L13312155929.147L13424450162.102L13424450175.106L16057223713.8  L19546883927.102L19546883930.106L2275137097.0   L24131365012.103L24131365017.99 L27188209011.122L30443457480.6  L35655538631.9  L38077847203.1  L39332637397.0  L39540652971.1  L39844638933.0  L42411609006.0  L47230721777.103L47230721788.99 L48117620903.104L48117620904.100L50790580594.6  L5162232212.2   L52237888267.158L54922193708.156L60098763854.3  L61387209310.157L61956910058.155L62018535662.1  L6912107235.103 L6912107246.99  L8247844460.152 L9356559676.11  P5152549648.152 Q10592386204.123Q10592386207.127Q21721340005.124Q21721340008.128Q22358563588.126Q24131365012.128Q24131365017.124Q24137657765.122Q24137657789.126Q30147450662.124Q30223088057.123Q30223088058.127Q30871588746.150Q31314676345.122Q34796740410.127Q4125667684.149 Q4279611329.151 Q48117620905.127Q48117620906.123Q48132302223.126Q48132302231.122Q52741535643.150Q5935758158.151 Q59668625896.128Q60382659730.128Q60382659743.124Q64133651577.150Q67397950268.123Q6897428426.126 Q6897428434.122 Q6912107235.128 Q6912107246.124 Q7917062807.128 Q7917062810.124 00000?00@00O00P00h01701H01I01X01l02F02`03?03T03i03j04504@04T04k05D05H05I05M05N05O05]05k06M06o07F07G08208_08i09V0:?0:B0:M0:X0:g0;R0;S0;^0;i0;j0;k0;l0<70<B0<M0<X0<Y0<d0<o0=?0=@0=A0=N0=[0>=0>_0?A0?c0@30@@0@A0@B0@C0@P0@Q0@\0@g0A20A=0AQ0AeS2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1FS1R3HIA2LF3LFB2h32FB3sp1S2LF3LFB2FB3sp1S1R2LF3LFB2FB3sp1FS2LF3LFB2FB3sp1S2LF3LFB2FB3sp11p2PBS2LF3LFB2FB3sp14SP1R2F82F0S2LF3LFB2FB3sp14SP1R2F82F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2LF3LFB2FB3sp12F82F0S2LF3LFB2FB3sp12F82F0SS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB3sp11c2HcS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1h2sp2lo3TOP5HTOP3S2spSS2FBSSS1R2LF3LFB3ALOS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2sp2lo3LOS3SLOFS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP12F02H7S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S1R2lo3LOSS1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp13SP14SP1R2F0S1R5NEEDR2LF2sp2lo3SLO3LFB2FB3sp14SP1R2F0S1RS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS2LF3LFB2FBS2LF3LFB2FBFFFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB1p2PBFFS2LF3LFB1p2PBS2LF3LFB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2LF3LFB2FB1p2PBS2LF3LFB1p2PBFFFS2LF3LFB1p2PBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  #[using="LFB TOP SLO LOS kbs NEEDR IMG"]
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Ph3,(<.$51.VR,VHIA,)PLBa,(=.$>.)PLBb,(=.$>.)Pm0,P,(9.&40.)(:.(9.&8.))Pm2x,P,(9.&40.)(:.(9.&8.))Pmm,P,(9.&40.)(:.(9.&8.))PWA,(=.$5:.)PWB,(=.$5:.)PFB,$0.Psp1,$0.Pxra,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Ps3v,(9.&40.)Ps4v,(9.&40.)Ps5v,(9.&40.)Ps6v,(9.&40.)Ps7v,(9.&40.)Ps11v,(9.&40.)Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)P,(2<.$51.VR,VHIA,R23.R21.(1?.(20.$0.$0.)(21.$0.$0.R1;.+80.)VLF,)R1>.)P,Px,$0.P,(27.$51.VR,VHIA,Vh,R1.)(27.$51.VR,VHIA,R26.R2.)P,(11.$0.(24.$51.VR,VHIA,R25.)(24.$51.VR,VHIA,Vh,))P,(11.$0.(1>.$51.VR,VHIA,R26.)(1>.$51.VR,VHIA,Vh,))P,(10.(1.(42.(1:.&40.Vsp,)+90.)R1>.)(1.R1>.(42.(1:.&40.Vsp,)+80.)))P,(11.$0.(45.R1?.+20.)=)P,(11.$0.(45.R21.+40.)=)P,(32.VR,R29.VLF,R22.+80.)P,(32.VR,R29.VLF,R23.+80.)P,(5>.(27.$51.VR,VHIA,Vh,)R24.+80.)P,PB,$0.Pj,$0.P,(2>.(20.$0.$0.)(21.$0.$0.R2.R1.)VLF,)(2?.(1.(2.R28.+80.)R3.)(1.(2.R3.R2.)R28.))P,Pb',$>.P,(2>.$>.R1.R2>.)(2>.$>.R2.R2>.)P,(55.$51.R2:.R27.(1?.$56.(57.R?.)(1?.$56.(57.R>.)(1?.$56.(57.R=.)(23.$56.)))))P,(55.$51.R2;.(2.(52.R28.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))P,(55.$51.R2<.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))P,(55.$51.R2=.(2.R29.+18.)(1?.$56.(57.(46.&40.R2:.))(23.$56.)))P,(19.$51.R2>.R2:.(2.R2:.+18.))P,(19.$51.R2?.(2.R2;.+20.)(2.(1:.&40.Vsp,)-60.))P,(19.$51.R30.Vlo,R2<.)P,(18.$51.R31.)P,(59.$51.VR,VHIA,R37.R36.VLF,(1:.&40.Vsp,)(1=.VR,)R31.R34.R32.)P,(59.$51.VR,VHIA,R38.R36.VLF,(1:.&40.Vsp,)(1=.VR,)R31.R34.R33.)(5;.$51.(49.VR,)(27.$51.VR,VHIA,R39.)(5?.R39.R38.R37.R36.R35.R33.R32.)(13.(14.R2?.(46.&40.R30.)Vgp,Vtp,R2>.R2=.R2<.Vsp,(46.&40.R30.)R2;.R2:.R29.R28.R27.R26.R25.R24.(46.&40.R31.)R1?.R1>.R1=.R1<.R1;.(46.&40.(2.(52.R31.+3.)(53.(49.VR,))))(46.&40.R31.)R1:.Vs11,R23.R22.R21.R20.)VF,(46.&40.+;2;<<.)Vfc,(16.(9.&40.))R34.(17.$51.)))")
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
      (XQ : mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Lms,$50.(8.P,(9.&40.)(:.(9.&8.))Lmm,P,(9.&40.)(:.(9.&8.))(8.(9.&40.)Lxra,(9.&40.)(8.(9.&40.)Lt0,(9.&40.)(8.(9.&40.)Lt1,(9.&40.)(8.(9.&40.)Lt2,(9.&40.)(8.(9.&40.)La0,(9.&40.)(8.(9.&40.)La1,(9.&40.)(8.(9.&40.)La2,(9.&40.)(8.(9.&40.)La3,(9.&40.)(8.(9.&40.)La4,(9.&40.)(8.(9.&40.)La5,(9.&40.)(8.(9.&40.)La6,(9.&40.)(8.(9.&40.)La7,(9.&40.)(8.(9.&40.)Lt3,(9.&40.)(8.(9.&40.)Lt4,(9.&40.)(8.(9.&40.)Lt5,(9.&40.)(8.(9.&40.)Lt6,(9.&40.)(8.(9.&40.)Ls3v,(9.&40.)(8.(9.&40.)Ls4v,(9.&40.)(8.(9.&40.)Ls5v,(9.&40.)(8.(9.&40.)Ls6v,(9.&40.)(8.(9.&40.)Ls7v,(9.&40.)(8.(9.&40.)Ls11v,(9.&40.)(10.(11.$50.R18.(13.(14.R16.(46.&40.O5.)Vgp,Vtp,R15.R14.R13.Vsp,(46.&40.O5.)R12.R11.R10.R?.R>.R=.R<.R;.(46.&40.O6.)R6.R5.R4.R3.R2.(46.&40.(2.(52.O6.+3.)(53.(49.VR,))))(46.&40.O6.)R1.Vs11,R:.R9.R8.R7.)VF,(46.&40.+;2;<<.)Vfc,(16.(9.&40.))R17.(17.$51.)))(10.(2<.$51.VR,VHIA,O<.O9.(1?.(20.$0.$0.)(21.$0.$0.O6.+80.)VLF,)R17.)(10.(55.$51.R17.O6.(1?.$56.(57.O4.)(1?.$56.(57.O3.)(1?.$56.(57.O2.)(23.$56.)))))(10.(55.$51.R17.(2.(52.O6.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))(10.(55.$51.R17.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))(10.(55.$51.R17.(2.O5.+18.)(1?.$56.(57.(46.&40.O6.))(23.$56.)))(10.(19.$51.R17.O5.(2.O5.+18.))(10.(19.$51.R17.(2.O5.+20.)(2.(1:.&40.Vsp,)-60.))(10.(19.$51.R17.Vlo,O5.)(10.(18.$51.R17.)(10.(59.$51.VR,VHIA,O;.O:.VLF,(1:.&40.Vsp,)(1=.VR,)O7.O8.R17.)A1.O1.R17.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition CALLQ (RA XA PLO : Z) (hq hp : HST asegs R HIA) (LBa LBq : list blk) (m0 : mem) (WA : list ivl) (FB sp1 : Z) (w0 w1 w2 : word)
      (XQ : mem -> Prop) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Lms,$50.(8.P,(9.&40.)(:.(9.&8.))Lmm,P,(9.&40.)(:.(9.&8.))(8.(9.&40.)Lt0,(9.&40.)(8.(9.&40.)Lt1,(9.&40.)(8.(9.&40.)Lt2,(9.&40.)(8.(9.&40.)La3,(9.&40.)(8.(9.&40.)La4,(9.&40.)(8.(9.&40.)La5,(9.&40.)(8.(9.&40.)La6,(9.&40.)(8.(9.&40.)La7,(9.&40.)(8.(9.&40.)Lt3,(9.&40.)(8.(9.&40.)Lt4,(9.&40.)(8.(9.&40.)Lt5,(9.&40.)(8.(9.&40.)Lt6,(9.&40.)(8.$0.Lp2,$0.(8.(9.&40.)Llenw,(9.&40.)(10.(11.$50.R10.(13.(14.(46.&40.O?.)(46.&40.O5.)Vgp,Vtp,R>.R=.R<.Vsp,(46.&40.O5.)(46.&40.O>.)(46.&40.R2.)R1.R;.R:.R9.R8.R7.(46.&40.O6.)(46.&40.VC,)(46.&40.(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))(46.&40.(2.O6.+20.))(46.&40.(2.O6.+40.))(46.&40.(2.VC,+10.))(46.&40.(2.(52.O6.+3.)(53.(49.VR,))))(46.&40.O6.)(46.&40.(53.(49.VR,)))Vs11,R6.R5.R4.R3.)VF,(46.&40.$60.)Vfc,(16.(9.&40.))R?.(17.$51.)))(10.(2<.$51.VR,VHIA,O<.O9.(1?.(20.$0.$0.)(21.$0.$0.O6.+80.)VLF,)R?.)(10.(55.$51.R?.O6.(1?.$56.(57.O4.)(1?.$56.(57.O3.)(1?.$56.(57.O2.)(23.$56.)))))(10.(55.$51.R?.(2.O6.+20.)(1?.$56.(57.(46.&40.R2.))(23.$56.)))(10.(55.$51.R?.(2.O6.+40.)(1?.$56.(57.R1.)(23.$56.)))(10.(55.$51.R?.(2.(52.O6.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))(10.(55.$51.R?.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))(10.(55.$51.R?.(2.O5.+18.)(1?.$56.(57.(46.&40.O6.))(23.$56.)))(10.(19.$51.R?.O5.(2.O5.+18.))(10.(19.$51.R?.(2.O5.+20.)(2.(1:.&40.Vsp,)-60.))(10.(19.$51.R?.Vlo,O5.)(10.(18.$51.R?.)(10.(59.$51.VR,VHIA,O;.O:.VLF,(1:.&40.Vsp,)(1=.VR,)O7.O8.R?.)(10.(3:.$51.R?.VKEY,Vkbs,)(10.(48.$51.(49.VR,)(27.$51.VR,VHIA,O<.)R?.VKEY,(3<.(38.(9.&8.)Vkbs,)))(10.(1.(2.VKEY,+2.)R2.)(10.(1.(2.R2.(1:.&40.R1.))(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))(10.(1.O=.R2.)A1.O1.R?.)))))))))))))))))))))))))))))))))")
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

  Lemma EPIQ_ex : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Phq,(<.$51.VR,VHIA,)Php,(<.$51.VR,VHIA,)PLBa,(=.$>.)PLBq,(=.$>.)Pm0,P,(9.&40.)(:.(9.&8.))PWA,(=.$5:.)PFB,$0.Psp1,$0.Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)PT,StPXQ,P,R1.P,P,(9.&40.)(:.(9.&8.))SpPms,$50.P,(61.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.Lmm,P,(9.&40.)(:.(9.&8.))(8.R4.Lt,R4.A2.R4.R1.R2.)R1.)(8.R4.Lt,R4.(61.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.A1.R4.R1.R3.))")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros (mm & xra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & s3v & s4v & s5v & s6v & s7v & s11v
                             & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & [t HX]).
    exists t. unfold EPIQ. exists mm, xra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, s3v, s4v, s5v, s6v, s7v, s11v.
    repeat (split; [assumption|]). exact HX.
  Qed.


  Local Ltac2 Set LiaOrc.tbl := fun () => "03R0@C23920765559.173C23922862675.151C60407910007.172C60410007123.150D10780387598.151D10782484778.173D16069757090.173D16071854214.151D2455419791.173 D2457516971.151 D32456773204.173D32458870384.151D46113380110.151D46115477290.173D56536395888.151D56538493012.173D5982099855.173 D5984197035.151 D68221095944.151D68223193132.173K34017150414.173K34019247594.151K34019247594.153K65868372942.173K65870470122.153L10912730231.1  L1107921052.165 L13340048728.1  L13511390815.22 L13513313310.28 L1384220064.165 L13951498865.3  L16720171459.143L17609328382.22 L17611537599.28 L19698471166.22 L19700476607.28 L21644325741.3  L21654730866.2  L22070304172.28 L2275137097.0   L24206288344.2  L24817214193.2  L2621559066.1   L27832436138.125L27832436139.148L27938633021.22 L27940753276.28 L29731203473.22 L29733262288.28 L31015320791.7  L31473906376.3  L33312312071.22 L33314451782.28 L34014826108.3  L34521824657.28 L3482443989.28  L3484572308.22  L35653441506.9  L38235734261.1  L39650474714.3  L41251426164.1  L41663468825.143L41663468825.165L42488948659.2  L47870616696.2  L48067958343.28 L48069962758.22 L48455046775.1  L49233373885.2  L49354241059.143L49858401057.0  L5021251703.1   L53527181501.2  L5491309809.2   L55180610054.22 L55182815303.28 L57387012359.22 L57389345606.28 L576250137.143  L576250137.165  L58786296421.22 L59308586248.2  L59308632045.10 L59427880762.143L59726336417.0  L60098763854.3  L60448817524.1  L6058464020.22  L6060730709.28  L62275882349.3  L63344940145.3  L64526681523.2  L65882689660.3  L66298372189.2  L66572625893.3  L66584664650.28 L66586861579.22 L66925227178.126L66925227178.149L68526664119.7  L8163705040.8   L8163714305.5   L881835912.0    L9080220944.4   L9356559676.11  O14785264606.148O14787361786.170O19173376225.173O19175473349.153O21228041722.170O21230138846.148O30010457231.151O30012554411.171O3076189820.170 O3078286936.148 O33647379806.151O33649476986.171O40095405918.151O40097503098.171O424351700.149  O426448880.171  O44938202843.149O44940300031.171O49699726460.170O49701823576.148O55209884805.149O55211981985.171O55516142064.171O55518239188.149O63649880056.153O63651977180.173O64471909102.171O64474006218.151O67168963243.171O67171060367.151O7437325788.173 O7439422968.151 O7439422968.153 P13947775218.170P13949872342.148P21647862485.149P21649959665.171P21656429038.171P21658526154.149P24827162710.151P24829259890.171P34019247594.151P39654189145.173P39656286333.153P42484919333.151P42487016449.171P47874275067.171P47876372191.149P49228642366.170P49230739482.148P53529750042.148P53531847230.170P5494959730.171 P5497056854.151 P62260666314.149P62262763502.171P63339218646.148P63341315826.170P64538971685.151P64541068801.171P66292560634.151P66294657758.171Q10592398491.168Q10592533181.151Q10594630297.173Q10598576410.125Q10598576411.148Q10598692432.146Q11133374175.151Q11135471355.173Q19561565648.126Q19561565648.149Q19561597648.125Q19561597649.148Q21765573510.173Q21767670690.151Q27942454161.151Q27944551349.173Q2803826605.151 Q2805923721.173 Q29720193674.168Q29722292289.146Q29775981542.151Q29778078658.173Q30220517308.173Q30222614424.151Q32435106995.173Q32437204119.151Q33228598872.148Q33228598873.125Q34667424921.173Q34669132443.168Q34669522109.151Q34671222864.146Q34671239194.126Q34671239194.149Q3477426724.151 Q3479523840.173 Q35333702489.126Q35333702489.149Q41412201211.173Q41414298335.151Q48118064779.151Q48120161967.173Q51218566552.151Q51220663740.173Q55202266689.146Q55208551562.168Q56530976407.151Q56533073587.173Q59321559671.151Q59323656787.173Q9356756743.128 Q9356888860.150 Q9633850158.148 Q9633850159.125 Q9634014255.126 Q9634014255.149 Q9644583048.151 Q9646680236.173 00000400800<00@00V00l01e02^02_02`03603L03b04804N04d04e04f05a06\07e07f08]09f0:]0:^0;^0;c0<60<I0<J0<K0=I0>B0?;0@40@m0@n0@o0AF0AG0AO0AP0AU0Ak0BA0C20Cc0D70DK0Dd0E00E?0EN0EO0Ef0F\0GR0Gj0Gn0Go0H30HI0H_0H`0Ha0IU0JI0JM0JN0KF0KG0KH0KI0KJ0L>0M20MA0MP0Mf0N<0NL0NR0O00O10O20O<0O@0PA0QN0QO0QP0QQ0QR0QS0Q^0Qj0R60RL0Rb0S;0S<0SQ0SR0Sa0TL0TM0TN0TO0TP0TQ0TR0TS0TT0TU0TV0TW0TX0TY0TZ0T[0T\0T]0T^0T_0T`0Ta0Tb0Tc0Td0Te0Tf0Tg0Th0Ti0Tj0Tk0Tl0Tm0U[0VI0VJ0VK0Vf0WA0Wo0X]0X^0ZA0[Z0\F0]20]`0^N0_<0_j0`X0aF0b40bb0c=0cX0dF0e40e`0fL0fc0g:0gI0gX0gg0h60hE0hT0hc0i20iR0j20jR0k20k`0lN0m40mZ0mj0n:0nI0nX0no0oF0oU0od0oe0of10510D10S10b11111@11O11^12112D12S12b13113@13f14L14[14j15915H15I15J15K15L15a16616H16Z16l17>17P17bS2FBS2FBS2FBS2FBS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3sp13SP13SPR4SP1R2F0S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3sp13SP13SPR4SP1R2F0FFS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1FFS1R3HIA1h2LF2sp3kbs3TOP3LFB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S1R3HIA1h2LF2sp3kbs3TOP3LFB2FB3sp12h13SP15Ehtop3SPR4SP1R2F0S2LF3KEY3kbs2lo3LFB2FB3sp13x283APK2p12Lw2LR4Hp1a2KE3x163x293x303x315POST0FS2LF3KEY2lo1l2KB3LFB2FB3sp13x143APK2x23x153x163x174POSTS2LF3KEY3kbs2lo3LFB2FB3sp13x283APK2p12Lw2LR4Hp1a2KE3x163x293x303x315POST0S2LF3KEY2lo1l2KB3LFB2FB3sp13x143APK2x23x153x163x174POSTFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p14Hp1a2p23Hp24Hp2aS3sp1S3KEY3kbs2KB2FB3sp1S3KEY3kbs2KB2FB3sp1FFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p12Lw2LR4Hp1a3HLwS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FFS3KEY3kbs2FB3sp12p13Hp1SS2sp3sp1FS3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S3KEY3kbs2FB3sp13APKS3KEY3kbs2FB3sp13APKS3KEY3kbs2p14Hp1a2p24Hp2aS2r23RR23KT2S3kbs2FB3sp12F0S3kbs2FB3sp12F0FS3KEY3kbs2FB3sp12p13Hp1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R3HIA1h2sp2lo3TOP4HTOPS2loFS2FBS2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1FFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S2FBFS2LF2sp3KEY3kbs2K02KB3LFB2FB3sp13SPR4SP1R2F02p13Hp14Hp1aSFFFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S3kbs2FB3sp12F0S3kbs2FB3sp12F0S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S3KEY3kbs2FB3sp1S1i2HiS3KEY3kbs2K02p13Hp12p24Hp2a2KNFSS1R2lo3LOSS2FBS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3DKS3ALO3ACP2F02F1S1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3DKS3ALO3ACP2F02F12p13Hp14Hp1aFFFFFS2r13RR12KTS3kbs2FB3sp1S3kbs2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S2LF2sp3kbs3LFB2FB3sp1S3KEY3kbs2p14Hp1a2p24Hp2aFS3KEY3kbs2p23Lw24HLw2SS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOFFS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOFS1R5NEEDR2LF2sp3KEY3kbs2lo3LOS3SLO3LFB2FB3sp13SP13x283DKS3ALO2F14FBLO2p14Hp1a3x163x293x303x315POST0S1R5NEEDR2LF2sp3KEY2lo1l2KB3LOS3SLO3LFB2FB3sp13SP13x143APK3DKS3ALO2F12x23x153x163x174POSTS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS2LF3kbs2lo3LFB2FB3sp14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP14FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB3ALO2F1S2LF2sp3kbs3LFB3sp13SP1S2LF2sp3kbs3LFB3sp13SP1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S2LF2sp3kbs3LFB2FB3sp13SPR2F02F8S1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP13ALOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP13ALOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1S1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP1S2LF3kbs3LFB3sp1S2LF3kbs3LFB3sp1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF2sp3kbs3LFB3sp13SP1S2LF2sp3kbs3LFB3sp13SP1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBFFS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs2lo3LFB3sp1S2LF3kbs2lo3LFB3sp1S2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3ALOS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBS2LF3kbs3LFB2FBFFFFS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB3sp14SP1RS2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0S2LF3kbs3LFB2FB2F0". (* [comment removed for export] *)
  Lemma seg_A : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "PFB,$0.Psp1,$0.Ph1,(<.$51.VR,VHIA,)Pm1,P,(9.&40.)(:.(9.&8.))Pxra,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Plenj,(9.&40.)P,(10.(1.(42.(1:.&40.Vsp,)+90.)R17.)(1.R17.(42.(1:.&40.Vsp,)+80.)))P,(11.$0.(45.R18.+20.)=)P,(2<.$51.VR,VHIA,R18.VLB,(1?.(20.$0.$0.)(21.$0.$0.R1:.+80.)VLF,)R17.)P,(11.P,$0.Sp(27.$51.VR,VHIA,R19.)(27.$51.VR,VHIA,Vh,))P,(11.$0.(24.$51.VR,VHIA,R1:.)(24.$51.VR,VHIA,Vh,))P,(11.$0.(1>.$51.VR,VHIA,R1;.)(1>.$51.VR,VHIA,Vh,))P,(11.$0.(45.R1>.+40.)=)P,(32.VR,VLB,VLF,R1?.+80.)P,(55.$51.R1=.R20.(1?.$56.(57.R<.)(1?.$56.(57.R;.)(1?.$56.(57.R:.)(23.$56.)))))P,(55.$51.R1>.(2.R21.+20.)(1?.$56.(57.(46.&40.VKEY,))(23.$56.)))P,(55.$51.R1?.(2.R22.+40.)(1?.$56.(57.R;.)(23.$56.)))P,(55.$51.R20.(2.(52.R23.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))P,(55.$51.R21.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))P,(55.$51.R22.(2.R24.+18.)(1?.$56.(57.(46.&40.R25.))(23.$56.)))P,(19.$51.R23.R25.(2.R25.+18.))P,(19.$51.R24.(2.R26.+20.)(2.(1:.&40.Vsp,)-60.))P,(19.$51.R25.Vlo,R27.)P,(18.$51.R26.)P,(59.$51.VR,VHIA,Vh,VLB,VLF,(1:.&40.Vsp,)(1=.VR,)(23.$5:.)Vm,R27.)P,(3:.$51.R28.VKEY,Vkbs,)P,(48.$51.(49.VR,)(27.$51.VR,VHIA,Vh,)R29.VKEY,(3<.(38.(9.&8.)Vkbs,)))P,(2?.(11.$0.(3<.(38.(9.&8.)Vkbs,))=)(2?.(1.(2.R2=.+80.)VKEY,)(1.(2.VKEY,(3<.(38.(9.&8.)Vkbs,)))R2=.)))P,(2?.(1.(2.VKEY,(3<.(38.(9.&8.)Vkbs,)))Vlo,)(1.(1:.&40.Vsp,)VKEY,))P,(18.$51.Vm,)P,(2=.$51.Vm,VLB,VC,(39.VC,))(5;.$51.(49.VR,)(27.$51.VR,VHIA,Vh,)Lms,$50.(2?.(61.R30.Vh,VLB,VLB,Vm,(23.$5:.)R32.R31.R1>.R1=.R1<.Lmm,P,(9.&40.)(:.(9.&8.))(2=.$51.R1.VLB,VC,(39.VC,))R1.)(62.+;2::<.(2.VC,+10.)(2.VKEY,+4.)R30.Vh,VLB,VLB,Vm,(23.$5:.)R32.R31.R1>.R1=.R1<.Lmm,P,(9.&40.)(:.(9.&8.))(2=.$51.R1.VLB,VC,(39.VC,))R1.))(13.(14.R2=.(46.&40.R30.)Vgp,Vtp,R2<.R2;.R2:.Vsp,(46.&40.R30.)R29.R28.R27.R26.R25.R24.R23.R22.(46.&40.R31.)(46.&40.VC,)(46.&40.(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))(46.&40.(2.R31.+20.))(46.&40.(2.R31.+40.))Vs7,(46.&40.(2.(52.R31.+3.)(53.(49.VR,))))(46.&40.R31.)(46.&40.(53.(49.VR,)))Vs11,R21.R20.R1?.R1>.)VF,(46.&40.+;2:28.)Vfc,(16.(9.&40.))R2>.(17.$51.)))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "04I0@C17025492443.192C23922862675.215C60410007123.216D10780387598.216D1310172651.194 D16071854214.216D2302662246.192 D2457516971.216 D27413640265.194D32312377831.194D32458870384.216D37764614195.192D43080244883.192D46113380110.216D56536395888.216D59521016234.192D5984197035.216 D60109196847.194D60109446735.192D66149944741.194D67928118627.216D68669309656.194K19417199362.215K20197146615.194K21212095580.192K34019247594.216K37211889074.192K40320258448.194K41580779312.192K54254745587.192K54254745587.194K55088519473.192K56742996226.215K65614493584.194K65870470122.216L10278198556.27 L10470256643.204L10912730231.1  L11266288813.9  L11269007652.4  L11377594986.2  L13176305223.2  L13340048728.1  L13513376638.27 L13951498865.3  L14405467828.2  L15445091466.182L15822417165.1  L15904255106.18 L16215250139.3  L1685717371.0   L17611600863.27 L19421690004.2  L19700409823.27 L20184474625.2  L21218866939.2  L21644325741.3  L21654730866.2  L21866712442.1  L2275137097.0   L23137366490.1  L24206288344.2  L24817214193.2  L2545017055.181 L25784868313.1  L2621559066.1   L27758563447.2  L27800688430.1  L27832436140.190L27940814876.27 L28604189903.3  L29311557968.153L29311558097.153L29428292188.18 L29733199024.27 L32027975233.0  L32675610705.18 L33314520614.27 L34014826108.3  L3482382261.27  L3482526763.18  L35653441506.9  L37224515140.2  L38146119331.3  L38235734261.1  L38350716672.3  L39650474714.3  L40324500070.2  L41251426164.1  L41409160545.3  L41582364055.4  L41663468825.181L41663468825.204L42488948659.2  L43445289383.1  L44163628344.204L44182274304.3  L46533908870.3  L47870616696.2  L48068024615.27 L48455046775.1  L49233373885.2  L5021251703.1   L52941874306.3  L53527181501.2  L54232767084.7  L54242110469.3  L54244916338.3  L54716365463.3  L5491309809.2   L55085943702.3  L55182884647.27 L56755282580.2  L56775193499.11 L57389278246.27 L576250137.181  L576250137.204  L58451400700.3  L59308586248.2  L59308628304.1  L59308632045.12 L59308873939.4  L60056205954.3  L60098763854.3  L60448817524.1  L6060664373.27  L61603606271.2  L62275882349.3  L62584254982.3  L63344940145.3  L63505931041.0  L64526681523.2  L64903376861.3  L65258828961.0  L65601858662.2  L65698399962.1  L65882689660.3  L66298372189.2  L66584597802.27 L66925227178.191L7049614941.2   L7738195705.2   L8122120014.3   L881835912.0    L9080220944.4   L9356559676.11  L9365803230.9   L9365812872.5   L9744944814.1   O14785264606.213O1478916974.192 O15410436215.192O15806046987.215O17025492443.192O19175473349.216O21230138846.213O29029543562.215O30010457231.215O3078286936.213 O33647379806.215O33934863603.192O35530008476.215O38903829125.215O40095405918.215O424351700.214  O44938202843.214O49701823576.213O50702732434.192O54941931932.215O55209884805.214O55518239188.214O56414299794.192O59625529265.192O61363827850.215O63649880056.216O64474006218.215O67171060367.215O7439422968.216 O8932501257.192 P11263960254.192P11387568333.215P13949872342.213P14399962227.194P16213722748.192P21212095580.192P21647862485.214P21658526154.214P24827162710.215P27752269830.194P38141074233.215P38338851482.215P39656286333.216P41419110342.192P42484919333.215P44186274970.215P47876372191.214P49230739482.213P52940256805.192P53529750042.213P54719981421.194P5497056854.215 P60050384933.192P61592333368.192P62260666314.214P63339218646.213P64538971685.215P66292560634.215P7750690063.192 P8134093492.192 Q10103930589.192Q10592398492.211Q10592533181.216Q10598576412.190Q10598691372.188Q10750552072.190Q11133374175.216Q11801279589.192Q11801586693.216Q13762724344.192Q14946898661.192Q15766564435.192Q15825002892.191Q16071854214.216Q17139219548.216Q19469071352.216Q19561565648.191Q19561597654.190Q19750898618.190Q21538057956.191Q21540267236.192Q21767670690.216Q23236331406.192Q24064611734.192Q25158727472.192Q25160678704.191Q27880293120.193Q2803826605.216 Q29720193677.211Q29722293309.188Q29775981542.216Q30222614424.216Q30802955094.189Q32312377831.194Q32437204119.216Q33228598879.190Q34669132444.211Q34669522109.216Q34671223852.188Q34671239194.191Q34964382778.192Q35333702489.191Q37527221250.216Q41414298335.216Q41602360616.192Q45248764730.192Q45629188794.191Q48117823211.192Q48118064779.216Q48360113622.192Q49698585326.190Q51218566552.216Q52590069023.191Q53647085228.193Q55202265661.188Q55208551565.211Q56530976407.216Q57828105177.216Q61820201889.216Q64193412887.191Q64709088086.216Q65210003448.216Q65314376097.216Q66149944741.194Q67259744550.192Q9356756743.193 Q9356855175.172 Q9633850153.190 Q9634014255.191 Q9644583048.192 Q9644583048.216 Q9740947091.190 00000100500900T00U01Y02K02L02M03:03U04^05P05k06F06G06H07>07b08O09U09V0:Z0;D0;E0<S0=B0=l0>Q0?B0?m0@J0AN0B80CF0DK0DL0DM0Df0Dg0Dh0E00E50EH0EI0EJ0FA0FE0Fl0Fm0Fn0Gg0Gh0Ha0Hb0Hc0Hd0He0Hi0Hj0Hm0I50I60IQ0IT0IY0IZ0I]0J80Ji0K00K10K20KY0Km0Kn0L[0Lj0Lk0Ma0NM0Ne0Nf0Ng0Nk0Nl0Nm0Nn0O20O30O40OO0Oj0Ok0On0QA0QB0QJ0QK0R?0RC0RD0RE0RF0RG0Rd0Re0Rf0Rg0Rh0Ri0S]0S^0T30TB0T]0U80UB0UH0UL0V30V=0V>0VH0VL0Wa0Wb0Wc0Wo0X00X10X20X=0X>0X?0XB0XC0XD0XP0Xk0Y30Y40Y50Y60YE0Z00Z10ZF0ZI0ZJ0ZK0ZL0ZM0ZN0ZO0ZP0ZQ0ZR0ZS0ZT0ZU0ZV0ZW0ZX0ZY0ZZ0Z[0Z\0Z]0Z^0Z_0Z`0Za0Zb0Zc0Zd0Ze0Zf0Zg0[P0\G0]80^A0^g0^h0^i0_G0`80a90b30c:0dh0eF0f50g<0gm0h^0i<0im0jS0kD0kb0lj0mH0n90nh0oB10H11:11\11n12@12R12d13513G13H13I13J13d14@14Q15>16516616^17F17W18@18i19Z19[19\1:E1:n1;Q1;d1<61<H1<b1=41=L1=o1>01>B1>T1>f1?81?J1@31@E1@F1@X1@Y1@Z1@k1An1BW1C41CO1Ca1DU1E81EJ1E\1E]1FH1FI1F`1Fa1Fb1Fc1GF1GG1G_1H71HL1Ha1I61IK1I\FS2FBS2FBS2LF2sp1C3kbs3LFB2FB3sp12dNFS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB2FB3sp13SP12dN3SPR4SP1R2F02C02N0S2LF2sp1C3kbs3LFB2FB3sp14lenw2p22dN2HB5Ha_st5Hl_stFFS2LF2sp1C3kbs3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS2LF2sp1C3kbs3LFB2FB3sp12dNS1R3HIA1h2LF2sp1C3kbs2lo3TOP3LFB2h22FB3sp13SP15Ehtop2dN3SPR4SP1R2F02C02N0S2LF2sp1C3kbs3LFB2FB3sp14lenw2p22dN2HB5Ha_st5Hl_stS2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNFFS1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS1R2LF2sp1C3kbs2lo3LOS3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12sz2dN2HB5Ha_st5Hl_stS1R3HIA1h2LF2sp1C3kbs3TOP3LFB2h22FB3sp13SP15Ehtop2dN3SPR4SP1R2F02C02N0FS2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN3APC3x163x293x303x314POSTS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stFS2LF3KEY3kbs2lo3LFB2FB3sp14lenw2p23x283KP23KL23APK2dN3LRW3x163x293x303x314POSTS2LF1C3kbs3LFB2FB4lenw2p22dN3APC2HB5Ha_st5Hl_stS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stS2LF2sp3KEY3kbs2lo3LFB3sp13SP13DKS2dNS2LF3KEY3kbs3LFB2FB4lenw2p23APK2dN2HB5Ha_st5Hl_stS2LF1C3KEY3kbs3LFB3DKC2dN2sz2HB5Ha_st5Hl_stS2LF2sp3kbs2lo3LFB3sp13SP12dNS2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN3APC3x163x293x303x314POSTS2LF1C3kbs3LFB2FB2sz2dN3APC2HB5Ha_st5Hl_stS2LF3KEY3kbs2lo3LFB2FB3sp14lenw2p23x283KP23KL23APK2dN3LRW3x163x293x303x314POSTS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp14lenw2p23SP13KP23ALO3ACP2F03LRWFFS1R2lo3LOS3sp12dN3ALO3NCEFFS2lo3sp1S3sp1S3KEY3kbs2KB2FB3sp1FFS1R2LF2sp1C3kbs3LFB2FB3sp12dN3ACV3SPR4SP1R2F02C03CCE2N0S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVFSS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F02F8FFFFS2FBSS1CS2sp3sp1FS2LF2sp1C3kbs3LFB2FB3sp12dNS1CS3sp1FS1CS2LF2sp1C3kbs3LFB2FB3sp12dNS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F0S1C1b1KFFS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACVS3KEY3kbs2FB3sp13APKSS1R5NEEDR2sp1C2lo3LOS3SLO3sp13SP13ALO3ACV3CCES3kbs2FB3sp12F0FS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP14SP1M3ALO3ACP2F0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP14SP1M3ALO3ACVS1R3HIA1h2sp2lo3TOP4HTOPFFS2loFFFS2FBFFS2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNFS1CS2LF2sp1C3KEY3kbs2K02KB3LFB2FB3sp14lenw2p23KP22dN3SPR4SP1R2F02C02N03LRW2p33Hp34Hp3aFS2dN3NRNFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1S2FBFFFFS3KEY4lenw2p23KP23LRW2p34Hp3aFFFFFS1R5NEEDR2sp3kbs2lo3LOS3SLO2FB3sp13SP13ALO3ACP2F02F1FS2dN3NRN3CBR1q1r1H2H0S3kbs2FB3sp12F0S2LF2sp1C3kbs3LFB2FB3sp12dNS2LF2sp1C3kbs3LFB2FB3sp12dNS2rv2RV2K2S1i2HiS2K1S3KEY3kbs2K04lenw2p23KP23LRW2p34Hp3a2KNS2dN2N12Z0FS1R2lo3LOSS2FBS1R5NEEDR2sp3KEY3kbs2lo3LOS3SLO2FB3sp14lenw2p23SP14SP1M3KP23KL23DKS3ALO3ACP2F02F13LRWFFS2r33RR33KT3FSFS2sp2lo3sp1SFS1CFFS3kbs2FB3sp1S2LF2sp1C3kbs3LFB2FB3sp12dNS2lo3sp1FFSS2sp2lo3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS3KEY3kbs2p33Lw34HLw3S1CFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS1R2LF1C3kbs2lo3LOS3LFB3sp12dN2AN3ALO3CCES1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALO3CCES1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12sz2dN3ALO3CCE2HB5Ha_st5Hl_stS1R2LF1C3kbs2lo3LOS3LFB3sp12dN3ALO3CCEFFS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB2sz2dN3ALO3CCE2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN2AN3ALO3CCES2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN2AN3APC3x163x293x303x314POSTS1R5NEEDR2LF2sp1C3KEY3kbs2lo3LOS3SLO3LFB2FB3sp14lenw2p23SP13x283KP23DKS2dN3ALO2F13CCE3LRW3x163x293x303x314POSTS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB2dN3ALO2F1S2LF1C3KEY3kbs2lo3LFB2FB3sp14lenw2p23x282dN2AN3APC3x163x293x303x314POSTS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF1C3kbs3LFB2sz2dN2AN2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp14lenw2p23SP12dN4FBLO2HB5Ha_st5Hl_stS2LF3kbs2lo3LFB2FB3sp12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB2FB3sp13SP12dN4FBLOS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB2dN3ALO2F1S2LF2sp3kbs3LFB3sp13SP12dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p22dN3ALO2F12HB5Ha_st5Hl_stS2LF1C3kbs3LFB2FB4lenw2p22dN2AN3APC2HB5Ha_st5Hl_stS1R2LF1C3kbs2lo3LOS3LFB2dN3ALO3CCES2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF1C3kbs3LFB2dNS2LF3kbs3LFB2FB2dNFFFS2LF1C3kbs3LFB2dN2HB5Ha_stS1R2LF3kbs2lo3LOS3LFB2dN3ALOS2LF1C3kbs3LFB2dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP12dNS1R5NEEDR2LF2sp1C3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALO3CCEFS2LF2sp1C3kbs3LFB2FB3sp12dN3SPR2F02F82C0S2LF2sp1C3kbs3LFB2FB3sp12dN3SPR2F02F82C0S2LF1C3kbs3LFB2dNS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB3sp13SP12dN3ALOFFS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB4lenw2p22dN2HB5Ha_st5Hl_stS2LF1C3kbs3LFB2dN2sz2HB5Ha_st5Hl_stS2LF3kbs3LFB3sp12dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF2sp3kbs3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dN2F02HBS2LF1C3kbs3LFB2sz2dN2HB5Ha_st5Hl_stFS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNS1R5NEEDR2LF2sp3kbs2lo3SLO3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dNFS2LF3kbs3LFB2FB2dNFFS2LF1C3kbs3LFB2dNS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2FB4lenw2p22dN3ALO2HB5Ha_st5Hl_stS1R5NEEDR2LF2sp3kbs2lo3LOS3SLO3LFB2dN3ALOS2LF2sp3kbs2lo3LFB3sp13SP12dNS2LF3kbs3LFB2FB2dN2HB5Ha_stS2LF3kbs3LFB2FB2dNS2LF2sp1C3kbs3LFB2FB3sp12dN2AN3SPR4SP1R2F02C03NAL2N0S2LF1C3kbs3LFB2dN2sz2HB5Ha_st5Hl_stS2LF3kbs3LFB2FB2dNS2LF3kbs3LFB2FB2dNFS1R3HIA1h2LF2sp3kbs3TOP3LFB3sp13SP12dN4HTOPFS2LF1C3kbs3LFB2dN2C02HBFFFS2LF1C3kbs3LFB2sz2dN2HB5Ha_st5Hl_stFS2LF3kbs3LFB3sp12dN4SP1RS2LF3kbs3LFB3sp12dN4SP1RS2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF3kbs3LFB2FB2dN2F0S2LF1C3kbs3LFB2dN". (* [comment removed for export] *)
  Lemma seg_B : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Ph2,(<.$51.VR,VHIA,)PLBa,(=.$>.)PLB2,(=.$>.)Pm0,P,(9.&40.)(:.(9.&8.))Pm2,P,(9.&40.)(:.(9.&8.))PWA,(=.$5:.)PFB,$0.Psp1,$0.Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Plenw,(9.&40.)Pp2,$0.Prv,$0.Pr2,$?.P,(10.(1.(42.(1:.&40.Vsp,)+90.)R16.)(1.R16.(42.(1:.&40.Vsp,)+80.)))P,(11.$0.(45.R17.+20.)=)P,(2<.$51.VR,VHIA,R1?.R1=.(1?.(20.$0.$0.)(21.$0.$0.R19.+80.)VLF,)R1;.)P,Px,$0.P,(27.$51.VR,VHIA,Vh,R1.)(27.$51.VR,VHIA,R22.R2.)P,(11.$0.(24.$51.VR,VHIA,R21.)(24.$51.VR,VHIA,Vh,))P,(11.$0.(1>.$51.VR,VHIA,R22.)(1>.$51.VR,VHIA,Vh,))P,(11.$0.(45.R1=.+40.)=)P,(32.VR,R22.VLF,R1>.+80.)P,(55.$51.R21.R1?.(1?.$56.(57.R?.)(1?.$56.(57.R>.)(1?.$56.(57.R=.)(23.$56.)))))P,(55.$51.R22.(2.R20.+20.)(1?.$56.(57.(46.&40.R<.))(23.$56.)))P,(55.$51.R23.(2.R21.+40.)(1?.$56.(57.R>.)(23.$56.)))P,(55.$51.R24.(2.(52.R22.+3.)(53.(49.VR,)))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.+?1.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.+?2.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.+?3.))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(1?.$56.(58.(46.&8.=))(23.$56.))))))))))))))))))P,(55.$51.R25.(2.(1:.&40.Vsp,)-60.)(1?.$56.(57.Vs10,)(1?.$56.(57.Vs9,)(1?.$56.(57.Vs8,)(1?.$56.(57.Vs7,)(1?.$56.(57.Vs6,)(1?.$56.(57.Vs5,)(1?.$56.(57.Vs4,)(1?.$56.(57.Vs3,)(1?.$56.(57.Vs2,)(1?.$56.(57.Vs1,)(1?.$56.(57.Vs0,)(1?.$56.(57.Vra,)(23.$56.))))))))))))))P,(55.$51.R26.(2.R23.+18.)(1?.$56.(57.(46.&40.R24.))(23.$56.)))P,(19.$51.R27.R24.(2.R24.+18.))P,(19.$51.R28.(2.R25.+20.)(2.(1:.&40.Vsp,)-60.))P,(19.$51.R29.Vlo,R26.)P,(18.$51.R2:.)P,(59.$51.VR,VHIA,R2?.R2>.VLF,(1:.&40.Vsp,)(1=.VR,)R2:.R2<.R2;.)P,(59.$51.VR,VHIA,R30.R2>.VLF,(1:.&40.Vsp,)(1=.VR,)(1?.(20.$0.$0.)(21.$0.$0.(2.VC,+8.)(2.VC,+10.))(23.(20.$0.$0.)))R2<.R2<.)P,(63.VR,R30.VLF,(1:.&40.Vsp,)R2<.(2.VC,+8.)+8.)P,Pb,$>.P,(2>.$>.R1.R32.)(2>.$>.R2.R32.)P,(3:.$51.R2?.VKEY,Vkbs,)P,(48.$51.(49.VR,)(27.$51.VR,VHIA,R34.)R30.VKEY,(3<.(38.(9.&8.)Vkbs,)))P,(1.(2.VKEY,+2.)R1;.)P,(1.(2.R1<.(1:.&40.R1=.))(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))P,(2?.(11.$0.(3<.(38.(9.&8.)Vkbs,))=)(2?.(1.(2.R31.+80.)VKEY,)(1.(2.VKEY,(3<.(38.(9.&8.)Vkbs,)))R31.)))P,(2?.(1.(2.VKEY,(3<.(38.(9.&8.)Vkbs,)))Vlo,)(1.(1:.&40.Vsp,)VKEY,))P,(2?.(1.(2.VKEY,(3<.(38.(9.&8.)Vkbs,)))VC,)(1.(2.VC,+>8.)VKEY,))P,(2=.$51.R36.R38.VC,R1>.)P,(11.$0.(64.R1?.)=)P,P,(11.$0.R21.=)(11.$0.(65.(66.R21.))+1.)P,(2?.(11.$0.R22.=)(11.$0.R22.$67.))(5;.$51.(49.VR,)(27.$51.VR,VHIA,R3>.)Lms,$50.(2?.(61.R3?.R3?.R3>.R3=.R3<.R3:.R39.R38.R29.R28.R27.Lmm,P,(9.&40.)(:.(9.&8.))(8.$0.Llenv,$0.(2=.$51.R2.R3?.VC,(68.R1.(66.R25.)(69.R25.))))R1.)(62.+;2;48.(2.VC,+20.)(2.(2.R25.(1:.&40.R26.))+2.)R3?.R3?.R3>.R3=.R3<.R3:.R39.R38.R29.R28.R27.Lmm,P,(9.&40.)(:.(9.&8.))(8.$0.Llenv,$0.(10.(2=.$51.R2.R3?.VC,(68.R1.(66.R25.)(69.R25.)))(11.$0.(65.(66.R25.))+1.)))R1.))(13.(14.(46.&40.+;2::<.)(46.&40.R37.)Vgp,Vtp,R36.R35.R34.Vsp,(46.&40.R37.)(46.&40.R23.)R33.R32.R31.R30.R2?.R2>.R2=.(46.&40.R38.)(46.&40.VC,)(46.&40.(2.VKEY,(3<.(38.(9.&8.)Vkbs,))))(46.&40.(2.R38.+20.))(46.&40.(2.R38.+40.))(46.&40.(2.VC,+10.))(46.&40.(2.(52.R38.+3.)(53.(49.VR,))))(46.&40.R38.)(46.&40.(53.(49.VR,)))Vs11,R2<.R2;.R2:.R29.)VF,(46.&40.+;2::<.)Vfc,(16.(9.&40.))R3:.(17.$51.)))")
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
  Lemma rp_fin : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Phq,(<.$51.VR,VHIA,)Php,(<.$51.VR,VHIA,)PLBq,(=.$>.)PWA,(=.$5:.)PFB,$0.Psp1,$0.Pw0,(9.&40.)Pw1,(9.&40.)Pw2,(9.&40.)Prq,$?.Pms,$50.P,(61.R;.R:.VLB,R9.Vm,R8.R7.R6.R5.R4.R3.Lmm,P,(9.&40.)(:.(9.&8.))(2=.$51.R1.R:.VC,R3.)R1.)P,Px,$0.P,(6:.(1?.(20.$0.$0.)(21.$0.$0.VC,(2.VC,+>8.))(23.(20.$0.$0.)))R1.)(6:.R;.R2.)P,Px,$0.P,(27.$51.VR,VHIA,R=.R1.)(27.$51.VR,VHIA,R?.R2.)P,(11.$0.(1>.$51.VR,VHIA,R>.)(1>.$51.VR,VHIA,R=.))P,(10.(1.(42.(1:.&40.Vsp,)+90.)R:.)(1.R:.(42.(1:.&40.Vsp,)+80.)))P,(11.$0.(45.R;.+20.)=)P,(11.$0.(45.R=.+40.)=)P,(32.VR,VLB,VLF,R>.+80.)P,(32.VR,R11.VLF,R?.+80.)P,(5>.(27.$51.VR,VHIA,Vh,)R10.+80.)P,PB,$0.Pj,$0.P,(2>.(20.$0.$0.)(21.$0.$0.R2.R1.)VLF,)(2?.(1.(2.R14.+80.)R3.)(1.(2.R3.R2.)R14.))P,Px,$0.P,(27.$51.VR,VHIA,Vh,R1.)(27.$51.VR,VHIA,R18.R2.)P,(11.$0.(24.$51.VR,VHIA,R17.)(24.$51.VR,VHIA,Vh,))P,(11.$0.(1>.$51.VR,VHIA,R18.)(1>.$51.VR,VHIA,Vh,))P,(11.$0.(25.$51.VR,VHIA,R19.)(25.$51.VR,VHIA,Vh,))P,(1.(28.$51.VR,VHIA,R1:.)(2.(28.$51.VR,VHIA,Vh,)(29.(3<.(38.(9.&8.)Vkbs,)))))P,(1.(2:.$51.VR,VHIA,R1;.)(2.(2:.$51.VR,VHIA,Vh,)$2;.))P,Pb,$>.P,(2>.$>.R1.R1;.)(2?.(2>.$>.R2.VLB,)(2>.$>.R2.(30.R15.)))P,Pb,$>.P,(2>.$>.R1.VLB,)(2>.$>.R2.R1=.)P,Pb,$>.P,(2>.$>.R1.(30.R16.))(31.(2>.$>.R2.VLB,))P,Pb,$>.P,(2>.$>.R1.(30.R17.))(32.VR,VLB,VLF,(33.$0.$0.R2.)(34.$0.$0.R2.))P,(1.(35.R1>.)(2.(35.VLB,)(6.(3<.(38.(9.&8.)Vkbs,))+1701.)))(6;.$51.(6<.$51.VR,VHIA,R21.Vmo0,)(4?.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VC,(3<.(38.(9.&8.)Vkbs,))Vlo,Vm,Vmo0,)R17.)")
(* [comment removed for export] *).
  Proof.
    intros until ms. intros EQ WSUB HCSp ESp SP1 SP1M F64 FRSH FRSHq CFB AP HCSq ETq ESq EFq EVq EFRq L1 L2 L3 L4 L5.
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
    unfold rsa_parse_pubkey_postA_c.
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
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4| exact L5].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis RB : mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY.
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0210?L10121468914.25L10127712114.4 L1044568644.12 L1045152775.11 L1045152775.12 L11585923358.11L11586385757.10L11586385757.11L12595682813.9 L12595843834.9 L12595843837.8 L13657235190.1 L13658852356.2 L14093053380.4 L14671903450.1 L14885752793.6 L14889971800.9 L14890139480.9 L1540877545.3  L16256253080.6 L16256414616.7 L16446017371.25L1741360775.7  L17565801997.5 L1820677675.25 L19959024712.1 L19964958796.25L19979640288.25L21179676237.3 L21193694771.25L21204179871.25L2164292835.4  L2275137097.0  L22923669014.9 L23137366490.1 L2397623502.7  L24128180555.1 L24926391073.0 L25985555144.1 L26892418956.1 L27188209011.3 L27356981623.3 L27800688430.1 L27884611213.1 L28390317327.1 L28555178628.10L28567569027.9 L28762784221.6 L28762787805.5 L2953011965.10 L2975321653.25 L30417338446.25L31362055200.1 L3199309172.5  L32381825919.0 L32454903270.1 L32624459940.2 L33126711374.3 L33213852813.1 L33337549682.25L3480283673.25 L3482382261.25 L35653441506.9 L35666090444.8 L36222876443.2 L37156630869.0 L37622523289.3 L37796632789.0 L37814404089.2 L3789236036.8  L37898896573.25L38012506529.0 L38291272584.5 L38723264084.4 L38737777364.5 L39306246569.9 L39845491246.1 L40281191306.3 L43350740717.6 L46452926541.3 L48345000542.9 L50790580594.6 L50980187747.9 L51174981929.8 L51508673957.0 L5159408642.6  L52045659405.3 L52615975131.8 L52665112138.7 L52665116118.10L52680898955.25L52758365172.6 L53413695971.4 L55116274681.2 L55126760974.2 L56523586534.1 L5901681115.3  L59203503582.9 L59255599441.8 L59256028753.7 L59256028758.8 L59314923118.3 L59361649295.6 L60098763854.3 L60438662093.2 L60660409869.25L62018535662.1 L6203936179.1  L6247173588.26 L6249348728.33 L62672175878.25L627252352.12  L627704515.11  L627704515.12  L63158919349.6 L65566735028.9 L66557520514.1 L67028235242.8 L67092310858.3 L6899380056.1  L7034380190.8  L7034867865.8  L7034867870.7  L7338931048.33 L7343048040.26 L7546167771.7  L9356559645.11 L9631767084.2  L973128649.0   00000b01101201301401501601701801901:01?01D01S01V01o02002102=02R02l03d03e04704m05205g06\06f07Q08<08F08G08k08n09B09F09G09L09P09Y09e09h09l0:00:10:Y0;20;30;U0<G0=G0=J0=_0=`0=d0=k0>50>90?80?h0@X0A00AP0AY0AZ0Ab0Ac0Ao0BN0CN0CO0Ce0D20DD0DE0DH0DQ0Dm0E70EY0F00FZ0GI0GJ0Gd0H00HJ0Hc0IK0JJ0Jd0Jn0K80KC0KG0KS0L50L60L70L80LB0L[0Le0Ll0M_0Mb0Mg0Mh0Mi0N[0N\0N]0N^0O40OV0O[0P:0PE0PI0PJ0PK0PL0PM0PN0Ph0QS0QZ0Q[S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP12p33KP3S3KEY2K02p33KP3FFFFFFFFFS3kbsS3kbsS1C3KEY3kbs3DKCS1CS2LB3kbs4lenw3LB24CNT22W1FFS2sp3sp13SP1S1R3HIA1h3FR02h24HFR2S1R3HIA1h3kbs4PHI02h24VOL2S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p35lenw33KL34LRW3FS1R3HIA1h4BUDF3FR0S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p24lenw3KL23LRWS3sp1S1R3HIA5NEEDR1h2sp1C3KEY3kbs2lo2K03SLO3TOP2C03sp13SP1S1R3HIA5NEEDR1h2sp1C3KEY3kbs2lo2K03SLO3TOP2C03sp13SP1S1C2FB3APCS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP1S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP1S1C1A1k2HASS1R3HIA1h3kbs3BUD2h24VOL25lenw34MONOS1CS1R1C2lo3LOS3ALO3CCES2FBSS3sp1S2spS2FB1c2HcS3KEY2p23KP2S1CS2FBS2FBFS2LB3kbs4lenw3LB24CNT25lenw33LB34CNT32W2S3KEY3kbs2KB2p35lenw33KL3FS2sp3KEY3kbs2lo3DKS3sp13SP11a2Ha1KS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP12p23KP2S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKC2C03sp13SP12p35lenw33KP33KL3S1CS3KEY3kbs2p24lenw3KL2SS2FBS2dN2N1S1C2FB3APCS2FBS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKC2C03sp13SP12p24lenw3KP23KL2S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP14SP1MS1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO2C03sp13SP14SP1MS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h3kbs3BUD4PHI04lenw4MONOS2LB4C24HSS1C1x2HxSS5lenw34LRW3S1R3HIA1h3kbs4lenw2h24MONO4HV2'S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKS2C03sp13SP12p35lenw33KP33KL3SS3KEY3kbs2p35lenw33KL3S1R3HIA1h3FR0S1R3HIA1h3kbs4PHI0FS1CS1R3HIA1hS2LB4C24H4lenw3LB24CNT24W24NS1C2FB3APCS1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCS1R5NEEDR2sp2lo3LOS3SLOS3KEY3kbs2p24lenw2p35lenw33KL35KPLO35KPLOnS3KEY3kbs2p24lenw3KP23KL21a2Ha2p35lenw33KP33KL3SS3KEY3kbs2p24lenw3KL24KPLOS2sp3sp13SP1S2sp3KEY3kbs2lo3DKS1a2Ha1KS1R3HIA1h2h24HFR22h34HFR3S1R3HIA1h3kbs2h24VOL25lenw32h34MONO4HV3'S1R5NEEDR2sp1C3KEY3kbs2lo2K03SLO3DKS2C03sp13SP12p24lenw3KP23KL2S3KEY3kbs2p35lenw33KP33KL3S1C1A1k2HAS4lenw3LRWS4lenw4LRWnS2FBS3KEY2p33KP3S1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCFFFS3kbs2NE1KS3KEY3kbs2p24lenw3KP23KL2S1R2lo3LOSS2dE2N1S1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p35lenw33KL3S1RS3sp1FFS1R5NEEDR2sp3KEY3kbs2lo2KB3SLO3sp13SP12p24lenw3KL2FFFS1R3HIA1h4BUDF2h24HFR2S1R5NEEDR2sp1C2lo3SLO3sp13SP14STKCS3kbsS1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2LB3kbs2DPS2FBFFFFFS1R5NEEDR2sp1C2lo3SLO4STKCS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S2FB2F0S". (* [comment removed for export] *)
  Lemma rp_main : ltac2:(CDefT.buildp (gd_tbl_A_rsa_parse_pubkey_c24 ()) "Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)P,(2<.$51.VR,VHIA,Vh,VLB,VLF,Vm,)P,(26.$51.VR,VHIA,Vh,Vmo0,)P,(19.$51.Vm,Vlo,(1:.&40.Vsp,))P,(18.$51.Vm,)P,(48.$51.(49.VR,)(27.$51.VR,VHIA,Vh,)Vm,VKEY,(3<.(38.(9.&8.)Vkbs,)))(4>.$51.(4?.$51.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VC,(3<.(38.(9.&8.)Vkbs,))Vlo,Vm,Vmo0,)(12.(13.(14.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(46.&40.VC,)(46.&40.VKEY,)(46.&40.(3<.(38.(9.&8.)Vkbs,)))R>.R=.R<.R;.R:.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(46.&40.$5=.)Vfc,(16.(9.&40.))Vm,(17.$51.))Vmo0,))")
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
              | (lazymatch goal with |- cnt24 _ <= _ => idtac end; (pose proof (Z.div_pos LEN 5889 ltac:(clear; lia) ltac:(clear; lia)) as DP; clear - DP; lia)) | match goal with |- ?g => idtac "FINA-LEFT:" g end ]. }

    (* [comment removed for export] *)
    destruct CQ as (mc & c0 & c1 & c2 & ca3 & ca4 & ca5 & ca6 & ca7 & c3 & c4 & c5 & c6 & p2 & lenw
                    & -> & HHc & FHDc & PSLc & LSLc & FSHXc & SAVEc & SLOTc & ST16c & SThic & STloc & MIc & PRESc & HKYc & OKEYc & KP2 & KL2 & KPLO & RATc).
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
    pose proof RB as RB'. unfold mpi_read_binary_stmtA_r_c, A_MPI_READ_BINARY in RB'.
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
              | first [ (lazymatch goal with |- context [cnt24] => idtac end; clear - C24H; unfold C24_RSA_PP, C24_RB_c in *; lia) | match goal with |- ?g => idtac "CALL1-PRE-LEFT:" g end ] ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h2 & LB2 & dN & rv
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & RV & RV0 & FRS2 & CNT2).
    rewrite LENI in CNT2.
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
              | (lazymatch goal with |- cnt24 _ <= _ => idtac end; (pose proof (w24_one LEN (bv_unsigned lenw) ltac:(clear - LRW; lia) ltac:(clear - KPLO KL2; lia)) as W1; clear - W1 CNT2; lia)) | match goal with |- ?g => idtac "FINB-LEFT:" g end ]. }

    (* [comment removed for export] *)
    pose proof LRW as LRWn. pose proof KPLO as KPLOn.
    clear FHDc PSLc LSLc FSHXc SAVEc SLOTc ST16c SThic HKY2 OKEY2 PRESb2 PRESa2h RAT2 KP2 KL2 LRW.
    destruct CQ as (mc' & d0 & d1 & d2 & da3 & da4 & da5 & da6 & da7 & d3 & d4 & d5 & d6 & p3 & lenw3
                    & -> & HHd & FHDd & PSLd & LSLd & FSHXd & SAVEd & SLOTd & ST16d & SThid & STlod & MId & PRESd & HKYd & OKEYd & KP3 & KL3 & KPLO3 & [lenv [RATd SGNN]]).
    cbn [r_N r_E] in RATd, SGNN.
    pose proof (bv_unsigned_in_range 64 lenw3) as LRW3. unfold bv_modulus in LRW3. cbn [Z.pow Z.of_N Pos.pow] in LRW3.
    destruct (sub_input asegs mc' KEY kbs p3 (bv_unsigned lenw3) HKYd ltac:(clear - KP3; lia) ltac:(clear - LRW3; lia) KL3) as [HIB3 LENI3].
    set (ibs3 := firstn (Z.to_nat (bv_unsigned lenw3)) (skipn (Z.to_nat (p3 - KEY)) kbs)) in HIB3, LENI3.
    flat constr:(RATd) 13%nat. intros _ _ _ _ _ _ _ ALLd _ _ _ CIN2 _. cbn [r_N r_E] in ALLd. unfold RSA_CTX_SIZE in CIN2.
    unfold rsa_mpds in ALLd. cbn [r_N r_E] in ALLd.
    pose proof (Forall_inv ALLd) as MNd. pose proof (Forall_inv (Forall_inv_tail ALLd)) as MEd.
    pose proof (hm_aobj_block asegs R HIA h2 LB2 _ mc' C 232 HHd CIN2) as OCd.
    flat constr:((hm_apart asegs R HIA h2 LB2 _ mc' HHd)) 2%nat. intros HBRd BAd.
    pose proof RB as RB2. unfold mpi_read_binary_stmtA_r_c, A_MPI_READ_BINARY in RB2.
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
              | first [ (lazymatch goal with |- context [cnt24] => idtac end; pose proof (w24_range (4 * chars_to_limbs (bv_unsigned lenw))) as W24N; clear - C24H CNT2 W24N; unfold C24_RSA_PP, C24_RB_c in *; lia) | match goal with |- ?g => idtac "CALL2-PRE-LEFT:" g end ] ]. }
    cbv beta. intros ms6 mo6 (mo1 & [HK1 MF1] & PO).
    destruct PO as (e0 & e1 & e2 & ea1 & ea2 & ea3 & ea4 & ea5 & ea6 & ea7 & e3 & e4 & e5 & e6 & m3 & mo3 & h3 & LB3 & dE & rv3
                    & E6 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & RV3 & RV30 & FRS3 & CNT3).
    rewrite LENI3 in CNT3.
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
            | (lazymatch goal with |- cnt24 _ <= _ => idtac end; (pose proof (w24_two LEN (bv_unsigned lenw) (bv_unsigned lenw3) ltac:(clear - LRWn; lia) ltac:(clear - LRW3; lia) ltac:(clear - KPLOn KPLO3 KL3; lia)) as W2; clear - W2 CNT2 CNT3; lia)) | match goal with |- ?g => idtac "FINC-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  Theorem A_rsa_parse_pubkey_spec_s_c :
    asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_RP -> mpi_size_stmtA asegs AL A_MPI_SIZE_RP ->
    rsa_complete_stmtA asegs R HIA A_RSA_COMPLETE_RP -> rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY_RP ->
    mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY -> rsa_parse_pubkey_stmtA_c asegs R HIA A_RSA_PARSE_PUBKEY
(* [comment removed for export] *).
  Proof.
    intros GT MSZ RC CK RB. unfold rsa_parse_pubkey_stmtA_c. intros until slo.
    intros HH HK LFB RAT HKY K0 KB CRK DKC DKS ST LOS SLO SLOS TOP SPA TPV SSH SSLO SSHI MI RAE OKEY BUD BUDF C24H -> -> ->.
    eapply rp_main; eassumption.
  Qed.
End WalkRP.

Theorem A_rsa_parse_pubkey_spec_c : forall (R : art_layout) (HIA : artA asegs R), asan_img_ok (arl_AL R) ->
    arl_uar_got R = A_UAR_GOT_RP -> arl_smalloc R 1 = A_SMALLOC_1_RP -> 0 <= arl_need_smalloc R -> 0 <= arl_need_rt R ->
    asn1_get_tag_stmtA asegs (arl_AL R) A_ASN1_GET_TAG_RP -> mpi_size_stmtA asegs (arl_AL R) A_MPI_SIZE_RP ->
    rsa_complete_stmtA asegs R HIA A_RSA_COMPLETE_RP -> rsa_check_pubkey_stmtA asegs R HIA A_RSA_CHECK_PUBKEY_RP ->
    mpi_read_binary_stmtA_r_c asegs R HIA A_MPI_READ_BINARY -> rsa_parse_pubkey_stmtA_c asegs R HIA A_RSA_PARSE_PUBKEY
(* [comment removed for export] *).
Proof. intros. apply A_rsa_parse_pubkey_spec_s_c; assumption. Qed.

(* [comment removed for export] *)
