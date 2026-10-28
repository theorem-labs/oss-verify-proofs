(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_getsig_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01c756816db25df6 0 5 0 1 37 1 58 1 71 1 72 1P03250fd0ebf8c04a 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P03d4c216d96623e6 0 5 0 1 37 1 58 1 71 1 72 1P0420301cba726c93 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P047539d331b15aaa 0 5 0 1 37 1 58 1 71 1 72 1P048605e309bd4ff6 0 4 0 1 58 1 71 1 72 1P04fbd238ca8f48ef 0 4 0 1 63 1 71 1 72 1P069b6261b781bd05 0 5 0 1 37 1 58 1 71 1 72 1P06cf51ef14cd54e1 0 4 0 1 63 1 71 1 72 1P070cec0655b31458 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P076f4dbb2aa194e5 0 6 0 1 59 1 60 1 63 1 71 1 72 1P07a05ea13ba6ce9f 0 6 0 1 59 1 60 1 63 1 71 1 72 1P07bb93aa1ed46c49 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P07bd5cfe7d13dbff 0 4 0 1 63 1 71 1 72 1P0a2ad1653a803705 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0a92317f98c34216 0 4 0 1 63 1 71 1 72 1P0b912c9be8d0381a 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P0c8aae9a23b4e03a 0 4 0 1 63 1 71 1 72 1P0e448eef8c8cdbc9 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0e8ed50c92447e2a 0 4 0 1 58 1 71 1 72 1P0f8c99a374c7d1bf 0 4 0 1 58 1 71 1 72 1P0f97fc42f60fd359 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P0f9ea8dafad03636 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0fac678c658f7c7f 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0fc704060b943142 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0fdb3bcb1c10834b 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1006b94c8066ca2d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P11259444a4fd0637 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1201cbe12a63d477 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1210a42fc682e5ab 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P123ba2ba6493a44c 0 4 0 1 63 1 71 1 72 1P12712b2068ef7c75 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P13572b19a3c9eca2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P135fef66856680e0 0 3 0 1 44 1 52 1P13bce61432332a87 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P14d72314c98b1aa4 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P153d93411a54aa43 0 6 0 1 59 1 60 1 63 1 71 1 72 1P166ef9d96eebda22 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P16e1f7381cbc8419 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P172126a10cbe67f3 0 5 0 1 37 1 58 1 71 1 72 1P175e8a28f8034405 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P17ef706a44748c26 0 5 0 1 37 1 58 1 71 1 72 1P1927cf1c7e852210 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1995b0aad19f7f6a 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1a1573fd1fe479a5 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1a57218be31af8e1 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1bae1fde569d222f 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1bb1d383f0fc8570 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1c117fd68e0b4f70 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1c30e1b272369607 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1c3ecc616fb177ba 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1cb8cf0bf7473331 0 5 0 1 37 1 58 1 71 1 72 1P1d0c95009f7dfe36 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1db9dc72f57c23ca 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P211a6108251ec6f1 0 4 0 1 63 1 71 1 72 1P213e49533e6c7cad 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2240873383a9a7fb 0 4 0 1 58 1 71 1 72 1P2324924553a37824 0 6 0 1 59 1 60 1 63 1 71 1 72 1P235defaa089aab62 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P238b6f44cc271eb6 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P24ae1cfe558120ed 0 4 0 1 58 1 71 1 72 1P253ece906a94c0c7 0 5 0 1 37 1 58 1 71 1 72 1P256c04762f114a00 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P258f5db12f39c379 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P259202e5578babd2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P259b703e6d9fc8e3 0 3 0 1 43 1 49 1P25ec0256921c5348 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2655b5a55116d00d 0 5 0 1 37 1 58 1 71 1 72 1P26a10a57a5d9b5b6 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P26a5d9f1c5de226e 0 4 0 1 58 1 71 1 72 1P26a67818adbbc65c 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2716c6296f149989 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2742c09ee49832d1 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P275bf85e18e60585 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P28c5e64c8fcf485f 0 4 0 1 58 1 71 1 72 1P2973629039d68961 0 4 0 1 58 1 71 1 72 1P2aa88b896180b13b 0 4 0 1 63 1 71 1 72 1P2b338d7ab70a692e 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2c2dee816df264a5 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P2c5762266746f2b1 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2d52314a2c4bccf6 0 5 0 1 37 1 58 1 71 1 72 1P2e14dbca7f9f0aa5 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2f25b715c8ce3ea2 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2f830176c7245ee2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P300ec2648a75b8d9 0 4 0 1 58 1 71 1 72 1P3012dc346477ea20 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P30c45e3c64316a9d 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P31659a5c5d86e41e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3185af627e380ba1 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P31cc20dae1853bae 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P322d0a117cafd42c 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3374fd575b8ef6e7 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3378d9f41ca0c9a6 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P33ac4d7a01f2c757 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P33ef8a82c40a7688 0 4 0 1 63 1 71 1 72 1P368c27b3cc8532d9 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P36928c4d8f60ccb4 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P385b6acd5475aed6 0 5 0 1 37 1 58 1 71 1 72 1P387b7396c440de56 0 6 0 1 59 1 60 1 63 1 71 1 72 1P38cc692ba8809979 0 4 0 1 58 1 71 1 72 1P391c2d54895e74a0 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3965d8fd9fba0324 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P39cca0aab014a085 0 4 0 1 58 1 71 1 72 1P3aaec500c7e2ffc3 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3b04e58addf6fe49 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3bcd464030875a56 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3d0ed0510e23797c 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P3d6771cb8dd47016 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3d95d7393085c898 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3da72452192fabe6 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3db4f2556d162fce 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3e3367af71e0243d 2 59 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P3ea2d4178eab15e8 0 4 0 1 63 1 71 1 72 1P3eec468d66bc9005 0 4 0 1 63 1 71 1 72 1N00df2f2b19ca3faaN031c161bb9016c7fN03cdc5ac9dbd9388N04197fcce6a5ea8bN051a3342731255ffN05ed3d98258b7c76N063fd68b7797aa8fN0833dccac1b16381N0b3cb2977f4c6344N0d33da03594f2162N0dd5379e2e117cf4N0ee149cc9be864e8N0f19760cb839ffb5N0f2f7c7f3431ffcbN0f5504ad5a38dc8dN11917e4946466e4dN16f1a815b4188532N178b45407d32d6cdN1afec69e243f9ac0N1b24aad112763f7dN1ba1e83f73288a2dN1c38a0187ecd4e3bN1cd5994b2f169a04N1d854e068a87a571N1e75e4a661b145dfN1ff8adb45ac06872N20f3d2d1d6b58a1bN21f17ba69298f64cN22786cd1479ef628N23f37d9c1155bed5N24839e15cca3d669N25597797954b46d9N26a14b4bb86cadb6N291030cb18f4cea9N29bede5e853614f8N2d1e8f419f4ba379N2d9fb690b46ff480N2e1fe2e80659eee3N2f457f8bc9192dadN2f4d75648cf871abN302688c9383d017cN313eccfb604ccdc8N326c6661db1c5dadN35e962b3669917daN374070d2de4ec9adN39ca021f36e5e6f8N3abe9a8169f8fccbN3b1a1a4f25d3239b"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_getsig () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_getsig_A.pkcs7_getsig_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_getsig_A.A_PKCS7_GETSIG"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_getsig_A.pkcs7_getsig_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP SIGB P END BUF lo slo : Z) (bs : list byte) (pad : word).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= SIGB \/ SIGB + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ SIGB + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SIGB.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : SIGB mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis SGB : 0 < SIGB /\ SIGB + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - PKCS7_GETSIG_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : SIGB + 24 <= lo \/ bv_unsigned sp <= SIGB.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo SIGB 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIGB 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.   (* [comment removed for export] *)

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold PKCS7_GETSIG_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (pkcs7_getsig_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SIGB P END lo slo pad).
  Local Notation W := [(PP, PP + 8); (SIGB, SIGB + 24)].
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.

  Ltac rw_at_hyp :=
    match goal with
    | H : rw_cells _ ?m ?A' ?cs |- rw_cells _ ?m ?A _ =>
        first [ exact H | replace A with A' by (clear; lia); exact H ]
    end.
  Ltac bw_side :=
    first
      [ eassumption
      | lazymatch goal with
        | |- rw_cells _ _ _ _ => rw_at_hyp
        | |- PATH _ _ _ _ _ _ _ _ => unfold PATH;
            first [ left; split; [ reflexivity |]; split; [ reflexivity |]; split; [ reflexivity | solve [ clear; lia ] ]
                  | right; split; [ reflexivity |]; split; [ reflexivity |]; split; [ reflexivity |]; split; assumption ]
        | |- crange _ _ _ => solve_crange
        | |- client_wrange _ _ _ _ _ _ => solve_client_wrange
        | |- wcover _ _ _ _ _ _ _ => solve_wcover
        | |- shadow_free _ _ _ _ _ _ _ =>
            first [ match goal with WL : wlow _ _ _ |- _ => apply (shadow_free_of_wlow _ _ _ _ _ _ _ WL); qlia end
                  | match goal with WL : wlow _ _ _, FR : fresh_apart _ _ _ _ _, HHx : HM _ _ _ _ _ _ _ |- _ =>
                      eapply (shadow_free_of_fresh' _ _ _ _ _ _ _ _ _ _ _ _ _ WL FR HHx); qlia end ]
        | |- forall b, In b _ -> In b _ =>
            let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb;
            first [ exact Hb | apply fdata_cons_sub; exact Hb | right; exact Hb ]
        | |- forall x, _ <= x < _ -> _ \/ in_block _ x =>
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
            first [ left; clear_disj; lia
                  | right; match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; clear - Hx; lia] end
                  | right; exists (x - (x - _), 64) ]
        | |- _ \/ _ => first [ solve [clear_mods; clear_disj; lia] | pqlia ]
        | |- _ => first [ qlia | pqlia ]
        end ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@D10639329459.126D10692844218.166D10692844218.167D10692844218.168D14735680649.194D18607476203.165D2459889674.191 D27388597713.191D29720839482.194D32452855249.191D3254889317.164 D3386124073.191 D33956323578.166D33956323578.167D33956323578.168D41452831839.191D46793042006.126D50254960491.166D53232575014.166D53232575014.167D53232575014.168D560907438.128  D58077997354.166D59942523331.127D60098777666.127D60111245650.126D62011770188.128D62960757940.127D68409458026.191D6897397615.191 L12219578755.2  L13948747720.1  L15756354262.7  L16596701601.0  L1685717371.0   L17921795213.184L19013159470.0  L19685319514.180L19980016842.7  L21866712442.2  L22066801146.3  L22286006383.182L22941438733.2  L29738741675.1  L33801907085.2  L3551623394.2   L35680140202.3  L36180999398.120L3876079316.5   L39076636629.0  L39332637397.0  L39618635427.2  L40228640085.0  L40316771656.2  L41786593184.175L43055370171.118L44166924249.3  L48117620907.106L50616353679.182L50790731766.8  L52249874585.0  L56854270298.123L57355539152.170L58071656716.181L58790154276.6  L59308677456.15 L59393203371.1  L64009471222.1  L64787780871.1  L6776896075.2   L7040749983.124 L8518322573.2   L9356559645.13  L9873114841.7   P1056307012.164 P1056307012.166 P12226132804.194P21870859916.194P22945712379.194P33789407355.194P36462068749.165P36465839390.164P40332238735.194P44164039966.194P53499894264.164P53499894264.166P6761429132.194 P8514048635.194 Q10523111608.132Q10651763882.134Q10651763890.130Q12636765557.194Q12660624644.136Q1530342990.166 Q21842126289.191Q22712450012.194Q23927511185.132Q23927511197.137Q25513505925.193Q26030354684.194Q27940636720.191Q31021924279.164Q31801074431.191Q32440606517.191Q32681824661.194Q32681887700.132Q33196749121.136Q33947335980.190Q33967969366.191Q3482560409.191 Q34964698202.194Q35653441506.111Q38248895676.138Q40216283646.191Q40271359350.166Q42439168719.164Q42439382240.139Q42439443119.194Q43880146016.138Q46805771343.134Q46805771351.130Q47230721789.132Q48132468010.191Q49698585326.192Q50796826103.166Q59852654197.191Q59865321072.194Q59865520191.139Q59932040168.131Q59932040173.135Q60109315147.111Q60740903729.130Q61503024048.193Q6192914196.164 Q62011770181.137Q62011770185.132Q6203643061.191 Q62950270618.135Q62950270623.131Q63766058673.190Q64683599817.139Q67026483294.165Q67038703949.164Q6897397615.191 Q7166002681.131 Q8699115497.194 Q9356560156.147 Q9633850153.191 00000F00G00H00I01V01W01X02903N03o04004104Z05C05D05e06;06<06=06>06?06]07?07U08408S08k09A09B09c09d09i0:70:80:90::0:;0:\0;40;50;A0;b0;c0;g0;h0;o0<90<O0<b0<c0<d0<n0<o0=00=c0>@0>A0>`0?A0?R0?S0@M0@N0A30AI0A\0A`0Ad0Ah0Ai0BO0BP0C?0C[0DR0EI0F?0GA0HC0IE0Im0In0JV0KM0LF0M?0N70O90OI0OW0Oe0P^0Pm0QC0QQ0R90RX0Rk0SV0T=0TZ0U90Ul0Um0Un0Uo0V>0V[0WL0X>0Xm0YO0Y]0Y^0Z10ZG0Z]0[I0[Z0[h0\60\G0\f0]>0]Y0]o0^00^10^A0^Q0^e0_80_g0`60`C0`P0`_0`o0a?0aX0b;0b^0cA0cO0cb0d_0e60eOS2LF2sp2PP4SIGB2bs3LFBFFFS1R2LF2sp2PP4SIGB2lo2bs3PPB3SGB3SLO3LOS3LFB3SPR3sp12FB3H223SP12HB5Ha_st5Hl_stFFS2LF2sp2PP4SIGB2bs3LFB3sp12FB3H22S1R3HIA1h2LF2sp2PP4SIGB2bs3PPB3SGB3TOP3LFB3SPR3sp12FB3H223SP12h15Ehtop2HB5Ha_st5Hl_stS2LF2sp2PP4SIGB2bs3LFB3sp12FB3H22FFS2LF2sp2PP4SIGB3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP4SIGB3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP4SIGB2bs3LFB3sp12FB3H22S2LF2sp2PP4SIGB2bs3LFBFFFFS1R3HIA1h2LF2sp2PP4SIGB2bs3LFBS2LF2sp2PP4SIGB2bs3LFB3sp13H203H22S2LF2sp2PP4SIGB2bs3LFBS1R2LF2sp2PP4SIGB2lo2bs3LOS3LFBS1R2LF2sp2PP4SIGB2lo2bs3LOS3LFBS1R2LF2sp2PP4SIGB2bs3LFBS2LF2sp2PP4SIGB2bs3LFBFS2LF2sp2PP4SIGB2bs3LFB3sp12FB3H22FS3sp1S1R2lo3LOS3ALOSSFSS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS1R3HIA1h2sp3TOP3sp13SP1FS2sp3sp13SP1S2LF2sp2PP4SIGB2bs3LFB3sp13H222FBFS2FBFS2bs2EQS2FB2x22HxS2LF2sp2PP4SIGB2bs3LFBS2sp2lo3SLO3sp13SP1SSS3sp14SP1MSFS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'S2LF2sp2PP4SIGB2lo2bs3SLO3LFBFS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS2LF2sp2PP4SIGB2bs3LFB3sp13H222FBS1R2sp2lo3SLO3LOSSS2LF2sp2PP4SIGB2bs3PPB3SGB3SPA3LFB3SPR3sp13H183H193H203H22FS2LF2sp2PP4SIGB2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS2bsS2spFS2LF2sp2PP4SIGB2bs3LFB3SPR3sp13H183H22FS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP2lo2bs3SLO3DS13LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'2HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'2HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'2HB5Ha_st5Hl_stS2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2bs3LFB3sp12FB3H202HB5Ha_st5Hl_stS2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12FB2HB5Ha_st5Hl_stS2LF2sp4SIGB1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp4SIGB1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp4SIGB2lo2bs3SLO3DS23LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'2HB5Ha_st5Hl_stS1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP12HB5Ha_st5Hl_stS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2bs3LFB2FBS2LF2sp2bs3LFB3sp12FB3H202HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3LFB3sp13H202FB2HB5Ha_st5Hl_stS2LF2sp2lo2bs3LFB3sp12FB2HB5Ha_st5Hl_stS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp12FB3SP15FRSH'FFFS2LF3BUF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S2LF2sp2PP4SIGB2bs3PPB3SGB3LFB3SPR3sp12FB3H223F64S2LF2sp2PP4SIGB2bs3PPB3SGB3LFB3SPR3sp12FB3H224SP1MS2LF2sp2lo2bs3SLO3LFB3sp12FB3SP12HB5Ha_st5Hl_stS1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFB3sp12FB2HB5Ha_st5Hl_stS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS2LF2bs3LFB3sp12HB5Ha_stS1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2bs3LFB3sp13H222HBFFS2LF4SIGB2bs3LFBS2LF4SIGB2bs3LFBS1R2LF2lo2bs3LOS3LFBS2LF2PP4SIGB2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP12FB2HB5Ha_st5Hl_stS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS2LF2bs3LFB3sp1S2LF4SIGB2bs3LFBS2LF4SIGB2bs3LFBS2LF2sp2lo2bs3LFB3sp13H20S1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2PP4SIGB2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOP3sp12FB3SP12HB5Ha_st5Hl_stS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Ptg0,(0.&40.)Plen0,$1.Pq0,$1.P,(2.$3.VR,VHIA,Vh,VLB,VLF,Vm,)P,(4.$3.Vm,VPP,(5.$6.(7.(8.&40.VP,))(9.$6.)))P,(4.$3.Vm,VSIGB,(:.R5.Vpad,R4.R3.))P,(;.$3.Vm,VBUF,Vbs,)P,(<.$3.Vm,Vlo,(=.&40.Vsp,))P,(>.$3.(?.VR,)Vm,Vslo,(=.&40.Vsp,))P,(10.$3.Vm,)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VPP,+8.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VSIGB,+18.)P,(11.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)Vm,VBUF,(13.(14.(0.&8.)Vbs,)))(15.$3.(?.VR,)(12.$3.VR,VHIA,Vh,)(16.$3.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VSIGB,VP,VEND,Vlo,Vslo,Vpad,Vm,)(17.(18.Vra,Vsp,Vgp,Vtp,R19.R18.R17.Vs0,Vs1,(8.&40.VPP,)(8.&40.VEND,)(8.&40.VSIGB,)R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(8.&40.$19.)Vfc,(1:.(0.&40.))Vm,(1;.$3.)))")
(* [comment removed for export] *).
  Proof.
  intros until q0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_PKCS7_GETSIG.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  unfold buf_cells in HSG.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. intros EGOT ELO EHI EGSB.
  carve_frame 96%nat ST.
  (* [comment removed for export] *)
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 167%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64);
                  [ exact HHc | exact LFB | clear; lia | clear; lia | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); exact ST1
                  | exact LOS | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SLO3 SP1; lia
                  | rewrite (unsigned_lit sp1) by (clear - SP1 SPR SLO LOS ALO ACV; lia); clear - SP1 TOP; lia
                  | assumption | exact TPV | reflexivity ])
      end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
        replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
        replace (Z.to_nat (64 * 2 ^ 0)) with 64%nat in FRM by reflexivity.
        replace (64 * 2 ^ 0) with 64 in FRSH, HH1 by reflexivity.
        cbn [zcells] in FSH.
        zstep. zstep. zstep.
        zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        (* [comment removed for export] *)
        apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [24; 8; 24; 8]%nat) in FRM; [| reflexivity].
        cbn [mk_CB_cells app] in FRM.
        chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat FD G2.
        replace (FB + 24 + 8) with (FB + 32) in FD, G2 by (clear; lia). replace (FB + 32 + 24) with (FB + 56) in G2 by (clear; lia).
        lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
          destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
        (* [comment removed for export] *)
        lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
        replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in SPILL by (clear; lia).
        lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -80); rename ST2x into STK2 end.
        destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -80) (sp1 + 8) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
        cb8_to_c8 SLOT0 (@nil cell). rename SLOT0 into SLOT.
        (* [comment removed for export] *)
        assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
        pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
        assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
        assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
        pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
        pose proof (fresh_apart_client _ LB LF lo SIGB 24 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
        pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
        pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
        (* [comment removed for export] *)
        zstep.
        lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
        pose proof (hm_abase asegs R HIA h1 LB _ m4 ltac:(eassumption)) as AB3.
        eapply body_walk with (FB := FB) (spv := sp1) (s2v := FB) (sp1 := sp1) (LF' := (FB, 64) :: LF) (h1 := h1) (m0 := m).
        all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_pkcs7_getsig_spec : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_getsig ()) "PR,$1<.PHIA,(1=.$3.R1.)P,(1>.(?.R2.))P,(1?.$1.(20.R3.)$21.)P,(1?.$1.(22.R4.=)$23.)(24.$3.R5.R4.$19.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  unfold pkcs7_getsig_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
