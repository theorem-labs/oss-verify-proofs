(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P004326b45863c7cc 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P007d21820ee92ff0 0 6 0 1 58 1 61 1 80 1 100 1 101 1P00e56bed7d04285a 1 1 16 3 0 1 101 1 102 1 10 47 4 66 4 71 4 74 4 81 4 82 4 83 4 100 4 103 4 104 64P00fe0f0ff9e92894 1 2 32 3 0 1 101 1 104 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 105 1 106 1P01d3be7faacc26e5 0 3 0 1 48 1 63 1P0250c3f72abf2e6f 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P02f144f56047edde 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P0362059128482e71 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P0416663ca200837d 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P045ffcdeda568fd3 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P049ac30b55e66b7f 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P051e74a205f1749f 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P05618fcf84f6a8f6 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P058ce943cc8c66f5 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P059f93f6f77e0228 1 2 32 3 0 1 100 1 103 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 2 104 1 105 1P064c4ed5e36399cc 0 8 1 1 42 1 67 1 72 1 82 1 85 1 101 1 102 1P065648212b79035b 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P06f1d50949bf71fe 0 6 0 1 49 1 54 1 64 1 83 1 84 1P073dff1692051064 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P07544a22fa9d0c81 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P07d47af9df80d275 0 5 0 1 35 1 63 1 83 1 84 1P0820aa0e3448784a 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P089795834f2640c7 0 4 0 1 63 1 83 1 84 1P098d90f590de85b0 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P09afa590c9d3ead9 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P09b80248db4c5404 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P09e32b4412f050d5 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P0a5f770b7c42789f 0 5 0 1 35 1 63 1 83 1 84 1P0ab394f8f790db1b 0 5 0 1 35 1 63 1 83 1 84 1P0ad4635a7a204ac1 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P0bae4ed2ba97a6b8 0 5 0 1 35 1 63 1 83 1 84 1P0bbe3495350901d2 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P0c5b62cf2605abfa 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P0c70079f43b44a08 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P0c7be38c4a2c5e48 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P0d8780a02b35392a 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P0d8947548c3ce9a5 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P0dd01051c67d43db 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P0dda16215a2b7027 0 8 1 1 42 1 67 1 72 1 82 1 92 1 101 1 102 1P0e041349e6cf7a5a 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P0e51e2fc1ad3790c 0 4 0 1 63 1 83 1 84 1P0e61ebecbde5fcc7 0 7 0 1 41 1 66 1 71 1 81 1 100 1 101 1P0f4eeff06ff37e90 1 1 64 2 0 1 100 1 3 6 1 101 1 102 64P0faba23cf161156b 1 2 32 3 0 1 102 1 103 1 32 3 1 1 101 1 104 1 2 105 2 106 2P108df2799682f55c 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P10926c62d05f3c3a 0 6 0 1 49 1 54 1 64 1 83 1 84 1P10d76ab551d78335 0 5 0 1 35 1 63 1 83 1 84 1P10e635355213a321 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P10eacf464bca297a 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P10fde42fd56b19fe 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P118e0082dd501e53 1 2 32 3 0 1 101 1 104 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 105 1 106 1P11a05040d4fac7ab 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P11a17f81bb993e8c 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P121b77be5cc232d4 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P122973d4afde05e0 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P12549f4db1436182 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P1264b150aafe27b8 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P1288d55a0eaf4639 0 6 0 1 49 1 54 1 64 1 83 1 84 1P12a909f77a6b2478 0 6 0 1 49 1 54 1 64 1 83 1 84 1P138e75f1b3596ce4 0 6 0 1 49 1 54 1 64 1 83 1 84 1P13a07aaa62c74581 1 2 32 3 0 1 101 1 104 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 105 1 106 1P14055daa258ecf16 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P14454a564f42c637 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P14c5ab79500ddd4a 0 4 0 1 63 1 83 1 84 1P14ccac2ac0959cc0 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P14f7e2d1dee256e0 1 2 32 3 0 1 101 1 104 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 105 1 106 1P152c2c3e683c3492 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P155cf124e7448144 0 4 0 1 63 1 83 1 84 1P1580787d388b1197 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P15b2fdaddd75dbae 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P15d83add2d14aced 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P15ed302b205c6408 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P1600876ed7a32c77 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P16445694dbc8da9c 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P1656f64895a6201f 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P16e684f38353b236 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P16e997958fca4b32 0 5 0 1 35 1 63 1 83 1 84 1P17159981129b27bf 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P1717fbc0efa8b47f 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P171c57f2a7464f39 1 1 16 3 0 1 102 1 103 1 4 62 2 101 2 104 2 105 32P173a5ca4400e8d0c 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1754f000dcd9094d 0 5 0 1 35 1 63 1 83 1 84 1P17d9252027015ef3 0 8 1 1 42 1 67 1 72 1 82 1 87 1 101 1 102 1P1801204e9030b6f0 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1875974b109a5b1e 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P188fbfbe15e4d094 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P1893fbd669b194fa 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P1906bc952228e223 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P192d59a49957b024 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P19f5136773cc7bf5 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P1a1acaf687971247 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1a4b02f63e61ecc8 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P1a74bc325f40cf5d 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1a8310615dccb544 0 8 0 1 41 1 66 1 71 1 81 1 86 1 100 1 101 1P1b75696a1f7495f0 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P1bb3efc4ababaf7c 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P1c05fe91e25ee26e 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P1c21c89138e53937 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1c86273b57605156 0 6 0 1 49 1 54 1 64 1 83 1 84 1P1cd8b3287be0abf9 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P1d0af4684679e404 1 1 16 3 0 1 102 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 105 64P1d83228e5b7b9a29 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P1da5661cde7cb811 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P1dc337bc1fbf7a60 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1e972eded0ed904c 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P1ec42965f8ca8ee2 0 4 0 1 63 1 83 1 84 1P1eea329e4505062e 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P1effb1957b975216 1 2 32 3 0 1 100 1 103 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 2 104 1 105 1P1f1e7639dd3baf4e 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P1f2a895b75f684c0 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P1f5986be40eafba3 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P1f6fbcb2389b2b24 0 3 0 1 32 1 47 1P1f8ea71a956583fd 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P206b6dbc0cee162f 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P20d167f96e585149 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P20d2714cbe208c13 0 6 0 1 49 1 54 1 64 1 83 1 84 1P21168a49de698c5d 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P214078cb50d004f9 1 1 16 3 0 1 101 1 102 1 4 61 2 100 2 103 2 104 32P216375d063d36e45 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P21ab7e3f9e025674 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P220b57afbfdf961e 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P220be64481a39549 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P2231af7353b5ef6e 0 4 0 1 63 1 83 1 84 1P225bff2a8160c129 0 6 0 1 49 1 54 1 64 1 83 1 84 1P23075b931cf33516 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P23180fadd712bbf8 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P2360c724990bf2bc 1 1 16 3 1 1 27 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P23a25079cb3500f6 1 1 16 2 0 1 83 1 3 7 1 84 1 85 16P23e7bd6f2fd2855c 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P240f026751db1d91 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P24ef16da2e688e71 1 2 16 3 1 1 27 1 84 1 16 3 0 1 28 1 85 1 2 86 1 87 1P2511c4833aacea7d 1 1 16 3 0 1 102 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 105 64P25893a07b09fa3e1 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P25c6078fdacec732 0 4 0 1 63 1 83 1 84 1P260319a4d0b28de0 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P2627218fdb85f7aa 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P26784bf55cf9b9d6 0 6 0 1 49 1 54 1 64 1 83 1 84 1P26dc345bad5439b6 0 4 0 16 62 16 83 16 84 16P26eb395371887220 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P276181ac13099d10 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P276ec6649aa5f8bf 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P27f3123e88148830 1 2 32 3 0 1 100 1 103 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 2 104 1 105 1P281a0b8ad79a7d5a 0 6 0 1 31 1 61 1 80 1 100 1 101 1P2962533051cc4bcc 1 2 32 3 1 1 101 1 104 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 105 1 106 1P29e9a70915c003e5 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P2a20a5a45fa97a04 0 9 0 1 41 1 66 1 71 1 81 1 82 1 83 1 100 1 101 1P2a8dda09c8d3445e 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P2aa8749781c04205 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P2b03367b4076b1f2 1 1 64 2 5 1 100 1 3 0 1 101 1 102 64P2b645c87eed653ba 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P2bb6b1e47b702c35 0 5 0 1 35 1 63 1 83 1 84 1P2be687c6a8a366ca 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P2be9f416eb6bb257 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P2c001c9c81f460c7 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P2cf28409958c1c57 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P2d35bfd6c3ef85cb 0 5 0 1 35 1 63 1 83 1 84 1P2d6b9eecbf112794 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P2d86130e705d33d2 1 2 16 2 0 1 85 1 16 2 1 1 84 1 2 86 1 87 1P2d8a81636bdb31ce 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P2dc3e9003a8ed949 0 4 0 1 63 1 83 1 84 1P2ddeffd442d5e9cc 0 4 0 1 63 1 83 1 84 1P2ddf865fedde7662 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P2dfc2050295d1cfe 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P2f52b7c81a37f6de 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P2f654e6812cb9ea0 0 8 0 1 41 1 66 1 71 1 81 1 91 1 100 1 101 1P2fa70900f409d96d 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P2fdf4acdc26356a5 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P3099ee0716604001 0 6 0 1 49 1 54 1 64 1 83 1 84 1P30a8991343f9cf32 0 4 0 1 63 1 83 1 84 1P30c0e691c9ca510f 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P314096a3dbc65414 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P31a86c4b02e31109 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P31e7680e43a546d0 1 1 16 3 0 1 102 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 105 64P3220b935c6c63165 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P332f283350b3730e 0 4 0 1 63 1 83 1 84 1P33a2c283afd2877f 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P340ba14f882ad761 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P34ebc3a9d6dcc305 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P35204a1e4b91603b 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P354e5228e1cc80c9 0 6 0 1 49 1 54 1 64 1 83 1 84 1P355a4ca5dc62e270 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P35a8cf0897e29674 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P3609074869723426 1 1 16 3 0 1 102 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 105 64P3659ff3384aaec34 0 5 0 1 35 1 63 1 83 1 84 1P367d3a4e49c6c0f6 1 1 16 2 1 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P3693e41dc4216f57 0 6 0 1 66 1 71 1 81 1 100 1 101 1P36eff5db911f498d 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P37034a7f02d88f63 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P377efd68fd7b3e5b 0 5 0 1 35 1 63 1 83 1 84 1P37e88f2a99dc8977 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P388c83b5827fee44 0 6 0 1 49 1 54 1 64 1 83 1 84 1P38e36f7bb1d80596 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P390bf96ec57eb5b6 0 6 0 1 49 1 54 1 64 1 83 1 84 1P391a0863ca2ce264 0 6 0 1 49 1 54 1 64 1 83 1 84 1P39af04f6883146c7 0 7 0 1 49 1 54 1 64 1 74 1 83 1 84 1P3a617b6c4db5e8ee 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P3a6d34c8de1a92dd 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P3ab9bc185e434100 0 5 0 1 35 1 63 1 83 1 84 1P3ae40e78b3627ad0 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P3afedeccb71bdbd9 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1P3b421671a3c113d2 0 7 0 1 41 1 66 1 71 1 81 1 100 1 101 1P3c1aeed2c673e4be 0 5 0 1 35 1 63 1 83 1 84 1P3d0b1636a5ecaf75 0 5 0 1 35 1 63 1 83 1 84 1P3d7c5b67f39daadc 0 4 0 1 63 1 83 1 84 1P3dbcf88a8ed854b2 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P3e04c81ff6a91584 0 4 0 1 63 1 83 1 84 1P3e23672ed3e08ac3 0 4 0 1 63 1 83 1 84 1P3e305fa68d00127b 1 1 16 4 1 1 29 1 44 1 84 1 9 49 1 50 1 55 1 58 1 65 1 66 1 67 1 85 1 86 16P3eb19af663e04c78 0 7 1 1 50 1 55 1 65 1 75 1 84 1 85 1P3f12a957b6801d91 0 7 0 1 49 1 54 1 64 1 69 1 83 1 84 1P3f302c0abcbeeb1e 0 7 1 1 50 1 55 1 65 1 70 1 84 1 85 1P3f3b6fcebb16c31c 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P3f6f8854962822a0 0 7 1 1 50 1 55 1 65 1 68 1 84 1 85 1P3fa79f0554ad6ed6 0 10 2 1 51 1 56 1 57 1 59 1 66 1 67 1 68 1 85 1 86 1P3fecccfca6fc25d3 0 8 0 1 49 1 54 1 64 1 65 1 66 1 83 1 84 1N0016fcf2b8b049cfN003dc90316c5fbb4N004bea42b0464ee1N015bde59473c06b6N01d7132552036a22N021bbad100b53d11N02aa9295be4dc326N04a4b65e948b6ddbN04ea44e2a6005df3N05bf75eab4f1bcfdN060dfc610b0f2144N0770c6c4793f65d7N086e10729da9dd4cN08a8fd25758b9c4aN0a94ba439dcac3ccN0ad75a6c32371035N0b6545062a1d69cfN0b8aa06ba67b9ddfN0be5ebd86d16b28fN0d0a488a9fbd999aN0d28a2eba53c199fN0db5285817cc2fd4N0e111b272663f253N0e962cf73e017ee6N0ecd25bd8a3e6f83N0f50e12096c45597N0fb4daf8fb995ac7N1004614330bd7c1dN10279e7c517dcbe6N10c54915398118a7N10e1e71582711a75N1114ca4ef200677eN11abd28f5da6e068N11eb1afb93eb8327N11ecf8cc2f432fedN130077a3307a93dbN1410f9b77b7bfc52N149a01b672253cdaN14bd9e443c802f22N15b8d36883fc42c8N16b3ed2a6155cc23N173008ed8379e8e8N1836e69a22c0bb9fN192de655de1ec567N199f6d0d4daf551eN19c75af3110ab198N1afd330251eae028N1c25be95c7a676e5N1cbd811ad004be8eN1dd7865f27cde4b0N1e506f62404781c6N1ebed7656d9d654dN1fe88d872d41b334N210d93d8e0565e47N21d5523c0a25f5faN21fb50a83cfd17a0N22045c414bd23d06N225c039f0e3d7049N246498fe2b906d3eN25013221e3a85eb2N251f944978d6e0c7N2540d3e37d5af676N25646b9b2d221dcaN261a64f2ed099a73N2630ac2efa4f48eeN2858bd79c9fd2b31N28d1a32a03a269ccN2a364ddbaf304f4fN2a71bc3195c088c5N2c512e16e0fc1465N2ceb0b68dedb6edfN2d0981f3b26d35bcN2e6454d8b7fa7ea3N2e9fb597b104b004N2ed589bff4c4e106N2fbd4e2dd09aaf15N2fd11b06744b49b7N315f81e8a922c4d4N31a40eb3b40a4a4fN33a57bfaffa697eeN349b8786d404fb59N354460745bff1284N35e0a2b58bc1c761N36751cbe296f0fcdN385dda483b04f859N3894785640b28b5dN3916ef00309bd6f1N39310f49aeb66cdbN396967621be6df12N3ab33498b73cf56cN3b9ac2a8f7e74614N3daf2a5c7596d0dcN3dc301f3754dfcfeN3e0ca37090352b3eN3f39323d71a263c9"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_pkcs7_signers_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Spec.RepCrt.signer_cells"; "OSSVerify.KrLib.Spec.Rep.buf_cells"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.ARt.sshad"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "OSSVerify.KrLib.A.A_pkcs7_parse_A.A_PKCS7_GETSIGNERS"].


Definition A_WFREE : Z := 0x68f08.                (* [comment removed for export] *) (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis CALLOC : arl_calloc R = A_WCALLOC.
  Hypothesis FREE : arl_free R = A_WFREE.
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  Variables (PHIsi : Z -> Z) (FFRsi : Z -> Z -> Z) (CNTsi : Z -> Z) (STKsi : Z).
  Hypothesis SIGNER : pkcs7_signer_stmtA asegs R HIA PHIsi FFRsi CNTsi STKsi A_PKCS7_SIGNER.
  Hypothesis PHIsi_mono : forall n n', 0 <= n <= n' -> 0 <= PHIsi n <= PHIsi n'.
  Hypothesis FFRsi_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRsi n d <= FFRsi n' d.
  Hypothesis CNTsi_mono : forall n n', 0 <= n <= n' -> 0 <= CNTsi n <= CNTsi n'.
  Hypothesis STKsi0 : 0 <= STKsi.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55853786883.20000003S1R". (* [comment removed for export] *)
  Let NRT : arl_need_malloc R <= arl_need_rt R /\ arl_need_free R <= arl_need_rt R.
  Proof. unfold arl_need_rt. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition STKs : Z := 176 + Z.max (Z.max STKsi 16) (Z.max (arl_need_smalloc R) (arl_need_rt R)).

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (PP P END BUF SIG DALG lo slo d : Z) (bs : list byte) (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF <= LFMAX_CRT + 1)%nat.
  Hypothesis HPP : rw_cells asegs m PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis HBY : bytes_at asegs m BUF bs.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis B30 : n < 2^30.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis HSG : rw_cells asegs m SIG (signer_cells 0 0 sj).
  Hypothesis ALS : SIG mod 8 = 0.
  Hypothesis SG0 : 0 < SIG.
  Hypothesis CWS : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) SIG SIGNER_SIZE.
  Hypothesis SGLO : SIG + SIGNER_SIZE <= lo.
  Hypothesis DSB : SIG + SIGNER_SIZE <= BUF \/ BUF + n <= SIG.
  Hypothesis HDA : rw_cells asegs m DALG (buf_cells dtg dpad dlen dq).
  Hypothesis ALD : DALG mod 8 = 0.
  Hypothesis DA0 : 0 < DALG.
  Hypothesis CRDA : client_range L (LB ++ fdata LF) lo DALG 24.
  Hypothesis DALO : DALG + 24 <= lo.
  Hypothesis Q1 : BUF <= dq. Hypothesis Q2 : 0 <= dlen. Hypothesis Q3 : dq + dlen <= BUF + n.
  Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
  Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
  Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKs.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis NDL : List.NoDup (map fst LB).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_pkcs7_cinfo.A_UAR_GOT, A_fuzz_entry.A_UAR_GOT in UARG; unfold A_SMALLOC_0 in SM0; unfold STKs in SLO; unfold SIGNER_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSH0 :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_A ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lx1,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La0,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)Lk0,(5.&40.)(1.(5.&40.)Lk8,(5.&40.)(1.(5.&40.)Lk16,(5.&40.)(1.(5.&40.)Lk24,(5.&40.)(1.(7.(5.&8.))Lj32,(7.(5.&8.))(8.(9.$0.R1<.(:.(;.R17.(<.&40.R1:.)Vgp,Vtp,R16.R15.R14.Vsp,(<.&40.R1:.)R13.(<.&40.VEND,)R12.R11.R10.R?.R>.R=.(<.&40.R1;.)(<.&40.(=.(>.VR,)))(<.&40.(?.R1;.+20.))(<.&40.VSIG,)(<.&40.VPP,)Vs7,(<.&40.VDALG,)(<.&40.R1;.)(<.&40.(?.(10.R1;.+3.)(=.(>.VR,))))Vs11,R<.R;.R:.R9.)VF,(<.&40.+9843<.)Vfc,(11.(5.&40.))R18.(12.$4.)))(8.(8.(13.(14.(15.&40.Vsp,)+;0.)R1:.)(13.R1:.(14.(15.&40.Vsp,)+:0.)))(8.(9.$2.(16.R1:.+20.)=)(8.(17.$4.VR,VHIA,R19.VLB,(18.(19.$2.$2.)(1:.$2.$2.R1;.+40.)VLF,)R18.)(8.(9.P,$2.Sp(1;.$4.VR,VHIA,R19.)(1;.$4.VR,VHIA,Vh,))(8.(9.$2.(1<.$4.VR,VHIA,R19.)(1<.$4.VR,VHIA,Vh,))(8.(9.$2.(1=.$4.VR,VHIA,R19.)(1=.$4.VR,VHIA,Vh,))(8.(9.$2.(1>.$4.VR,VHIA,R19.)(1>.$4.VR,VHIA,Vh,))(8.(9.$2.(1?.$4.VR,VHIA,R19.)(1?.$4.VR,VHIA,Vh,))(8.(9.$2.(20.$4.VR,VHIA,R19.)(20.$4.VR,VHIA,Vh,))(8.Pmo,$21.(22.(23.$4.VR,VHIA,R1:.R1.)(23.$4.VR,VHIA,Vh,R1.))(8.(9.$2.(16.R1;.+40.)=)(8.(24.VR,VLB,VLF,R1;.+40.)(8.(25.$4.R18.R1;.(18.$26.(27.R8.)(18.$26.(27.R7.)(18.$26.(27.R6.)(28.$26.)))))(8.(25.$4.R18.(?.R1;.+20.)(18.$26.(27.(<.&40.=))(28.$26.)))(8.(25.$4.R18.(?.(10.R1;.+3.)(=.(>.VR,)))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.=))(18.$26.(29.(<.&8.+?3.))(18.$26.(29.(<.&8.+?3.))(18.$26.(29.(<.&8.+?3.))(28.$26.))))))))))(8.(25.$4.R18.(?.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R18.R1:.(18.$26.(27.R5.)(18.$26.(27.R4.)(18.$26.(27.R3.)(18.$26.(27.R2.)(18.$26.(2:.#10.R1.)(18.$26.(27.(<.&40.R1;.))(28.$26.))))))))(8.(2;.$4.R18.(?.R1:.+38.)(?.(15.&40.Vsp,)-68.))(8.(2;.$4.R18.Vlo,R1:.)(8.(2<.$4.R18.)(8.(25.$4.R18.VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))(8.(25.$4.R18.VSIG,(2=.==Vsj,))(8.(25.$4.R18.VDALG,(2>.Vdtg,Vdpad,Vdlen,Vdq,))(8.(2?.$4.R18.VBUF,Vbs,)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R18.VPP,+8.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R18.VSIG,+<8.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R18.VDALG,+18.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R18.VBUF,(31.(32.(5.&8.)Vbs,)))(8.(33.(13.(?.R1;.+40.)VPP,)(13.(?.VPP,+8.)R1;.))(8.(33.(13.(?.R1;.+40.)VSIG,)(13.(?.VSIG,+<8.)R1;.))(8.(33.(13.(?.R1;.+40.)VDALG,)(13.(?.VDALG,+18.)R1;.))(8.(33.(9.$2.(31.(32.(5.&8.)Vbs,))=)(33.(13.(?.R1;.+40.)VBUF,)(13.(?.VBUF,(31.(32.(5.&8.)Vbs,)))R1;.)))(8.(34.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(28.$35.)Vm,R18.)(36.$4.(>.VR,)R18.Vslo,(15.&40.Vsp,)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 NDL; try lx_pin1 Q3; try lx_pin1 Q2; try lx_pin1 Q1; try lx_pin1 ALD; try lx_pin1 ALS; try lx_pin1 B30; try lx_pin1 B5; try lx_pin1 B47; try lx_pin1 ALP; try lx_pin1 sj; try lx_pin1 dq; try lx_pin1 dlen; try lx_pin1 dpad; try lx_pin1 dtg; try lx_pin1 bs; try lx_pin1 d; try lx_pin1 P; try lx_pin1 mo0; try lx_pin1 NRT; try lx_pin1 STKsi0; try lx_pin1 CNTsi_mono; try lx_pin1 FFRsi_mono; try lx_pin1 PHIsi_mono; try lx_pin1 SIGNER; try lx_pin1 CNTsi; try lx_pin1 FFRsi; try lx_pin1 PHIsi; try lx_pin1 GETTAG; try lx_pin1 FREE; try lx_pin1 CALLOC; try lx_pin1 HMND; try lx_pin1 DIMG.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0250@D10637083020.195D10639329459.119D14196765248.195D18512717141.196D18514816885.120D18607476203.163D2457697672.194 D3162359811.195 D32458983507.194D3254889317.162 D32604263327.197D3267764854.163 D3385912464.193 D36106837486.195D42574804762.196D43510757705.196D45254614292.196D45702202657.193D46793042006.119D46795284841.195D50254960491.164D51038213418.164D55346665922.164D55346665922.165D55346665922.166D560907438.121  D60098777666.120D60109264994.196D60109265005.195D60111245650.119D61005654077.196D61016138269.120D62011770180.197D62011770188.121D65008438061.194D68409210579.193D6897083606.193 L10775412921.167L10837002389.2  L12654381620.1  L15756354262.7  L17193996438.1  L17607390836.169L1832968857.11  L19548981073.169L19980016842.11 L21980071943.1  L24524441946.121L26892418956.1  L27729706458.190L29738741675.1  L31170831519.164L32508069537.0  L33483560980.12 L33485826452.1  L35653441506.10 L38308634325.0  L39076636629.0  L39280637297.0  L39332637397.0  L40226756952.1  L40228640085.0  L43055369633.137L45363093875.200L48117620909.100L48119718058.165L48119718061.164L49130057368.11 L50790731766.10 L51038230838.191L53537894342.3  L54437681876.8  L57355539152.167L57355539152.174L58790154276.11 L59308634497.16 L60098763854.6  L61437265048.2  L67922604617.0  L6910010088.164 L7040749983.122 L7715476710.139 L9356559645.15  P1056307012.164 P28348577804.164P54301534716.164Q10533598597.123Q10594483354.201Q11276122434.202Q11288706168.123Q13345046842.123Q13349241856.202Q1530342990.164 Q23216651711.201Q23937998252.123Q23937998260.125Q31021924279.161Q31158247845.200Q31158247869.204Q31170831519.202Q31599749226.123Q31603944784.202Q32440833928.200Q36104740330.202Q38248895665.126Q40271359350.164Q41137788007.123Q41150370141.202Q42439168719.161Q42439382255.127Q42441479404.206Q43880146029.126Q45252517151.202Q47241206720.123Q48119718060.201Q48132302231.200Q50796826103.164Q56533317808.201Q59310664043.123Q59310664043.200Q59323247696.201Q59323247697.202Q59865520176.127Q59867617331.206Q6192914196.161 Q62022254700.125Q62022254708.123Q64681502661.206Q64683599814.127Q6897428426.204 Q6897428434.200 Q6910010088.202 Q9350548487.145 00000^01L01M02<02j02k02l02m03X03Y04K04L04M04N04O04P04Q05<05j06X06Y07E07F07G08;08o09d0:V0;H0<=0<l0=Z0>E0?30?^0?_0@J0A=0AE0AJ0AX0A]0BR0B[0CP0Cn0D20Di0Dm0EX0E\0F<0F=0F>0F?0F]0F^0F_0F`0Fa0Ff0Fg0HT0ID0JE0K40Kc0Kl0LG0M60MB0M]0M^0NW0O20OD0ON0OV0OW0P70Pb0QP0R;0Rg0ST0TB0U00UP0UQ0UR0US0UT0V<0V\0WY0XJ0Y90YY0Z90ZY0ZZ0Z[0Z\0Z]0[K0[n0[o0\00\V0]J0^00^a0^b0_Q0`@0`o0aZ0a[0a\0a]0a^0a_0a`0aa0bB0bm0cX0dK0eL0el0fL0fl0gUS1R5STKsi2LF2sp2PP2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABFS1R5STKsi2LF2sp3SIG2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABFFFS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBFS1R3HIA5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2h12FBFFFFFFS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2sp2PP2bs3LFB4lxHn3sp13H264LFB'2FBFS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H243H264LFB'FFS1R5STKsi2LF2sp4DALG2bs3LFB4lxHn3sp13H264LFB'3x142HxS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS3PPB3SGB3DABS1R5STKsi2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2lo2bs3LFB3LOS4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3LOS3PPB3SGB3DABS1R5STKsi2LF2sp3SIG2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBFS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS1R5STKsi2LF2sp3slo2bs3LFB4SLOS3ALO4lxHn4LFB'2FB2F1S3BUF2bsS3BUFS1R2lo3LOS3ALOS3sp1S1R5STKsi2LF2sp2bs3LFB3SPR4lxHn3sp13H264LFB'2FB2F02F8S1R5STKsiS1R5STKsi2LF2sp2bs3LFB3SPR4lxHn3sp13H264LFB'2FB2F02F8S1R3HIA5STKsi1h2sp3TOP3sp13SP1S2spS1R5STKsi2LF2sp2bs3LFB3SPA3SPR4lxHn3sp13H223H233H243H26S2spS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FBS2FBS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBSFFS1R3HIA5STKsi1h2sp2lo3TOP4HTOPSSSSS3sp1SS1R3NS15STKsi2LF2sp2PP1P3END3BUF3SIG4DALG2lo2bs3LFB3PP02B12B22B33DPB3SG03DSB3DA02D12D22D33SLO3SPR3PPB3SGB3DABS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H264LFB'2FB1c2HcS1R3NS15STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3SLO3LOS3ALO3PPB3SGB3DABS1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R5STKsiS1R3NS15STKsi2sp2lo3SLO3LOSS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H243H264LFB'2FBS2sp3sp13SP1S1R5STKsi2sp2lo3SLO3sp13SP1FS1R5STKsi2LF2sp2bs3LFB3ACV3SPR4lxHn3sp13H264LFB'2FB2F02F1S1R5STKsi2sp2lo3SLO3sp13SP1S1R5STKsi2FB2F02KbS1R2lo3LOSS2LF3LFBSS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2sp2bs3LFB3SPR4lxHn3sp13H223H26S1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R5STKsi2LF2PP2lo2bs3LFB4PPLO4lxHn3sp14LFB'S1R5STKsi2LF3SIG2lo2bs3LFB4SGLO4lxHn3sp14LFB'S1R5STKsi2LF4DALG2lo2bs3LFB4DALO4lxHn3sp14LFB'S1R5STKsi2LF2sp2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBFFFFS1R5STKsi2LF2sp2bs3LFB4lxHn3sp13H244LFB'S1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG2bs3LFB3TOP4HTOP3PPB3SGB3DABS1R3HIA5STKsi1h2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R3HIA5STKsi1h2LF2sp2bs3LFB3TOP4HTOP4lxHn4LFB'S1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBFFFFS1R5STKsi2LF2PP3SIG4DALG2lo2bs3LFB3PPB3SGB3DABS1R3HIA5STKsi1h2LF2bs3LFB4lxHn4LFB'FFS1R5STKsi2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R5STKsi2LF2PP3SIG4DALG3slo2bs3LFB4SLOS3PPB3SGB3DABS1R5STKsi2LF3slo2bs3LFB4SLOS4lxHn4LFB'S1R5STKsi2LF2sp2PP3SIG4DALG2lo2bs3LFB3PPB3SGB3DABFS1R5STKsi2LF2PP3SIG4DALG2bs3LFB3ALO3PPB3SGB3DABS1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS3ALO4lxHn4LFB'S1R5STKsi2LF2sp2lo2bs3LFB3SLO3LOS4lxHn4LFB'FFFFFFFS1R5STKsi2LF2bs3LFB4lxHn3sp14LFB'S1R5STKsi2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R5STKsi2LF2PP3SIG4DALG2bs3LFB3PPB3SGB3DABS1R3HIA5STKsi1h2LF2sp3slo2bs3LFB3TOP4HTOP4lxHn4LFB'S1R3HIA5STKsi1h2LF2sp2PP3SIG4DALG3slo2bs3LFB3TOP4HTOP3PPB3SGB3DABS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2bs3LFB4lxHn4LFB'2FBS1R5STKsi2LF2bs3LFB4lxHn3sp13H253H264LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS D3 D2 D1 DALO CRDA DA0 HDA DSB SGLO CWS SG0 HSG DPB B3 B2 B1 BIN HBY PPLO CWP PP0 HPP LFB STKsi NS1 SM0 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(36.$4.(>.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VSIG,+<8.)P,(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VDALG,+18.)P,(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VBUF,(31.(32.(5.&8.)Vbs,)))(37.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)$38.(:.(;.Vra,Vsp,Vgp,Vtp,R13.R12.R11.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VSIG,)(<.&40.VDALG,)R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(<.&40.$39.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH ST SS MI OPP OSG ODA OBUF.
  unfold A_PKCS7_GETSIGNERS.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 TOP HTOP; lia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) [] HH ltac:(clear - LOS SLO NS1; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add length] in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSG) as SGB.
  cbn [cells_size csize Nat.add length signer_cells] in SGB.
  pose proof (rw_cells_bound _ _ _ _ HDA) as DAB.
  cbn [cells_size csize Nat.add length buf_cells] in DAB.
  destruct (hm_apart asegs R HIA h _ _ _ HH) as [BR _].
  rewrite Forall_forall in BR.
  destruct (BR _ ltac:(apply in_or_app; left; exact BIN)) as (_ & _ & BCE & BIMG).
  cbn [fst snd] in BCE, BIMG.
  clear BR.
  (* [comment removed for export] *)
  pose proof (conj HBY (conj HPP (conj HSG (conj HDA (conj OPP (conj OSG (conj ODA (conj OBUF I)))))))) as EBOX.
  clear OPP OSG ODA OBUF.
  carve_frame 160%nat ST.
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
  lx_hide1 EBOX.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52984] [] 285%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -160) ST ltac:(clear - SP1 SLO NS1; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 338308) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (unfold LFMAX_CRT in LFB; clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | clear - SLO SP1 TOP NS1; lia
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). kland Kb.
          rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      change (64 * 2 ^ 0) with 64 in *. change (8 * 2 ^ 0) with 8 in FSH. change (Z.to_nat 64) with 64%nat in FRM. change (Z.to_nat 8) with 8%nat in FSH.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ SIG 200 FB 64 FRSH CWS ltac:(clear; lia) ltac:(clear; lia) LOS) as APSG.
      assert (APD : FB + 64 <= DALG \/ DALG + 24 <= FB).
      { eapply (fresh_apart_client R LB LF lo DALG 24 FB 64 FRSH CRDA); [clear; lia| clear; lia| clear - ALO LOS; lia]. }
      assert (APB : n = 0 \/ FB + 64 <= BUF \/ BUF + n <= FB).
      { destruct (Z.eq_dec n 0) as [E0|NE]; [left; exact E0| right]. destruct FRSH as (_ & _ & _ & F3'). apply F3'. apply in_or_app. left. exact BIN. }
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
      lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
      destruct (stk_split asegs m3 sp1 (sp1 + 56) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
      destruct (stk_carve asegs m3 sp1 (sp1 + 56) 56 STlo ltac:(clear; lia)) as [_ [jrs RSL]]. clear STlo.
      replace (sp1 + 56 - Z.of_nat 56) with sp1 in RSL by (clear; lia).
      apply (rw_cells_split_CB asegs m3 sp1 [] 56 jrs [] [8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity]. cbn [mk_CB_cells app] in RSL.
      cb8_to_c8 RSL (@nil cell).
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 RSL [c1] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 RSL [c1; c2] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 RSL [c1; c2; c3] end.
      lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5] end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 8; 16; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      chunk_split FREST 1%nat FLNK FRMb. chunk_split FRMb 1%nat G4 FRMc. clear FLNK FRMc.
      lazymatch type of G4 with rw_cells _ _ ?a _ => replace a with (FB + 32) in G4 by (clear; lia) end.
      cb8_to_c8 G4 (@nil cell).
      cbn [zcells] in FSH.
  (* [comment removed for export] *)
  lx_hide1 EBOX. lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x9843c] [] 285%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  (* [comment removed for export] *)
      destruct EBOX as (HBY' & HPP' & HSG' & HDA' & OPP & OSG & ODA & OBUF & _).
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES) as HPF;
        assert (CRP : client_range L (LB ++ fdata LF) (bv_unsigned sp) PP 8) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWP)| exact PPLO]);
        assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) SIG 200) by (eapply client_range_lower; [exact (client_range_of_w L _ _ _ _ _ CWS)| exact SGLO]);
        assert (CRD' : client_range L (LB ++ fdata LF) (bv_unsigned sp) DALG 24) by (eapply client_range_lower; [exact CRDA| exact DALO]);
        assert (CRB : client_range L (LB ++ fdata LF) (bv_unsigned sp) BUF n) by (eapply client_range_block; [apply in_or_app; left; exact BIN| clear; lia| clear; lia]);
        assert (OPP1 : aobj asegs AL CS mx PP 8);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OPP | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRP| clear; lia] ] |];
        assert (OSG1 : aobj asegs AL CS mx SIG 200);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OSG | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRS| clear; lia] ] |];
        assert (ODA1 : aobj asegs AL CS mx DALG 24);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact ODA | intros xq Hxq; eapply hcs_below_top; exact Hxq | right; split; [exact CRD'| clear; lia] ] |];
        assert (OBUF1 : aobj asegs AL CS mx BUF n);
        [ eapply presA_aobj0; [ exact CSOK | exact HPF | exact OBUF | intros xq Hxq; eapply hcs_below_top; exact Hxq
                              | destruct (Z.eq_dec n 0) as [E0|NE]; [left; rewrite E0; clear; lia| right; split; [exact CRB| clear; lia]] ] |];
        assert (HB1 : bytes_at asegs mx BUF bs);
        [ eapply presA_bytes_at0; [exact HPF| exact HBY'| destruct (Nat.eq_dec (length bs) 0) as [E|NE]; [left; exact E| right; split; [exact CRB| exact I]]] |];
        assert (HPP1 : rw_cells asegs mx PP [C8 (Z_to_bv 64 P)]);
        [ eapply presA_rw_cells; [exact HPF| exact HPP'| exact CRP| exact I] |];
        assert (HSG1 : rw_cells asegs mx SIG (signer_cells 0 0 sj));
        [ eapply presA_rw_cells; [exact HPF| exact HSG'| cbn [cells_size csize Nat.add length signer_cells]; exact CRS| exact I] |];
        assert (HDA1 : rw_cells asegs mx DALG (buf_cells dtg dpad dlen dq));
        [ eapply presA_rw_cells; [exact HPF| exact HDA'| cbn [cells_size csize Nat.add length buf_cells]; exact CRD'| exact I] |];
        clear HPF end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [assumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      repeat match goal with |- _ /\ _ => split end;
        first [ eassumption | exact PRES
              | lazymatch goal with
                | |- _ \/ _ => first [exact APP | exact APSG | exact APD | exact APB]
                end
              | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
