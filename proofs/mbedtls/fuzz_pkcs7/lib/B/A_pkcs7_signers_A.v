(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts A_mpi_stmtA A_pkcs7_parse_A A_pkcs7_signer_stmt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000918eadec15168 1 11 64 2 9 1 101 1 64 2 11 1 101 1 64 2 12 1 102 1 64 2 49 1 102 1 16 3 0 1 102 1 103 1 16 3 1 1 101 1 104 1 16 2 3 1 103 1 16 2 6 1 104 1 16 2 30 1 103 1 16 2 100 1 103 1 16 3 2 1 42 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 109 64P005c0d8372b360db 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P0067b1e33c288fd7 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P00c51dd7d59f27c0 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P011a7a39e618eef5 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P01912672a8e802aa 1 6 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 3 0 1 33 1 100 1 32 7 0 1 66 1 71 1 79 1 81 1 91 1 100 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 8 0 1 41 1 66 1 71 1 81 1 91 1 100 1 101 1P0196447e5bb08914 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P023ace2f616c6770 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P025dda75382679d4 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P027909f210e803e8 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P02928a2be85a4cc0 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N02dfb4d4a7bf476aN034dc44ccf7d54fdP035b9118c7d5a478 1 12 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 16 3 0 1 101 1 102 1 16 2 2 1 102 1 16 2 5 1 103 1 16 2 29 1 102 1 16 3 62 1 101 1 102 1 16 2 99 1 102 1 32 4 61 1 100 1 103 1 110 16 32 3 30 1 103 1 107 16 512 5 30 16 41 16 101 16 102 16 103 16 4 61 1 100 1 103 1 107 16N036045e1f9ff4cbeN0383c826ecaf0815P03bfde62049dbdf2 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P03dd189235885684 1 5 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 6 0 1 66 1 71 1 79 1 81 1 100 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 7 0 1 41 1 66 1 71 1 81 1 100 1 101 1P042783bc4587bdf7 1 10 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 16 3 0 1 94 1 95 1 16 3 1 1 93 1 96 1 16 2 3 1 96 1 16 2 9 1 95 1 16 2 37 1 95 1 16 3 55 1 94 1 95 1 16 2 92 1 95 1 4 54 2 93 2 96 2 100 32P04319571609d3335 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P044b2c0e97f2678a 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P04e0ca54d94dbb15 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N0580ebf8a957c266N05b5c47f70a227a9P05b73bdbfb7f29ab 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P0661027ad0663e8c 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P06617d017f78b1bc 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P066da47661d4ec4a 1 7 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 1 1 36 1 101 1 32 3 0 1 88 1 102 1 32 7 1 1 67 1 72 1 80 1 82 1 87 1 101 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 8 1 1 42 1 67 1 72 1 82 1 87 1 101 1 102 1N06f4dd4c3b585368P071838765caabcf0 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1N0776db209a5f2a86N07c8403098c5e1aeP07e38552ef430c29 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N07f28da77875c156N08fdb07c34b311e5P09799ae33312fe00 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P097d8d635ac885d2 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1N098591255fda40c5P09932ef4374f607d 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P09d6f30b4d503960 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P09dcf4b1d7900f4f 1 6 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 32 3 0 1 40 1 92 1 32 7 0 1 58 1 63 1 71 1 73 1 83 1 92 1 32 9 48 1 57 1 58 1 63 1 66 1 73 1 74 1 75 1 93 1 8 0 1 48 1 58 1 63 1 73 1 83 1 92 1 93 1P09e0f76778db7e14 1 7 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 1 1 34 1 101 1 32 3 0 1 93 1 102 1 32 7 1 1 67 1 72 1 80 1 82 1 92 1 101 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 8 1 1 42 1 67 1 72 1 82 1 92 1 101 1 102 1N09fddc583e1d49dcN0a6c54ac9fa2c3d6P0a853888d02aa390 1 11 64 2 9 1 101 1 64 2 11 1 101 1 64 2 12 1 102 1 64 2 49 1 102 1 16 3 0 1 102 1 103 1 16 3 1 1 101 1 104 1 16 2 3 1 103 1 16 2 6 1 104 1 16 2 30 1 103 1 16 2 100 1 103 1 16 3 2 1 42 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 109 64P0a879777ef67e314 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P0a9ed93490486dab 1 10 64 2 8 1 100 1 64 2 10 1 100 1 64 2 11 1 101 1 64 2 48 1 101 1 16 3 0 1 101 1 102 1 16 2 2 1 102 1 16 2 5 1 103 1 16 2 29 1 102 1 16 2 99 1 102 1 16 3 1 1 41 1 102 1 10 47 4 66 4 71 4 74 4 81 4 82 4 83 4 100 4 103 4 108 64N0add23032c28f850P0b3090af2c87dc9d 0 3 0 1 50 1 68 1P0b89f3205a818524 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P0bf9928baa974fa6 1 4 16 2 2 1 100 1 16 2 5 1 101 1 16 2 29 1 100 1 16 2 99 1 100 1 6 0 1 66 1 71 1 81 1 100 1 101 1N0bff24696d7a32a8P0c05295e45eaafca 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P0c20b48ee5c9e9b1 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P0c47ac53422cb20d 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P0caf4658a182e943 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P0cec8700b334875a 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1N0cefc9a843bf333eN0d259706acd990a0N0d3b81053a601782N0d4edbca8bfc1774P0d96d6430117a6c9 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1N0de981a70c79df68P0e1772ed63e4ecba 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P0e1b57f28f818734 1 6 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 32 9 49 1 58 1 59 1 64 1 67 1 74 1 75 1 76 1 94 1 32 3 0 1 31 1 94 1 32 3 1 1 30 1 93 1 2 98 1 100 1P0e425c1db8056653 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1N0e63888cab19583fP0e99a52bfb4bc1b9 1 3 16 2 0 1 71 1 16 2 23 1 71 1 16 2 70 1 71 1 3 7 1 72 1 73 16P0efdfdb1816fe837 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1N0f5b485b78923338P0f92d9320e9f3b5b 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N0fa993aae433cdd3P105d1caebdb8efe0 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P10c8932be43cd859 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1N10f2f64e2d13dd9dN11221bd2e07a4f9aP113b527777dcfe4a 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P11cb621bf0b1f349 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P11ddb0fdb7a4982c 1 7 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 32 3 1 1 45 1 93 1 32 3 0 1 78 1 94 1 32 7 1 1 59 1 64 1 72 1 74 1 77 1 93 1 32 9 49 1 58 1 59 1 64 1 67 1 74 1 75 1 76 1 94 1 8 1 1 49 1 59 1 64 1 74 1 77 1 93 1 94 1N127fec31f86f7ffbP12ba3a5888f3e158 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1N12bb303663b56108N12bf73f3e148a113P12d264a38c5df8ce 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 16 50 16 71 16 72 16P12d40afd6276934e 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1N12e957401b8ad45dP13161697d7ac0089 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P1339d882c0eb518a 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N13753b3da07afe20P13830488b3c1becb 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P139ed3a6f80d48eb 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P13e8ae52ee5d3255 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1N140b79cc9392c66bN140d3ae38e0f8fc6P142ddfe9f9b6a2a6 1 5 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 32 6 0 1 58 1 63 1 71 1 73 1 92 1 32 9 48 1 57 1 58 1 63 1 66 1 73 1 74 1 75 1 93 1 7 0 1 48 1 58 1 63 1 73 1 92 1 93 1N14395364a6ecef7dP144a657249024537 1 5 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 32 8 0 1 58 1 63 1 71 1 73 1 74 1 75 1 92 1 32 9 48 1 57 1 58 1 63 1 66 1 73 1 74 1 75 1 93 1 9 0 1 48 1 58 1 63 1 73 1 74 1 75 1 92 1 93 1P148e4177ad8a72ea 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P14ab4df636fec5bd 1 6 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 32 3 0 1 42 1 92 1 32 7 0 1 58 1 63 1 71 1 73 1 78 1 92 1 32 9 48 1 57 1 58 1 63 1 66 1 73 1 74 1 75 1 93 1 8 0 1 48 1 58 1 63 1 73 1 78 1 92 1 93 1N14d841c711d1644fN14e01bd3fd38f0f7N14f37eeffe8e7063P151374b471a7c9ab 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N15602e0b40428c06P15bcc7a4111026fc 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P17344a7d4d02ac93 1 5 64 2 0 1 100 1 64 2 8 1 100 1 64 2 10 1 100 1 64 2 11 1 101 1 64 2 48 1 101 1 3 9 1 101 1 102 64P1764fbe62537483a 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1N17762f52ee9b9934P17af00f15dc70b4d 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P17ddfb6c2601bd23 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P18a632041f7a871c 1 9 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 102 1 103 1 32 3 1 1 101 1 104 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 2 108 2 109 2P18b55b4e7c37fcb4 1 12 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 3 0 1 100 1 103 1 64 2 8 1 102 1 64 2 10 1 102 1 64 2 11 1 103 1 64 2 48 1 103 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 64 3 59 1 101 1 107 32 2 2 104 1 113 1 2 107 1 113 1P18c3fa0fad55a42e 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P191388bbcb01b8d8 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P192c86201b9f6b40 1 12 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 3 0 1 100 1 103 1 64 2 8 1 102 1 64 2 10 1 102 1 64 2 11 1 103 1 64 2 48 1 103 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 64 3 59 1 101 1 107 32 2 2 104 1 113 1 2 107 1 113 1P192e147829837878 1 12 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 3 0 1 100 1 103 1 64 2 8 1 102 1 64 2 10 1 102 1 64 2 11 1 103 1 64 2 48 1 103 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 32 10 41 1 47 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 102 1 2 2 107 1 112 1 2 2 104 1 113 1 2 107 1 113 1P1930fad7667d80fc 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P1a8162e0ae5d18ba 1 5 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 8 0 1 66 1 71 1 79 1 81 1 82 1 83 1 100 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 9 0 1 41 1 66 1 71 1 81 1 82 1 83 1 100 1 101 1N1ab4f33c533188bbP1ae3bb68edfb57b5 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P1ae410eebb1d13a0 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N1b1614f3d70b7b11N1b48cafdd62c9c20P1b56fb4ac17bd638 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P1b75c5f1c35f6cf6 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N1b8f433a3743ba78N1c552761369d5595P1ce989a4f9f236a5 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N1cf40112d5ce6b9aP1d176e4111e5dddd 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1N1d7db85ff63436bdP1d8cb05d7a58a1e6 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P1dcbd2955ff4fc23 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1N1e3a195fc6950d92P1e75860b07814585 1 8 32 2 11 1 95 1 32 2 12 1 94 1 32 2 54 1 94 1 32 3 2 1 5 1 94 1 32 3 1 1 7 1 95 1 32 4 2 1 37 1 66 1 94 1 32 10 2 1 60 1 65 1 66 1 68 1 73 1 75 1 76 1 77 1 94 1 32 9 50 1 59 1 60 1 65 1 68 1 75 1 76 1 77 1 95 1 11 2 1 50 1 60 1 65 1 66 1 68 1 75 1 76 1 77 1 94 1 95 1P1ef3113d1cfd0c77 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P1f7bef742ca3653e 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P1f855e135d064870 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P1fc3ff41b51eddfd 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P1fcca022a1a439c4 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P20068165832dbdbf 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P2027edf98fdda3ef 1 13 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 101 1 104 1 32 3 1 1 102 1 103 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 2 108 1 114 1 2 2 105 1 115 1 2 108 1 115 1P20655aa9b4e21cbd 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P2088c0598fa7be03 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P20ab242690908fae 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1N20da363fcb86da38P20eb53d2982fc55b 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P20edb6717aa86922 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P20f62d5acc4d418b 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1N219365fb38e20181P22050686bac93b50 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P223eae05ebf18ba7 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N22484ceac522b448P2296c77a8cc9e199 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1N22dbaecbe94c5e60P22ff452d61e51926 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P22ffe56d0810d8f9 1 4 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 32 5 0 1 2 1 38 1 72 1 93 1 6 0 1 38 1 53 1 72 1 92 1 93 1P233c489bff7f2091 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P235057467dcddf88 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P236dde79bf8b4042 0 3 0 1 31 1 49 1P23b98c05d39351fb 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N240c9e568a7870e2P24b9feee0873c275 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P24ff958ccc4de1a6 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P2501312c9b6a5c8b 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P25054aa260080ff5 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N250aa4a67601b371P259022d303bc27fe 1 7 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 32 3 1 1 41 1 93 1 32 3 0 1 85 1 94 1 32 7 1 1 59 1 64 1 72 1 74 1 84 1 93 1 32 9 49 1 58 1 59 1 64 1 67 1 74 1 75 1 76 1 94 1 8 1 1 49 1 59 1 64 1 74 1 84 1 93 1 94 1N26135a4d31cc48deP2642f4fa0c12c255 1 9 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 16 3 0 1 93 1 94 1 16 2 2 1 95 1 16 2 8 1 94 1 16 2 36 1 94 1 16 3 54 1 93 1 94 1 16 2 91 1 94 1 4 53 2 92 2 95 2 99 32N269ef79f0128e715P26af81b0a9601a8e 1 6 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 32 9 49 1 58 1 59 1 64 1 67 1 74 1 75 1 76 1 94 1 32 4 0 1 51 1 69 1 94 1 32 4 1 1 32 1 50 1 93 1 2 98 1 100 1N26c966835192a4f4N27065068f75ebbcbP27a048fad0c31b88 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P27ab776af2c1a438 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P27f80ca8a81efb5b 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P27fd2df3b094d011 1 5 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 6 0 1 66 1 71 1 79 1 81 1 100 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 7 0 1 41 1 66 1 71 1 81 1 100 1 101 1N282963d0658dd898N287c7ddfded32b0eN29101387431904ebP292954d70c37c335 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P2978d049758a3266 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P298d5d3b21b6a101 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P29969e4679f8c3bb 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1N29cd9ff0bd4010b2P29edd659fe4c9c3e 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1N2a787f9730c70c82P2aeb6fd9cf471c99 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P2b1287f150fc441f 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P2b7ccc65c29320bc 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1N2b8f2845df1b7e5eP2b919d46188cdad4 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P2bdaaac2951c1f2d 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1N2c1e137f02ea0d72P2c89a2b29732f203 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P2d13fea6865a57cd 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P2d3db21ad1beda58 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P2d71ca51a5bd0a77 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P2de9cf60222fcfc0 1 6 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 3 0 1 35 1 100 1 32 7 0 1 66 1 71 1 79 1 81 1 86 1 100 1 32 9 41 1 65 1 66 1 71 1 74 1 81 1 82 1 83 1 101 1 8 0 1 41 1 66 1 71 1 81 1 86 1 100 1 101 1P2decf235e71b0290 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P2dfc9ffa16151913 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N2e56e0acb54cb5b5P2e621c5ad3258c88 1 13 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 101 1 104 1 32 3 1 1 102 1 103 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 64 3 60 1 102 1 108 32 2 2 105 1 115 1 2 108 1 115 1N2e66483d780198e8P2e738c72554ffef0 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P2ea1079368712c70 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P2eb43eb730c08a09 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1N2ebc30290381a43eP2ed5aee8300cbab0 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P2f1b5467e28229fa 1 13 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 101 1 104 1 32 3 1 1 102 1 103 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 2 108 1 114 1 2 2 105 1 115 1 2 108 1 115 1P2f1ecb2779d882cb 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P2f6b27fc4569bf31 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P2f8a6220e3b8183b 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1N2f9baf89b0d7cdf3P2fae859a4beb2d6c 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P3080d4b2d342138a 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N30c0963a2b1aa43bP30f8a12aeab6d929 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1N317f21df919f7cf6N319ba81a05045ea9N31c92047689d12abN31ed9e2bbe0a432eP323bbc8e35a62c8b 1 4 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 32 5 0 1 5 1 31 1 80 1 101 1 6 0 1 31 1 61 1 80 1 100 1 101 1P324cace3980d67e9 1 11 64 2 9 1 101 1 64 2 11 1 101 1 64 2 12 1 102 1 64 2 49 1 102 1 16 3 0 1 102 1 103 1 16 3 1 1 101 1 104 1 16 2 3 1 103 1 16 2 6 1 104 1 16 2 30 1 103 1 16 2 100 1 103 1 16 3 2 1 42 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 109 64P3296d0494be2283f 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P335ba5bdde265798 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P33903d002e40531e 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P33e4a62db2d704cf 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1P33fbbcdc3470a2e7 1 5 32 2 0 1 94 1 32 2 1 1 93 1 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 2 95 1 96 1N345a09b3317a9312P346d138db9b9ab94 1 3 32 2 9 1 93 1 32 2 10 1 92 1 32 2 52 1 92 1 5 0 1 53 1 72 1 92 1 93 1P3484902007d8c303 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1N351a8516c1b03600N3595a5ea0af05921P35cbcd4988480a68 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 28 1 72 1 16 6 38 1 43 1 53 1 63 1 64 1 73 1 7 1 1 38 1 43 1 53 1 63 1 72 1 73 1P36451f1f815d451f 1 11 64 2 9 1 101 1 64 2 11 1 101 1 64 2 12 1 102 1 64 2 49 1 102 1 16 3 0 1 102 1 103 1 16 3 1 1 101 1 104 1 16 2 3 1 103 1 16 2 6 1 104 1 16 2 30 1 103 1 16 2 100 1 103 1 16 3 2 1 42 1 103 1 10 48 4 67 4 72 4 75 4 82 4 83 4 84 4 101 4 104 4 109 64P3697901f5be1dee1 1 4 64 2 8 1 100 1 64 2 10 1 100 1 64 2 11 1 101 1 64 2 48 1 101 1 3 0 1 101 1 102 64N36c712192b4b63e1P36ee693a04e2eda6 1 7 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 1 1 38 1 101 1 32 3 0 1 86 1 102 1 32 7 1 1 67 1 72 1 80 1 82 1 85 1 101 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 8 1 1 42 1 67 1 72 1 82 1 85 1 101 1 102 1P36f4a5eb84f10ffc 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N3764f57fc181f362N376a0505cc312061N3790d15222898c7bP3793fd3cf31e4b47 1 3 32 2 1 1 100 1 32 2 3 1 101 1 32 2 60 1 100 1 6 0 1 58 1 61 1 80 1 100 1 101 1N379be17d47e7bd71P37a0ecd1c42af766 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P37b4f8de8f66d2ec 1 7 32 2 10 1 94 1 32 2 11 1 93 1 32 2 53 1 93 1 32 3 1 1 43 1 93 1 32 3 0 1 80 1 94 1 32 7 1 1 59 1 64 1 72 1 74 1 79 1 93 1 32 9 49 1 58 1 59 1 64 1 67 1 74 1 75 1 76 1 94 1 8 1 1 49 1 59 1 64 1 74 1 79 1 93 1 94 1N3818319f359bd931N38412de5b9ff1a89P389e9649eb7131eb 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1N38c03c42c5795830P38c5748f6e66edec 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1N38e296e3075dfd2bN3927f70fc98c5e66N393c09431ff12619N396019fe815bfc44N396c7a0e686fcd39N39a2c49238f21d8fP39b7f7822646761d 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 32 1 72 1 16 6 38 1 43 1 53 1 56 1 57 1 73 1 7 1 1 38 1 43 1 53 1 56 1 72 1 73 1P3a5e26f850a43240 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P3a6ac2e5da41dd7c 1 14 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 16 3 0 1 102 1 103 1 16 3 1 1 101 1 104 1 16 2 3 1 103 1 16 2 6 1 104 1 16 2 30 1 103 1 16 3 63 1 102 1 103 1 16 2 100 1 103 1 2 2 109 1 112 1 32 4 62 1 101 1 104 1 112 16 32 3 31 1 104 1 108 16 512 5 31 16 42 16 102 16 103 16 104 16 4 62 1 101 1 104 1 108 16N3a72388e625a79d9N3a837ba0dbd8675cP3ae581f6d6ea6f05 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 27 1 71 1 16 6 37 1 42 1 52 1 62 1 63 1 72 1 7 0 1 37 1 42 1 52 1 62 1 71 1 72 1P3b665fbb28dee3c1 1 13 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 101 1 104 1 32 3 1 1 102 1 103 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 2 2 108 1 114 1 2 2 105 1 115 1 2 108 1 115 1P3b898b8c99a7f696 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1N3b911a8fdaa400daP3be7f60b4c2a54bb 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P3c18c8f61d03a8d4 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P3c625603c08a27e1 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P3c665f2e5a871b5e 1 6 16 2 25 1 73 1 16 2 72 1 73 1 16 6 39 1 44 1 54 1 59 1 60 1 74 1 16 3 2 1 3 1 73 1 16 3 1 1 5 1 74 1 16 4 2 1 24 1 45 1 73 1 10 2 1 39 1 44 1 45 1 47 1 54 1 55 1 56 1 73 1 74 1N3c6787cc4016bda5N3c9fba6d47cb4e0fN3cae0cf84fb4d0a7P3db948fa78802164 1 4 16 2 24 1 72 1 16 2 71 1 72 1 16 3 1 1 30 1 72 1 16 6 38 1 43 1 53 1 58 1 59 1 73 1 7 1 1 38 1 43 1 53 1 58 1 72 1 73 1P3dc3f35cc52d6701 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1P3dd8cb18aaeed6d4 1 2 16 2 23 1 71 1 16 2 70 1 71 1 6 0 1 37 1 42 1 52 1 71 1 72 1P3e3e1b6ee11d57d6 1 2 16 2 23 1 71 1 16 2 70 1 71 1 4 0 1 51 1 71 1 72 1P3ec2d8bb5b650bcd 1 2 16 2 23 1 71 1 16 2 70 1 71 1 8 0 1 37 1 42 1 52 1 53 1 54 1 71 1 72 1P3ee156d08aa23c64 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1N3f4ca8291f5fe596P3f5cea8d105b789b 1 2 16 2 23 1 71 1 16 2 70 1 71 1 5 0 1 25 1 51 1 71 1 72 1P3f9ca4bb1b57e4b5 1 13 32 2 2 1 101 1 32 2 4 1 102 1 32 2 61 1 101 1 32 3 0 1 102 1 103 1 32 3 1 1 101 1 104 1 64 2 9 1 103 1 64 2 11 1 103 1 64 2 12 1 104 1 64 2 49 1 104 1 32 9 42 1 66 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 32 10 42 1 48 1 67 1 72 1 75 1 82 1 83 1 84 1 102 1 103 1 64 3 60 1 102 1 109 32 2 2 105 1 115 1 2 109 1 115 1P3feb255c354ee7e6 1 4 16 2 23 1 71 1 16 2 70 1 71 1 16 3 0 1 29 1 71 1 16 6 37 1 42 1 52 1 57 1 58 1 72 1 7 0 1 37 1 42 1 52 1 57 1 71 1 72 1"%lxh.
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
Ltac2 gd_tbl_A_pkcs7_signers_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.signer_cells"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_parse_A.A_PKCS7_GETSIGNERS"].


Definition A_WFREE : Z := 0x6947c.                (* [comment removed for export] *) (* [comment removed for export] *)

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
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pkcs7_signers_A ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lx1,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La0,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(5.&40.)Lk0,(5.&40.)(1.(5.&40.)Lk8,(5.&40.)(1.(5.&40.)Lk16,(5.&40.)(1.(7.(5.&8.))Lj32,(7.(5.&8.))(8.(9.$0.R1;.(:.(;.R16.(<.&40.R19.)Vgp,Vtp,R15.R14.R13.Vsp,(<.&40.R19.)R12.(<.&40.VEND,)R11.R10.R?.R>.R=.R<.(<.&40.R1:.)(<.&40.VSIG,)(<.&40.(?.R1:.+20.))Vs5,(<.&40.VPP,)(<.&40.(=.(>.VR,)))Vs8,(<.&40.R1:.)(<.&40.(?.(10.R1:.+3.)(=.(>.VR,))))Vs11,R;.R:.R9.R8.)VF,(<.&40.+98;1<.)Vfc,(11.(5.&40.))R17.(12.$4.)))(8.(8.(13.(14.(15.&40.Vsp,)+;0.)R19.)(13.R19.(14.(15.&40.Vsp,)+:0.)))(8.(9.$2.(16.R19.+20.)=)(8.(17.$4.VR,VHIA,R18.VLB,(18.(19.$2.$2.)(1:.$2.$2.R1:.+40.)VLF,)R17.)(8.(9.P,$2.Sp(1;.$4.VR,VHIA,R18.)(1;.$4.VR,VHIA,Vh,))(8.(9.$2.(1<.$4.VR,VHIA,R18.)(1<.$4.VR,VHIA,Vh,))(8.(9.$2.(1=.$4.VR,VHIA,R18.)(1=.$4.VR,VHIA,Vh,))(8.(9.$2.(1>.$4.VR,VHIA,R18.)(1>.$4.VR,VHIA,Vh,))(8.(9.$2.(1?.$4.VR,VHIA,R18.)(1?.$4.VR,VHIA,Vh,))(8.(9.$2.(20.$4.VR,VHIA,R18.)(20.$4.VR,VHIA,Vh,))(8.Pmo,$21.(22.(23.$4.VR,VHIA,R19.R1.)(23.$4.VR,VHIA,Vh,R1.))(8.(9.$2.(16.R1:.+40.)=)(8.(24.VR,VLB,VLF,R1:.+40.)(8.(25.$4.R17.R1:.(18.$26.(27.R7.)(18.$26.(27.R6.)(18.$26.(27.R5.)(28.$26.)))))(8.(25.$4.R17.(?.R1:.+20.)(18.$26.(27.(<.&40.=))(28.$26.)))(8.(25.$4.R17.(?.(10.R1:.+3.)(=.(>.VR,)))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.+?1.))(18.$26.(29.(<.&8.=))(18.$26.(29.(<.&8.+?3.))(18.$26.(29.(<.&8.+?3.))(18.$26.(29.(<.&8.+?3.))(28.$26.))))))))))(8.(25.$4.R17.(?.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R17.R19.(18.$26.(27.R4.)(18.$26.(27.R3.)(18.$26.(27.R2.)(18.$26.(27.(<.&40.VDALG,))(18.$26.(2:.#10.R1.)(18.$26.(27.(<.&40.R1:.))(28.$26.))))))))(8.(2;.$4.R17.(?.R19.+38.)(?.(15.&40.Vsp,)-68.))(8.(2;.$4.R17.Vlo,R19.)(8.(2<.$4.R17.)(8.(25.$4.R17.VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))(8.(25.$4.R17.VSIG,(2=.==Vsj,))(8.(25.$4.R17.VDALG,(2>.Vdtg,Vdpad,Vdlen,Vdq,))(8.(2?.$4.R17.VBUF,Vbs,)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R17.VPP,+8.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R17.VSIG,+<8.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R17.VDALG,+18.)(8.(30.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)R17.VBUF,(31.(32.(5.&8.)Vbs,)))(8.(33.(13.(?.R1:.+40.)VPP,)(13.(?.VPP,+8.)R1:.))(8.(33.(13.(?.R1:.+40.)VSIG,)(13.(?.VSIG,+<8.)R1:.))(8.(33.(13.(?.R1:.+40.)VDALG,)(13.(?.VDALG,+18.)R1:.))(8.(33.(9.$2.(31.(32.(5.&8.)Vbs,))=)(33.(13.(?.R1:.+40.)VBUF,)(13.(?.VBUF,(31.(32.(5.&8.)Vbs,)))R1:.)))(8.(34.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(28.$35.)Vm,R17.)(36.$4.(>.VR,)R17.Vslo,(15.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
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
  lx_hide1 EBOX.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x98a4c] [] 285%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0x end.
  lazymatch goal with FRx : rw_cells _ m0x (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
  replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
  destruct (stk_split asegs m0x lo sp1 (bv_unsigned sp + -160) ST ltac:(clear - SP1 SLO NS1; lia)) as [ST1 ST2]. clear ST.
  release_frame FRa ST2 (bv_unsigned sp + -104).
  destruct (stk_split asegs m0x sp1 (sp1 + 56) (bv_unsigned sp + -104) ST2 ltac:(clear - SP1; lia)) as [STlo SThi]. clear ST2.
  destruct (stk_carve asegs m0x sp1 (sp1 + 56) 56 STlo ltac:(clear; lia)) as [_ [jrs RSL]]. clear STlo.
  replace (sp1 + 56 - Z.of_nat 56) with sp1 in RSL by (clear; lia).
  apply (rw_cells_split_CB asegs m0x sp1 [] 56 jrs [] [8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity]. cbn [mk_CB_cells app] in RSL.
  cb8_to_c8 RSL (@nil cell).
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 RSL [c1] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 RSL [c1; c2] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 RSL [c1; c2; c3] end.
  lazymatch type of RSL with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => cb8_to_c8 RSL [c1; c2; c3; c4; c5] end.
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
  lx_hide1 EBOX. try lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 285%N). lx_tree.
  lxr_leaf. lx_carry. lx_unhide.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 339704) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
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
  lx_pre. lx_run_tac (PLAN [0x98b1c] [] 285%N). lx_tree.
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
