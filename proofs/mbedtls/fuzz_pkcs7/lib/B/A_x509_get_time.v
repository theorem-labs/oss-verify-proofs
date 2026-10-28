(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_x509_get_time.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_asn1_get_len A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_time_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00630e7e05963814 0 5 0 1 37 1 58 1 71 1 72 1P00917b8c6d06597c 1 1 16 2 0 1 71 1 3 9 1 72 1 73 16P00c9cdd7353cf7f6 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P010ab8c44ee338ea 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P023257b00a1d63b4 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0250e87951349084 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0336c981e9025b3b 0 4 0 1 58 1 71 1 72 1P036251315741a3bf 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P04ae3385c58abfcc 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P05583ae64fb11223 0 4 0 1 63 1 71 1 72 1P058453aeb14ab5cc 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P05a91eebe7100f61 0 6 0 1 59 1 60 1 63 1 71 1 72 1P05bc8b5fe4aa4154 0 5 0 1 37 1 58 1 71 1 72 1P05e8acd0e6d138d6 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0711e722c648b9c0 0 4 0 1 58 1 71 1 72 1P07f77a290d6b5d98 0 4 0 1 63 1 71 1 72 1P085694b65db84f09 0 6 0 1 59 1 60 1 63 1 71 1 72 1P08c4646b9eb35a6c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P09452115535087d5 0 4 0 1 58 1 71 1 72 1P0972be6456da75e8 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P09a76ebce976dd13 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P0ae167d4dad1765b 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0aedda66a83699e8 0 6 0 1 59 1 60 1 63 1 71 1 72 1P0bba72beb4ed92f1 0 4 0 1 63 1 71 1 72 1P0ca380a2b8fe605d 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0de853697ef55b4c 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P0e16201d2f2482fa 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P0e3d1f53b666f8a2 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P0e3ec30e5ac192bb 0 5 0 1 37 1 58 1 71 1 72 1P0fb3bafbfb235619 0 6 0 1 59 1 60 1 63 1 71 1 72 1P102a2f088ff360c5 0 5 0 1 37 1 58 1 71 1 72 1P10587313446c97e2 0 5 0 1 37 1 58 1 71 1 72 1P105f580eab8def4d 0 4 0 1 63 1 71 1 72 1P107926999f4b220a 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P10aa8abacc6676fd 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P10acbd4fe667814c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P10e10feb49f1de0b 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P10fa28a0f43e3091 0 4 0 1 63 1 71 1 72 1P111592e0a1010a00 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P123afc6a4278f7ba 0 4 0 1 58 1 71 1 72 1P128532816cd91ca9 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P12f15e4e2c7d0f83 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P13b36fb4e125c039 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P1513fed9feeae294 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P15da2dddb3649a1f 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P1625a6f37b282031 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P165a9d6abe0c53e5 0 5 0 1 37 1 58 1 71 1 72 1P16b2f1839211f5ea 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1707d0089a980db3 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P17835548b32fe62b 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P17d75c638d8fbcd8 0 5 0 1 37 1 58 1 71 1 72 1P17fd5e8d5935300f 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P18331d777b37eee7 0 4 0 1 58 1 71 1 72 1P18dc6e70f450fc18 0 6 0 1 59 1 60 1 63 1 71 1 72 1P194e218b93de119e 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P1b1bad95439a968f 0 4 0 1 58 1 71 1 72 1P1ba68387594627fc 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1bfd12f327afb89b 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P1d43613589ad45b9 0 5 0 1 37 1 58 1 71 1 72 1P1d4e8e26f3fba845 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P1d715000668e4a5c 0 3 0 1 44 1 52 1P1df15532e28d85fb 0 4 0 1 63 1 71 1 72 1P1e22bde0304f6467 0 5 0 1 37 1 58 1 71 1 72 1P1ead190218a36084 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1fd744b0403741e9 0 6 0 1 59 1 60 1 63 1 71 1 72 1P1ff1c19a1d5aeab1 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P205a20b7368de911 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P20a11957ae203e9a 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P2131d1fe7776a18c 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P21ec218d4d6c8d68 0 5 0 1 37 1 58 1 71 1 72 1P221a288f6578f31e 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P22d735294b996c05 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P232016865b9492a0 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2338c7f7104ecb79 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P240eaf80da119c82 0 4 0 1 58 1 71 1 72 1P244d33962e48ef75 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P248813b5c60f9471 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2488228da59e80fd 0 4 0 1 58 1 71 1 72 1P24d0296b99e28485 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P26828978d3f0c8f1 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P26a632c9eed5ed61 0 6 0 1 59 1 60 1 63 1 71 1 72 1P26f064456aaaa828 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2710c0f973dbdde9 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P2719436577eeb221 0 4 0 1 63 1 71 1 72 1P273b440d86a5e86a 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P27422c1d3aa02ccc 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P27def41a09a22b75 0 5 0 1 37 1 58 1 71 1 72 1P28c292a6d5707adc 0 4 0 1 63 1 71 1 72 1P291eca61c5095d69 0 5 0 1 37 1 58 1 71 1 72 1P298c6c653e0866c1 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P2a40b5847de1a721 0 4 0 1 58 1 71 1 72 1P2a77160e92697b38 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2ac6079860e7ffe4 0 4 0 1 63 1 71 1 72 1P2b52d969d1e964e0 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2b6bb091ee0f01aa 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2bc10c50227c6daf 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P2bce3e03bb27c601 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P2bd2759a51cda24a 0 3 0 1 43 1 49 1P2c22f9250460a590 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2c26e09738605a37 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2cf3342049833eb2 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2cfe3fd7d31aa07b 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2d17a7d50b58bda6 0 4 0 1 58 1 71 1 72 1P2d5f2eaaef4560a0 0 6 0 1 59 1 60 1 63 1 71 1 72 1P2f42b6155faf3642 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P2f616c7a50de5caa 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P2f6f774b4dfbc0c6 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P2faa0b56ea9b0efd 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P30fa49225b3e5f5f 1 1 16 2 35 1 71 1 3 0 1 72 1 73 16P317a568eb1441372 0 4 0 1 63 1 71 1 72 1P31e8f3f5fb190c67 2 59 1 1 4 3 2 1 74 1 75 1 5 0 4 65 4 73 4 76 4 77 16 1 1 4 3 1 1 73 1 76 1 4 0 4 74 4 75 4 77 16P329ff84dc1195b5a 0 4 0 1 63 1 71 1 72 1P32a5f2af0ada7829 0 4 0 1 58 1 71 1 72 1P33216b42182bab54 0 4 0 1 63 1 71 1 72 1P3407f8a8bb16bc5d 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P34366b1ccfc8d92a 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P345588e87b0174f8 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P34760070f3aba3d1 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P34aff1c9bf2a0e60 3 58 0 2 1 1 2 1 0 5 0 1 3 1 66 1 74 1 75 1 0 4 0 1 2 1 74 1 75 1P34c4e76d647c4505 0 5 0 1 37 1 58 1 71 1 72 1P34e39f946e988e03 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P353151e6f6c3a2a0 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P354780a4eaa5a04c 0 6 0 1 59 1 60 1 63 1 71 1 72 1P356c75dc3e310a31 2 60 1 1 8 3 2 1 74 1 75 1 5 0 2 65 2 73 2 76 2 77 16 1 1 8 3 1 1 73 1 76 1 4 0 2 74 2 75 2 77 16P35a0628ffe08d95f 0 4 0 1 58 1 71 1 72 1P36ba0e98e25c737e 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P36d179331ed714bb 0 4 0 1 63 1 71 1 72 1P3721b0f06ffd5a8f 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P377d7147a21d82d0 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P38b4eb82615cb1e8 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P38b98ee3b961765d 0 4 0 1 58 1 71 1 72 1P38ebf1ab43e455c9 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P391846c4fb8ce919 0 4 0 1 58 1 71 1 72 1P39ee402d580068e9 0 4 0 1 63 1 71 1 72 1P3aa0ffcff54e4a5c 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P3b41b70c46a7e21d 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P3bb70b15d0c1fbc0 1 2 16 3 0 1 45 1 73 1 16 3 1 1 44 1 72 1 2 74 1 75 1P3c6c3bcf9cd3799c 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3ce531869edeab8c 1 1 16 4 1 1 40 1 46 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3d4e51d65543ff72 0 5 0 1 37 1 58 1 71 1 72 1P3dc51edd57bb9a1d 1 2 16 2 0 1 73 1 16 2 1 1 72 1 2 74 1 75 1P3e39e7bf9a2dd95a 0 6 0 1 59 1 60 1 63 1 71 1 72 1P3eea59af6896d527 1 1 16 3 1 1 44 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16P3fdf5728b3938c92 1 1 16 2 1 1 72 1 7 43 1 53 1 60 1 61 1 64 1 73 1 74 16N015f92cd9df7080eN02c21f7ff878d22cN03191ebe36386b6eN04f343e639b82b82N068ccf11b27623fdN08d4dd10c2d49294N08e4b0e23d1f9a26N0914c7dad04c089cN09a9156ab33aebb1N0a59611aa497a5c1N0b6af78ea2fcd801N0dcdc7edb4618ea1N0ff3e8fcb3c695bcN1112c4bbfea0f594N123ebd10fe6b73c2N12a2a80377922188N1368941f289cd0e9N14d33fc636ddf55cN16894fe87922d362N17bc4e0cfc9adccaN18710000cc234989N1a335a8c4198c2cdN1b4d71c7cd81def6N1ca5a71c40aee58dN1e40cd1deffce94cN1e6c9e545dba2859N1f9df3e2f70e0dbaN21256ccca4497e23N212f46065ec0ccd3N215aded856bb3725N2174465f88785940N21ba32839ecfe913N236f3e1d776ffeaeN23e21ca920d72dc5N249083a665942121N256c75e8f4030e8fN25dc812222fc29fcN267566ce0c5cd500N26dc79c40ff0d020N289b0c0aa8ee22d9N2c1ac6e71b14a0f8N2fc13bde5a69244eN3114161fcf1f949cN31cf12d682d5a87bN32630e7ac2ca12eaN35f9e892165c1a7fN37854bfbed846b2dN37d2d4f9381a4346N385423f3522de078N38c63656460b8894N39f42aca94bc8c2dN3a48191bc9f78e37N3a68a4b0e6e4c797N3aa61b8b49e0024eN3c9b2ee69265c6faN3d78ad37ad0a30aaN3e5e285335e71230"%lxh.
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
Ltac2 gd_tbl_A_x509_get_time () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.P.P_x509_get_time.time_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_time_A.x509_get_time_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_time_A.A_X509_GET_TIME"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_SMALLOC_0"; "RocqVerifyHarness.AgentSubmission.B.A_x509_get_time_A.x509_get_time_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.

  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP TM P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= TM \/ TM + 24 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ TM + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= TM.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : TM mod 4 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis TMB : 0 < TM /\ TM + 24 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_GET_TIME_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 176 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : TM + 24 <= lo \/ bv_unsigned sp <= TM.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo TM 24.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) TM 24.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_GET_TIME_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_get_time_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP TM P END lo slo).
  Local Notation W := [(PP, PP + 8); (TM, TM + 24)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis LFB : (length LF < 512)%nat.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01b0@D10639329459.126D18607476203.165D2455714710.193 D27392810573.193D32457002573.193D3254889317.164 D3373657269.193 D33956323578.166D33956323578.167D33956323578.168D41440366531.193D46793042006.126D50254960491.166D50270443855.127D51038213418.166D51884306313.127D53232575014.166D53232575014.167D53232575014.168D560907438.128  D57551393334.166D57551393334.167D57551393334.168D60098777666.127D60111245650.126D62011770188.128D68405212918.193D6909863155.193 L14558062586.3  L15756354262.7  L17921795213.186L19013159470.0  L19980016842.7  L21980071943.1  L24524441946.123L25985555144.1  L27729706458.181L29738741675.1  L3551623394.2   L35680140202.3  L3801083770.3   L39076636629.0  L39332637397.0  L39618635427.2  L40228640085.0  L43055370171.118L44032381512.1  L48117620907.106L50790731766.8  L51052909836.182L52249874585.0  L54437681876.5  L57355539152.170L58790154276.6  L59308677456.15 L60558678699.1  L6152188705.0   L63738252715.1  L64009471222.1  L7040749983.124 L7715476710.120 L9356559645.13  L9873114841.7   P1056307012.164 P1056307012.166 P36462068749.165P36465839390.164P36495602352.164P36495602352.166Q10523111608.132Q10651763882.134Q10651763890.130Q12660624644.136Q1530342990.166 Q21829627469.193Q23927511185.132Q23927511197.137Q27944911788.193Q31021924279.164Q31805155683.193Q32436491433.193Q32681887700.132Q33196749121.136Q33963892682.193Q35653441506.112Q38248895676.138Q40228749922.193Q40271359350.166Q42439168719.164Q42439382240.139Q43880146016.138Q46805771343.134Q46805771351.130Q47230721789.132Q48119867062.193Q49077563264.193Q50276733793.135Q50276733796.131Q50796826103.166Q51882206626.131Q51882206631.135Q59865520191.139Q60109315147.112Q60740903729.130Q6192914196.164 Q62011770181.137Q62011770185.132Q63018782704.131Q64683599817.139Q67026483294.165Q67038703949.164Q6909863155.193 Q9356560156.147 Q9646450869.193 00000D00E00F00e01D01E01F01m02T02U03403H03I03]04=04Q04R04S04T05005105205305P05m06C06D06c06o07=07>07?07W07[08S08X09709;09B09L09X09Y09Z09d09e0:@0:E0:d0;50;X0;Y0;l0;m0<C0<V0<Z0<[0<_0<c0=G0=[0>J0>f0?]0@T0A<0A=0B40Bk0C;0CI0CW0Cf0D<0DJ0Di0E<0EY0F80Fk0Fl0Fm0G<0Gk0HM0H[0H\0Ho0IE0I[0Il0J:0JH0JY0K80KU0Kc0L10LL0LZ0Lh0Li0M=0MN0M]0Mj0N70NH0Nk0ON0P10P?0PV0PoS2LF2sp2PP2TM2bs3LFBFFS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3LFB3sp13H222FBFFS2LF2sp2PP2TM3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP2TM3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2LF2sp2PP2TM2bs3LFBFS2LF2sp2PP2TM2bs3LFBS2LF2sp2PP2TM2bs3LFB3sp13H203H22S2LF2sp2PP2TM2bs3LFBFFFS1R3HIA1h2LF2sp2PP2TM2bs3LFBFFFS1R2LF2sp2PP2TM2lo2bs3LOS3LFBS1R2LF2sp2PP2TM2lo2bs3LOS3LFBS1R2LF2sp2PP2TM2bs3LFBFS2LF2sp2PP2TM2bs3LFB3sp13H222FBS2sp3sp13SP1S1R2lo3LOS3ALOFSS1R3HIA1h2sp3TOP3sp13SP1S2spS2LF2sp2PP2TM2bs3PPB3TMB3SPA3LFB3SPR3sp13H183H193H203H22S3sp1S2LF2sp2PP2TM2bs3LFB3sp13H222FBS2FBS2bs2EQS2FB2x22HxS2sp3sp13SP1SSS3sp14SP1MSS2LF2sp2PP2TM2lo2bs3SLO3LFBS3sp1S1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSS2LF2sp2PP2TM2bs3LFB3sp13H203H222FBSS2sp2lo3SLO3sp13SP1FS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2FBSS2FBS2bsS2LF2sp2PP2TM2bs3LFB3SPR3sp13H183H22S2LF2sp2PP2TM2bs3LFBS1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2TM1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2TM1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S2LF2bs3LFB2FBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'FFS2LF3BUF2bs3LFBS2LF2sp2PP2TM2bs3PPB3TMB3LFB3SPR3sp13H222FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S2LF2TM2bs3LFBS2LF2TM2bs3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2TM2bs3LFBS2LF2TM2bs3LFBFS1R2LF2lo2bs3LOS3LFBS2LF2PP2TM2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS2LF2PP2TM2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_time ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Py,(0.&40.)Pmo,(0.&40.)Pdd,(0.&40.)Phh,(0.&40.)Pmi,(0.&40.)Ps,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VTM,(9.R8.R7.R6.R5.R4.R3.))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VTM,+18.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VTM,VP,VEND,Vlo,Vslo,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VTM,)R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until s.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_GET_TIME.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_0 in SM0.
  unfold time_cells in HSG.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
  carve_frame 160%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 576%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 176 <= sp1 <= bv_unsigned sp - 160) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -160) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
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
      flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 0)) with 64%nat in FRM by reflexivity.
      replace (64 * 2 ^ 0) with 64 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [24; 8; 8; 16; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HLEN FRM3. chunk_split FRM3 1%nat FD2 G2.
      replace (FB + 24 + 8) with (FB + 32) in HLEN, FD2, G2 by (clear; lia).
      replace (FB + 32 + 8) with (FB + 40) in FD2, G2 by (clear; lia). replace (FB + 40 + 16) with (FB + 56) in G2 by (clear; lia).
      cb8_to_c8 HLEN (@nil cell).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -160) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -160 + 56) with (bv_unsigned sp + -104) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -160) |- _ => release_frame FRa ST2x (bv_unsigned sp + -104); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 24) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp24 SLOT24].
      cb8_to_c8 SLOT24 (@nil cell).
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -104) (sp1 + 48) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp48 SLOT48].
      cb8_to_c8 SLOT48 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 64) ((FB, 64) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 64 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 24) (LB ++ fdata ((FB, 64) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 64 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo TM 24 FB 64 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 64 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_get_time_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_time ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.=)$23.)(24.$2.R5.R4.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM0.
  unfold x509_get_time_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
