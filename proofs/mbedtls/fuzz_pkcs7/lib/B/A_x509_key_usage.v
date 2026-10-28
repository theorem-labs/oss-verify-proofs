(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_bitstring.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_asn1_get_bitstring A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_key_usage_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0206b02f0d1dcf69 0 4 0 1 65 1 75 1 76 1P029fb043870351a3 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P036078d589db9b88 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P0364f07e2cc6419a 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P0452a3a9e633b2ff 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P048a564ae84e40f4 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P05964e734366b9b4 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P064d94d555991cea 0 6 0 1 59 1 60 1 65 1 75 1 76 1P06d48579645fdd59 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P06d6a6d835e02cb1 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P06e077378d3c92cf 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P08494fd35cd0bdd2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P0940ee6f9a356413 0 5 0 1 37 1 58 1 75 1 76 1P095bd94d096876d7 0 4 0 1 58 1 75 1 76 1P09c1541274de9176 0 6 0 1 59 1 60 1 65 1 75 1 76 1P09cab0ae0b6ca4c7 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P09e64317a24b6725 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P0aca35d4e1dd3375 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P0b5b73e080f55017 0 5 0 1 37 1 58 1 75 1 76 1P0c4f70447e96edb4 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P0c504c1e6d510da9 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P0d190b242d28a37d 0 5 0 1 37 1 58 1 75 1 76 1P0d70eb09a3c589f8 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P0e4d91b962ee5e0e 0 5 0 1 37 1 58 1 75 1 76 1P0ec8a00c1d8ed367 0 4 0 1 58 1 75 1 76 1P0f0f7c287d0b9177 0 6 0 1 59 1 60 1 65 1 75 1 76 1P0f641108870320a6 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P0ff29ebde50f8543 0 5 0 1 37 1 58 1 75 1 76 1P10f30b6522995f24 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P111394ecb48a868e 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P116143ec2d890fc2 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P1181fe76a0e8ddf8 0 4 0 1 65 1 75 1 76 1P122466185c888f15 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P12d7ff336b818a6d 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P1300993ad8c1d538 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P132e3474a64a8806 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P139c8fc3cace6c16 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P14e2c1fe0c9d237c 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P1534aa37acb77bd6 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P156549f4e18864ed 0 6 0 1 59 1 60 1 65 1 75 1 76 1P164be5745f3f2504 0 4 0 1 58 1 75 1 76 1P1670f40f7ff20827 0 4 0 1 58 1 75 1 76 1P17cfc916bf965825 1 1 16 2 0 1 75 1 3 9 1 76 1 77 16P17e1efd00c583eaa 0 6 0 1 59 1 60 1 65 1 75 1 76 1P19745e24db2bfe27 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P1b127265fa8c380d 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P1b72ba8943af90ee 0 6 0 1 59 1 60 1 65 1 75 1 76 1P1c01930079ee2bd0 0 4 0 1 65 1 75 1 76 1P1c1bf6ffbbae2761 0 5 0 1 37 1 58 1 75 1 76 1P1c6dd2bf6cef5c9c 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P1d0f0e18b27525e5 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P1ddf81211ba10aac 0 5 0 1 37 1 58 1 75 1 76 1P1e5d0fdaadb41fc8 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P1ec3e15091adbc67 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P1f11db0547a2423a 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P1f35b52e3d670f77 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P1fc1c41b7dd69f64 0 4 0 1 58 1 75 1 76 1P2017972899fd1859 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P2097c0ef030f9214 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P20d495002909e09f 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P21536199bd2712c3 0 4 0 1 65 1 75 1 76 1P22190fdba4204e11 0 4 0 1 65 1 75 1 76 1P2275f7b2d3704a44 0 6 0 1 59 1 60 1 65 1 75 1 76 1P22e678a9c94ccfd8 0 6 0 1 59 1 60 1 65 1 75 1 76 1P22efaa152bb3e4a7 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P22f519cb5991928e 0 4 0 1 65 1 75 1 76 1P23621d65b2374704 0 4 0 1 65 1 75 1 76 1P244a0cf96332d70d 0 5 0 1 37 1 58 1 75 1 76 1P252b1e09a9e4631d 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P258022b3953f8f07 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P26b36f90d1218f6e 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P2711d14215479f4b 0 6 0 1 59 1 60 1 65 1 75 1 76 1P275c37702f895ded 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P2763fb424c3d7567 0 5 0 1 37 1 58 1 75 1 76 1P279e9d565b9818bf 0 4 0 1 65 1 75 1 76 1P285d6ffaf68070d7 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P28bb2f1078e0c947 0 4 0 1 58 1 75 1 76 1P29446f17df65ace5 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P2a3a5b8639d6d149 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P2a7c892803821178 0 6 0 1 59 1 60 1 65 1 75 1 76 1P2abb3f226500c3e7 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P2ae368eff3879ab7 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P2c4f49742e893e08 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P2cb559fe198881c5 0 3 0 1 44 1 52 1P2d90eed3ac09c1a2 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P2da588fa43226f2f 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P2dabcc364f11c787 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P2dbdc2b43f254f50 0 3 0 1 43 1 49 1P2dfe3d707fe818d1 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P2e8258661d2d20bf 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P2e8edce19c8ef5b0 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P2f329d9f95b7f4a3 0 4 0 1 58 1 75 1 76 1P2f5dbcac6e82ed11 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P2fb2c12357956ffb 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P310fd71bc6735420 0 5 0 1 37 1 58 1 75 1 76 1P314583b09bf3cdb2 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P31fe639425b367dc 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P322e813be87001c1 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P3231ca174a577b16 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P3234db45c52792d2 0 4 0 1 65 1 75 1 76 1P32ccf1ba1ea27f00 0 4 0 16 57 16 75 16 76 16P32f34b0fcc0b3375 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1P336c57c897bd3b21 0 5 0 1 37 1 58 1 75 1 76 1P33a93540b4db7d2a 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P33fe94908444437f 1 2 16 2 0 1 77 1 16 2 1 1 76 1 2 78 1 79 1P342821fb69103aee 0 5 0 1 37 1 58 1 75 1 76 1P35ca361d8d1fead8 0 4 0 1 58 1 75 1 76 1P364d4af71cb0af34 1 1 16 2 1 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P379fed864dc75d46 0 6 0 1 59 1 60 1 65 1 75 1 76 1P37fc01dc8f68fdb5 0 4 0 1 65 1 75 1 76 1P380e2821dff9e9da 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P3917c463cc790dbc 0 4 0 1 58 1 75 1 76 1P399146324686d392 0 6 0 1 59 1 60 1 65 1 75 1 76 1P39fe1399009769ef 0 4 0 1 58 1 75 1 76 1P3a0f41a4e4a4ce83 2 60 1 1 8 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 8 1 1 8 3 1 1 77 1 80 1 4 0 2 78 2 79 2 81 16P3b4d859943556e9b 2 59 1 1 4 3 2 1 78 1 79 1 5 0 1 67 1 77 1 80 1 81 4 1 1 4 3 1 1 77 1 80 1 4 0 4 78 4 79 4 81 16P3c16519a50671e6b 1 1 16 3 1 1 44 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P3c775a84a867dcde 0 4 0 1 65 1 75 1 76 1P3e1b77fa6ee05763 1 1 16 4 1 1 40 1 46 1 76 1 7 43 1 53 1 60 1 61 1 66 1 77 1 78 16P3e258e2bedf5c525 0 4 0 1 65 1 75 1 76 1P3ec86a87727021b0 0 4 0 1 58 1 75 1 76 1P3edf38dd243061f2 0 4 0 1 58 1 75 1 76 1P3f42e6f8529ce4ec 1 2 16 3 1 1 44 1 76 1 16 3 0 1 45 1 77 1 2 78 1 79 1P3f9537ef2e5f6153 3 58 0 2 1 1 2 1 0 5 0 1 3 1 68 1 78 1 79 1 0 4 0 1 2 1 78 1 79 1N0032dcfe7571c084N00c7efa524c14934N011ec8a5344c547bN01e7eca06f3fc163N02a6aee7738b5ea7N078f79d7b669ac60N07da8b642578b3bfN0b769d0b68254bc1N0bcf95e2dc4f3bd5N0e7322c727322086N1081d9d6a022e396N10e987427e78dd78N1184f497b0332b72N11e1face1e69347cN1238d6db9dd492b1N125c316e162f87b8N138fbd4e5dda3449N139180e91641e07fN178739b4aac288d2N18293299cc1cebf6N18d864833e285f59N1a1e498618d5e772N1a3bef09ebc8c8a5N1d4581b3b07ad81aN21ed0fc379ba1210N259374bf4774018dN27b183670ac4fd64N27c506e2e640e846N286e8f09deb1ff1fN2ad347cac2140252N2c43fc375878b494N2d6f9eae31687599N2db93b3674a1f16cN2dedbd6dc4f66bb2N2eb05162648095a5N2f2be0e066ede15dN306ccd6a7191c524N30d41b005e4aadf3N31463c58322db4a3N3174d763991e12caN320b925e2c24ade3N32484eab46a00f05N34ccf7e3bdb07578N34e1238afded5f08N35e31e65c9f0dde2N3875042ecea046c9N38d32e21138d0f17N38d81f6546d096e6N3c8de7f7a8691983N3c973495524da966N3f95d1264800a4e7"%lxh.
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
Ltac2 gd_tbl_A_x509_key_usage () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_key_usage_A.x509_ku_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_key_usage_A.A_X509_KEY_USAGE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_x509_key_usage_A.A_SMALLOC_1U"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_x509_key_usage_A.A_AMEMSET_U"; "RocqVerifyHarness.AgentSubmission.B.A_x509_key_usage_A.x509_ku_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GBS : asn1_get_bitstring_stmtA asegs AL A_ASN1_GET_BITSTRING.
  Hypothesis AMS : arl_amemset R = A_AMEMSET_U.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP KU P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= KU \/ KU + 4 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ KU + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= KU.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : KU mod 4 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis KUB : 0 < KU /\ KU + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_KU_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - 112 - arl_need_amem R.
  Hypothesis RTA0 : 0 <= arl_need_amem R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : KU + 4 <= lo \/ bv_unsigned sp <= KU.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo KU 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) KU 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_KU_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_ku_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP KU P END lo slo).
  Local Notation W := [(PP, PP + 8); (KU, KU + 4)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1U.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0@D10639329459.125D18607476203.164D2455714710.190 D27392810573.190D32457002573.190D3254889317.163 D33572813991.126D3373657269.190 D33956323578.165D33956323578.166D33956323578.167D41388959683.190D46793042006.125D50254960491.165D50466429785.126D51665424694.165D51665424694.166D51665424694.167D53232575014.165D53232575014.166D53232575014.167D560907438.127  D58077997354.165D60098777666.126D60111245650.125D62011770188.127D68405212918.190D6909863155.190 L12745310030.0  L12758705305.0  L15756354262.7  L17076861729.0  L17523603370.3  L17921795213.183L19980016842.7  L27293603243.1  L29738741675.1  L35228767239.1  L3551623394.2   L36180999398.119L37156630869.0  L3876079316.5   L39268637205.0  L39332637397.0  L39618635427.2  L43055370171.117L48117620907.105L50790731766.8  L52255793882.180L56854270298.122L57355539152.169L58071656716.181L58790154276.6  L59257759329.3  L59308677456.15 L59393203371.1  L6203936179.1   L64009471222.1  L7040749983.123 L9356559645.13  L9873114841.7   P1056307012.163 P1056307012.165 P36462068749.164P36465839390.163P37509984720.163P37509984720.165Q10523111608.131Q10651763882.133Q10651763890.129Q12660624644.135Q1530342990.165 Q23927511185.131Q23927511197.136Q27944911788.190Q29477837696.190Q31021924279.163Q32436491433.190Q32681887700.131Q33196749121.135Q33587492489.134Q33587492492.130Q33963892682.190Q35653441506.111Q38248895676.137Q4011963981.190 Q40228749922.190Q40271359350.165Q42439168719.163Q42439382240.138Q43880146016.137Q46805771343.133Q46805771351.129Q47230721789.131Q48119867062.190Q50481107314.130Q50481107319.134Q50796826103.165Q54406581368.130Q55251119459.190Q59865520191.138Q60109315147.111Q60740903729.129Q6192914196.163 Q62011770181.136Q62011770185.131Q64683599817.138Q67026483294.164Q67038703949.163Q6909863155.190 Q9356560156.146 Q9646450869.190 00000D00E00F00e01D01E01Y01Z02A02h02i03H03\03]04104204304404504604704S05305P05m06C06D06c06d06e07307407>07?07W07[07_07c07j08>08?08R08S08T08^09909X09i0:H0;@0;A0;d0<:0<F0<Y0<]0<b0<f0=J0>90>U0?L0@C0@k0@l0Ac0BZ0Bj0C80CF0CU0Ck0DJ0D]0E:0EW0F60F70F80FG0FU0Fc0GR0H40HB0HP0HQ0Hd0I:0IP0Ia0Io0J=0JN0Jm0K;0KI0Kd0L50Lh0Li0M=0MN0M]0Mj0N70NZ0O=0O`0On0PE0P^S2LF2sp2PP2KU2bs3LFBFFS2LF2sp2PP2KU2bs3LFB3sp13H222FBS2LF2sp2PP2KU2bs3LFB3sp13H222FBFS2LF2sp2PP2KU2bs3LFBFS2LF2sp2PP2KU3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP2KU3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP2KU2bs3LFB3sp13H222FBS2LF2sp2PP2KU2bs3LFBFS2LF2sp2PP2KU2bs3LFBFFFFFFS1R3HIA1h2LF2sp2PP2KU2bs3LFBS2LF2sp2PP2KU2bs3LFB3sp13H203H22S1R2LF2sp2PP2KU2lo2bs3LOS3LFBS1R2LF2sp2PP2KU2lo2bs3LOS3LFBS1R2LF2sp2PP2KU2bs3LFBFS2LF2sp2PP2KU2bs3LFB3sp13H222FBSSS1R2lo3LOS3ALOSS2FB2x22HxFS1R3HIA1h2sp3TOP3sp13SP1S2FBS2FBS2spS2bs2EQS2LF2sp2PP2KU2bs3LFBSS2sp2lo3SLO3sp13SP1SSS3sp14SP1MS2LF2sp2PP2KU2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSS2LF2sp2PP2KU2bs3LFB3sp13H222FBS2LF2sp2PP2KU2bs3PPB3KUB3SPA3LFB3SPR3sp13H183H193H203H22FS2LF2sp2PP2KU2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S2sp3sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS3sp1S2bsS2LF2sp2PP2KU2bs3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS2LF2sp2KU1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2KU1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPFFS2LF3BUF2bs3LFBS2LF2KU2bs3LFBS2LF2KU2bs3LFBS2LF2sp2PP2KU2bs3PPB3KUB3LFB3SPR3sp13H222FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBS2LF2bs3LFB2FBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS2LF2KU2bs3LFBS2LF2KU2bs3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFBS2LF2PP2KU2bs3LFBS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'FS1R2LF2lo2bs3LOS3LFBS2LF2PP2KU2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pv0,(0.&40.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VKU,(4.$5.(9.R3.)(8.$5.)))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VKU,+4.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VKU,VP,VEND,Vlo,Vslo,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R17.R16.R15.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VKU,)R14.R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until v0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_KEY_USAGE.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_1U in SM1.
  rt_facts.
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO; lia)) as PRES.
  flat constr:(IMG') 4%nat. flclear IMG'. intros EGOT ELO EHI EGSB.
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
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 201%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340076 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96);
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
      replace (Z.to_nat (8 * 2 ^ 1)) with 16%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 1)) with 128%nat in FRM by reflexivity.
      replace (64 * 2 ^ 1) with 128 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [24; 8; 24; 64; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat BSL FRM3. chunk_split FRM3 1%nat FD2 G2.
      replace (FB + 24 + 8) with (FB + 32) in BSL, FD2, G2 by (clear; lia).
      replace (FB + 32 + 24) with (FB + 56) in FD2, G2 by (clear; lia). replace (FB + 56 + 64) with (FB + 120) in G2 by (clear; lia).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 1%nat FRa SPILL end.
      replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -88); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -88) sp1 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 128) ((FB, 128) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 128 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 88) (LB ++ fdata ((FB, 128) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo PP 8 FB 128 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo KU 4 FB 128 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 128 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_key_usage_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_key_usage ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.+1.)$23.)P,(1>.$1?.(24.R5.)$25.)(26.$2.R6.R5.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM1 AMS. pose proof (A_asn1_get_bitstring_spec (L := arl_L R) (arl_AL R) IMG) as GBS.
  unfold x509_ku_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
