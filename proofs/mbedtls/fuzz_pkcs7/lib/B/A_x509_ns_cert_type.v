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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_ns_cert_type_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0048b388077b04db 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P023f0481c5dc7772 0 4 0 1 67 1 77 1 78 1P03020f5d43a3f6c5 0 3 0 1 44 1 54 1P032f5947ed89e027 0 4 0 1 60 1 77 1 78 1P052b8c0f301140b2 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P053f78ccb9c8eaa4 0 5 0 1 37 1 60 1 77 1 78 1P05818354c705a9ee 0 3 0 1 43 1 51 1P05849961432db288 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P059b695e01e9366f 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P0612cc7937c0bc54 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P0697a491dacc5022 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P06cb3be0d6e31911 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P06ee32c2fe61fd5c 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P077ec2bdd880682f 0 5 0 1 37 1 60 1 77 1 78 1P07a387d48b5ba5f9 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P07f4efacb4485c9c 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P0868b83369b7f752 0 5 0 1 37 1 60 1 77 1 78 1P0879c44f676baf35 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P094e0558c845803d 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P0a014c30bdcbba68 0 5 0 1 37 1 60 1 77 1 78 1P0ab75e5409b51921 0 4 0 1 67 1 77 1 78 1P0d64ed036a3be5a9 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P0da08df6cccccd7b 0 4 0 1 60 1 77 1 78 1P0e1d9e4539c3b086 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P0e41bcde18f2cacc 0 5 0 1 37 1 60 1 77 1 78 1P0fcb4ecdb9a7711f 0 5 0 1 37 1 60 1 77 1 78 1P0fedfdaebcd5c003 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P10481926f10aaae7 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P1106b63f744e9dc8 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P110790ce3b226909 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P110af13beaa0fc15 0 6 0 1 61 1 62 1 67 1 77 1 78 1P114069f392438948 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P11771a3f3231abb1 0 6 0 1 61 1 62 1 67 1 77 1 78 1P119e5b7938ad2547 0 5 0 1 37 1 60 1 77 1 78 1P11cf43193017ded8 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P11e896fcdad7fe81 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P1273f846c401e234 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P12dc8955c79e4134 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P138fa817dd4aeb7a 0 4 0 1 60 1 77 1 78 1P14eb19db6a80bfb6 0 4 0 1 67 1 77 1 78 1P158f04745c2fdca1 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P1633189358aaca8a 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P171b4e4603d47ff2 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P18cd97d4709c2aa7 0 4 0 1 67 1 77 1 78 1P19678b9f132ea429 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P19886476095cf776 0 4 0 1 67 1 77 1 78 1P1a7a2cf20491c128 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P1a800e673875a6a4 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P1ae15df724075d3b 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P1b6db7bea1aa0e9c 0 6 0 1 61 1 62 1 67 1 77 1 78 1P1c0c77fc15ea3ec3 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P1d3eb163b2ba8ebc 0 4 0 1 67 1 77 1 78 1P1d996e2dedf7e96f 0 4 0 1 60 1 77 1 78 1P1ed188b6aade125b 0 6 0 1 61 1 62 1 67 1 77 1 78 1P1f02c6096ef47ea0 0 4 0 1 60 1 77 1 78 1P1f2be8931839eb20 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P1f31403223e41ca8 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P20213b004afa0bac 0 4 0 1 60 1 77 1 78 1P20432bb9ee1ea1d0 1 2 16 2 0 1 79 1 16 2 1 1 78 1 2 80 1 81 1P219867b9778744f6 1 1 16 2 0 1 77 1 3 9 1 78 1 79 16P22f65623a731e702 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P231e291ab1ec7618 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P23b01f60f5d8918c 0 6 0 1 61 1 62 1 67 1 77 1 78 1P241dae199819c238 0 6 0 1 61 1 62 1 67 1 77 1 78 1P2423f08bd10f6c33 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P242a647d4590e4c6 0 4 0 1 67 1 77 1 78 1P2510357af5dd9029 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P25a0bcea70116b3d 0 4 0 16 59 16 77 16 78 16P25ac134761cd8144 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P25b3afd450955f51 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P25eb339d0b12da3d 0 4 0 1 60 1 77 1 78 1P26309e8d8d5e5946 0 5 0 1 37 1 60 1 77 1 78 1P270a7e80ce0201fb 0 6 0 1 61 1 62 1 67 1 77 1 78 1P2728775d001e4c69 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P2771c643c81fb01c 0 4 0 1 60 1 77 1 78 1P2790540180fdf93d 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P27a407724c89f4d2 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P28233e399e3f6862 0 6 0 1 61 1 62 1 67 1 77 1 78 1P284025529eb75ec3 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P2846c6796032600f 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P29f34003dc2d2e09 0 4 0 1 60 1 77 1 78 1P29fbd125b2cd34a0 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P2a3b799e0ef7149d 0 4 0 1 67 1 77 1 78 1P2b290f26c8b7541b 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P2c69ed856007853b 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P2c7ca9a16235bdcc 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P2cd957f1160fea2b 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P2d44d4585dd3a58c 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P2d5d8d5a179a1a07 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P2d7516d44589311e 0 4 0 1 60 1 77 1 78 1P2df0ad0845195587 0 6 0 1 61 1 62 1 67 1 77 1 78 1P2e3ea64c5507e058 0 6 0 1 61 1 62 1 67 1 77 1 78 1P2e584a48da114888 0 5 0 1 37 1 60 1 77 1 78 1P2fee970e9531d4e7 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P303214010ac83f45 0 6 0 1 61 1 62 1 67 1 77 1 78 1P309a7eeb0f135653 0 4 0 1 67 1 77 1 78 1P313e6733bc2347c7 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P31c1515026cf0aed 0 4 0 1 60 1 77 1 78 1P31c63de2580b8eaa 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P343110610a0bca4d 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P34476734d6dcce81 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P34a88adbe1fc0c96 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P34b722c1a7780932 0 5 0 1 37 1 60 1 77 1 78 1P353cf959dbb86a59 0 4 0 1 67 1 77 1 78 1P367397fd243ac9e1 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P369a250416fb558d 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P36ba25a9294c500c 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P375f58006ee7e2a2 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P3767cbf56e75eecc 0 6 0 1 61 1 62 1 67 1 77 1 78 1P37915fb102f34450 1 1 16 4 1 1 40 1 48 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P3794918adb8bcf98 1 1 16 2 1 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P37da097a85a22be8 0 4 0 1 67 1 77 1 78 1P38343552ef24847d 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P38c75b9285015966 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P392beeb475249da1 2 62 1 1 8 3 2 1 80 1 81 1 5 0 1 69 1 79 1 82 1 83 8 1 1 8 3 1 1 79 1 82 1 4 0 2 80 2 81 2 83 16P39fd5a751a2c4da4 0 5 0 1 37 1 60 1 77 1 78 1P3aed2dcab7633115 1 2 16 3 1 1 46 1 78 1 16 3 0 1 47 1 79 1 2 80 1 81 1P3b4cfa9149454efc 0 4 0 1 60 1 77 1 78 1P3c72f8053981950a 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P3ceace55c4c10602 0 4 0 1 67 1 77 1 78 1P3d2cf4e781428cdd 3 60 0 2 1 1 2 1 0 5 0 1 3 1 70 1 80 1 81 1 0 4 0 1 2 1 80 1 81 1P3d9b18b32c0fa24d 1 1 16 3 1 1 46 1 78 1 7 45 1 55 1 62 1 63 1 68 1 79 1 80 16P3ec6da271a4e8872 2 61 0 5 0 1 2 1 69 1 79 1 80 1 0 4 0 1 1 1 79 1 80 1P3f16c93072cf9cda 0 5 0 1 37 1 60 1 77 1 78 1N01d8c6edd373d5fcN020818995132fb8aN03a3b080fb6b8672N044c0907b945eac7N0674aca7132ab53cN0886a20a4c70f9b9N08c532f3fdf648e3N0a4f362832d72b0eN0ba622e3858243c9N0d91e0757067f495N0fd736e618af90c6N1205524483c879acN1358f8fce6417839N144d1d1273e473a6N14e2bf62276c4013N15e6c6dadb2074b6N160d7558ae8763edN1652f5a49267006aN165423066d19c409N1a27342b6ffb14d6N1b88cafdb02df23fN1c73d05e02a3b3d3N1cc0c5df86ecaff7N1d5ddaca9b51c843N1db39debe1e6e7bdN226088f6fdd0d134N23358b4bc89d7154N256857aa1a6928d8N28b99144aa4cb95eN2a11ba2cdfe6b476N2bde69974011d6a0N2d7833c002fea68dN2df8fa1688b07ac8N300ade80199aa65fN30535fc360285b2dN305831a6a188df5dN31532d021cd4814fN32f87f6ad5e7d8f2N34b0f39e51b9ddddN34bb2259973bdc91N36a99b3da7042ffbN378e56acdf430936N38e73209b7cb2a0eN39f32e6ac09a6527N3aa9f3c0f2b9daabN3ab43542ca697ae2N3aef17efde059572N3b402514e14e96feN3b4094048f54ad35N3c0ea7e1bc42d92cN3d2542550f30ac03"%lxh.
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
Ltac2 gd_tbl_A_x509_ns_cert_type () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_ns_cert_type_A.x509_ns_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_ns_cert_type_A.A_X509_NS_CERT_TYPE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_x509_ns_cert_type_A.A_SMALLOC_1N"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_x509_ns_cert_type_A.A_AMEMSET_N"; "RocqVerifyHarness.AgentSubmission.B.A_x509_ns_cert_type_A.x509_ns_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GBS : asn1_get_bitstring_stmtA asegs AL A_ASN1_GET_BITSTRING.
  Hypothesis AMS : arl_amemset R = A_AMEMSET_N.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP NS P END BUF lo slo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B2 : P <= END.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= NS \/ NS + 1 <= PP.
  Hypothesis D4 : Z.of_nat (length bs) = 0 \/ PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D5 : Z.of_nat (length bs) = 0 \/ NS + 1 <= BUF \/ BUF + Z.of_nat (length bs) <= NS.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis PPB : 0 < PP /\ PP + 8 <= 2^64.
  Hypothesis NSB : 0 < NS /\ NS + 1 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_NS_STACK_A.
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
  Hypothesis DS2 : NS + 1 <= lo \/ bv_unsigned sp <= NS.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo PP 8.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo NS 1.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW1 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) NS 1.
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
    unfold X509_NS_STACK_A in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_ns_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP NS P END lo slo).
  Local Notation W := [(PP, PP + 8); (NS, NS + 1)].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1N.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01`0@D10639329459.124D18607476203.165D2455714710.191 D26321392058.166D26321392058.167D26321392058.168D27392810573.191D32457002573.191D3254889317.164 D3373657269.191 D33956323578.166D33956323578.167D33956323578.168D41388959683.191D46793042006.124D50254960491.166D53232575014.166D53232575014.167D53232575014.168D560907438.126  D58077997354.166D59036699141.125D60098777666.125D60111245650.124D61058262105.125D62011770188.126D68405212918.191D6909863155.191 L12745310030.0  L12758705305.0  L15756354262.7  L17523603370.3  L17921795213.184L19980016842.7  L26368079009.0  L27293603243.1  L29738741675.1  L35228767239.1  L3551623394.2   L36180999398.118L37156630869.0  L3876079316.5   L39220637093.0  L39332637397.0  L39618635427.2  L43055370171.116L48117620907.105L50790731766.8  L52255793882.181L56854270298.123L57355539152.170L58071656716.182L58790154276.6  L59257759329.3  L59308677456.15 L59393203371.1  L6203936179.1   L64009471222.1  L7040749983.124 L9356559645.13  L9873114841.7   P1056307012.164 P1056307012.166 P16944208628.164P16944208628.166P36462068749.165P36465839390.164Q10523111608.130Q10651763882.132Q10651763890.128Q12660624644.134Q1530342990.166 Q23927511185.130Q23927511197.135Q27944911788.191Q29477837696.191Q31021924279.164Q32436491433.191Q32681887700.130Q33196749121.134Q33963892682.191Q35653441506.110Q38248895676.136Q4011963981.191 Q40228749922.191Q40271359350.166Q42439168719.164Q42439382240.137Q43880146016.136Q46407961466.129Q46805771343.132Q46805771351.128Q47230721789.130Q48119867062.191Q50796826103.166Q55251119459.191Q59026210859.133Q59026210862.129Q59865520191.137Q60109315147.110Q60740903729.128Q61064556146.129Q61064556151.133Q6192914196.164 Q62011770181.135Q62011770185.130Q64683599817.137Q67026483294.165Q67038703949.164Q6909863155.191 Q9356560156.147 Q9646450869.191 00000A00B00C00D00E00F00b01>01?01@01d02H02I02e03603703803903:03S04004D04^05805L05_05`06<06=06>06L06V06W06o07007407807<07C07T07U07h07i07j08408L08k09<09X0:I0:J0:j0;@0;L0;_0;c0;h0;l0<M0=<0=X0>O0?F0@=0A40A\0A]0Am0B;0BI0BX0Bn0CM0C`0D=0DZ0E90E:0E;0EJ0F20FT0Fb0G00G10GD0GZ0H00HA0HR0H`0Hn0I?0I^0J90Jl0K:0KH0KI0K]0Kn0L<0LJ0LY0Lf0M30MV0N90N\0Nj0OA0OZS2LF2sp2PP2bs3LFBFFFFFS2LF2sp2PP2bs3LFB3sp13H222FBS2LF2sp2PP2bs3LFB3sp13H222FBFFS2LF2sp2PP3BUF2bs3LFB3sp13H223x142HxS2LF2sp2PP3BUF2bs3LFB3sp13H223x142HxFS2LF2sp2PP2bs3LFB3sp13H222FBS2LF2sp2PP2bs3LFBFFFFS1R3HIA1h2LF2sp2PP2bs3LFBS2LF2sp2PP2bs3LFB3sp13H203H22S2LF2sp2PP2NS2bs3LFBS1R2LF2sp2PP2lo2bs3LOS3LFBS1R2LF2sp2PP2lo2bs3LOS3LFBS2LF2sp2PP2NS2bs3LFBS1R2LF2sp2PP2bs3LFBFS2LF2sp2PP2bs3LFB3sp13H222FBSSS1R2lo3LOS3ALOS2FB2x22HxFS1R3HIA1h2sp3TOP3sp13SP1SS2FBS2FBS2spS2bs2EQS2LF2sp2PP2bs3LFBSS2sp2lo3SLO3sp13SP1SSS3sp14SP1MS2LF2sp2PP2lo2bs3SLO3LFBS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSS2LF2sp2PP2bs3LFB3sp13H222FBS2LF2sp2PP2bs3PPB3SPA3LFB3SPR3sp13H183H193H203H22FS2LF2sp2PP2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S2sp3sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS3sp1S2bsS2LF2sp2PP2bs3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2PP1P3END3BUF2lo2bs2B12B22B33SLO3DS13LFB3sp13SP1S2LF2sp2NS1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp2NS1P3END3BUF2lo2bs2B12B22B33SLO3DS23LFB3sp13SP1S2LF2sp3BUF2lo2bs3SLO3DS43LFB3sp13SP12NEFS1R2LF2sp2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3SLO3LFB3sp13SP1S1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPFFS2LF3BUF2bs3LFBS2LF2sp2PP2bs3PPB3LFB3SPR3sp13H222FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF2lo2bs3LFBS2LF2bs3LFB2FBFS1R3HIA1h2LF2bs3LFBS1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF2sp2lo2bs3LFBS2LF2PP2NS2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2LF2sp2lo2bs3SLO3LOS3LFBS1R2LB2LF2sp2lo2bs3SLO3LOS3LFB3ALO3sp13SP12FB5FRSH'S2LF2NS2bs3LFBS2LF2NS2bs3LFBFS1R2LF2lo2bs3LOS3LFBS2LF2PP2NS2bs3LFBS2LF2NS2bs3LFBS2LF2NS2bs3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_ns_cert_type ()) "Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pv0,(0.&8.)P,(1.$2.VR,VHIA,Vh,VLB,VLF,Vm,)P,(3.$2.Vm,VPP,(4.$5.(6.(7.&40.VP,))(8.$5.)))P,(3.$2.Vm,VNS,(4.$5.(9.R3.)(8.$5.)))P,(:.$2.Vm,VBUF,Vbs,)P,(;.$2.Vm,Vlo,(<.&40.Vsp,))P,(=.$2.(>.VR,)Vm,Vslo,(<.&40.Vsp,))P,(?.$2.Vm,)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VPP,+8.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VNS,+1.)P,(10.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)Vm,VBUF,(12.(13.(0.&8.)Vbs,)))(14.$2.(>.VR,)(11.$2.VR,VHIA,Vh,)(15.$2.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VPP,VNS,VP,VEND,Vlo,Vslo,Vm,)(16.(17.Vra,Vsp,Vgp,Vtp,R17.R16.R15.Vs0,Vs1,(7.&40.VPP,)(7.&40.VEND,)(7.&40.VNS,)R14.R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(7.&40.$18.)Vfc,(19.(0.&40.))Vm,(1:.$2.)))")
(* [comment removed for export] *).
  Proof.
  intros until v0.
  intros HH HPP HSG HBUF ST SS MI OPP OSG OBUF.
  unfold A_X509_NS_CERT_TYPE.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_1N in SM1.
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
  lx_pre. lx_run_tac (PLAN [0x5306c] [] 193%N). lx_tree.
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
      pose proof (fresh_apart_client _ LB LF lo NS 1 FB 128 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 128 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_ns_cert_type_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_ns_cert_type ()) "PR,$1;.PHIA,(1<.$2.R1.)P,(1=.(>.R2.))P,(1>.$1?.(20.R3.)$21.)P,(1>.$1?.(22.R4.+1.)$23.)P,(1>.$1?.(24.R5.)$25.)(26.$2.R6.R5.$18.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG UARG SM1 AMS. pose proof (A_asn1_get_bitstring_spec (L := arl_L R) (arl_AL R) IMG) as GBS.
  unfold x509_ns_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
