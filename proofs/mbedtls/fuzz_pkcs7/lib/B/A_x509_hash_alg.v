(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_oid_md_alg A_pkcs7_cinfo.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_hash_alg_A.
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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000943d0fe31d631 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P0065366e2973370b 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P00e55c53e421b380 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P02ef76416e944d39 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P0408ee3ff5f797f3 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P04a2d0ad5bd0f6e3 1 1 16 3 1 1 44 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P04d564a50ae1d5f4 0 4 0 1 58 1 70 1 71 1P04fa18a2c173cc4e 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P05117ca06683e10b 0 4 0 1 65 1 70 1 71 1P051fcfbd3e89d569 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P0674f13d5cc6c9ed 1 1 16 3 1 1 44 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P06eacebfc6628b16 0 4 0 1 65 1 70 1 71 1P0742a62a5fffb318 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P0775083ac6f5f7c5 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P083cbadb648c4dd1 0 4 0 1 58 1 70 1 71 1P08c3efd38ed9c9a4 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P08dc7e4e8335a0bc 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P0969f9fdebea91a8 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P0be053056dd2c2b4 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P0e3b0088ee673f7f 0 4 0 1 65 1 70 1 71 1P0ea05f292b689159 0 5 0 1 37 1 58 1 70 1 71 1P0f372027a1390c07 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P10437fe563d03a96 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1045fbbc0847e93c 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P10729782b9e30538 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1092f65785ee01af 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P10c7807011ee11d8 0 4 0 1 58 1 70 1 71 1P10e4d852e59c4c04 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P11579997b700fd29 1 1 16 2 1 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P1167606627beff86 0 4 0 1 65 1 70 1 71 1P116a5594af9cfbd5 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P118f165b51e16de3 1 1 16 2 1 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P122bac80ce0b5976 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P123e957eeefcf437 0 4 0 1 58 1 70 1 71 1P12b7947355e89e13 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P13394a15e75b9357 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P135d2fdede6fde39 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P137500bfa66e482d 0 4 0 1 65 1 70 1 71 1P140211020cdeea9e 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P14ae18f8e3e764e3 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P1645a1a37207d7eb 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1743b413bacc2239 0 4 0 1 58 1 70 1 71 1P17be73a716de26d9 0 4 0 1 65 1 70 1 71 1P180b5468026f36b6 0 4 0 1 65 1 70 1 71 1P1884d570ccf59843 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P18d285d5dcc05aa3 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P18e3d5d2a27a78a0 0 5 0 1 37 1 58 1 70 1 71 1P195bcf74bb3e6b57 0 5 0 1 37 1 58 1 70 1 71 1P197bc8caf8cb3a9f 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P1a55d4a8d7afa69e 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1aaaefbc20a23f5f 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P1b082a41fae2ab56 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P1b1549e8153bbdc9 1 1 16 3 1 1 44 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P1b4a4ad6d6adecc1 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P1b4af0e692e691d6 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P1beefc85ee692cfd 0 5 0 1 37 1 58 1 70 1 71 1P1c89bf433b9a586b 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P1d471b3d39e82347 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P1d6ff25281e9d580 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P1d8dcf45f2ff73ba 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P1dd4bb9350c8e058 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P1dd9fabd35660ac3 1 1 16 3 1 1 44 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P1e11edc5032802d2 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P1e26c67f7f2042d6 0 4 0 1 58 1 70 1 71 1P1e44f305b535ec0c 0 5 0 1 37 1 58 1 70 1 71 1P1f117fa31ed478d1 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P1f12ae8adcf77afc 0 4 0 16 57 16 70 16 71 16P1f2d1104a952cd77 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P1f9b588cf25200be 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P2091a0ca7a289ba5 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P21896a7d0f958b2f 0 5 0 1 37 1 58 1 70 1 71 1P21964e3433a4bf45 0 5 0 1 37 1 58 1 70 1 71 1P21b8b1546f5f2291 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P21cb8e55a2820b22 0 5 0 1 37 1 58 1 70 1 71 1P256239222b9596e9 1 2 16 2 0 1 72 1 16 2 1 1 71 1 2 73 1 74 1P262a76921de43b53 1 1 16 3 1 1 44 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P26c91bd84a83e7e7 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P272145c4322abf6b 1 1 16 2 1 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P27f744c30709e906 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P282888a7c15896b7 0 3 0 1 43 1 49 1P28737a7ccd6f5c26 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P28d2a9859bec3ab4 0 5 0 1 37 1 58 1 70 1 71 1P29509005b398ecd8 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P2b1384ac35d94c60 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P2b4614fc36ea9a82 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P2c395c214de44704 0 4 0 1 58 1 70 1 71 1P2e66d2f9024fb9c0 0 4 0 1 65 1 70 1 71 1P2ed90509916b5aff 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P2ee7af5602a28252 0 4 0 1 65 1 70 1 71 1P305edd38ea1c69ed 0 4 0 1 58 1 70 1 71 1P311031be69c06b11 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P3209d5813ea29d78 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P32572a44f8f0ccb6 0 4 0 1 65 1 70 1 71 1P32707d3b6868be94 0 7 0 1 59 1 60 1 61 1 62 1 70 1 71 1P32bbf37cc7a3b775 0 5 0 1 37 1 58 1 70 1 71 1P3340a0fc5f6616e5 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P334232d7b7686790 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P334a094a51d86c61 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P372a0fd68d778e99 0 3 0 1 44 1 52 1P372ead4639572eb7 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P37a0d2f57e9f5736 1 1 16 2 0 1 70 1 3 9 1 71 1 72 16P38556694ca91d7a1 0 4 0 1 58 1 70 1 71 1P3900df6c6d075e88 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P3968669bc03bc8bc 0 5 0 1 37 1 58 1 70 1 71 1P3a742823a9397484 1 1 16 4 1 1 40 1 46 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P3a88db15174f8f89 2 64 1 1 8 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 8 1 1 8 3 1 1 72 1 75 1 4 0 2 73 2 74 2 76 16P3b82cf8f637212b9 1 1 16 2 1 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P3bcbee2d3fbbdcb4 1 2 16 3 1 1 44 1 71 1 16 3 0 1 45 1 72 1 2 73 1 74 1P3c2b22cb9bdd3718 1 1 16 2 1 1 71 1 8 43 1 53 1 60 1 61 1 62 1 63 1 72 1 73 16P3c60e865c4790b4c 0 4 0 1 58 1 70 1 71 1P3c820ac89be26646 2 63 1 1 4 3 2 1 73 1 74 1 5 0 1 67 1 72 1 75 1 76 4 1 1 4 3 1 1 72 1 75 1 4 0 4 73 4 74 4 76 16P3cb156d549041add 0 4 0 1 65 1 70 1 71 1P3d819588db7c3efe 3 62 0 2 1 1 2 1 0 5 0 1 3 1 68 1 73 1 74 1 0 4 0 1 2 1 73 1 74 1P3ff98ad870061d75 0 4 0 1 58 1 70 1 71 1N00ced1d091606b3bN020dc2866e83d542N038d819aa50db369N06b46c1e53144325N0744e6c3db3f2ff6N0aa52ee678d8a836N0c90cf78d02d15adN0de628a82afdceadN101c636fd23e3433N14296d6d0f3135dbN16c28b8922d619a4N1a8a3cb5731b74bfN1cd8872fe948ef53N1f36e200b90f7897N1ff95debfe37d8d7N20b047adfdf0770dN20c295064ff547a6N21091ffb86032c8fN2214c06593cbea38N22fb803b7987837fN23172913f84adf9cN23f292f4fda56f3fN24b6a0ea0278bd6fN2502a5918bd46df9N26e37b1bb4e4b702N2876140f86fcec1eN28bac8ec647b8d1fN2a5b7aaa2ef73b15N2ab99639daa95d61N2bf7595e787d9f40N2c1d6cea98170b68N2db064dc36393325N2e071edc3d8de3ffN2f82cb359186f9a6N3005b463cdad3991N30f77bd08e21925aN31b56d771003d427N334dc9e9c498f5e9N35f5251b0f36bba0N370a493691b67a78N3739024fc3d46968N3a7852a031c3f449N3cf305d40924f62bN3d64756552935e26N3daa37ae0dab58ebN3e421184a311a270N3f04de2169c3605fN3f4df7df85affebe"%lxh.
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
Ltac2 gd_tbl_A_x509_hash_alg () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.A_x509_hash_alg_A.x509_hash_postA"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.B.A_x509_hash_alg_A.A_X509_HASH_ALG"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.A_oid.oid_rt_hyps"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_UAR_GOT"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_x509_hash_alg_A.A_SMALLOC_2H"; "RocqVerifyHarness.AgentSubmission.B.A_x509_hash_alg_A.x509_hash_stmtA"].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis MDALG : oid_lookup1_stmtA asegs R HIA A_OID_GET_MD_ALG 64.

  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (ALG MGF BUF ap lo slo : Z) (bs : list byte) (atag apad alen : word).
  Hypothesis HAP : ltac2:(CDefT.buildp (gd_tbl_A_x509_hash_alg ()) "(0.(1.(2.$3.Vap,=)(2.$3.(4.&40.Valen,)=))(1.(5.VBUF,Vap,)(5.(6.Vap,(4.&40.Valen,))(6.VBUF,(7.(8.(9.&8.)Vbs,))))))")
(* [comment removed for export] *).
  Hypothesis B47 : BUF + Z.of_nat (length bs) + 8 <= 2^47.
  Hypothesis D1 : MGF + 4 <= ALG \/ ALG + 24 <= MGF.
  Hypothesis D2 : Z.of_nat (length bs) = 0 \/ MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF.
  Hypothesis AL1 : ALG mod 8 = 0.
  Hypothesis AL2 : MGF mod 4 = 0.
  Hypothesis ALGB : 0 < ALG /\ ALG + 24 <= 2^64.
  Hypothesis MGFB : 0 < MGF /\ MGF + 4 <= 2^64.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - X509_HASH_STACK_A.
  Hypothesis SLO3 : lo <= bv_unsigned sp - 112 - arl_need_smalloc R.
  Hypothesis RTS0 : 0 <= arl_need_smalloc R.
  Hypothesis SLO4 : lo <= bv_unsigned sp - X509_HASH_STACK_A - arl_need_bcmp R.
  Hypothesis RTB0 : 0 <= arl_need_bcmp R.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis DS1 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS2 : MGF + 4 <= lo \/ bv_unsigned sp <= MGF.
  Hypothesis DS4 : Z.of_nat (length bs) = 0 \/ BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CR1 : client_range L (LB ++ fdata LF) lo ALG 24.
  Hypothesis CR2 : client_range L (LB ++ fdata LF) lo MGF 4.
  Hypothesis CR4 : client_range L (LB ++ fdata LF) lo BUF (Z.of_nat (length bs)).
  Hypothesis CW2 : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) MGF 4.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold X509_HASH_STACK_A in SLO, SLO4;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation POSTA := (x509_hash_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MGF lo slo).
  Local Notation W := [(MGF, MGF + 4)].
  Local Notation SAVEL := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Hypothesis LFB : (length LF < 512)%nat.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2H.

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
  Local Ltac2 Set LiaOrc.tbl := fun () => "01\0@D18607476203.161D23960434386.162D23960434386.163D23960434386.164D2455714710.188 D27392810573.188D30282477627.124D32457002573.188D3254889317.160 D3373657269.188 D33746000322.162D33746000322.163D33746000322.164D33956323578.162D33956323578.163D33956323578.164D35662971424.124D50254960491.162D563007111.125  D58077997354.162D60111245650.124D62022258533.125D67392436163.188D68405212918.188D6909863155.188 L13948747720.1  L15609264775.1  L15756354262.7  L17921795213.181L19685319514.178L19980016842.7  L20858515662.0  L22066801146.3  L29738741675.1  L32463525127.1  L33021350305.0  L33750044167.1  L3551623394.2   L36180999398.118L3876079316.5   L39076636629.0  L39268637205.0  L39618635427.2  L43055370171.116L43300649301.0  L48117620909.102L50790731766.8  L56854270298.119L57355539152.166L57781587882.3  L58071656716.179L58790154276.6  L59308677456.15 L62611547911.1  L64009471222.1  L64787780871.1  L66747997337.0  L7040749983.120 L9356559645.13  L9873114841.7   P28293278204.162P36462068749.161P36465839390.160P42311556712.160P42311556712.162P55254318092.160Q10523111614.128Q12660624646.132Q1530342990.162 Q23927511187.133Q23927511191.128Q2521097805.188 Q30270012474.127Q30280497415.131Q31021924279.160Q31376482607.188Q32436491433.188Q33196749123.132Q33963892682.188Q35653441506.110Q35658894881.127Q35660991260.131Q38248895666.134Q38723551228.130Q40271359350.162Q4194868318.188 Q42304729984.188Q42439168719.160Q42439382242.135Q42565117115.127Q43880146030.134Q47230721787.128Q48119867062.188Q50796826103.162Q54431339875.188Q59865520189.135Q60109315147.110Q6192914196.160 Q62011770187.133Q62011770191.128Q62770373554.128Q64683599819.135Q67026483294.161Q67038703949.160Q68714454036.130Q6909863155.188 Q9356560156.143 Q9646450869.188 00000100200300400500V00l01M01N01O02402502Z03C03l03m04C04D04b05D05c06;06\06]07>07C07G07U07V08708O08P08\08`08d08e08i09009F09Y09Z09[09e0:B0:C0:b0;30;o0<00<:0<_0=50=H0=L0=P0=T0=U0>E0?40?P0@A0A50A60Ag0BX0CI0CY0Ch0D>0DQ0E00E>0EM0E\0F;0F[0F\0Fk0G^0H@0HO0H^0Hl0I;0IN0IO0Il0JB0JX0Jg0K80KI0Kn0LO0MH0MI0M]0Ml0N90NF0NG0Nj0OM0P00P?0PM0Pd0Q=FFFFFS2LF2sp3ALG3MGF2bs3LFB3sp13H222FBS2LF2sp3ALG3MGF2bs3LFBS2LF2sp3ALG3MGF2bs3LFB3sp13H222FBFFS2LF2sp3ALG3MGF2bs3LFB3sp13H223x142HxFS2LF2sp3ALG3MGF2bs3LFB3sp13H223x142HxS2LF2sp3ALG3MGF3BUF2bs3LFB3sp13H223x142HxS2LF2sp3ALG3MGF3BUF2bs3LFB3sp13H223x142HxFS2LF2sp3ALG3MGF2bs3LFBFS1R3HIA1h2LF2sp3ALG3MGF2bs3LFBS2LF2sp3ALG3MGF2bs3LFB3sp13H203H22S1R2LF2sp3ALG3MGF2lo2bs3LOS3LFBS1R2LF2sp3ALG3MGF2bs3LFBS2LF2sp3ALG3MGF2bs3LFB3sp13H222FBFS2LF2sp3ALG3MGF2bs3LFB3sp13H222FBS3sp1S2FBS1R2lo3LOS3ALOFS2LF2sp3ALG3MGF2bs3LFB3sp13H222FBS1R3HIA1h2sp3TOP3sp13SP1SS2sp3sp13SP1S2FBS2FBSS2FBS2bs2EQS2LF2sp3ALG3MGF2bs3LFBS2sp2lo3SLO3sp13SP1SSS3sp14SP1MS2LF2sp3ALG3MGF2lo2bs3SLO3LFBSS1R2LF2sp2lo2bs3SLO3LOS3LFB3ALOS1R2sp2lo3SLO3LOSS2LF2sp3ALG3MGF2bs4ALGB4MGFB3SPA3LFB3SPR3sp13H183H193H203H22FS2FB2x22HxS2LF2sp3ALG3MGF2bs3LFB3sp13H203H222FBS1R2sp2lo4SLO33sp13SP1S1R3ACV2FB2Kb2F02F1S2FBS2bsS2spSS2LF2sp3ALG3MGF2bs4ALGB4MGFB3LFB3SPR3sp13H183H22S1R2sp2lo3slo3SLO4SLOS4SLOL3ALO3ACV3SPR3sp13SP1S2sp2lo3slo3SLO4SLOL3sp13SP1S1R2LF2sp3ALG2lo2bs3SLO4SLO44RTB03DS13LFB3sp13SP1S1R2LF2sp3BUF2lo2bs3SLO4SLO44RTB03DS43LFB3sp13SP12NEFS1R2LF2sp3MGF2lo2bs3SLO4SLO44RTB03DS23LFB3sp13SP1S1R2LF2sp3MGF2lo2bs3SLO4SLO44RTB03DS23LFB3sp13SP1S1R2LF2sp3ALG2lo2bs3SLO4SLO44RTB03DS13LFB3sp13SP1S1R2LF2sp2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H20S1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS2LF2bs3LFB2FBS2LF3MGF2bs3LFBS2LF3MGF2bs3LFBS1R3HIA1h2LF2sp2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs4SLO43LFB3sp13SP1FS2LF3BUF2bs3LFBS2LF2sp3ALG3MGF2bs4ALGB4MGFB3LFB3SPR3sp13H222FB3F64S1R3HIA1h2LF2sp2lo2bs3TOP3LFB4HTOPS2LF3MGF2bs3LFBS2LF3MGF2bs3LFBS2LF2lo2bs3LFBS2LF3ALG2bs3LFBS1R3HIA1h2LF2bs3LFBFS1R2LB2LF2bs3LFB3ALO2FB5FRSH'S1R2LF3slo2bs4SLOS3LFBS1R2LF3slo2bs4SLOS3LFBS2LF3MGF2bs3LFBS2LF2sp2lo2bs3LFBS1R2LF2bs3LFB3ALOS1R2LF2sp2lo2bs4SLO44RTB03LOS3LFB3ALOS1R2LF2sp2lo2bs4SLO44RTB03LOS3LFBS1R2LB2LF2sp2lo2bs4SLO44RTB03LOS3LFB3ALO3sp13SP12FB5FRSH'FS1R2LF2lo2bs3LOS3LFBS2LF2bs3LFB3sp1S1R2LF2bs3LFBS1R2LF2bs3LFBFS1R3HIA1h2LF2sp3slo2bs3TOP3LFB4HTOPS1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S1R2LF2sp2lo2bs3SLO3LOS3LFB3sp13SP1S2LF3ALG2bs3LFBS2LF2bs3LFB2FBS2LF2bs3LFB3sp13H213H22S1R2LB2LF2bs3LFB2FB5FRSH'". (* [comment removed for export] *)
  Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_hash_alg ()) "Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pv0,(9.&40.)P,(:.$;.VR,VHIA,Vh,VLB,VLF,Vm,)P,(<.$;.Vm,VALG,(=.$>.(?.Vatag,)(=.$>.(?.Vapad,)(=.$>.(10.Valen,)(=.$>.(10.(11.&40.Vap,))(12.$>.))))))P,(<.$;.Vm,VMGF,(=.$>.(?.R3.)(12.$>.)))P,(13.$;.Vm,VBUF,Vbs,)P,(14.$;.Vm,Vlo,(4.&40.Vsp,))P,(15.$;.(16.VR,)Vm,Vslo,(4.&40.Vsp,))P,(17.$;.Vm,)P,(18.$;.(16.VR,)(19.$;.VR,VHIA,Vh,)Vm,VALG,+18.)P,(18.$;.(16.VR,)(19.$;.VR,VHIA,Vh,)Vm,VMGF,+4.)P,(18.$;.(16.VR,)(19.$;.VR,VHIA,Vh,)Vm,VBUF,(7.(8.(9.&8.)Vbs,)))(1:.$;.(16.VR,)(19.$;.VR,VHIA,Vh,)(1;.$;.VR,VHIA,Vh,VLB,VLF,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VMGF,Vlo,Vslo,Vm,)(1<.(1=.Vra,Vsp,Vgp,Vtp,R18.R17.R16.Vs0,Vs1,(11.&40.VALG,)(11.&40.VMGF,)R15.R14.R13.R12.R11.R10.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(11.&40.$1>.)Vfc,(1?.(9.&40.))Vm,(20.$;.)))")
(* [comment removed for export] *).
  Proof.
  intros until v0.
  intros HH HALG HMGF HBUF ST SS MI OALG OMGF OBUF.
  unfold A_X509_HASH_ALG.
  unfold A_UAR_GOT in UARG.
  unfold A_SMALLOC_2H in SM2.
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
  lx_pre. lx_run_tac (PLAN [0x531fc] [] 263%N). lx_tree.
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO; lia)) as [ST1 ST2]. clear ST.
      replace (Z_to_bv 64 340476 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 2)) by (rewrite SM2; reflexivity).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 2) with (lo := lo) (sz := 160);
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
      replace (Z.to_nat (8 * 2 ^ 2)) with 32%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 2)) with 256%nat in FRM by reflexivity.
      replace (64 * 2 ^ 2) with 256 in FRSH, HH1 by reflexivity.
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb; [| exfalso; (flat constr:(FRSH) 3%nat; flclear FRSH; intros F0 F1 _); clear - Kb F0 F1 ALO ACV LOS SLO SPR; lia ].
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 256 junkf [] [24; 8; 8; 24; 4; 4; 8; 8; 40; 8; 112; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 1%nat FH FRM1. chunk_split FRM1 1%nat G1 FRM2. chunk_split FRM2 1%nat HPL FRM3. chunk_split FRM3 1%nat RZ1 FRM4.
      chunk_split FRM4 2%nat OTG FRM5. chunk_split FRM5 1%nat OLN FRM6. chunk_split FRM6 1%nat OPW FRM7. chunk_split FRM7 1%nat RZ2 FRM8.
      chunk_split FRM8 1%nat HLN FRM9. clear G1 RZ1 RZ2 FRM9.
      replace (FB + 24 + 8) with (FB + 32) in HPL by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24) with (FB + 64) in OTG by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8) with (FB + 72) in OLN by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 8) with (FB + 80) in OPW by (clear; lia).
      replace (FB + 24 + 8 + 8 + 24 + 8 + 8 + 8 + 40) with (FB + 128) in HLN by (clear; lia).
      cb8_to_c8 HPL (@nil cell). cb8_to_c8 OLN (@nil cell). cb8_to_c8 OPW (@nil cell). cb8_to_c8 HLN (@nil cell).
      cb4_to_c4 OTG (@nil cell).
      lazymatch type of OTG with rw_cells _ _ _ [?c0; _] => cb4_to_c4 OTG [c0] end.
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
      (* [comment removed for export] *)
      lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 2%nat FRa SPILL end.
      replace (bv_unsigned sp + -96 + 16) with (bv_unsigned sp + -80) in SPILL by (clear; lia).
      lazymatch goal with ST2x : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa ST2x (bv_unsigned sp + -80); rename ST2x into STK2 end.
      destruct (stk_slot asegs m3 sp1 (bv_unsigned sp + -80) (sp1 + 8) 8 STK2 ltac:(clear; lia) ltac:(clear - SP1; lia)) as [jsp0 SLOT0].
      cb8_to_c8 SLOT0 (@nil cell).
      (* [comment removed for export] *)
      assert (INF : In (FB, 256) ((FB, 256) :: LF)) by (left; reflexivity).
      pose proof (hcs_fake asegs R HIA h1 LB _ m3 FB 256 HH1 INF) as CFB. rewrite Ehcs in CFB.
      assert (INH : In (FB, 24) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; left; reflexivity).
      assert (IND : In (FB + 32, 216) (LB ++ fdata ((FB, 256) :: LF))) by (apply in_app_iff; right; right; left; reflexivity).
      pose proof (fresh_apart_client _ LB LF lo ALG 24 FB 256 FRSH CR1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP1.
      pose proof (fresh_apart_client _ LB LF lo MGF 4 FB 256 FRSH CR2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP2.
      pose proof (fresh_apart_client0 _ LB LF lo BUF (Z.of_nat (length bs)) FB 256 FRSH CR4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as AP4.
      pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'.
      idtac "BODY".
      eapply body_walk with (FB := FB) (sp1 := sp1) (h1 := h1) (m0 := m).
      all: bw_side.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Walk.

Lemma A_x509_hash_alg_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_hash_alg ()) "PR,$21.PHIA,(22.$;.R1.)P,(23.R2.R1.)P,(2.$3.(24.R3.)$25.)P,(2.$3.(26.R4.+2.)$27.)(28.$;.R5.R4.$1>.)")
(* [comment removed for export] *).
Proof.
  intros R HIA ORT UARG SM2. flat constr:(ORT) 2%nat. intros IMG _. pose proof (A_asn1_get_tag_spec (arl_AL R) IMG) as GT.
  pose proof (A_oid_get_md_alg_spec R HIA ORT) as MDALG.
  unfold x509_hash_stmtA. intros. subst.
  eapply main_walk; eauto.
Qed.
