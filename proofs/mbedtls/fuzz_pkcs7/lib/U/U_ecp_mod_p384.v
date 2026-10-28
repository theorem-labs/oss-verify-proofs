(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_core_mla U_mpi_core_add U_ecp_red.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_SumsArr LxU_SumsEcp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01829c31ed64a208 1 1 4 1 0 1 2 84 1 116 1P023da8cca651a499 0 3 0 1 86 1 93 1P033bbbefa00a561d 2 97 1 1 8 3 2 1 118 1 121 1 4 0 2 119 2 120 2 122 16 1 1 8 3 1 1 119 1 120 1 5 0 1 86 4 118 1 121 1 122 8P04888151a9ea104d 1 1 4 1 0 1 3 24 1 31 1 56 1P056e6dda8cd45c9d 1 1 4 1 0 1 3 42 1 49 1 74 1P059c55f2d60f8364 1 1 4294967295 9 0 4294967296 29 4294967296 32 4294967295 37 4294967296 39 1 41 4294967295 43 4294967296 45 1 92 1 2 48 1 94 1P05ad6e486768f1a4 1 1 4 1 0 1 3 40 1 47 1 72 1P0603f3e9c703db39 1 1 4 1 0 1 3 18 1 25 1 50 1P090fe0fb680e20ad 0 3 0 1 86 1 93 1P092d38507ecc7a52 0 2 0 1 8 1P09c561aef261ba94 1 1 4294967296 1 0 1 2 2 1 102 1P09e25783e9f65e0b 0 3 0 1 88 1 95 1P0a03669572d7e370 1 1 4 1 0 1 2 86 1 118 1P0a43ab11f42cc368 1 1 16 3 0 1 120 1 121 1 8 87 4 89 1 110 1 111 1 112 1 119 1 122 1 123 16P0ad1ff156811b3b4 1 1 16 3 0 1 122 1 123 1 8 89 4 91 1 112 1 113 1 114 1 121 1 124 1 125 16P0b0cd914a9c39413 2 97 1 1 8 3 2 1 118 1 121 1 4 0 2 119 2 120 2 122 16 1 1 8 3 1 1 119 1 120 1 5 0 1 86 4 118 1 121 1 122 8P0b7982370251ac71 0 2 0 1 2 1P0bd2c6eb51669058 0 2 0 1 121 1P0c233ba77e027acb 0 3 0 1 88 1 95 1P0cd891e70c41d21a 1 1 16 3 0 1 120 1 121 1 8 87 4 89 1 110 1 111 1 112 1 119 1 122 1 123 16P0cf8b16683336d0d 1 1 8 3 1 1 126 1 129 1 4 2 2 127 2 128 2 130 16P0d3f710a0817d6ad 0 6 0 16 82 16 90 64 97 64 124 16 125 16P0d4fc0963a6ffdbe 1 1 4 1 0 1 2 90 1 124 1P0d9e0626fd698cf4 0 3 0 1 86 1 93 1P0f030740edeb2611 2 100 1 1 8 3 2 1 120 1 123 1 4 0 2 121 2 122 2 124 16 1 1 8 3 1 1 121 1 122 1 5 0 1 88 4 120 1 123 1 124 8P11f234bd09873669 1 1 16 3 0 1 122 1 123 1 8 89 4 91 1 112 1 113 1 114 1 121 1 124 1 125 16P1246a2a04cc06b01 1 1 16 2 93 1 125 1 3 0 1 124 1 126 16P12847c3f6ed9196a 0 2 0 1 120 1P1394622a9812391a 1 1 16 3 0 1 120 1 121 1 8 87 4 89 1 110 1 111 1 112 1 119 1 122 1 123 16P1445afb5497a4354 2 103 1 1 8 3 2 1 122 1 125 1 4 0 2 123 2 124 2 126 16 1 1 8 3 1 1 123 1 124 1 5 0 1 90 4 122 1 125 1 126 8P163c6df3771119d4 0 3 0 1 88 1 95 1P1652418533039391 1 1 4 1 0 1 3 52 1 59 1 84 1P1675fce31ec0c01b 0 3 0 1 90 4 97 4P1699742bbc0fb6fb 1 1 4 1 0 1 2 88 1 120 1P17e5ed45c30c78f4 0 2 0 1 2 1P17ec8956db5455cb 1 1 16 3 0 1 118 1 119 1 8 85 4 87 1 108 1 109 1 110 1 117 1 120 1 121 16P1815f1a92f133109 1 1 4 1 0 1 3 14 1 21 1 46 1P192ce9c9c8ca12c6 1 1 4 1 0 1 2 86 1 118 1P1933b6dfb9d9da65 1 1 4 1 0 1 3 90 1 97 1 124 1P19c0c12840b1480c 2 103 1 1 8 3 2 1 122 1 125 1 4 0 2 123 2 124 2 126 16 1 1 8 3 1 1 123 1 124 1 5 0 1 90 4 122 1 125 1 126 8P1b4e175bee6d0eed 0 3 0 1 86 1 93 1P1b57a2a8b39ce0ae 1 1 4 1 0 1 3 32 1 39 1 64 1P1c0446a9382b46c8 1 1 4 1 0 1 3 50 1 57 1 82 1P1c40c6b4d12d849e 1 1 16 3 0 1 122 1 123 1 8 89 4 91 1 112 1 113 1 114 1 121 1 124 1 125 16P1c649c9e84ab2f4a 1 1 4 1 0 1 2 86 1 118 1P1cb69a0110150a2e 1 1 4 1 0 1 3 26 1 33 1 58 1P1d9452fea179f33e 1 1 4294967295 9 0 4294967296 30 4294967296 31 4294967295 38 4294967296 40 1 42 4294967295 44 4294967296 46 1 93 1 2 47 1 94 1P1da174881ee37b63 0 6 0 1 32 1 40 1 41 1 46 1 48 1P1e949fc00dbc7328 0 5 0 1 114 1 115 1 124 1 125 1P1eed190665260420 1 1 4 1 0 1 3 28 1 35 1 60 1P1ef2e80762055f14 1 1 4 1 0 1 2 88 1 120 1P209282e6ca357ac5 1 1 4 1 0 1 3 46 1 53 1 78 1P214ab4f9b64a854e 2 100 1 1 8 3 2 1 120 1 123 1 4 0 2 121 2 122 2 124 16 1 1 8 3 1 1 121 1 122 1 5 0 1 88 4 120 1 123 1 124 8P21d2346f3c91d7d6 1 1 4 1 0 1 3 56 1 63 1 88 1P22158b2651833b90 1 1 16 3 0 1 126 1 127 1 8 91 4 93 1 114 1 115 1 116 1 125 1 128 1 129 16P22affc7bc169c918 1 1 4 1 0 1 3 34 1 41 1 66 1P2356822502d59d9f 1 1 4 1 0 1 3 38 1 45 1 70 1P23dc8654b46754dd 0 2 0 1 2 1P24cfff00546863e8 0 3 0 1 84 1 91 1P24db3edd1c06fcdf 0 3 0 1 88 1 95 1P24f29d7b1881517e 0 2 0 1 2 1P24f6dfe387966218 1 1 4 1 0 1 2 84 1 116 1P253275a9cb3ddd7b 1 1 4 1 0 1 3 22 1 29 1 54 1P264f21244191ff44 2 103 1 1 8 3 2 1 122 1 125 1 4 0 2 123 2 124 2 126 16 1 1 8 3 1 1 123 1 124 1 5 0 1 90 4 122 1 125 1 126 8P2769ebe348075028 0 2 0 1 121 1P2c15901be78cf1bf 2 103 1 1 8 3 2 1 122 1 125 1 4 0 2 123 2 124 2 126 16 1 1 8 3 1 1 123 1 124 1 5 0 1 90 4 122 1 125 1 126 8P2d0f832e3112f7e8 1 1 4 1 0 1 2 84 1 116 1P2d8b804d594940a5 1 1 4294967296 1 0 1 2 2 1 106 1P2e07fe1b30e92b8a 0 10 0 16 90 64 92 16 113 16 114 16 115 16 124 16 125 16 126 16 127 16P2e7adf5e83eb2332 0 2 0 1 120 1P2eb0035987f71fb3 1 1 4294967296 1 0 1 2 8 1 100 1P2edb1e310d1e6404 1 1 4 1 0 1 3 54 1 61 1 86 1P2fea2bbd1f196ecc 2 97 1 1 8 3 2 1 118 1 121 1 4 0 2 119 2 120 2 122 16 1 1 8 3 1 1 119 1 120 1 5 0 1 86 4 118 1 121 1 122 8P307961e8f4b683ec 1 1 8 3 0 1 127 1 128 1 5 2 1 92 4 126 1 129 1 130 8P30f8c0d6f4aa76c8 0 3 0 1 84 1 91 1P311a062abbd7cdea 1 1 4 1 0 1 3 44 1 51 1 76 1P317547cac071b282 1 1 4 1 0 1 3 12 1 19 1 44 1P31d460e21166fb4a 2 100 1 1 8 3 2 1 120 1 123 1 4 0 2 121 2 122 2 124 16 1 1 8 3 1 1 121 1 122 1 5 0 1 88 4 120 1 123 1 124 8P31fc3eed81cf0483 0 3 0 1 90 4 97 4P32cc825fb70837f4 1 1 4 1 0 1 2 86 1 118 1P3370af5560eb38a7 1 1 4 1 0 1 2 84 1 116 1P337b03f0738a204a 0 2 0 1 2 1P33b1ff813588a6ca 0 3 0 1 84 1 91 1P343a6351d70ad927 0 10 0 16 90 64 92 16 113 16 114 16 115 16 124 16 125 16 126 16 127 16P35005c0e995f31c6 1 1 16 3 0 1 122 1 123 1 8 89 4 91 1 112 1 113 1 114 1 121 1 124 1 125 16P359710978db9e436 0 2 0 1 2 1P361f569a7d2a873e 2 97 1 1 8 3 2 1 118 1 121 1 4 0 2 119 2 120 2 122 16 1 1 8 3 1 1 119 1 120 1 5 0 1 86 4 118 1 121 1 122 8P36507d240294b0cb 0 2 0 1 120 1P377485c5aac365cc 1 1 4 1 0 1 2 88 1 120 1P377f3c1aa719a0dc 0 6 0 1 91 4 93 1 114 1 127 1 128 1P37addb5950908e39 1 1 4 1 0 1 3 48 1 55 1 80 1P38217aad9b97794c 2 100 1 1 8 3 2 1 120 1 123 1 4 0 2 121 2 122 2 124 16 1 1 8 3 1 1 121 1 122 1 5 0 1 88 4 120 1 123 1 124 8P3837fa4c06b8ec56 1 1 4 1 0 1 3 16 1 23 1 48 1P38da89c122db55f8 0 3 0 1 84 1 91 1P395cfe8a0f32974d 1 1 4 1 0 1 2 88 1 120 1P398a4e851044b8bf 1 1 16 3 0 1 118 1 119 1 8 85 4 87 1 108 1 109 1 110 1 117 1 120 1 121 16P39d7add5e226ce29 1 1 16 3 0 1 118 1 119 1 8 85 4 87 1 108 1 109 1 110 1 117 1 120 1 121 16P3a692232257dc547 1 1 16 3 0 1 118 1 119 1 8 85 4 87 1 108 1 109 1 110 1 117 1 120 1 121 16P3b66563139205f9a 1 1 4 1 0 1 3 58 1 65 1 90 1P3b8de5dfb2e92be3 1 1 4294967296 1 0 1 2 2 1 104 1P3c9b8767299f69ac 1 1 16 3 0 1 120 1 121 1 8 87 4 89 1 110 1 111 1 112 1 119 1 122 1 123 16P3d3a3b4145536690 1 1 4 1 0 1 3 30 1 37 1 62 1P3eb245429f81972a 0 6 0 1 31 1 39 1 42 1 45 1 47 1P3eb59ebe28ca677f 0 5 0 1 113 1 114 1 123 1 124 1P3f710a4a55719127 1 1 4 1 0 1 3 20 1 27 1 52 1P3f7af6d5b4dca1d0 1 1 4 1 0 1 3 36 1 43 1 68 1N006f613aab4396b4N00902163feacf3c3N009937e5b246dc50N00dacb71a36d538cN013c3bdd831453d1N014b635ca58cfe4aN0182e25f8f2c0e4fN01f72c24838a70c1N025ac4ab9489d21fN03bdcb99da8a0688N04974362a3846807N05636edc731fceaaN083937f33549b5ecN09f793d77e145ec5N09f7c098dee0330fN0b45468648e7c322N0bbc205063487b46N0cf6a986246d588aN0e423e44c1b09ff2N0f33a444c531c2d6N0f62be0213679940N106e6d477e18bf03N1146ec9b12994f1eN11da6f9d557e6a8aN137bc9aed3ac3587N15525b90be0ce326N15cc761546ab7bf3N15da85d445e742a0N1616e32d7a1b9814N17e64082243f4416N180fa77ca592d3e7N180fe3aea12cc85eN181678f668021895N18555972fa1e7be6N18eefabec414fe70N194de955f1c573c2N195451b9cf8c7632N1a80f8c67b824429N1b38b2fce415eac5N1ba39f6a8c718f7bN1bcf8b246b706a3cN1c82205307de8617N1d8408b7e2cf08eeN1d8d764175ef8631N1e5daa37e5c696e5N1e79411eeaf072d8N1f5cd64416d44a1eN207a115c52eaccfcN2362c0dfa0e90d35N236fc26608d6560bN23d0ee89fc35f3b0N23d9e67b629019c2N24073c5e6e2a2253N261db0117465366aN27239a5a757ea0deN2799048a454006c4N284f4520f76c4d6dN28971346680dfa88N28c85d4082e9b329N29bc2709b629230dN2a5c2a8ab9ca2f4aN2aa7d79968ad1ca3N2bc3080fed10315eN2bd51595cb15cb52N2c10a1e57b77511fN2c49e8e54d0ca348N2dcb17b3cf0338b1N2ee89c63765da359N2f2ed2354346765dN30710a20ccbc8babN3094748576e8ea2aN315c4befb90c771fN31e1e496572942c1N3286a54d1fe4d222N32ad99ddfc09237eN346c12ace79ddca7N35a45f68b9e26396N35a5a162c31391c2N366b6694b277c8aaN37574d9ef52ca86dN38644998af90e6c5N38affd44c30b08bfN39aa8cda03118299N3bf890e88ccc526fN3c4410105a3704feN3c7e31dec68aeb66N3cfe781722ea094bN3d09e52bf03b714eN3dcb59e3f175110eN3fc416a48479c0f4"%lxh.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_ECP_MOD_P384 : Z := 0x3ce38.

(* [comment removed for export] *)
Ltac ecp_leaf_gc :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | u32arr _ _ _ _ => fail | rw_cells _ _ _ _ => fail | bytes_at _ _ _ _ => fail
    | context [zlow _ _] => clear H | context [zswrap _ _] => clear H | context [Z.b2z _] => clear H
    end end;
  repeat match goal with
  | H : 0 <= ?v + 2147483648 |- _ => is_var v; clear H
  | H : 0 <= - ?v + 2147483647 |- _ => is_var v; clear H
  | H : 0 <= ?v, H' : 0 <= - ?v + 18446744073709551615 |- _ => is_var v; clear H H'
  end;
  repeat match goal with v : Z |- _ => clear v end.

Section RED.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0240@L10007733624.111L10009931224.220L10009931224.222L10311464405.81 L11093748286.110L11803550370.82 L11805629605.85 L11879608932.81 L13098889560.111L13098889560.81 L14795424372.81 L18868739288.111L18868739288.81 L19026695374.123L20806881524.81 L2138888664.111 L2138888664.81  L21541644120.111L21541644120.81 L2211492706.81  L24167279349.81 L26416551794.4  L26828156276.81 L27144187718.114L2759026548.81  L28689697126.220L28689697126.222L28692136132.74 L29012665503.110L29834048600.111L29834048600.81 L3043381336.111 L3043381336.81  L32855866356.81 L35609665496.111L35609665496.81 L37321587599.81 L37321635735.102L38017522480.129L3818668784.81  L3820734411.220 L3820734411.222 L38282648152.111L38282648152.81 L38866126964.81 L43061838089.78 L44622288685.83 L44622288685.84 L44891662068.81 L4541941209.2   L45425587647.3  L45674082520.111L45674082520.81 L46154007276.220L4643969249.110 L47401587060.81 L4742244590.226 L4742244590.227 L4742244590.228 L4742244590.229 L4742244590.230 L4742244590.231 L47759495350.226L47759495350.227L47759495350.228L47759495350.229L47759495350.230L47759495350.231L48472962717.111L48962555340.83 L49698585326.83 L49698585326.84 L50903118708.80 L52102261165.226L52102261165.227L52102261165.228L52102261165.229L52102261165.230L52102261165.231L52155532688.111L52361663192.111L52361663192.80 L52616107219.126L53410279412.81 L53714065071.83 L53714065071.84 L54106875608.111L54106875608.81 L54391891673.84 L54392444536.227L54392444536.228L54392444536.229L54392444536.230L54392444923.228L54392444923.229L54392444923.230L54392444923.231L54398396379.227L54398396379.228L54398396379.229L54398396379.230L55013023064.111L55013023064.81 L57628696595.14 L57628700040.8  L59314873579.229L59314873579.230L59314873579.231L59314873579.232L59438513268.81 L60330452198.80 L61500549818.113L62417105880.111L62417105880.81 L63559401084.114L63566334731.81 L63698771125.114L65349003981.81 L65451395828.81 L65502165646.74 L65502251305.123L65699637964.225L65699637964.227L68616792782.222L7024252226.226 L7024252226.227 L7024252226.228 L7024252226.229 L7035960241.81  L7040613684.112 L8769959412.81  L9144264913.81  00000:00T00n01>01H02102V02l03603@03J03T03^04G04Q04[04e04o05905L05V05d05n06R06\07M08>08\08]08g09109;09E09O09Y09c0:I0:o0;e0<80<[0=>0=H0=R0=\0>:0?20@M0@W0@X0@Y0@c0@m0AG0AQ0A[0B:0C40D10Dn0Eh0F]0GD0Gn0HX0IB0Il0JS0K10KS0L30M60M@0Ma0NE0Ni0OM0P10PR0P\0Pf0Q00QI0QS0Qo0Rn0S80SB0So0Ti0Uc0V]0WW0XR0YM0ZH0[C0\=0]70^10^k0_50_?0_k0`D0aU0bb0d30e@0eJ0eT0f=0fG0fQ0fc0fm0g>0gh0h20h<0hJ0hl0iN0ih0jI0jj0kK0kl0l60l@0lJ0lTS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsfS1L2sp2dX3DHI2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2I4S1L2HI2sp1h2dX4HTOP2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22B0S2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L2sp2dX2lo3SLO2XBS2sp2dX2XBS2dX3dX22n22N2S2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB1HS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XBS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp2dX2XBFFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB3dX22n22P'5lxwsf1a2C12C21L2lo3ACL3SPB2X02B02B41l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n02C2S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n0S1L3HLS2sp2dX2lo3SLO3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XBS2ra2sp2dX3SPB2XB2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C11n2C2S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21nS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L2HI2sp1h2dX2XB3dX21a1CS2sp2dX2XBS2ra2sp2dX2XB2HB5Ha_st5Hl_stS2sp2s02dX2XB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2sp2dX2XBS2sp2dX2XBS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS2sp2dX2XBS2sp2dX2XBS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C21l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C21l2l02Rb1HS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS2sp2dX2XBS2sp2dX2XBS1L2sp2dX2XB2I32I4S2sp2dX2XBS2sp2dX2XB2xx3HxxS1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB". (* [comment removed for export] *)
  Lemma U_ecp_mod_p384_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P384 U_MEMSET_FUNC 24 176.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P384. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(MA) 2%nat. intros FLt1 _. flat constr:(FLt1) 4%nat. flclear FLt1. intros CH XAL X0 _. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add mpi_cells length] in XB. clear CH.
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 48%nat ST.
    do 10 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (MA1 : mpd_at usegs m1 LB dX).
    { eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; lia|].
      intros O. flat constr:((mpdr_blk_facts usegs L m LB dX (proj1 MA) O HBR)) 5%nat. intros _ _ I3 I4 _. cbn. lia. }
    assert (PX1 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1) by (eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]).
    clear HH MA MU WM.
    (* [comment removed for export] *)
    pose proof (U_mpi_grow_spec L HI HFREE HCALLOC HLS SW DIMG HND) as SG. unfold mpi_grow_stmt, U_MPI_GROW in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 24); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3ce60)) with (Z_to_bv 64 0x3ce60) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (OLDL : md_own dX = LHeap -> 0 < md_p dX /\ md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros O. flat constr:((mpdr_blk_facts usegs L m1 LB dX (proj1 MA1) O HBR)) 5%nat. intros _ _ I3 I4 _. lia. }
    presx_stack usegs L PXg ltac:(unfold mpd_ivs; destruct (md_own dX) eqn:?; cbn;
                                 [ split; [lia| exact I] | split; [lia|]; split; [pose proof (OLDL eq_refl); lia| exact I] | exfalso; apply NST; reflexivity ]).
    assert (PX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply (heap_presx_weaken usegs L); [exact PXg| lia| intros x Hx; exact Hx]. }
    clear PX1 ST MI SOK MK HH1 MA1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 _.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & _)|[Er EdX]] FRr]; [exfalso; subst r; apply K; reflexivity|]. subst dX2.
      zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 24 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
      flat constr:((grow_ok_facts _ _ _ _ _ _ _ MA2 OUT2 GR ltac:(lia))) 9%nat. intros O2 N2 S2 P2 EA2 LEN IN2 PAL2 U.
      flat constr:((proj1 (Forall_forall _ _) HBR2 _ IN2)) 5%nat. intros B0 _ _ B4 B5. cbn in B0, B4, B5.
      assert (APX : md_addr dX + 16 <= md_p dX2 \/ md_p dX2 + 4 * md_n dX2 <= md_addr dX).
      { eapply (new_limbs_apart_range usegs L HI) with (SP := bv_unsigned sp); [exact HH2| exact MA2| exact OUT2| exact FRr| lia| exact DI1| exact DI2| | lia| exact XP| exact O2].
        intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      flat constr:(MA2) 2%nat. intros (CH2 & _) _. rewrite EA2, S2, P2 in CH2. unfold mpi_cells in CH2.
      set (P' := md_p dX2) in *. set (n2 := md_n dX2) in *. set (ws0 := md_limbs dX2) in *.
      pose proof (u32arr_bound _ _ _ _ U) as UB. assert (PB : P' + 4 * n2 <= 2 ^ 64) by lia. clear UB.
      pose proof (same_from_refl (Z.to_nat n2) ws0) as FS.
      clear MU WM. pose proof (munch_refl [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      pose proof (conj HH2 I) as HH0. clear HH2. pose proof (conj MA2 I) as MA0. clear MA2.
      clearbody ws0.
      (* [comment removed for export] *)
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 24 <= n2) by (clear -N2; lia).
      clear MU. pose proof (munch_refl [(P', P' + 4 * n2); (lo, bv_unsigned sp)] m2) as MU.
      pose proof (sumsecp_ok [P']) as LXSUMS.
      apply (lxp_aevtM_of_evt _ _ _ _ MK). lx_mkR.
      lx_run_tac (PLANS [] [] 400%N SUMSECP); lx_tree.
      (* [comment removed for export] *)
      all: try (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
             tryif lx_is_zlit e then fail else
             match goal with H1 : 0 <= e, H2 : 0 <= - e |- _ => replace e with 0 by (clear -H1 H2; lia) end end).
      all: lx_gen_regs; apply evt_done; try clear U; try clear LEN; try clear MU; try clear WM;
        let mx := lx_cur_mem in let xP := constr:(P') in let xm := constr:(m2) in let xlo := constr:(lo) in let xsp := constr:(sp) in
        lazymatch goal with Hu : u32arr _ mx xP ?l |- _ => rename Hu into U;
          assert (LEN : Z.of_nat (length l) = n2)
            by (first [ rewrite ?upd_length; exact (unlock _ LEN0)
                      | lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ => rewrite Hl end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption]
                      | rewrite ?upd_length;
                        lazymatch goal with |- Z.of_nat (length ?l2) = _ => lazymatch goal with Hl : Z.of_nat (length l2) = _ |- _ => rewrite Hl end end;
                        rewrite ?upd_length; first [exact (unlock _ LEN0) | assumption] ]);
          (* [comment removed for export] *)
          repeat match goal with Hl : Z.of_nat (length _) = Z.of_nat (length _) |- _ => clear Hl end;
          set (lxwsf := l) in U, LEN; clearbody lxwsf; ecp_leaf_gc
        end;
        lazymatch goal with Hm : munch _ xm mx |- _ =>
          assert (MU : munch [(P', P' + 4 * n2); (md_addr dX, md_addr dX + 16); (lo, bv_unsigned sp)] m2 mx)
            by (eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia);
          match goal with SO : statics_ok _ _ xm |- _ =>
            eapply (statics_ok_munch usegs L) in SO; [| exact Hm| intros aa Ha _; cbn; clear -Ha B5 DI1 DI2 ACL DHI LO0; lia] end;
          clear Hm end;
        lazymatch goal with Hw : wmono _ xm mx |- _ => rename Hw into WM end;
        try clear ST2; lx_release_frame; lazymatch goal with Hs : stk _ mx xlo ?h |- _ => (tryif constr_eq h (bv_unsigned sp) then idtac else replace h with (bv_unsigned sp) in Hs by (clear; lia)); rename Hs into ST2 end;
        let xa := constr:(md_addr dX) in
        try clear CH2; lazymatch goal with Hc : rw_cells _ mx xa _ |- _ => rename Hc into CH2 end;
        repeat match goal with H : lx_opq _ _ _ _ _ _ _ |- _ => clear H end.
      all: (flat constr:(HH0) 2%nat; flclear HH0; intros HH2 _). all: (flat constr:(MA0) 2%nat; flclear MA0; intros MA2 _).
      1: {
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mfin end.
        apply aevtM_done. unfold mpi_binop_post.
        try match goal with Kz : bv_unsigned ?v = 0 |- _ => is_var v; replace v with (Z_to_bv 64 0) in * by (apply bv_eq; rewrite Kz; reflexivity) end.
        lazymatch type of U with u32arr _ _ _ ?wsf =>
          (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] => lazymatch xa0 with Z_to_bv 64 0 => flexi 17%nat; exists LB2, (relimb dX2 wsf), 0 | _ => flexi 17%nat; exists LB2, (relimb dX2 wsf), MBEDTLS_ERR_ECP_BAD_INPUT_DATA end end) end.
        split; [first [reflexivity| do 2 f_equal; apply bv_eq; vm_compute; reflexivity]|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
        split. { apply (@HEAP_munch usegs L HI h2 _ m2 mfin mo2 _ lo HH2 MU WM ACL).
                 intros a Ha NO. cbn in NO. rewrite HT2.
                 destruct (Z_le_dec P' a) as [C1|C1]; [destruct (Z_lt_dec a (P' + 4 * n2)) as [C2|C2]|].
                 - right. right. exists (P', 4 * n2). split; [exact IN2| cbn; lia].
                 - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                   + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                     exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                     unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                   + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                     exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                     unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..]. }
        split. { eapply relimb_at; [exact MA2| exact O2| rewrite EA2, S2, P2; unfold mpi_cells; exact CH2| exact U| rewrite LEN; reflexivity]. }
        split. { eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; rewrite O2; discriminate| reflexivity]. }
        split. { eapply (reducer_presx usegs L HI) with (lo' := lo); [exact HH2| exact MA2| exact OUT2| exact FRr| exact O2| exact EA2| exact PX2| | exact WM| lia| lia| exact DHI| exact DI1| exact DI2].
                 rewrite EA2. exact MU. }
        split; [assumption|].
        eapply reducer_R_ok; [exact MA2| exact OUT2| exact GR| lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_ECP_BAD_INPUT_DATA; lia].
      }
      1: {
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mfin end.
        apply aevtM_done. unfold mpi_binop_post.
        try match goal with Kz : bv_unsigned ?v = 0 |- _ => is_var v; replace v with (Z_to_bv 64 0) in * by (apply bv_eq; rewrite Kz; reflexivity) end.
        lazymatch type of U with u32arr _ _ _ ?wsf =>
          (lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ ?xa0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] => lazymatch xa0 with Z_to_bv 64 0 => flexi 17%nat; exists LB2, (relimb dX2 wsf), 0 | _ => flexi 17%nat; exists LB2, (relimb dX2 wsf), MBEDTLS_ERR_ECP_BAD_INPUT_DATA end end) end.
        split; [first [reflexivity| do 2 f_equal; apply bv_eq; vm_compute; reflexivity]|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
        split. { apply (@HEAP_munch usegs L HI h2 _ m2 mfin mo2 _ lo HH2 MU WM ACL).
                 intros a Ha NO. cbn in NO. rewrite HT2.
                 destruct (Z_le_dec P' a) as [C1|C1]; [destruct (Z_lt_dec a (P' + 4 * n2)) as [C2|C2]|].
                 - right. right. exists (P', 4 * n2). split; [exact IN2| cbn; lia].
                 - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                   + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                     exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                     unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                 - destruct (Z_le_dec (md_addr dX) a); [destruct (Z_lt_dec a (md_addr dX + 16))|].
                   + destruct (XCW a ltac:(lia)) as [Q|[Q|([bb kk] & Hb & Rb)]]; [left; lia| right; left; exact Q| right; right].
                     exists (bb, kk). split; [| exact Rb]. flat constr:(OUT2) 5%nat. flclear OUT2. intros _ _ _ K2 _. apply K2; [exact Hb|].
                     unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [Eb|[]]. injection Eb; intros; subst. cbn in Rb. pose proof (XP eq_refl). lia.
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..].
                   + left. destruct (Z_le_dec lo a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; (flsplit; repeat split); try exact I; lia..]. }
        split. { eapply relimb_at; [exact MA2| exact O2| rewrite EA2, S2, P2; unfold mpi_cells; exact CH2| exact U| rewrite LEN; reflexivity]. }
        split. { eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; rewrite O2; discriminate| reflexivity]. }
        split. { eapply (reducer_presx usegs L HI) with (lo' := lo); [exact HH2| exact MA2| exact OUT2| exact FRr| exact O2| exact EA2| exact PX2| | exact WM| lia| lia| exact DHI| exact DI1| exact DI2].
                 rewrite EA2. exact MU. }
        split; [assumption|].
        eapply reducer_R_ok; [exact MA2| exact OUT2| exact GR| lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED, MBEDTLS_ERR_ECP_BAD_INPUT_DATA; lia].
      }
  all: match goal with |- ?gg => idtac "REDLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

