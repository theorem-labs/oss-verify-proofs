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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c1c63d2e859a27 1 1 16 3 0 1 96 1 97 1 8 63 4 65 1 86 1 87 1 88 1 95 1 98 1 99 16P0105fd27b64fb922 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P01db0d0dfb9bae39 0 2 0 1 2 1P02e16b9e59b2eadf 1 1 4 1 0 1 2 62 1 94 1P03d35e74e38a25aa 0 3 0 1 64 1 71 1P041db88ecfd71349 0 2 0 1 95 1P05b710099a46f258 0 3 0 1 64 1 71 1P063c2a29531cfdff 1 1 4 1 0 1 2 64 1 98 1P07084bab4c4ac79e 1 1 4294967296 1 0 1 2 2 1 82 1P0752d0cb4cfd3edb 1 1 4294967296 1 0 1 3 4 1 12 1 90 1P09350945f9418187 0 3 0 1 64 1 71 1P098c1b14199bb42e 1 1 4 1 0 1 3 16 1 23 1 48 1P0abe8dc451141442 0 3 0 1 60 1 67 1P0ad2464a7e365ebe 1 1 4 1 0 1 3 14 1 21 1 46 1P0ae1bd4a1e7f5593 1 1 4 1 0 1 2 64 1 98 1P0aef4530010ba1e5 0 3 0 1 60 1 67 1P0b934e59bdafd7c5 1 1 4 1 0 1 3 40 1 47 1 72 1P0bfc422f212f114e 1 1 4 1 0 1 2 64 1 98 1P0dbd4c80fc153037 0 5 0 1 87 1 88 1 97 1 98 1P0e6ba57843344344 1 1 4 1 0 1 3 30 1 37 1 62 1P0ed5e74976a2377c 2 72 1 1 8 3 2 1 97 1 98 1 4 0 2 96 2 99 2 100 16 1 1 8 3 1 1 96 1 99 1 5 0 1 64 4 97 1 98 1 100 8P0f3e94272596d258 0 2 0 1 2 1P0f49cff7167b6d4b 1 1 4 1 0 1 3 28 1 35 1 60 1P0f9690f3b0e1cea0 1 1 4 1 0 1 2 64 1 98 1P0fe625f625375451 0 3 0 1 64 1 71 1P1003d7460297b37e 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P10ad74dba34c7603 0 3 0 1 60 1 67 1P115c27336c8b2917 2 72 1 1 8 3 2 1 97 1 98 1 4 0 2 96 2 99 2 100 16 1 1 8 3 1 1 96 1 99 1 5 0 1 64 4 97 1 98 1 100 8P11bed2170b0cc7a3 0 3 0 1 4 1 12 1P12e3e6ca790a6e6f 1 1 4 1 0 1 3 42 1 49 1 74 1P12e8314bf65722bb 0 12 0 4294967296 14 4294967296 16 1 17 4294967296 19 4294967297 21 4294967297 23 4294967297 25 1 28 4294967296 30 4294967297 32 1 77 1P130decba4dab2927 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P136cd749aa1a1c7f 0 12 0 4294967296 13 4294967296 15 1 18 4294967296 20 4294967297 22 4294967297 24 4294967297 26 1 27 4294967296 29 4294967297 31 1 76 1P137c5f1c38a3d081 1 1 16 3 0 1 94 1 95 1 8 61 4 63 1 84 1 85 1 86 1 93 1 96 1 97 16P13e9f8461b31fed4 2 72 1 1 8 3 2 1 97 1 98 1 4 0 2 96 2 99 2 100 16 1 1 8 3 1 1 96 1 99 1 5 0 1 64 4 97 1 98 1 100 8P13eba78120cde145 0 3 0 1 60 1 67 1P143fa8b036a1f74c 1 1 4 1 0 1 2 60 1 92 1P14db534c07388a65 0 2 0 1 94 1P1687ce1241ddbc54 2 69 1 1 8 3 2 1 95 1 96 1 4 0 2 94 2 97 2 98 16 1 1 8 3 1 1 94 1 97 1 5 0 1 62 4 95 1 96 1 98 8P16f4819f3f7a1865 0 3 0 1 64 1 71 1P1847166795e84366 2 72 1 1 8 3 2 1 97 1 98 1 4 0 2 96 2 99 2 100 16 1 1 8 3 1 1 96 1 99 1 5 0 1 64 4 97 1 98 1 100 8P186f2ab5b56af6b4 1 1 16 3 0 1 94 1 95 1 8 61 4 63 1 84 1 85 1 86 1 93 1 96 1 97 16P18ff9014c6b9c771 2 69 1 1 8 3 2 1 95 1 96 1 4 0 2 94 2 97 2 98 16 1 1 8 3 1 1 94 1 97 1 5 0 1 62 4 95 1 96 1 98 8P19cc68396d1c1aa8 1 1 16 3 0 1 96 1 97 1 8 63 4 65 1 86 1 87 1 88 1 95 1 98 1 99 16P1a61187d33455dcb 1 1 4 1 0 1 3 18 1 25 1 50 1P1b8dc5a1dc9c721f 0 5 0 1 88 1 89 1 98 1 99 1P1bbd73bd47c42aa2 0 2 0 1 94 1P1c79af62aca0442a 0 2 0 1 2 1P1cac14b121d106b7 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P1cd94cab4ff71955 1 1 4 1 0 1 2 62 1 94 1P1d55bff46572908f 0 8 0 1 15 1 20 1 22 1 24 1 26 1 29 1 31 1P1ddd366c8ed6ab05 1 1 4 1 0 1 2 60 1 92 1P2017df84ba05ce2e 0 3 0 1 62 1 69 1P201d3e42790181d3 1 1 4 1 0 1 2 64 1 98 1P2035a82af34cf56f 0 8 0 1 16 1 19 1 21 1 23 1 25 1 30 1 32 1P21efb3afef88d986 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P21ff45520c22afe2 1 1 4 1 0 1 3 38 1 45 1 70 1P226e5ab049c3cde0 0 2 0 1 95 1P23bf6cf3dec3c430 1 1 4 1 0 1 3 22 1 29 1 54 1P24da1d162dfb3131 1 1 4 1 0 1 3 26 1 33 1 58 1P25d66ad15ede2a6c 1 1 4 1 0 1 2 60 1 92 1P2622289695d82812 1 1 4 1 0 1 3 24 1 31 1 56 1P272e4f297179b643 1 1 4 1 0 1 2 64 1 98 1P27a8c1232a8615a5 1 1 16 3 0 1 94 1 95 1 8 61 4 63 1 84 1 85 1 86 1 93 1 96 1 97 16P2857736bf03e3d63 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P285dfefcc13d1b42 1 1 4 1 0 1 2 64 1 98 1P287843f30e3f6705 0 3 0 1 62 1 69 1P28e795917a3c0a46 1 1 16 3 0 1 94 1 95 1 8 61 4 63 1 84 1 85 1 86 1 93 1 96 1 97 16P297ff6caad0f47e4 1 1 4 1 0 1 3 20 1 27 1 52 1P29c4a66149f2ecf1 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P2a68383b1e80ef27 0 3 0 1 62 1 69 1P2a965294a1f84f5a 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P2c01e41c75e24d0f 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P2c1aaff1bd5b4ca6 1 1 4 1 0 1 2 64 1 98 1P2c4360fbe194b5ac 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P2c52a0da5c496ab4 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P2e9eee9955fd9825 1 1 4 1 0 1 3 34 1 41 1 66 1P2f1476d34dead2cc 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P2f5c58846f646713 0 3 0 1 64 1 71 1P2f735f40cb86f0d3 0 2 0 1 94 1P3095e2bf5e18fa35 1 1 4 1 0 1 3 12 1 19 1 44 1P323439bf5d5087cb 1 1 4 1 0 1 3 36 1 43 1 68 1P3270efbc72891b98 1 1 4 1 0 1 2 60 1 92 1P33418387a10fd3f3 0 3 0 1 62 1 69 1P344320fb24ac9bb0 0 3 0 1 64 1 71 1P353dd996bc88cc9e 2 69 1 1 8 3 2 1 95 1 96 1 4 0 2 94 2 97 2 98 16 1 1 8 3 1 1 94 1 97 1 5 0 1 62 4 95 1 96 1 98 8P35d17bc5dff1a9d4 1 1 4 1 0 1 2 62 1 94 1P37764fffad6c7f35 1 1 16 3 0 1 96 1 97 1 8 63 4 65 1 86 1 87 1 88 1 95 1 98 1 99 16P37ce2411f5a39f8e 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16P37df0944f661327a 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P3a22426a656648f2 0 3 0 1 64 1 71 1P3a4fcd904f38c930 2 69 1 1 8 3 2 1 95 1 96 1 4 0 2 94 2 97 2 98 16 1 1 8 3 1 1 94 1 97 1 5 0 1 62 4 95 1 96 1 98 8P3bd7a553b0f8c442 2 74 1 1 8 3 2 1 101 1 102 1 4 0 2 100 2 103 2 104 16 1 1 8 3 1 1 100 1 103 1 5 0 1 66 4 101 1 102 1 104 8P3c28ba1e10c74243 1 1 16 3 0 1 96 1 97 1 8 63 4 65 1 86 1 87 1 88 1 95 1 98 1 99 16P3c4d07004deab2cc 1 1 4 1 0 1 2 62 1 94 1P3c868775f6c3581f 1 1 4 1 0 1 3 32 1 39 1 64 1P3cd46c2d8644cad4 1 1 16 3 0 1 100 1 101 1 8 65 4 67 1 88 1 89 1 90 1 99 1 102 1 103 16N0205a97b1740c446N03230d63b2fcf26aN033deab77c17bf0fN04f6b02f7a96b80bN06aacda67e8ef26aN089b4cce6ae09ff6N093d78176b294572N09e082f90de4db0bN0d373c39e0bc9bdeN0da3385cd3783edeN103979ee301145e1N1305046ebd8c4207N142ce9ff81dafd5fN14be368d96772967N1677add9a98a1f9fN1704910e0cb8dc67N1811e514fcce063cN1842fbe345b64a81N18432673e036201aN19aa74a7b60f2c20N1aa32780a28ad6bdN1ab4bbac73ed0851N1b19d51759c7db75N1c4fccb1a04b990aN1cbd07bef7aa8651N1d1f86384fac49bfN2179326cdbfc5efcN219d85db9ae454f2N22b8881b8cfe6282N22ec4ebf72001b64N249110764590fc18N25917ae62fd21546N25f4a8f42d6c44caN265a8c7318df0bbeN275d688cf0aaa8b9N2899a19e4b6beaabN2a42e853bb01e1d3N2ab5df6ec6d46d8dN2c3aecd183cbc88fN2cc517dd52c1a3faN2d331cd68c45708dN2dd8e4a8019e1e69N2f4af53b6c0c4332N2f5d8572a66e2c52N30919c698ba77161N31bc69ab5682aab7N331754f9fcc17d26N337ec55d6fdc7b17N34171690f6ae4524N34428af27745a1b8N356e5d7a249e1df2N357e1f1e8aeaa1bdN35c6eb25fd1349faN361fcb2def1eb198N399002db0dfad808N3b38ee22a1a6fc73N3bfcde832bab3584N3ca10da09e33e9f8N3d5af38f9bf03f6cN3db567265f447015N3f28d9449fe28287"%lxh.
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

Definition U_ECP_MOD_P256 : Z := 0x3ca24.

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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@L10311464405.81 L11803550370.82 L11805629605.85 L12836469452.83 L19026695374.123L21765854580.81 L21887662552.111L21887662552.80 L2211492706.81  L23587552326.114L24167279349.81 L27775132660.81 L28689697126.193L28692136132.74 L29012665503.110L33510041944.111L33510041944.81 L33635213816.111L33637411160.193L34290115814.80 L35754698159.83 L35754698159.84 L38017522480.129L3818668784.81  L3820734411.193 L38443780964.81 L39945925021.111L40357717490.4  L41562522430.110L41930202676.112L41942718641.81 L43061838089.78 L44321724939.81 L44622288685.83 L44622288685.84 L45293014477.81 L4541941209.2   L45425587647.3  L45691222419.6  L46154007276.193L4742244590.199 L4742244590.200 L4742244590.201 L4742244590.202 L47501154741.114L47759495350.199L47759495350.200L47759495350.201L47759495350.202L49698585326.83 L49698585326.84 L50807132385.110L52102261165.199L52102261165.200L52102261165.201L52102261165.202L52616107219.126L54391891673.84 L54392444536.200L54392444536.201L54392444923.201L54392444923.202L54398396379.200L54398396379.201L57628696595.14 L57628700040.8  L59314873579.202L59314873579.203L63559401084.114L65054579130.113L65117534096.111L65502165646.74 L65502251305.123L65699637964.198L66083662040.111L66083662040.81 L68616792782.193L7024252226.199 L7024252226.200 L7190686615.102 L7190734735.81  L9144264913.81  L9716869748.80  00000@00i01N02002Y02c02m03703J03n04804B05305Q05R05\05f06006J06T07007O08E08X09;09Q09o0:=0:G0:Q0:[0;90;C0<;0=60=`0=a0=b0>A0>[0?:0@40@n0Ac0B40B[0CE0Co0DV0E60EY0Ec0FD0Fh0GL0Gm0HF0I30Im0Jg0Kb0L]0MW0NQ0O=0OV0Pg0R40RF0Ro0S90SC0SQ0T30T=0TG0Ta0UB0Uc0VI0Vo0W90WCS1L2sp2dX3DHI2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2I4S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22B0S2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L2sp2dX2lo3SLO2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB1HS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XBS2ra2sp2dX2XB2HB5Ha_st5Hl_stS2sp2s02dX2XB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XBS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L2HI2sp1h2dX4HTOP2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2dX3dX22n22N2S2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2sp2dX2XBS1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_st2s1S1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XBFFS5lxv165lxv205lxv215lxv232H22H3S2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2XB2xx3HxxS2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n0S2ra2sp2dX3SPB2XB2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB2HB5Ha_st5Hl_st2s1S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21nS1L2HI2sp1h2dX2XB3dX21a1CS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C21l2l02Rb1HS1L2sp2dX2XB2I32I4S1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS2sp2dX2XBS2sp2dX2XB". (* [comment removed for export] *)
  Lemma U_ecp_mod_p256_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P256 U_MEMSET_FUNC 16 96.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P256. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(MA) 2%nat. intros FLt1 _. flat constr:(FLt1) 4%nat. flclear FLt1. intros CH XAL X0 _. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add mpi_cells length] in XB. clear CH.
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 32%nat ST.
    do 8 zstep.
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
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 16); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3ca44)) with (Z_to_bv 64 0x3ca44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 16 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
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
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 16 <= n2) by (clear -N2; lia).
      clear MU. pose proof (munch_refl [(P', P' + 4 * n2); (lo, bv_unsigned sp)] m2) as MU.
      apply (lxp_aevtM_of_evt _ _ _ _ MK). lx_mkR.
      lx_run_tac (PLAN [] [] 400%N); lx_tree.
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

