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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P019836532aa6236c 0 3 0 1 46 1 53 1P0216031de7874649 0 2 0 1 79 1P0590c93596a4a800 1 1 4 1 0 1 3 28 1 35 1 60 1P05c0634a03f5e911 2 44 1 1 8 3 2 1 77 1 78 1 4 0 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 5 0 1 44 4 77 1 78 1 80 8P05c2d7134a9d5781 1 1 4 1 0 1 2 46 1 78 1P05c7381e1a41954e 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P05c939cc62510bde 0 3 0 1 46 1 53 1P0689f3f003b2ce4d 2 44 1 1 8 3 2 1 77 1 78 1 4 0 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 5 0 1 44 4 77 1 78 1 80 8P08b29d4be403ac37 1 1 4 1 0 1 2 46 1 78 1P08d14f3e3c0497ba 0 4 0 1 8 1 19 1 27 1P0948c015333b9253 1 1 4 1 0 1 3 30 1 37 1 62 1P0974c2a9ebf7e00b 1 2 16 3 0 1 76 1 77 1 16 7 43 4 45 1 66 1 67 1 68 1 75 1 78 1 2 79 1 80 1P0981963e0486823c 2 50 1 1 8 3 2 1 81 1 82 1 4 0 2 80 2 83 2 84 16 1 1 8 3 1 1 80 1 83 1 5 0 1 48 4 81 1 82 1 84 8P098855faf1d5b5fd 0 2 0 1 2 1P0cbfd94eb870dd1f 1 1 4 1 0 1 2 48 1 82 1P0db67471c8a9422e 0 3 0 1 42 1 49 1P0e74848c29bdfaf2 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P0e8e610bdbcd68ff 0 3 0 1 48 1 55 1P109366be02fb8305 1 2 16 3 0 1 80 1 81 1 16 7 47 4 49 1 70 1 71 1 72 1 79 1 82 1 2 83 1 84 1P10ab0a2ddfd5bf64 1 1 4 1 0 1 2 48 1 82 1P10ea28326d977d76 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P129459ab8c196ce2 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P133918f2c17a428a 1 1 4 1 0 1 2 42 1 74 1P13680f0dd4beff56 1 1 4 1 0 1 2 46 1 78 1P1429bd686db405f8 1 1 4 1 0 1 2 42 1 74 1P1549503887c7754e 0 2 0 1 78 1P157b27519beaf48a 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P15c7206c5009deed 1 1 4 1 0 1 3 26 1 33 1 58 1P16ab67d406687349 1 2 16 3 0 1 76 1 77 1 16 7 43 4 45 1 66 1 67 1 68 1 75 1 78 1 2 79 1 80 1P1aabc5e8c071f068 1 2 16 3 0 1 80 1 81 1 16 7 47 4 49 1 70 1 71 1 72 1 79 1 82 1 2 83 1 84 1P1b1d16e8c686558b 1 1 4 1 0 1 3 18 1 25 1 50 1P1c27ea6c4d8fa0d6 1 2 16 3 0 1 76 1 77 1 16 7 43 4 45 1 66 1 67 1 68 1 75 1 78 1 2 79 1 80 1P1c5ce982a3ad54ea 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P1cd80f0816b320da 1 1 4 1 0 1 2 48 1 82 1P1d66a095e620427e 0 3 0 1 48 1 55 1P1f1bf38937a3e8a5 0 8 0 4294967296 6 4294967296 8 1 11 4294967296 19 1 25 4294967296 27 1 73 1P20296843812c5612 1 1 4 1 0 1 3 36 1 43 1 68 1P215539605c1d30c8 0 8 0 4294967296 5 4294967296 7 1 12 4294967296 20 1 26 4294967296 28 1 72 1P21a089ea196a0623 0 3 0 1 48 1 55 1P21be3d1c1a9a44da 2 44 1 1 8 3 2 1 77 1 78 1 4 0 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 5 0 1 44 4 77 1 78 1 80 8P22870821df803531 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P248d8d3f0c744f76 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P2495368f8d5c6c7d 0 2 0 1 2 1P24ca42c39f28b0cc 0 3 0 1 42 1 49 1P24e45ec7d798ded6 1 1 4 1 0 1 3 16 1 23 1 48 1P252c428698d25d70 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P256ac4bb60209ebb 1 1 4 1 0 1 3 24 1 31 1 56 1P262c01fe3a0940ac 2 50 1 1 8 3 2 1 81 1 82 1 4 0 2 80 2 83 2 84 16 1 1 8 3 1 1 80 1 83 1 5 0 1 48 4 81 1 82 1 84 8P26746546fe626394 0 3 0 1 48 1 55 1P26ee5ebca6ced78c 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P27cd74d424df907e 0 2 0 1 78 1P27da01ca283cc431 0 2 0 1 79 1P285050070551f441 0 3 0 1 48 1 55 1P28f7ec198950341b 0 3 0 1 48 1 55 1P29295fcdb3f33965 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P2a702ac1911489d5 1 1 4 1 0 1 3 38 1 45 1 70 1P2b3c6e01bf0b8745 0 5 0 1 72 1 73 1 82 1 83 1P2c95e02fa9516df1 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P2cf1837d670ea221 2 44 1 1 8 3 2 1 77 1 78 1 4 0 2 76 2 79 2 80 16 1 1 8 3 1 1 76 1 79 1 5 0 1 44 4 77 1 78 1 80 8P2cf1d7b34e05fc50 1 1 4 1 0 1 2 48 1 82 1P2dcc807c3a14c4b4 0 3 0 1 46 1 53 1P2e10cfdc88a8fa16 1 2 16 3 0 1 84 1 85 1 16 7 49 4 51 1 72 1 73 1 74 1 83 1 86 1 2 87 1 88 1P2f997fc1a8427524 1 1 4 1 0 1 3 14 1 21 1 46 1P3114155c91434943 0 5 0 1 71 1 72 1 81 1 82 1P31b273b89ce16ffb 1 1 4 1 0 1 3 20 1 27 1 52 1P31bdb3507ec1875f 1 2 16 3 0 1 80 1 81 1 16 7 47 4 49 1 70 1 71 1 72 1 79 1 82 1 2 83 1 84 1P32fb4e312599623d 1 1 4 1 0 1 3 22 1 29 1 54 1P33382927dedaad97 1 1 4 1 0 1 2 42 1 74 1P338ec8f4e65dd5da 1 1 4 1 0 1 3 32 1 39 1 64 1P33ef25ea247d0f5a 1 1 4 1 0 1 3 34 1 41 1 66 1P33fc105651401b22 0 3 0 1 42 1 49 1P34fb6d4bc7009172 0 3 0 1 48 1 55 1P35fbf6ad9d3e43e4 2 52 1 1 8 3 2 1 85 1 86 1 4 0 2 84 2 87 2 88 16 1 1 8 3 1 1 84 1 87 1 5 0 1 50 4 85 1 86 1 88 8P36aebe1dd79dd631 0 4 0 1 7 1 20 1 28 1P39dd4aaf7da633f7 1 1 4 1 0 1 2 48 1 82 1P3aaa1bf3880b7e64 1 1 4 1 0 1 2 42 1 74 1P3b7d0fcebdd24acf 1 1 4 1 0 1 3 12 1 19 1 44 1P3c314be2f6a196c7 1 1 4 1 0 1 2 48 1 82 1P3c46cf909d9cb7b0 1 2 16 3 0 1 76 1 77 1 16 7 43 4 45 1 66 1 67 1 68 1 75 1 78 1 2 79 1 80 1P3c6e42292c016a4f 1 1 4 1 0 1 2 48 1 82 1P3c7762a9cc9df698 0 3 0 1 42 1 49 1P3cee6591ce41c3ad 0 2 0 1 78 1P3d83426ce73b2cfb 2 50 1 1 8 3 2 1 81 1 82 1 4 0 2 80 2 83 2 84 16 1 1 8 3 1 1 80 1 83 1 5 0 1 48 4 81 1 82 1 84 8N008044534bc94be9N0087778b8112fb14N0177c8b3c501276aN0468fe8fd608fd92N0de8c069e4c8898dN0ece39d19425293fN0fbea72645b81911N12b05da524a3c8cfN12bdd29eea0e6eabN145be2c1cb820907N148cbaca9cb84995N16720d12c08bcb20N18f68e5b60870546N19eecb54ce8ba566N1d27596ec74a5b82N1d7da63f8c1c7f61N1ee3a79e03e3b773N217f74c039f69e2bN21bf8679fc14aa37N240c20ffb97a160fN247bc93b01063d2aN25afb9bc41f79074N261777b8d10c7288N2669c9f0b41678f5N272c44da9534195fN27ec7f01bd700411N281a228f2dbcca1fN2cd66e49e960832bN32d497612b2e63ebN360ccf0c05c11101N3d25b227c68dc61eN3d32e13afa41e8bfN3e34de8a7db809beN3e5bfb585ff46964N3e5faf444fcae76cN3e8d127ee43d4377"%lxh.
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

Definition U_ECP_MOD_P224 : Z := 0x3c780.

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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01K0@L10311464405.81 L11774327555.81 L11803550370.82 L11805629605.85 L13294724630.84 L1862307142.114 L19026695374.123L20433961190.80 L2211492706.81  L24167279349.81 L28689697126.188L28689697126.189L28692136132.74 L29012665503.110L31401241662.110L32049487064.111L32049487064.80 L3525463959.102 L3525477263.81  L38017522480.129L3818668784.81  L3820734411.188 L3820734411.189 L3828146333.111 L39584519051.81 L42123129938.4  L43061838089.78 L44210575460.81 L44622288685.83 L44622288685.84 L4541941209.2   L45425587647.3  L45444918220.83 L45851186869.114L45907855535.83 L46154007276.188L46748113268.80 L47185360784.111L4742244590.194 L4742244590.195 L4742244590.196 L4742244590.197 L4742244590.198 L47759495350.194L47759495350.195L47759495350.196L47759495350.197L47759495350.198L49530535345.81 L49542658868.112L49698585326.83 L49698585326.84 L52102261165.194L52102261165.195L52102261165.196L52102261165.197L52102261165.198L52616107219.126L54391891673.84 L54392444536.195L54392444536.196L54392444536.197L54392444923.196L54392444923.197L54392444923.198L54398396379.195L54398396379.196L54398396379.197L55980858593.110L56552377779.111L56552377779.81 L57628696595.14 L57628700040.8  L59314873579.197L59314873579.198L59314873579.199L63559401084.114L65502165646.74 L65502251305.123L65699637964.193L65699637964.194L67436143821.81 L68610690234.113L68616792782.189L7024252226.194 L7024252226.195 L7024252226.196 L8472509976.111 L8474769080.188 L8474769080.189 L9144264913.81  00000@00J01301X02402X03A03K03^03h04Y05J05h05i06306=06G06m07S08I08\09?09b0:@0:J0:X0;60;L0<D0=<0==0=>0=`0>10>M0>g0?10?;0?Z0@T0AQ0BK0C@0Cg0DQ0E;0Ee0FL0FV0F`0G@0G`0HA0He0II0Im0JN0Jg0KT0LN0MH0NB0O=0P80Q30Qm0Rg0Sa0Sk0T50T?0Tk0UD0VU0Wi0Y90YK0YU0Yc0ZE0Zg0[Q0\:0\T0]50]V0^70^A0^[0_50_?S1L2sp2dX3DHI2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2I4S2sp2s02dX2XB2HB5Ha_st5Hl_stS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22B0S2sp2dX2XBS1L2sp2dX2lo3SLO2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XBS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS2sp2dX2XBS2dX3dX22n22N2S1L3HLS2sp2dX2lo3SLO3SPB2X02XBS1L2HI2sp1h2dX4HTOP2XBS1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stFFS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XBS2sp2dX2XB2xx3HxxS2ra2sp2dX2XB2HB5Ha_st5Hl_stS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C21L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n02C2S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n0S2sp2dX2XBS2sp2dX2XBS2ra2sp2dX3SPB2XB2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB2HB5Ha_st5Hl_stS2sp2dX2XB3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB3dX22n22P'5lxwsf1a2C11n2C2S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21nS1L2HI2sp1h2dX2XB3dX21a1CS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1H2C2S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C12C21l2l02Rb1HS1L2sp2dX2XB2I32I4S2sp2dX2XBS2sp2dX2XB3dX2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB". (* [comment removed for export] *)
  Lemma U_ecp_mod_p224_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P224 U_MEMSET_FUNC 14 80.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P224. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
    flat constr:(MA) 2%nat. intros FLt1 _. flat constr:(FLt1) 4%nat. flclear FLt1. intros CH XAL X0 _. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add mpi_cells length] in XB. clear CH.
    flat constr:(XW) 3%nat. intros XCW XD XP.
    pose proof (client_wrange_where2 L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 16%nat ST.
    do 6 zstep.
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
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 14); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3c798)) with (Z_to_bv 64 0x3c798) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 14 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
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
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 14 <= n2) by (clear -N2; lia).
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

