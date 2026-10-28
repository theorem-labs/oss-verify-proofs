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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P029132a3ef6ed885 1 1 8 3 0 1 49 1 50 1 5 2 1 16 4 48 1 51 1 52 8P03c5ab67b5a3e7e9 1 2 16 3 0 1 47 1 48 1 16 7 14 4 16 1 37 1 38 1 39 1 46 1 49 1 2 50 1 51 1P03c6ae0f56d037bc 1 1 8 3 0 1 47 1 48 1 5 2 1 14 4 46 1 49 1 50 8P051c57dbf7063d3a 1 1 16 7 12 4 14 1 35 1 36 1 37 1 44 1 47 1 4 0 1 45 1 46 1 48 16P0589dfab30143069 1 2 16 3 0 1 48 1 49 1 16 7 15 4 17 1 38 1 39 1 40 1 47 1 50 1 2 51 1 52 1P081c52c54cfce7d0 0 6 0 1 15 4 17 1 38 1 49 1 50 1P0c986a7f9a6bc7ef 1 1 4 1 0 1 3 14 1 21 1 46 1P0d7f7d3f36a1d2d9 0 3 0 1 12 4 19 4P0d93723ebe21d431 1 1 16 2 15 1 45 1 3 0 1 44 1 46 16P0da9768e19a90477 1 1 4 1 0 1 2 12 1 44 1P0e19de459945379b 1 1 4 1 0 1 2 14 1 46 1P0e2ace8664caf3ce 0 5 0 1 38 1 39 1 46 1 47 1P0ea831404a3fb6f8 0 4 0 16 3 16 46 16 47 16P0ed95083eacc4e81 0 4 0 16 1 16 44 16 45 16P0f7e87ec42451a99 0 6 0 1 13 4 15 1 36 1 47 1 48 1P14087455e649787c 1 1 16 7 14 4 16 1 37 1 38 1 39 1 46 1 49 1 4 0 1 47 1 48 1 50 16P1427a33e9445546e 1 1 4 6 8 1 14 1 35 1 36 1 37 1 44 1 4 0 1 18 4 45 1 46 4P14c806ba6d371c57 1 1 16 2 0 1 44 1 3 2 1 45 1 46 16P16064aceaf12b19d 1 1 16 7 14 4 16 1 37 1 38 1 39 1 46 1 49 1 4 0 1 47 1 48 1 50 16P1630fb3b1e6652b2 1 1 16 2 17 1 47 1 3 0 1 46 1 48 16P17457661f3fb0614 0 5 0 1 36 1 37 1 44 1 45 1P17b022ef0ec9b5e0 1 1 16 7 12 4 14 1 35 1 36 1 37 1 44 1 47 1 4 0 1 45 1 46 1 48 16P184078352874ac17 0 5 0 1 36 1 37 1 44 1 45 1P18e0a8459fa20f15 1 2 16 3 0 1 48 1 49 1 16 7 15 4 17 1 38 1 39 1 40 1 47 1 50 1 2 51 1 52 1P1a13f53960e269f2 0 3 0 1 12 4 19 4P1a9a1bbd8b4c20a5 1 1 8 3 1 1 47 1 48 1 6 2 1 38 1 39 1 46 1 49 1 50 8P1cf298a027e2a2db 0 5 0 1 38 1 39 1 46 1 47 1P1dddecf2b9e8ab63 2 15 1 1 8 3 2 1 48 1 51 1 4 0 2 49 2 50 2 52 16 1 1 8 3 1 1 49 1 50 1 5 0 1 16 4 48 1 51 1 52 8P1ecfc7b8f9058067 1 2 16 3 0 1 45 1 46 1 16 7 12 4 14 1 35 1 36 1 37 1 44 1 47 1 2 48 1 49 1P1eeb635e20d12cf4 1 1 8 3 1 1 46 1 49 1 4 2 2 47 2 48 2 50 16P2091cbac7b6e5149 1 2 16 3 0 1 48 1 49 1 16 7 15 4 17 1 38 1 39 1 40 1 47 1 50 1 2 51 1 52 1P2093b0ea57c78cc9 1 1 8 3 0 1 48 1 51 1 4 2 2 49 2 50 2 52 16P21848e925f4ec7df 0 5 0 1 36 1 37 1 44 1 45 1P21cfd877b82892d0 1 1 8 3 1 1 48 1 51 1 4 2 2 49 2 50 2 52 16P2488397a862de772 0 5 0 1 38 1 39 1 46 1 47 1P24f9eb7d1013ebe0 1 1 4 1 0 1 2 12 1 44 1P27ba001a867da108 1 1 8 3 0 1 46 1 49 1 4 2 2 47 2 48 2 50 16P29038cec3bb341e7 1 1 8 3 1 1 49 1 50 1 6 2 1 40 1 41 1 48 1 51 1 52 8P2ada0ba687e81ec0 1 1 4 1 0 1 3 12 1 19 1 44 1P2b80835f3eef1692 0 3 0 1 14 4 21 4P2c0a5ec273191243 0 6 0 1 17 1 21 4 38 1 49 1 50 1P2cfefcd18f814fc0 0 5 0 1 38 1 39 1 46 1 47 1P2d03b20abd600b40 2 15 1 1 8 3 2 1 48 1 51 1 4 0 2 49 2 50 2 52 16 1 1 8 3 1 1 49 1 50 1 5 0 1 16 4 48 1 51 1 52 8P2d162db5035a1e85 1 1 4 1 0 1 2 14 1 46 1P2da82b7b1a44b21a 1 1 8 3 1 1 46 1 49 1 4 2 2 47 2 48 2 50 16P2dc3fe88649ac710 1 1 8 3 0 1 47 1 48 1 5 2 1 14 4 46 1 49 1 50 8P30bc3c359b64f9fe 0 3 0 1 14 1 21 1P314bdd59b6a8c026 1 2 16 3 0 1 45 1 46 1 16 7 12 4 14 1 35 1 36 1 37 1 44 1 47 1 2 48 1 49 1P3171385b04d16dc8 1 2 16 2 0 1 45 1 16 4 4 1 12 4 19 4 44 1 2 46 1 47 1P322f03492ab0c60f 0 6 0 1 15 1 19 4 36 1 47 1 48 1P32f7f5bd8108d389 1 2 16 3 0 1 45 1 46 1 16 7 12 4 14 1 35 1 36 1 37 1 44 1 47 1 2 48 1 49 1P33cf609f7cbca4c5 0 3 0 1 14 1 21 1P33dfcf5a10d7b1ed 0 3 0 1 12 1 19 1P38f71e05e1e677cc 1 1 4 1 0 1 3 12 1 19 1 44 1P3a88948c9d583e34 1 2 16 3 0 1 46 1 47 1 16 7 13 4 15 1 36 1 37 1 38 1 45 1 48 1 2 49 1 50 1P3aaac97b0b6ab5b9 0 6 0 1 13 4 15 1 36 1 47 1 48 1P3d9efb3bc5354d45 1 2 16 3 0 1 46 1 47 1 16 7 13 4 15 1 36 1 37 1 38 1 45 1 48 1 2 49 1 50 1P3f5f4d92c1d0c50e 1 1 16 2 0 1 46 1 3 4 1 47 1 48 16N0015fbb6c0516383N028b8e6b474ad7afN03f78d5475fd8f24N04faaa4efd67fffaN0553b480ac27d0aeN0768913a7b6ccc8eN078f07f7c1378377N0830439bd3404c0eN0fa630842f769142N1361283847c503a8N1892161840fa1aadN1bb5c9b5aec150beN2019a9e0c105e5bfN20588e107f3835d3N231d90c768a19f7fN26077592e1d0b755N28864d4026ce772dN289f7d32698717c2N36e34c527d9507f6N3c512c44ec99c37bN3ef787c30c30155f"%lxh.
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

Definition U_ECP_MOD_P521 : Z := 0x3d404.

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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@L10311464405.81 L11741095640.111L11741095640.80 L11803550370.82 L11805629605.85 L14792944527.81 L14792959895.102L16685523730.4  L19026695374.123L19354909044.81 L2211492706.81  L24167279349.81 L25382082548.81 L25618547375.83 L25618547375.84 L26924648792.111L26924648792.81 L27900861085.111L28689697126.152L28692136132.74 L29012665503.110L31378308326.80 L31392867444.81 L31484333067.81 L37414286068.81 L38017522480.129L3818668784.81  L3820734411.152 L43061838089.78 L43333627578.113L43442376564.80 L43654564952.111L43654564952.81 L44622288685.83 L44622288685.84 L45310944070.114L4541941209.2   L45425587647.3  L4742244590.158 L4742244590.159 L4742244590.160 L4742244590.161 L47759495350.158L47759495350.159L47759495350.160L47759495350.161L49630490545.81 L49642875188.112L49698585326.83 L49698585326.84 L51709126206.110L52102261165.158L52102261165.159L52102261165.160L52102261165.161L52155532688.111L52517350232.111L52519347192.152L52616107219.126L54391891673.84 L54392444536.159L54392444536.160L54392444923.160L54392444923.161L54398396379.159L54398396379.160L57628696595.14 L57628700040.8  L59314873579.161L59314873579.162L59499841752.111L59499841752.81 L63530081892.81 L63559401084.114L64112777397.114L65502165646.74 L65502251305.123L65699637964.157L66189523169.110L68616792782.152L7024252226.158 L7024252226.159 L7510805464.111 L7510805464.81  L798073292.83   L806311629.81   L9144264913.81  00000@00J00T01=01b02H02n03<03e03o04B04L04V05205W05a05k06I07:07X07Y07c07m08708A09709J09m0:K0;40;>0;H0;R0<J0=K0=o0>00>10>P0?J0@D0A90A`0BJ0C40C[0Ce0Co0DO0E80EB0Ec0FG0Fk0GL0GV0G`0H:0HS0I@0J:0K40Ko0Lj0Md0N^0OJ0Oc0Q40RA0RK0RU0Rk0S=0SN0SX0Sf0TH0TR0Tl0UM0Un0V80VB0Vd0WN0WXS1L2sp2dX3DHI2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2I4S1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3ACP3SPB2X02XBS2dX3dX22n22N2S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22B0S2sp2dX2XBS1L2sp2dX2lo3SLO2XBS2sp2dX2XBS2sp2dX2XBS2ra2sp2dX2XB2HB5Ha_st5Hl_stS2sp2s02dX2XB2HB5Ha_st5Hl_st2s12s22s3S2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBFS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB3dX22n23ws02P'2B02B4S1L2sp2dX2lo3ACL2XBS1L2sp2dX2lo3ACL2XB3dX22n22P'5lxwsfS1L3HLS2sp2dX2lo3SLO3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3SPA3SPB3XAL2X02XB2SXS2sp2dX2XBS2sp2dX2XBS2sp2dX2XBS1L3HLS2ra2sp2dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_stS1L3HLS2sp2s02dX2lo3SLO3ACL3DHI3SPB2X02XB2HB5Ha_st5Hl_st2s12s22s3S1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB1HFFS2sp2dX2XB3dX22n22P'5lxwsf1a2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C22C11L2lo3ACL3SPB2X02B02B41lS2sp2dX2XB3dX22n22P'5lxwsf1a2C21L2lo3ACL3SPB2X02B02B41l2l0S1L2sp2dX2lo3ACL3SPB2X02XB3dX22n22P'2B02B45lxwsf1a2l0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C11n2n0S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n02C1S2sp2dX2lo2XB3dX22n22P'5lxwsf1a2C21n2n0S2sp2dX2XBS2sp2dX2XBS2ra2sp2dX3SPB2XB2HB5Ha_st5Hl_stS2sp2s02dX3SPB2XB2HB5Ha_st5Hl_st2s12s22s3S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsf1a2C11nS2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21n2C1S2sp2dX2XB3dX22n22P'5lxwsf1a2C21nS2sp2dX2XBS2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS1L2HI2sp1h2dX2XB3dX21a1CS1L2HI3HLS2sp1h2dX2lo3SLO4HTOP3SPB2X02XB1a2NOS1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a1l2l0S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI2sp1h2dX2lo4HTOP3SPB2X02XB3dX22n22P'2B05lxwsf1a2l02l1S1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2HI3HLS2sp1h2dX2lo3SLO3SPB2X02XB3dX22n22P'2B05lxwsf1a1QS1L2sp2lo3ACL3DHI3DI13DI23dX22n22P'2B52aa2HaS2sp2dX2lo3dX22n22P'1x2HxS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B43APX5lxwsf1a2C11l2l02Rb1HS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XB2SX3dX22n22N22P'2B02B45lxwsf1a2C21l2l02Rb1HS2sp2dX2XBS2sp2dX2XBS1L2HI2sp1h2dX4HTOP2XBS1L2sp2dX2XB2I32I4S2sp2dX2XB2xx3HxxS2sp2dX2XBS2sp2dX2XB3dX2S2sp2dX2XB3dX22n22P'5lxwsf1a2C12C2S2sp2dX2XBS2sp2dX2XB3dX22n22P'5lxwsfS2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XB3dX22n22P'5lxwsf1a1l2l0S2sp2dX2XBS2sp2dX2XBS1L3HLS2sp2dX2lo3SLO3ACL3SPB2X02XBS1L3HLS2sp2dX2lo3SLO3ACL3SPA3ACP3SPB2X02XBS2sp2dX2XB". (* [comment removed for export] *)
  Lemma U_ecp_mod_p521_spec : ecp_reducer_stmt usegs L HI U_ECP_MOD_P521 U_MEMSET_FUNC 34 112.
  Proof.
    unfold ecp_reducer_stmt, U_ECP_MOD_P521. intros until lo. intros HH MA NST XW ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
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
    do 9 zstep.
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
    { eapply SG with (lo := lo) (h := h) (LB := LB) (dX := dX) (nb := 34); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
        first [ exact HH1 | exact MA1 | exact NST | exact TP | exact SOK | exact CA | reflexivity
              | split; [eapply (client_wrange_weak L); [exact XCW| intros b Hb; exact Hb| lia| lia| lia]| split; [exact XD| exact XP]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB2 dX2 r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT2 PXg SOK2 GR.
    replace (ret_pc (Z_to_bv 64 0x3d428)) with (Z_to_bv 64 0x3d428) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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
      zstep. zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      apply aevtM_done. unfold mpi_binop_post.
      flexi 17%nat. exists LB2, dX, r. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|].
      split; [exact PX2|]. split; [exact SOK2|]. subst r. apply reducer_R_fail.
    - (* [comment removed for export] *)
      destruct GR as [[(Er & G1 & G2 & G3 & G4 & G5)|[Er EdX]] FRr]; [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K; cbv in K; discriminate]. subst r.
      assert (GR : grow_R 34 dX LB 0 dX2) by (split; [left; exact (conj eq_refl (conj G1 (conj G2 (conj G3 (conj G4 G5)))))| exact FRr]). clear G1 G2 G3 G4 G5.
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
      clear FS. pose proof (lock LEN) as LEN0. assert (LXn2 : 34 <= n2) by (clear -N2; lia).
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
  all: match goal with |- ?gg => idtac "REDLEFT" gg end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RED.

