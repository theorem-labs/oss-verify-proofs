(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Arr MpiCoreAux MpiWalkAux Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepPk PkTmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_addsub P_ecp_keypair_init P_ecp_group_free P_ecp_group_load
     P_ecp_group_load_main P_ecp_defs P_ecp_mul_mod P_ecp_grp_id_list P_ecp_point_free P_asn1_get_sequence_of_A P_pk_wrap_eckey P_pk_free P_pk_type
     P_pk_ecc_set_group P_ecp_sinv P_string P_oid P_oidv P_oid_ec_grp P_oid_ec_grp_v P_ecp_group_init P_mpi_cmp P_mpi_bitlen P_pk_ecparams_A P_pk_ecparams_B P_pk_ecparams_C P_pk_ecparams_D P_pk_ecparams_E P_pk_ecparams_F P_pk_ecparams_G P_asn1_get_tag P_asn1_get_int P_asn1_get_mpi P_mpi_read_binary P_mpi_read_binary_proof P_mpi_lset P_pk_ecparams_H P_pk_ecparams_I P_pk_ecparams_J P_pk_ecparams_K P_pk_ecparams_L
     P_x509_get_hash_alg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chunk_split H n H1 H2 ::=
  lazymatch type of H with
  | OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells ?sg ?mx ?A ?cs =>
      let pre := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.firstn n cs) in
      let post := eval cbv beta iota delta [Corelib.Lists.ListDef.firstn Corelib.Lists.ListDef.skipn]
                 in (Corelib.Lists.ListDef.skipn n cs) in
      change (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx A (Corelib.Init.Datatypes.app pre post)) in H;
      apply (proj1 (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.CellsX.rw_cells_app sg mx A pre post)) in H;
      destruct H as [H1 H2];
      let z := eval cbv in (Stdlib.ZArith.BinInt.Z.of_nat (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.cells_size pre)) in
      change (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells sg mx (Stdlib.ZArith.BinInt.Z.add A z) post) in H2
  end.
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_ecparams () : Init.string Init.list := ["OSSVerify.KrLib.Lib.HeapIface.heap_layout"; "OSSVerify.KrLib.Lib.HeapIface.heap_iface"; "OSSVerify.KrLib.P.PImg.psegs"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.hl_free"; "OSSVerify.KrLib.P.P_mpi_free.P_FREE"; "OSSVerify.KrLib.Lib.HeapIface.hl_calloc"; "OSSVerify.KrLib.P.P_asn1_get_sequence_of_A.P_CALLOC"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.AStep.const_at"; "OSSVerify.KrLib.P.P_pk_free.P_RSA_INFO"; "OSSVerify.KrLib.P.P_ecp_sinv.ecp_ids_lok"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS_DONE"; "OSSVerify.KrLib.P.P_ecp_grp_id_list.P_ECP_IDS"; "OSSVerify.KrLib.P.P_pk_ecparams_A.pk_use_ecparams_stmt"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_defs.P_CA"; "OSSVerify.KrLib.P.P_ecp_defs.P_ONE"; "OSSVerify.KrLib.P.P_pk_free.P_EC_INFOS"; "OSSVerify.KrLib.P.P_oid_ec_grp.P_OID_EC_GRP_TBL"; "P_PK_USE_ECPARAMS"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"].


Definition P_PK_USE_ECPARAMS : Z := 0x274b8.

Local Ltac2 Set LiaOrc.tbl := fun () => "02:0@D12428150072.173D1502618809.173 D15533274118.173D17034783542.173D17101549393.173D19555549836.130D19555549836.131D20206238350.173D26645753678.173D27833221753.173D30430513401.173D3043126326.173 D30655052945.173D37677751573.174D44484923210.173D44622288685.130D44622288685.131D45377385681.173D49698585326.130D49698585326.131D49705053714.128D49705053714.129D52101704109.175D52517053689.173D58930681633.130D58930681633.131D59602862289.173D5995093843.128 D5995093843.129 D6001462191.130 D6001462191.131 D65848328670.173D66634421858.130D66634421858.131D67541566890.128D67541566890.129D7338982648.173 D8304906820.173 L10583121780.119L10642582443.8  L10970720858.12 L12428150072.165L13538230744.119L14187124966.127L14368736802.15 L14402542871.152L15428306564.0  L16583023168.7  L16593448436.119L1699531096.119 L17034783542.165L18933043916.4  L1952133860.4   L1952414579.14  L1952430182.10  L19555549836.121L19555549836.122L1958705606.4   L19609103886.11 L19609152795.14 L20206238350.165L20380070050.13 L20484935897.9  L22623124084.119L22887360285.1  L22949435034.13 L23071877398.3  L23072105364.9  L23072120961.14 L23569031128.118L23731286228.7  L26070834843.8  L26889789933.5  L26892418956.1  L26958885277.1  L2820999384.119 L28634040564.119L29771914138.14 L30696723928.119L3184191868.9   L32180269661.1  L35404584536.119L36821928733.1  L37834902488.119L38237953557.5  L38487028637.1  L38732773782.8  L41412906712.119L42544860248.119L43059266230.125L43178716788.119L44484923210.165L44705141405.1  L46698004596.119L47321328856.11 L47321378765.14 L4852815901.1   L49206295796.119L49683038808.119L49831622919.1  L50591402842.15 L51909942461.9  L52719427316.119L52798555062.2  L53519140790.1  L55067758299.6  L55074015712.7  L55074049134.14 L55074066299.9  L55074293241.4  L55216687476.119L57498839298.16 L57753205346.14 L58602127367.1  L58730277748.119L58743199945.9  L58789197907.119L59308632823.1  L59308873939.3  L59715876482.9  L6008652452.3   L61237962740.119L62438632883.155L63203763786.7  L63282926424.119L64402297560.119L64756283892.119L64933133993.0  L6636449414.1   L67265672308.118L7850239254.174 L8304906820.165 L8322245898.4   L8837713752.119 L9788620630.3   L9788864193.14  L9788913108.9   R38730382473.15200000100H01U01V01m01n01o02002o03F03]04\05306406507808a09809_0:l0;G0;b0<a0=80=h0?>0?U0?l0@C0@f0Ao0C<0D70EX0FG0G60GP0GQ0Ge0HB0HF0HG0H[0Ho0I@0IA0IB0IO0Ic0J70K10K50K60K70K80L60MZ0Mi0Mj0NS0OM0O^0Oe0P90P=0PA0PI0PJ0PK0P_0Pl0QI0QM0QQ0QU0Qi0R=0RA0RU0Rn0S20SF0SJ0S^0Sb0Sf0TC0TW0Tk0U_0V30V40V80VL0VM0Vn0W20WF0WZ0W^0Wb0X30XG0XO0XP0XQ0Xj0Xk0Xl0Xm0YA0YR0Yc0Yg0Z;0ZT0Zh0Zl0[60[E0[O0[c0\:0\K0\_0]30]G0]H0]I0]]0^40^50^A0^U0^]0^^0^_0_ZFS2ra2sp3PKA1C3PAR2bs2xsS1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2PL3SLO3ACL3ACP2C03BAC2xs4LENXFS2ra2sp3PKA1C3PAR2bs2xsFFFS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC2xsS2ra2sp3PKA1C3PAR2bs2xsS2ra2sp3PKA1C3PAR2bs2xsS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC2xsS2ra2sp3PKA1C3PAR2bs2xsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02xs3x171H3ACL3SPA3ACPFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C02HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp3PKA1C3PAR2bs2xsS2ra2sp3PKA1C3PAR2bs3SPR2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C3PAR2bs3SPR2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp3PKA1C3PAR2bs3SPR2HBS2ra2sp3PKA1C3PAR2bs3SPR2HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C02xs1a1HS2ra2sp3PKA1C3PAR2bs2xsS1L2HI2ra2sp2h03PKA1C3PAR2bs4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp2s02h03PKA1C3PAR2bs4HTOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S2ra2sp3PKA1C3PAR2bs2xsS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C3PAR2bs2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2PL3SLO3ACL3ACP2C03BAC2xs4LENXS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02HBS2ra2sp3PKA1C2lo3PAR2bs2xsFS2ra2sp3PKA1C3PAR2bsS1L1C3IL13IL23IL33CIM3DI13DI2S2spFS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L2sp2lo3SLO3HLSFSS3LEN2bs4LEN0S2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR2HD3SLO3ACL3ACP2C02xsS2rgFFFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR2HD3SLO2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3PAR2bs3NZP3NZR2HD3SLO2C02HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s82s93s103s11S1P3BUF2BP4BUF0FS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3BACS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR2HD3SLO3ACL3ACP2C02xsS1L2sp2lo3SLO3HLSS2sp2loS2ra2sp3PKA1C3PAR2bsS2spS2spS2sp3SPAFFS2ra2sp3PKA1C3PAR2bsS1P3BUF2bs2BPS1L1C3IL13IL23IL33CIM3DI13DI2S2spS2spS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2spS2ra2sp3PKA1C3PAR2bsS1L3HLS2sp2lo3PAR3DSR3SLOS2spS2ra2sp3PKA1C3PAR2bsS2spS2ra2sp3PKA1C3PAR2bsS2loS2spS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3ACP2C0S2ra2sp3PKA1C3PAR2bsFS2spS2ra2sp3PKA1C3PAR2bsFS1L2sp2lo3LEN1P3BUF2bs2PL3ACL3BACS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2spS2spS1L3HLS2sp2lo3SLOS2ra2sp3PKA1C3PAR2bsS2gv3INVSFS1L3HLS2sp2lo3SLO3ACL3DHIFFFS2ra2sp3PKA1C3PAR2bsS1L2sp2lo3SLO3HLSS1L2sp2lo3SLO3HLSS2spS2ra2sp3PKA1C3PAR2bsS1L3HLS2sp2lo3SLO3ACL3ACPS2ra2sp3PKA1C3PAR2bsS2KTS2rg2NF2Z0S2sp2lo3PAR3DSRS2rg2Hq2RRS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs2rgS3LEN1P3BUF2bs2PLS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsSSS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs2xsFS2rg2RR1q2HqS2ra2sp3PKA1C3PAR2bsS2sp3SPAFFS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3SPR3ACP2C02xs". (* [comment removed for export] *)
Theorem P_pk_use_ecparams_spec : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams ()) "PL,$0.PHI,(1.$2.R1.)P,(3.$4.(5.R2.)$6.)P,(3.$4.(7.R3.)$8.)P,(9.=(:.R4.))P,Pa,$4.P,(;.R6.R1.)(<.R7.R2.)P,(=.(9.(>.R6.)(?.R6.))(9.(10.R6.)(11.R6.)))P,Ph,(12.$2.R7.R6.)PLB,(13.$14.)Pm,P,(15.&40.)(16.(15.&8.))Pmo,$17.P,(18.$2.R;.R:.R4.R3.R2.R1.)(19.$4.(1:.(1;.$4.$4.)$4.(1<.$4.$4.)R4.))P,(1=.R8.$1>.+4.)P,(1?.R9.$20.$21.)(22.$2.R:.R9.$23.$24.$25.$26.$20.$21.$27.$28.$29.)")
(* [comment removed for export] *).
Proof.
  intros L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 IDL.
  unfold pk_use_ecparams_stmt, P_PK_USE_ECPARAMS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 mo0 h0 LB
         PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ.
  lazy zeta.
  intros HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD HPAR0 ALR NZR DSR RD RC HBS0 INB HBD LEN0 B63 BUF0 IDS0 SOK0 CA CAT CA_EC0
         ST0 SLO ACL HTOP SPA DHI TP MI0 RA A0 A1.
  subst a0 a1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0. pose proof (proj2 SPR0) as SPR. clear SPR0.
  dpose (P_pk_ecparams_B.ep_basics L HI m0 mo0 h0 LB C BUF bs HH0 INC INB) as (ACP & C0 & C16 & CAC & CIM & BAC & BIM).
  pose proof DIMG as [DI1 DI2]. dpose IDL as (IL1 & IL2 & IL3 & IL4).
  pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK0.
  assert (CX0 : ctx_now L HI mo0 h0 LB h0 LB [] m0 mo0).
  { split; [exact HH0|]. split; [reflexivity|]. split; [apply mo_frame_refl|]. split; [exact MI0|]. split; [exact SOK0|]. split; [apply lb_ext_refl| exact IDS0]. }
  pose proof (heap_presx_refl psegs L LB (bv_unsigned sp) [(P_ECP_IDS_DONE, P_ECP_IDS_DONE + 1); (P_ECP_IDS, P_ECP_IDS + 56)] m0) as PX0.
  pose proof HPAR0 as HPAR. unfold buf_cells in HPAR.
  (* [comment removed for export] *)
  pose proof (conj HH0 (conj MI0 (conj HPKA0 (conj HBS0 (conj HPAR0 I))))) as BOX. clear HPKA0 HBS0 HPAR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
  (* [comment removed for export] *)
  carve_frame 512%nat ST0.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with M : mem_inv psegs m1 |- _ => rename M into MI1 end. match goal with W : wmono psegs m0 m1 |- _ => rename W into WM1 end.
  match goal with S : stk psegs m1 lo _ |- _ => rename S into ST1 end.
  try clear HH0. try clear SOK0. ddestruct BOX as (HH0 & MI0 & HPKA0 & HBS0 & HPAR0 & _).
  destruct (P_pk_ecparams_D.ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL _ _ _ _ _ _ _ CX0 PX0 MU WM1 MI1 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX1 PX1].
  lazymatch goal with FR : rw_cells psegs m1 (bv_unsigned sp + -512) (CB 408 ?j :: ?rest) |- _ =>
    set (JJ := j) in FR; clearbody JJ; rename FR into FRA end.
  zstep. if_cases KT; zify_cond KT.
  - (* [comment removed for export] *)
    lazymatch type of FRA with rw_cells ?sg ?mx ?A (CB 408 ?j :: ?rest) =>
      change (rw_cells sg mx A (CB 408 j :: rest)) with (rw_cells sg mx A ([] ++ CB 408 j :: rest)) in FRA;
      apply (rw_cells_split_CB sg mx A [] 408 j rest [8; 192; 4; 4; 8; 192]%nat) in FRA; [| reflexivity]; cbn [mk_CB_cells app] in FRA
    end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb4_to_c4 FRA [c0; c1; c2] end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 FRA [c0; c1; c2; c3] end.
    chunk_split FRA 1%nat FR0 FRA1. chunk_split FRA1 1%nat FRG FRA2. chunk_split FRA2 2%nat FRM FRA3. chunk_split FRA3 1%nat FRL FRA4. chunk_split FRA4 1%nat FRR FRS.
    replace (bv_unsigned sp + -512 + 8) with (bv_unsigned sp + -504) in FRG by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192) with (bv_unsigned sp + -312) in FRM by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8) with (bv_unsigned sp + -304) in FRL by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8 + 8) with (bv_unsigned sp + -296) in FRR by (clear; lia).
    replace (bv_unsigned sp + -512 + 8 + 192 + 8 + 8 + 192) with (bv_unsigned sp + -104) in FRS by (clear; lia).
    destruct HBD as [(P0 & L0 & _)|[BP PL]].
    + eapply (P_pk_ecparams_L.spec0_null_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM);
        [exact P0| exact L0| exact CX1| exact PX1| exact HPAR| exact FR0| exact FRG| exact FRM| exact FRL| exact FRR| exact FRS| exact ST1].
    + eapply (P_pk_ecparams_K.spec0_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF tg pd bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP LEN0 PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM);
        [exact CX1| exact PX1| exact HPAR| exact FR0| exact FRG| exact FRM| exact FRL| exact FRR| exact FRS| exact ST1].
  - (* [comment removed for export] *)
    destruct HBD as [(_ & _ & TG0)|[BP PL]].
    { exfalso. subst tg. clear -KT. rewrite ?(sx32_small 0) in KT by lia. rewrite ?unsigned_lit in KT by lia. match type of KT with ?t => idtac "KT:" t end. lia. }
    lazymatch type of FRA with rw_cells ?sg ?mx ?A (CB 408 ?j :: ?rest) =>
      change (rw_cells sg mx A (CB 408 j :: rest)) with (rw_cells sg mx A ([] ++ CB 408 j :: rest)) in FRA;
      apply (rw_cells_split_CB sg mx A [] 408 j rest [208; 4; 4; 192]%nat) in FRA; [| reflexivity]; cbn [mk_CB_cells app] in FRA
    end.
    lazymatch type of FRA with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 FRA [c0] end.
    chunk_split FRA 1%nat FRa FRA1. chunk_split FRA1 1%nat FRE FRA2. chunk_split FRA2 1%nat FRb FRA3. chunk_split FRA3 1%nat FRc FRS.
    replace (bv_unsigned sp + -512 + 208) with (bv_unsigned sp + -304) in FRE by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4) with (bv_unsigned sp + -300) in FRb by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4 + 4) with (bv_unsigned sp + -296) in FRc by (clear; lia).
    replace (bv_unsigned sp + -512 + 208 + 4 + 4 + 192) with (bv_unsigned sp + -104) in FRS by (clear; lia).
    dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (P_pk_ecparams_H.ctx_bytes L DIMG sp m0 LB BUF bs HBS0 INB IDL BIM m1 PX1) as HBS1.
    set (xs := firstn (Z.to_nat LEN) (skipn (Z.to_nat (P - BUF)) bs)).
    assert (LENX : Z.of_nat (length xs) = LEN) by (subst xs; apply bytes_at_sub_length; clear -BP LEN0 PL; lia).
    assert (HXS : bytes_at psegs m1 P xs) by (subst xs; eapply bytes_at_sub; [exact HBS1| | |]; clear -BP LEN0 PL; lia).
    clearbody xs.
    pose proof (P_oid_get_ec_grp_vspec L) as SOG. unfold oid_lookup1v_stmt, oid_lookup1v_post, P_OID_GET_EC_GRP in SOG.
    clear MU. pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    zstep. zstep.
    acallx_sp (bv_unsigned sp + -512)
      (eapply SOG with (OID := PAR) (EXT := bv_unsigned sp + -304) (P := P) (LEN := LEN) (lo := lo) (xs := xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
       first [ exact HPAR | exact HXS | exact LENX | exact FRE | exact MI1 | exact SOK1 | exact CAT | exact DHI | eassumption | reflexivity
             | clear -DSR SLO HLS ACL ACP; lia
             | clear -BP LEN0 PL BAC ACL SLO HLS; lia
             | clear -SPA SPR; lia | clear -BUF0 BP; lia
             | clear -DHI ACL SLO HLS; lia
             | f_equal; clear; lia
             | match goal with |- ?g => idtac "OGLEFT" g end ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with M : mem_inv psegs m2 |- _ => rename M into MI2 end. match goal with W : wmono psegs m1 m2 |- _ => rename W into WM2 end.
    match goal with S : stk psegs m2 lo _ |- _ => rename S into ST2 end.
    match goal with H : rw_cells psegs m2 (bv_unsigned sp + -304) [C4 ?v] |- _ => rename H into FRE2; rename v into gv end.
    match goal with H : oid_vres ?r _ _ _ |- _ => rename H into VR; rename r into rg end.
    match goal with H : rg = 0 \/ rg = _ |- _ => rename H into RR end.
    destruct (P_pk_ecparams_D.ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL _ _ _ _ _ _ _ CX1 PX1 MU WM2 MI2 ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CX2 PX2].
    clear MU WM2 SOG HXS LENX HBS1 CX1 PX1 MK1 HH1 HT1 MF1 SOK1 EXT1 IDS1.
    dpose CX2 as (HH2 & _ & _ & _ & _). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    match goal with H : ?x = Z_to_bv 64 rg |- _ => subst x end.
    zstep. if_cases KG; zify_cond KG.
    + (* [comment removed for export] *)
      assert (Z0 : rg = 0).
      { unfold MBEDTLS_ERR_OID_NOT_FOUND in RR. clear -KG RR. apply Z.mod_divide in KG; [| lia]. destruct KG as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      destruct VR as [[NF _]|[_ INV]]; [exfalso; unfold MBEDTLS_ERR_OID_NOT_FOUND in NF; clear -NF Z0; lia|].
      assert (GVB : 0 <= bv_unsigned gv < 2^31) by (cbn in INV; clear -INV; lia).
      zstep. zstep.
      assert (SX : sx32 gv = Z_to_bv 64 (bv_unsigned gv)).
      { etransitivity; [| apply (sx32_small (bv_unsigned gv) GVB)]. f_equal. symmetry. apply definitions.Z_to_bv_bv_unsigned. }
      rewrite SX. clear SX.
      assert (STX : stk psegs m2 lo (bv_unsigned sp + -104)).
      { generalize FRa FRE2 FRb FRc ST2 SLO ACL ACP HLS SPR. clear. intros.
        release_frame FRa ST2 (bv_unsigned sp + -304). release_frame FRE2 ST2 (bv_unsigned sp + -300).
        release_frame FRb ST2 (bv_unsigned sp + -296). release_frame FRc ST2 (bv_unsigned sp + -104). exact ST2. }
      clear FRa FRE2 FRb FRc ST2.
      eapply (P_pk_ecparams_B.setgrp_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL)
        with (id := bv_unsigned gv); [exact CX2| exact PX2| exact GVB| exact FRS| exact STX].
    + (* [comment removed for export] *)
      zstep. zstep. zstep.
      assert (STX : stk psegs m2 lo (bv_unsigned sp + -104)).
      { generalize FRa FRE2 FRb FRc ST2 SLO ACL ACP HLS SPR. clear. intros.
        release_frame FRa ST2 (bv_unsigned sp + -304). release_frame FRE2 ST2 (bv_unsigned sp + -300).
        release_frame FRb ST2 (bv_unsigned sp + -296). release_frame FRc ST2 (bv_unsigned sp + -104). exact ST2. }
      clear FRa FRE2 FRb FRc ST2.
      eapply (P_pk_ecparams_B.exit_walk L HI HLS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ NZP DSP DPC NZR DSR RC SLO)
        with (g' := kp_grp (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ)) (NB := []);
        [exact CX2| | | reflexivity| | clear; lia| | | exact FRS| exact STX].
      * (* [comment removed for export] *) eapply P_pk_ecparams_B.kp_init_presx; [exact DIMG| exact KP0| exact PX2| exact MI0| exact MI2| exact INC|].
        cbn. generalize IL1 IL2 IL3 CIM DI1 DI2. clear. intros. repeat split; lia.
      * intros d1 d2 H1 H2 NE O1 O2. exfalso. revert H1 O1. unfold grp_mpds, kp_init, kp_grp, grp_init.
        cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
        intros H1 O1; decompose [or] H1; subst; cbn in O1; try discriminate; contradiction.
      * right. split; [clear; lia| split; reflexivity].
      * eapply (P_pk_ecparams_B.ctx_pka L HI sp m0 mo0 h0 LB PKA info C lo BUF bs HH0 HPKA0 DSP CWP PKD INC INB IDL). exact PX2.
      * eapply heap_presx_weak; [exact PX2| intros b Hb; exact Hb| clear; lia| intros a Ha; exact (proj2 Ha)].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
