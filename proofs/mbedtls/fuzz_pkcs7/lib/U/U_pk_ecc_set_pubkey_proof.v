(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad EcpPkGlue.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_addsub U_ecp_defs U_ecp_mul_mod U_ecp_group_load U_ecp_statics U_ecp_point_read_binary U_ecp_check_pubkey U_pk_ecc_set_group U_pk_ecc_set_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_ecc_set_pubkey_proof () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecc_set_pubkey.pk_ecc_set_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecc_set_pubkey.U_PK_ECC_SET_PUBKEY"].


Section SP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Variable MT : list modp_ent.
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_pubkey_proof ()) "(0.$1.VL,VHI,VMT,$2.$3.+5<?:8.$4.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_pubkey_proof ()) "(5.$1.VL,VHI,VMT,$6.$3.+5<?:8.$7.$8.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02A0@D10463954377.134D10463954377.135D19427582228.134D19427582228.135D27008441484.134D27008441484.135D27668705378.134D27668705378.135D35754698159.134D35754698159.135D35765334355.132D35765334355.133D44622288685.134D44622288685.135D49698585326.134D49698585326.135D49705053714.132D49705053714.133D64111535230.134D64111535230.135D67541566890.132D67541566890.133L10096046036.3  L10313298137.20 L10317707088.1  L12185527773.2  L13077569646.13 L13594640021.1  L14105627997.4  L16040374239.5  L18286901125.1  L18933043916.4  L19184957076.1  L19613267861.21 L19616998137.2  L20500844466.2  L21765854580.121L21887662552.120L21887662552.165L21887662552.167L22704456131.13 L22706389268.16 L22706553362.3  L22706553362.9  L22706555140.12 L22725724074.7  L22774446881.0  L2382249098.3   L24502405210.1  L24711474703.1  L24910648830.3  L24912203406.20 L25539204855.4  L25883288124.4  L25886142115.23 L26281289489.6  L26892418956.1  L27008441484.123L27008441484.124L27330447718.3  L27775132660.121L29638086697.3  L29644752985.10 L29867548506.4  L30541799330.1  L30770344128.2  L31706438898.3  L31708022150.13 L33510041944.121L33510041944.165L33510041944.167L34290115814.131L36835085397.7  L3818102408.2   L3820505084.20  L38436821893.4  L38441422440.20 L38587949608.2  L38607118800.9  L39935053602.176L39939624611.178L40147641242.6  L41295460820.3  L41562522430.175L41562522430.177L41596317241.6  L41942189128.1  L41993605856.13 L41993605856.20 L41997799904.1  L43040464916.4  L43059266230.129L43300649301.0  L44145255421.3  L44831294238.3  L45290653889.20 L45292491060.1  L45663184054.2  L46770840264.2  L46773451192.20 L47237210673.3  L47238708037.20 L50367744513.6  L51038692423.2  L51755541614.20 L5248022362.1   L52616404933.10 L52619573783.9  L54394092454.11 L56820386561.2  L57449116585.5  L57628696595.3  L57701871804.0  L58504028122.13 L58505774766.3  L59308585607.6  L59308661201.1  L59382514796.6  L59427867805.166L61577508833.20 L61579095185.4  L63665139414.5  L63918187566.1  L64111535230.123L64111535230.124L64185905645.3  L64188377241.20 L64308065920.1  L64312259968.13 L64312259968.20 L6450286553.1   L66083662040.121L66083662040.165L66083662040.167L66572612610.3  L66920871639.4  L67759822825.4  L67993259597.2  L68347083332.2  L7156140075.2   L7193059734.8   L7237223214.1   L8322245898.4   L8871589065.3   L9716869748.120 00000_01T02W03`03a03b04Y05V06906b07907P08O09T0:;0:h0;C0;^0;_0;`0<K0=60=70=A0=B0=H0=U0=V0=W0=j0=o0>30>80>90>:0>@0>T0>h0?<0?P0?g0@B0@J0@`0@l0A@0AA0AJ0AM0AP0AQ0A`0Ao0B00B10BF0BJ0CF0DH0DS0Dg0E00EM0EN0EQ0EV0EW0Ej0F>0FR0Ff0G:0GP0GQ0G^0G_0Go0H00HM0IA0J50JE0JF0JZ0Jn0KA0KE0KO0K\0K]0K^0LR0LS0L[0L\0Ld0Le0Ll0Lm0M:0M;0MN0M^0M_0Ml0Mo0NL0Ng0O@0OG0OW0O_0O`0P30P40PD0PH0PI0PJ0PZ0P[0Pk0Pn0Qh0Rh0Ri0S<0S=0SG0ST0SW0Sk0T?0TS0T^0Tf0Tg0Tm0U40U;0UX0U[0Uh0V10VES1L2HI2ra2sp1h3PKA1C2bs4HTOP3PKB2HB5Ha_st5Hl_stS1L2HI2ra2sp2s01h3PKA1C2bs4HTOP3PKB2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp3PKA1C2lo2bs3NZP3MC23SLO3ACL3DHI2C03PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo2bs3NZP3MC23SLO3ACL3DHI2C03PKB2HB5Ha_st5Hl_st2s1FFS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3SLO2C03PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo2bs3NZP3SLO2C03PKB2HB5Ha_st5Hl_st2s1S2ra2sp3PKA1C2bs3PKB2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C2bs3PKB2HB5Ha_st5Hl_st2s1S2ra2sp3PKA1C2bs3PKB2HBS2ra2sp3PKA1C2bs3PKB2HBS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3SLO3ACL3DHI2C03PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo2bs3NZP3SLO3ACL3DHI2C03PKB2HB5Ha_st5Hl_st2s1S2ra2sp3PKA1C2bs3SPR3PKB2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C2bs3SPR3PKB2HB5Ha_st5Hl_st2s1S2ra2sp3PKA1C2bs3SPR3PKB2HBS2ra2sp3PKA1C2bs3SPR3PKB2HBFFS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3SLO2C03PKB2HBS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3SLO2C03PKB2HBFS1L2sp3DHIFS1d2NDS1L2sp2lo3SLOFFS1L3PKA3PKD3MC13MC2S3DBPS2r1S3DBPFFS1A2DMS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS1L2sp2lo3ACL3DHI1a3Hd1S1L2sp2lo3ACL1a2Bb2kk2Hr2BcS1C1a2HaS1L2sp2lo3ACL3DHI1a2HaS2sp2lo1a2HsS1L2sp2lo3ACL1a1k2HkSS1L1C3CACS1CS1CFS2sp1C1B2bs3DBCS2sp3PKA2lo3DSPFFS1L2sp2lo3MC23ACL3DHIS2spS1L3HLS2ra2sp3PKA1C2lo1B2bs3NZP2HD3SLO2C03PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo1B2bs3NZP2HD3SLO2C03PKB2HB5Ha_st5Hl_st2s1S3PKA1C3DPCS2ra2sp3PKA1C2bs3PKBS2sp1a2HaS1L2HI2sp1h3PKA2lo3DSP1a2Ha1QFS1CS1C1gFS1L2sp1C2lo3ACL3CACS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS1L2sp2lo3ACL3DHI1A2L2FS1L2sp2lo3ACLFS1L2HI2sp1h4HTOPFS1L3HLS2sp2lo3MC23SLO3ACL3DHIS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3MC23SLO3ACL3DHI2C03PKBS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3MC23SLO3ACL3DHI2C03PKBS1L1A2L12L21a2HaFS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS1L2sp1C2lo3ACL3CACS2spS2sp1C3DMCS2sp1C2bs3DMCFFS1L3HLS2ra2sp3PKA1C2lo2bs3NZP3MC23SLO3ACL3DHI2C03PKBSS1C1a2HaFS2sp3SPAFS1C3DMCFS2sp1B2bs3DBMFS1L2sp1C2lo3ACL3CACS1L1C2CD1A2L12L2FS1L2sp2lo3SLOS1CS1L2HI2sp1h3PKA2lo3DSP1a2Ha1QS1L3HLS2sp1C2lo3SLO3ACL3CACS1L2HI2sp1h2lo4HTOP1a3HinS1L3BPLS1L2HI2sp1h4HTOPS1C1a2HaFS1L2sp1C2lo3ACL3CACFS1L1C2CD1a2Ha2HdS2E2FFS2sp2lo1B2bs3DSBFS2sp2lo1B2bs3DSBS1CS1L3HLS2ra2sp3PKA1C2lo2bs3NZP2HD3SLO2C03PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo2bs3NZP2HD3SLO2C03PKB2HB5Ha_st5Hl_st2s1FS1L2sp1C2lo3ACL3CACFS2sp1C3DMCS2sp1C2bs3DMCS1CS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2ra2sp3PKA1C2bs3PKBS2r13RR12HqS1C1d2APFS1a2HaS1L3BPHS1L3BPHS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS1CS2r13RR11q2HqS1L1C3CACS2ra2sp3PKA1C2bs3PKB". (* [comment removed for export] *)
  #[using="HLS DIMG HPRB HCPK"] Lemma U_pk_ecc_set_pubkey_spec : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_pubkey_proof ()) "(9.$1.VL,VHI,VMT,$:.$;.$<.+5<?:8.$7.$3.)")
(* [comment removed for export] *).
  Proof.
    unfold pk_ecc_set_pubkey_stmt, U_PK_ECC_SET_PUBKEY.
    intros until bp2. intros HH HPKA ALP NZP DSP CWP DPC PKD KP INC CD GL CS HBS B0 B63 CRB DSB DBC DBM CNT MC1 MC2 MCS DMC
           BP1 BP2 BPL BPH BPS DBP ST SLO ACL HTOP SPA DHI TP MI RA SOK CA A0 A1 A2.
    subst a0 a1 a2. unfold ECP_KEYPAIR_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0. pose proof (proj2 SPR0) as SPR. clear SPR0.
    pose proof alloc_ceiling_pos as ACP. pose proof DIMG as [DI1 DI2].
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0 & C16 & _ & CAC & CIM). cbn in C0, C16, CAC, CIM.
    dpose (loaded_group_facts usegs U_CA U_ONE id C g m GL CS) as (SGP & PRF & KIND & SP1 & SA1 & SB1 & VP & N1).
    dpose KP as (HG & ED & MD & FD & HQ & FQ). cbn [kp_grp kp_d kp_Q] in HG, ED, MD, FD, HQ, FQ.
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB.
    (* [comment removed for export] *)
    assert (GQL : forall d, In d (grp_mpds g) -> md_own d = LHeap -> C + 208 + 48 <= md_p d \/ md_p d + 4 * md_n d <= C + 208).
    { intros d Hd O. pose proof (N1 d Hd O) as ND.
      assert (MDd : mpdr_at usegs m LB d).
      { ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
        unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
      destruct (mpdr_blk_facts usegs L _ _ _ MDd O HBR) as (IN & _).
      assert (NEQ : (md_p d, 4 * md_n d) <> (C, 256)) by (rewrite ND; intros E; injection E as E1 E2; clear -E2; lia).
      assert (S1 : 0 < snd (md_p d, 4 * md_n d)) by (cbn [snd]; clear -ND; lia). assert (S2 : 0 < snd (C, 256)) by (cbn [snd]; clear; lia).
      pose proof (blocks_apart_neq LB _ _ HAP IN INC NEQ S1 S2) as AP.
      cbn [fst snd] in AP. clear -AP ND. lia. }
    (* [comment removed for export] *)
    pose proof (conj HH (conj MI (conj SOK (conj HPKA (conj HBS (conj CNT I)))))) as BOX.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KN0; zify_cond KN0.
    1-2: try (exfalso; clear -KN0 NZP PKB; try change (Z.of_nat 16) with 16 in PKB; rewrite ?unsigned_lit in KN0 by lia; lia).
    zstep. zstep. zstep. zstep. if_cases KA0; zify_cond KA0.
    1-2: try (exfalso; clear -KA0 ALP NZP PKB; try change (Z.of_nat 16) with 16 in PKB; rewrite ?unsigned_lit in KA0 by lia; rewrite ?land_7_mod in KA0; lia).
    zstep. zstep. if_cases KN1; zify_cond KN1.
    1-2: try (exfalso; clear -KN1 C0 C16 CAC ACP ACL SLO HLS SPR; rewrite ?unsigned_lit in KN1 by lia; lia).
    zstep. zstep. if_cases KA1; zify_cond KA1.
    1-2: try (exfalso; clear -KA1 C0 C16 CAC ACP ACL SLO HLS SPR; rewrite ?unsigned_lit in KA1 by lia; rewrite ?land_7_mod in KA1; lia).
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end. match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end.
    match goal with S : stk usegs m1 lo _ |- _ => rename S into ST1 end.
    try clear HH. try clear SOK. try clear HPKA. try clear HBS. try clear CNT. ddestruct BOX as (HH & MI & SOK & HPKA & HBS & CNT & _).
    (* [comment removed for export] *)
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (Asn1AuxA.HEAP_munch usegs L HI h LB m m1 mo lo _ HH ACL MU WM1).
      intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
    assert (HP1 : heap_presx usegs L LB (bv_unsigned sp) [(C + 208, C + 256); (U_MUL_COUNT, U_MUL_COUNT + 8)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM1|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR DHI Ha.
      destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
      rewrite Forall_forall in HBR. ddestruct (HBR b Hb) as (_ & _ & _ & Bc & _). destruct b as [Bb kk]; cbn in Hr, Bc. lia. }
    assert (SOK1 : statics_ok usegs L m1).
    { eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha _. cbn [outside]. clear -Ha DHI ACL SLO HLS. lia. }
    assert (DJ : forall a k, a + k <= alloc_ceiling -> disjoint_from [(lo, bv_unsigned sp)] a k).
    { intros a k Hk. cbn. clear -Hk ACL. lia. }
    assert (HG1 : ecp_group_at usegs MT m1 LB C g).
    { eapply ecp_group_at_munch; [exact HG| exact MU| exact WM1| exact MI| exact MI1| apply DJ; clear -CAC; lia|].
      intros d Hd O. ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & _).
      assert (MDd : mpdr_at usegs m LB d) by (unfold grp_mpds, pt_mpds in Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption).
      destruct (mpdr_blk_facts usegs L _ _ _ MDd O HBR) as (_ & _ & _ & P4 & _). apply DJ. exact P4. }
    assert (HQ1 : ecp_point_at usegs m1 LB (C + 208) (pt_init (C + 208) qX qY qZ)).
    { eapply ecp_point_at_munch; [exact HQ| exact MU| exact WM1| exact MI| exact MI1| apply DJ; clear -CAC; lia|].
      cbn. intros d [<-|[<-|[<-|[]]]]; cbn; intros; discriminate. }
    assert (HBS1 : bytes_at usegs m1 B bs).
    { eapply bytes_at_transport; [exact HBS| exact MU|]. cbn. clear -DSB. lia. }
    assert (CNT1 : rw_cells usegs m1 U_MUL_COUNT [C8 cnt]).
    { eapply rw_cells_transport; [exact CNT| exact MU| exact WM1|]. cbn. clear -MC2 DHI ACL. lia. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. clear MK.
    (* [comment removed for export] *)
    pose proof HPRB as SPR'. unfold ecp_point_read_binary_stmt, ecp_point_read_post, U_ECP_POINT_READ_BINARY in SPR'.
    eapply aevtM_cut.
    { eapply SPR' with (lo := lo) (h := h) (LB := LB) (G := C) (Q := C + 208) (g := g) (p := pt_init (C + 208) qX qY qZ) (B := B) (bs := bs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH1 | exact HG1 | exact SGP | exact PRF | exact HQ1 | exact HBS1 | exact CNT1 | exact TP | exact MI1 | exact SOK1 | exact CA
              | exact MC1 | exact MC2 | exact MCS | exact B0 | exact B63 | exact CRB | exact RA
              | reflexivity | f_equal; clear; lia
              | (* [comment removed for export] *) eapply client_range_blk; [exact INC| clear; lia| clear; lia]
              | (* [comment removed for export] *) intros a Ha; right; right; exists (C, 256); split; [exact INC| cbn; clear -Ha; lia]
              | (* [comment removed for export] *) intros a Ha Hd; exfalso; clear -Ha Hd CD; lia
              | exact ST1
              | unfold ECP_POINT_READ_STACK; clear -CAC ACL SLO HLS HTOP SPA SPR DMC DBC DBM DSB DHI; lia
              | (* [comment removed for export] *) solve [cbn; repeat constructor]
              | (* [comment removed for export] *) solve [cbn; repeat (constructor; [left; reflexivity|]); constructor]
              | intros _; right; clear; lia
              | intros _; exact GQL
              | match goal with |- ?gl => idtac "PRBLEFT" gl end ]. }
    clear SPR'.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & PT2 & PF2 & SG2 & DIS2 & SUB2 & COV2 & NEW2 & PX2 & SOK2 & HG2 & CNT2 & NONE2 & RR1).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    match type of HH2 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB2 end.
    match type of PT2 with ecp_point_at _ _ _ _ ?pp => rename pp into p' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r1 end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. clear MK1 NONE2.
    (* [comment removed for export] *)
    lazymatch goal with FR : rw_cells usegs m1 (bv_unsigned sp + -32) ?cs |- _ =>
      apply (heap_presx_rw_cells usegs L _ _ _ m1 m2 _ cs PX2) in FR;
        [| cbn [cells_size csize Nat.add]; intros a Ha; left; clear -Ha; lia
         | cbn [cells_size csize Nat.add disjoint_from]; split; [clear -CAC ACL SLO HLS SPR; lia| split; [clear -MC2 DHI ACL SLO HLS SPR; lia| exact I]]];
      rename FR into FR2 end.
    assert (HPKA2 : rw_cells usegs m2 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
    { eapply heap_presx_rw_cells; [exact PX2| eapply rw_cells_transport; [exact HPKA| exact MU| exact WM1| cbn; clear -DSP; lia]| |]; cbn [cells_size csize Nat.add disjoint_from].
      - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
      - split; [clear -DPC; lia| split; [clear -PKD MC1 MC2; lia| exact I]]. }
    assert (MD2 : mpdr_at usegs m2 LB2 (mpd_init (C + 192) pd)).
    { eapply mpdr_at_LB_any; [| cbn; discriminate].
      eapply mpdr_at_presx; [| exact PX2| exact MI1| exact MI2| | | cbn; intros; discriminate]; cbn [md_addr mpd_init disjoint_from].
      - eapply mpdr_at_munch; [exact MD| exact MU| exact WM1| exact MI| exact MI1| cbn; clear -CAC ACL; lia| cbn; intros; discriminate].
      - intros a Ha. right; right. exists (C, 256). split; [exact INC| cbn; clear -Ha; lia].
      - split; [clear; lia| split; [clear -DMC; lia| exact I]]. }
    (* [comment removed for export] *)
    assert (BPT : forall bp A, bad_point_ok usegs m LB A bp -> hl_data_lo L <= A -> A + 16 <= hl_data_hi L -> (forall a, A <= a < A + 16 -> ~ hl_static L a) ->
                  (U_MUL_COUNT + 8 <= A \/ A + 16 <= U_MUL_COUNT) -> bad_point_ok usegs m2 LB2 A bp).
    { (intros bp A dd_H; ddestruct dd_H as ([MDb SGb] & EAb & OWb & SG1); intros L1 L2 NS DM). split; [split; [| exact SGb]| exact (conj EAb (conj OWb SG1))].
      eapply mpdr_at_LB_any; [| rewrite OWb; discriminate].
      eapply mpdr_at_presx; [| exact PX2| exact MI1| exact MI2| | | rewrite OWb; intros; discriminate]; rewrite ?EAb.
      - eapply mpdr_at_munch; [exact MDb| exact MU| exact WM1| exact MI| exact MI1| rewrite EAb; cbn; clear -L2 DHI ACL; lia| rewrite OWb; intros; discriminate].
      - intros a Ha. right; left. split; [clear -Ha L1 L2; lia| apply NS; exact Ha].
      - cbn. split; [clear -L1 L2 CD; lia| split; [clear -DM; lia| exact I]]. }
    pose proof (BPT bp1 U_BAD_POINTS BP1 BPL ltac:(clear -BPH; lia) ltac:(intros a Ha; apply BPS; clear -Ha; lia) ltac:(clear -DBP; lia)) as BP1'.
    pose proof (BPT bp2 (U_BAD_POINTS + 16) BP2 ltac:(clear -BPL; lia) ltac:(clear -BPH; lia) ltac:(intros a Ha; apply BPS; clear -Ha; lia) ltac:(clear -DBP; lia)) as BP2'.
    clear BPT BP1 BP2.
    assert (PX02 : heap_presx usegs L LB (bv_unsigned sp) [(C + 208, C + 256); (U_MUL_COUNT, U_MUL_COUNT + 8)] m m2).
    { eapply heap_presx_trans; [exact HP1|]. eapply heap_presx_weak; [exact PX2| intros b Hb; exact Hb| clear; lia|].
      intros a Ha. cbn [outside] in Ha |- *. clear -Ha. lia. }
    clear HP1 MU WM1. try clear ST. try clear ST1.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (Z1 : r1 = 0).
      { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      subst r1. clear K1.
      zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      zstep.
      pose proof HCPK as SCK. unfold ecp_check_pubkey_stmt, ecp_check_post, U_ECP_CHECK_PUBKEY in SCK.
      eapply aevtM_cut.
      { eapply SCK with (lo := lo) (h := h2) (LB := LB2) (G := C) (Q := C + 208) (g := g) (p := p') (bp1 := bp1) (bp2 := bp2);
          first [ exact HH2 | exact HG2 | exact KIND | exact SP1 | exact SA1 | exact SB1 | exact VP | exact PT2 | exact PF2 | exact SG2 | exact CNT2
                | exact BP1' | exact BP2' | exact TP | exact MI2 | exact SOK2 | exact CA | exact MC1 | exact MC2 | exact MCS | exact BPL | exact BPH | exact BPS
                | reflexivity | f_equal; clear; lia
                | eapply client_range_blk; [apply SUB2; exact INC| clear; lia| clear; lia]
                | assumption
                | rewrite HT2; clear -HTOP; lia
                | unfold ECP_CHECK_PUBKEY_STACK; clear -CAC ACL SLO HLS SPA SPR DMC DBP DHI; lia
                | match goal with |- ?gl => idtac "CPKLEFT" gl end ]. }
      clear SCK.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
      ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & LEQ3 & PX3 & SOK3 & HG3 & PT3 & CNT3 & RR2).
      apply aevtM_done. unfold pk_ecc_set_pubkey_post.
      match type of HH3 with HEAP _ _ _ ?hh ?lb ?mm ?moo =>
        match goal with |- context [mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
          match type of CNT3 with rw_cells _ _ _ [C8 ?c3] =>
            deexists 14; dexists mm, moo, hh, lb, p', r, c3 end end end.
      split; [reflexivity|]. split; [exact RR2|].
      split; [exact MI3|]. split; [exact ST3|]. split; [eapply mo_frame_trans; [exact MF2| exact MF3]|]. split; [rewrite HT3; exact HT2|]. split; [exact HH3|].
      split. { split; [exact HG3|]. cbn [kp_grp kp_d kp_Q]. split; [reflexivity|]. split; [| split; [cbn; discriminate| split; [exact PT3| exact PF2]]].
               eapply mpdr_at_LB_any; [| cbn; discriminate].
               eapply mpdr_at_presx; [exact MD2| exact PX3| exact MI2| exact MI3| | | cbn; intros; discriminate]; cbn [md_addr mpd_init disjoint_from].
               - eapply client_range_blk; [apply SUB2; exact INC| clear; lia| clear; lia].
               - split; [clear -DMC; lia| exact I]. }
      split; [exact PF2|]. split; [exact SG2|]. split; [exact DIS2|].
      split; [intros b Hb; apply (proj2 (LEQ3 b)); apply SUB2; exact Hb|].
      split; [intros b Hb; apply COV2; apply (proj1 (LEQ3 b)); exact Hb|].
      split; [exact NEW2|].
      split. { eapply heap_presx_rw_cells; [exact PX3| exact HPKA2| |]; cbn [cells_size csize Nat.add disjoint_from].
               - intros a Ha. destruct (CWP a Ha) as [Q|[Q|(b & Hb & Hr)]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exists b; split; [apply SUB2; exact Hb| exact Hr]].
               - split; [clear -PKD MC1 MC2; lia| exact I]. }
      split. { eapply heap_presx_trans; [exact PX02|]. eapply heap_presx_weak; [exact PX3| exact SUB2| clear; lia|].
               intros a Ha. cbn [outside] in Ha |- *. clear -Ha. lia. }
      split; [exact SOK3| exact CNT3].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      release_frame FR2 ST2 (bv_unsigned sp).
      zstep.
      apply aevtM_done. unfold pk_ecc_set_pubkey_post.
      match type of CNT2 with rw_cells _ _ _ [C8 ?c2] => deexists 14; dexists m2, mo2, h2, LB2, p', r1, c2 end.
      split; [reflexivity|]. split; [exact RR1|].
      split; [exact MI2|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|]. split; [exact HH2|].
      split. { split; [exact HG2|]. cbn [kp_grp kp_d kp_Q]. split; [reflexivity|]. split; [exact MD2| split; [cbn; discriminate| split; [exact PT2| exact PF2]]]. }
      split; [exact PF2|]. split; [exact SG2|]. split; [exact DIS2|].
      split; [exact SUB2|]. split; [exact COV2|]. split; [exact NEW2|].
      split; [exact HPKA2|]. split; [exact PX02|]. split; [exact SOK2| exact CNT2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SP.
