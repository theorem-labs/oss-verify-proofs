(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_mpi_init U_mpi_addsub U_mpi_grow U_mpi_core_bitlen U_mpi_bitlen U_ecp_group_init U_ecp_group_free U_ecp_defs U_ecp_statics U_ecp_group_load U_ecp_group_load_c1 U_ecp_group_load_c2 U_ecp_group_load_c3 U_ecp_group_load_mx U_ecp_group_load_mx2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section GL.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Let case9 := case9 L HI HFREE HCALLOC HLS SW DIMG HND. Let case13 := case13 L HI HFREE HCALLOC HLS SW DIMG HND.
  Let case1 := case1 L HI HLS DIMG. Let case2 := case2 L HI HLS DIMG. Let case3 := case3 L HI HLS DIMG. Let case4 := case4 L HI HLS DIMG.
  Let case5 := case5 L HI HLS DIMG. Let case6 := case6 L HI HLS DIMG. Let case7 := case7 L HI HLS DIMG. Let case8 := case8 L HI HLS DIMG.
  Let case10 := case10 L HI HLS DIMG. Let case11 := case11 L HI HLS DIMG. Let case12 := case12 L HI HLS DIMG.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02@0@L10311464405.97 L1040637688.90  L11604093874.4  L11805629605.102L12292903720.124L17444027824.124L17706150254.154L18201890820.118L18769531822.154L19052804613.155L19876353013.154L20904604443.97 L21765854580.96 L21887662552.155L21887662552.95 L22229292978.154L22605185333.154L22813394866.154L24933905337.118L25325059957.154L2565288117.154 L25964652061.118L26069021550.154L27135024558.154L27775132660.96 L28035935925.154L28198323950.154L28246635314.154L28704457138.90 L29098255285.154L29638086697.126L31811310069.154L32195670001.152L32195670001.155L33510041944.155L33510041944.96 L34290115814.96 L34531233589.154L3507310894.154 L35754698159.100L35754698159.99 L36370720434.154L37626189746.154L37708033033.97 L3818668784.97  L38443780964.97 L39120847666.154L39473603378.154L39939650836.156L40285201202.154L40331046066.154L41320756718.154L41564619544.155L41940833546.125L41942718641.97 L42755330731.156L42755330731.159L43061838089.94 L44279828714.97 L44622288685.100L44622288685.99 L45122404428.118L45290769780.118L45293014477.97 L4575410798.154 L49138168885.154L49684086766.154L49698585326.100L49698585326.99 L50749560878.154L50809229511.155L51647477002.156L51647477002.4  L51857498741.154L52101695852.103L52101695852.149L52101695852.159L52101695852.161L52101802921.107L52101802921.153L52101802921.163L52101802921.165L52108543731.149L52108543731.150L52108543731.151L52108543731.160L52108543731.161L52108543731.162L52108543731.163L52343768477.147L5276823285.154 L52969527648.149L52969527648.160L52969527648.161L52970903990.156L52970903990.159L53027153221.155L53729035358.3  L54211225911.147L54391891673.101L54392444536.150L54392444536.151L54392444536.161L54392444536.162L54392444536.163L54398396379.150L54398396379.161L54398396379.162L54801566514.154L54854439730.154L5631186743.152 L5631186743.155 L5640938670.154 L56803718284.156L56803718284.159L57628696595.149L59246751494.151L59315053158.156L59633329942.155L61300838498.97 L62399284296.156L62399284296.159L63866083118.154L64791174709.154L65995528878.154L66083662040.155L66083662040.96 L6633241394.154 L66457424050.154L66527532485.153L6741498870.149 L6741498870.150 L6741498870.151 L6741498870.160 L6741498870.161 L6741498870.162 L6741498870.163 L67511028853.154L7190686615.116 L7190734735.97  L7193175862.117 L7193175862.118 L8804982534.151 L9716869748.95  00000B00N00W01A01l02802D02V02b03503A03M03Y03h04404@04L04X04h05405@05a05m06906E06Q06]06i07J07V07g08308?08N08]08i09509A09M09n0:I0:U0:a0:m0;B0;Z0;f0<20<V0<b0<n0=:0=I0=U0=a0>@0>_0?@0?k0@i0Aa0B80Be0CR0C^0Cj0D60D[0E:0EF0EU0Ej0F40F@0G30Gi0H_0I\0JM0K>0L20Lj0M=0MS0Mf0N<0NU0Nn0OD0Oo0P;0PO0Pf0Q=0Qa0RE0RQ0RY0Re0SU0TG0U90Un0Vg0W`0XJ0Y70Yh0Z40Z@0ZL0Z[0Zg0[e0\c0]W0]c0^70^F0^[0_>0_a0_m0`90`E0`T0``0`l0a80a90aJ0a^0ao0bC0bZ0c10cE0cQ0d:0dc0eL0f50fA0fMS1L2ra2sp1A3DHI2TBS2ra2sp1A2TBS2id2K11CS1L3HLS2ra2sp1A2lo3SLO3ACL3SPB3POS2TB1d2I4S1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2TB2SXS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2lo2TB2SXS2ra2sp1A2TBS2ra2sp1A2id2TB3IDRS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB1a2HaS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2id2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp2s01A2TB2HB5Ha_st5Hl_st2s1S2ra2sp1A2TB2HB5Ha_st5Hl_stS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L2ra2sp1A2lo3ACL2TBS1L2HI2ra2sp1h1A4HTOP2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2id2lo3SLO3SPB3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TB3HB05Ha_st5Hl_stS2ra2sp1A2id2TB3HB05Ha_st5Hl_stS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2TBS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2TB2SXS1L3HLS2ra2sp2s01A2lo3SLO3ACL3DHI3SPB3POS2TB2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp1A2lo3SLO3ACL3DHI3SPB3POS2TB2HB5Ha_st5Hl_stS2ra2sp1A3SPB2AL3POS2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3SPA3ACP3SPB3POS2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3SPA3ACP3SPB3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp2s01A3SPB2TB2HB5Ha_st5Hl_st2s1S2ra2sp1A3SPB2TB2HB5Ha_st5Hl_stS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2id3IDB2TB1CS2id3IDB1CS2ra2sp1A2TBS2ra2sp1A2TB1a1C1L3HLS2lo2ND3SLO3ACL3DHI3SPB3POS2SXS2ra2sp1A2TB1a1C1L3HLS2lo2ND3SLO3ACL3DHI3SPB3POS2SX2HoS2ra2sp1A2id2TB1a1C1L3HLS2lo2ND3SLO3ACL3DHI3SPB3POS2SXS2ra2sp1A2id2TB1a1C1L3HLS2lo2ND3SLO3ACL3DHI3SPB3POS2SX3IDR2HoS1L3HLS2ra2sp1A2lo3SLO3ACL3SPB3POS2TB1a1b2kk1C2B4S1L3HLS2ra2sp1A2lo3SLO3ACL3SPB3POS2TB1a1b2kk1C2B4S1L3HLS2ra2sp1A2id2lo3SLO3ACL3SPB3POS2TB1a1b2kk1C2B4S1L3HLS2ra2sp1A2id2lo3SLO3ACL3SPB3POS2TB3IDR1a1b2kk1C2B4S2ra2sp1A2TB1a2C11nS2ra2sp1A2TB1a2C21n2C1S2ra2sp1A2TB1a2C21nS2ra2sp1A2id2TB1a2C11nS2ra2sp1A2id2TB1a2C21n2C1S2ra2sp1A2id2TB1a2C21n2C1S2ra2sp1A2id2TB1a2C21nS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2TB2SXS2ra2sp1A2TBS2ra2sp1A2TB1a2C12C2S2ra2sp1A2id2TB1a2C12C2S2ra2sp1A2id2TB1a2C12C2S1L2ra2sp1A2id2ND2TB3HB05Ha_st5Hl_stS1L2ra2sp1A2id2ND2TB3HB05Ha_st5Hl_stS2ra2sp1A2TBS2id3IDBS2ra2sp1A2TBS1L2HI3HLS2ra2sp1h1A2lo3SLO4HTOP3SPB3POS2TB1a2NOS1L2HI3HLS2ra2sp1h1A2lo3SLO4HTOP3SPB3POS2TB1a1l2l0S1L2HI3HLS2ra2sp1h1A2lo3SLO4HTOP3SPB3POS2TB1a1l2l0S1L2HI3HLS2ra2sp1h1A2id2lo3SLO4HTOP3SPB3POS2TB1a1l2l0S1L2HI3HLS2ra2sp1h1A2id2lo3SLO4HTOP3SPB3POS2TB1a1l2l03IDRS1L2HI3HLS2ra2sp1h1A2id2lo3SLO4HTOP3SPB3POS2TB3IDR1a1l2l0S1L2HI3HLS2ra2sp1h1A2lo3SLO3SPB3POS2TB1a1QS1L2HI3HLS2ra2sp1h1A2id2lo3SLO3SPB3POS2TB1a1QS1L2HI3HLS2ra2sp1h1A2id2lo3SLO3SPB3POS2TB3IDR1a1QS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2id2lo3SLO3SPA3SPB2AL3POS2TB2SX3HB05Ha_st5Hl_stS1L3HLS2ra2sp1A2id2lo3SLO3SPA3SPB2AL3POS2TB2SX3HB05Ha_st5Hl_stS1L3HLS2ra2sp1A2lo2ND3SLO3ACL3DHI3SPB3POS2TB2SX1a2HaS2ra2sp1A2TBS2ra2sp1A2id2TB2K11CS2ra2sp1A2id2TBS1L2ra2sp1A2lo3SLO2TBS2ra2sp1A2id3POS2TB3HB05Ha_st5Hl_stS2ra2sp1A2id3POS2TB3HB05Ha_st5Hl_stS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2id2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBFS2ra2sp1A2TB1a2C1S2ra2sp1A2TB1a2C22C1S2ra2sp1A2TB1a2C2S2ra2sp1A2id2TB1a2C1S2ra2sp1A2id2TB1a2C22C1S2ra2sp1A2id2TB1a2C22C1S2ra2sp1A2id2TB1a2C2S2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB3POS2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB3POS2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB3POS2TBS1L3HLS2ra2sp1A2lo3SLO3ACL3ACP3SPB3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND case9 case13 case1 case2 case3 case4 case5 case6 case7 case8 case10 case11 case12"] Lemma U_ecp_group_load_spec : ecp_group_load_stmt usegs L HI U_MT U_CA U_ONE U_ECP_GROUP_LOAD U_MEMSET_FUNC.
  Proof.
    unfold ecp_group_load_stmt, U_ECP_GROUP_LOAD. intros until lo.
    intros HH G DIS CW ND IDB ST SLO ACL HTOP SPA DHI TP MI SOK CA RA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold ECP_GROUP_SIZE in CW, ND. dpose G as (_ & AL & POS & _).
    dpose G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT0 & _). pose proof (rw_cells_bound _ _ _ _ HT0) as TB. cbn [cells_size csize Nat.add length grp_tail_cells] in TB. clear HT0.
    assert (HBRf : Forall (fun b => block_range L (fst b) (snd b)) (grp_free_LB g LB))
      by (eapply block_range_forall_sub; [exact HBR| intros b Hb; eapply lb_free_mpds_sub; exact Hb]).
    pose proof (client_wrange_where2 L _ _ _ A 192 lo CW ltac:(lia) HBRf DHI ACL ltac:(lia)) as SX.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (G1 : ecp_group_at usegs U_MT m1 LB A g).
    { eapply ecp_group_at_munch; [exact G| exact MU| exact WM| exact (unlock _ MI00)| exact MI| cbn; lia|].
      intros d Hd O. ddestruct (mpdr_blk_facts usegs L m LB d) as (_ & _ & I3 & I4 & _); [| exact O| exact HBR|]; [| cbn; lia].
      ddestruct G as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX' & MY' & MZ') & MN & _).
      unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (PXA : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    clear G HH MU WM. rename HH1 into HH.
    (* [comment removed for export] *)
    zstep.
    pose proof (U_ecp_group_free_spec L HI HFREE HLS SW DIMG HND U_MT) as SG. unfold ecp_group_free_stmt, U_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LB) (g := g); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
        first [ exact HH | exact G1 | exact DIS | exact ND | exact TP | exact MI | exact SOK | exact CA | reflexivity
              | eapply (client_wrange_weak L); [exact CW| intros b Hb; exact Hb| lia| lia| lia]
              | match goal with |- stk _ _ _ _ => eassumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold ecp_group_free_post, ECP_GROUP_SIZE in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF & HTc & HH2 & GZ & GZC & PXg & SOK2).
    replace (ret_pc (Z_to_bv 64 0x3bb34)) with (Z_to_bv 64 0x3bb34) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PXg FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    assert (PXA2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m m2).
    { eapply heap_presx_trans; [exact PXA|]. eapply (heap_presx_weak usegs L); [exact PXg| intros b Hb; exact Hb| lia| intros x Hx; exact Hx]. }
    clear PXA FR GZ PXg ST MI SOK MK G1 HH. rename PXA2 into PXA. rename HH2 into HH. rename ST2 into ST. rename MI2 into MI. rename SOK2 into SOK. rename FR2 into FR.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (U_ecp_group_init_spec U_MT) as SI. unfold ecp_group_init_stmt, U_ECP_GROUP_INIT, ECP_GROUP_SIZE in SI.
    pose proof (conj HH I) as HH0. clear HH.
    eapply aevtM_cut_evt; [exact MK| eapply SI with (lo := lo) (LB := grp_free_LB g LB); rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia;
      first [exact GZC| exact ST| exact MI| reflexivity| lia] |].
    clear SI. unfold ecp_group_init_post, ECP_GROUP_SIZE. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia.
    cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & ip & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hp & -> & MUi & WMi & MI3 & GI & ST3).
    replace (ret_pc (Z_to_bv 64 0x3bb3c)) with (Z_to_bv 64 0x3bb3c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (rw_cells_transport usegs) in FR; [| exact MUi| exact WMi| cbn; lia].
    eapply (statics_ok_munch usegs L) in SOK; [| exact MUi| intros a Ha _; cbn; lia].
    clear ST MI GZC. rename ST3 into ST. rename MI3 into MI.
    destruct HH0 as [HH _].
    assert (HH3 : HEAP usegs L HI h2 (grp_free_LB g LB) m3 mo2).
    { apply (@HEAP_munch usegs L HI h2 _ m2 m3 mo2 _ lo HH MUi WMi ACL).
      intros a Ha NO. cbn in NO. rewrite HTc.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32 - 16) a); [destruct (Z_lt_dec a (bv_unsigned sp - 32))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32 - 16) a); [destruct (Z_lt_dec a (bv_unsigned sp - 32))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PXA3 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m m3).
    { eapply heap_presx_trans; [exact PXA|]. eapply heap_presx_of_munch; [exact MUi| exact WMi|].
      intros a Ha Hc Ho. cbn in Ho |- *. destruct Ho as [Ho _]. split; [exact Ho|]. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    clear HH PXA MUi WMi. rename HH3 into HH3. rename PXA3 into PXA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    (* [comment removed for export] *)
    ddestruct GI as (HD & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & HT & _).
    apply proj1 in MP. apply proj1 in MA. apply proj1 in MB. apply proj1 in MX. apply proj1 in MY. apply proj1 in MZ. apply proj1 in MN.
    cbn [md_addr mpd_init grp_init g_P g_A g_B g_G g_N pt_X pt_Y pt_Z pt_init md_p md_sg md_n md_pad] in MP, MA, MB, MX, MY, MZ, MN.
    replace (A + 56 + 16) with (A + 72) in MY by lia. replace (A + 56 + 32) with (A + 88) in MZ by lia.
    apply mpi_cells_join in MP. apply mpi_cells_join in MA. apply mpi_cells_join in MB. apply mpi_cells_join in MX. apply mpi_cells_join in MY. apply mpi_cells_join in MZ. apply mpi_cells_join in MN.
    change (bv_unsigned (Z_to_bv 64 1) mod 2 ^ 16 + 2 ^ 16 * bv_unsigned (Z_to_bv 64 0)) with 1 in MP, MA, MB, MX, MY, MZ, MN.
    rename MP into HP. rename MA into HA. rename MB into HB. rename MX into HX. rename MY into HY. rename MZ into HZ. rename MN into HN.
    unfold grp_tail_cells, grp_init in HT. cbn [g_pbits g_nbits g_h g_hpad g_modp g_tpre g_tpost g_tdata g_T g_Tsize] in HT. unfold grp_head_cells, grp_init in HD. cbn [g_id g_idpad] in HD.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    pose proof (conj HH3 I) as HH0. clear HH3.
    (* [comment removed for export] *)
    zstep. if_cases KA0; zify_cond KA0; [exfalso; rewrite ?unsigned_lit in KA0 by lia; lia|].
    zstep. zstep. if_cases KA1; zify_cond KA1; [exfalso; rewrite ?unsigned_lit in KA1 by lia; rewrite ?land_7_mod in KA1; lia|].
    zstep. zstep. zstep. zstep.
    if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (NID : ~ (1 <= id <= 13)) by (rewrite ?unsigned_lit_wrap in K1; intros C; rewrite Z.mod_small in K1 by lia; lia).
      zstep. zstep. zstep. zstep.
      zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
      try (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
      destruct HH0 as [HH3 _].
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      apply aevtM_done. unfold ecp_group_load_post.
      match type of HD with rw_cells _ _ _ [_; C4 ?ip] => match type of HP with rw_cells _ _ _ [_; _; C4 ?p1] => match type of HA with rw_cells _ _ _ [_; _; C4 ?p2] =>
      match type of HB with rw_cells _ _ _ [_; _; C4 ?p3] => match type of HX with rw_cells _ _ _ [_; _; C4 ?p4] => match type of HY with rw_cells _ _ _ [_; _; C4 ?p5] =>
      match type of HZ with rw_cells _ _ _ [_; _; C4 ?p6] => match type of HN with rw_cells _ _ _ [_; _; C4 ?p7] => match type of HT with rw_cells _ _ _ [_; _; _; C4 ?hp; _; _; _; _; _; _] =>
        deexists 16; dexists h2, MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, (grp_init A ip p1 p2 p3 p4 p5 p6 p7 hp), [], (grp_free_LB g LB)
      end end end end end end end end end.
      split. { first [reflexivity| do 2 f_equal; apply bv_eq; vm_compute; reflexivity]. }
      split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HTc|].
      split. { apply (@HEAP_munch usegs L HI h2 _ m3 m4 mo2 _ lo HH3 MU WM ACL).
               intros a Ha NO. cbn in NO. rewrite HTc.
               destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
               - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
               - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
               - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
      split; [intros b; cbn; tauto|]. split; [intros b Hb; destruct Hb|].
      split. { apply mpi_cells_of_sn in HP; [| lia]. apply mpi_cells_of_sn in HA; [| lia]. apply mpi_cells_of_sn in HB; [| lia]. apply mpi_cells_of_sn in HX; [| lia].
               apply mpi_cells_of_sn in HY; [| lia]. apply mpi_cells_of_sn in HZ; [| lia]. apply mpi_cells_of_sn in HN; [| lia].
               change (1 mod 2 ^ 16) with 1 in *. change (1 / 2 ^ 16) with 0 in *.
               eapply ecp_group_at_init; eassumption. }
      split. { intros d1 d2 H1 H2 NE O1 O2. exfalso. unfold grp_mpds, grp_init, pt_mpds, pt_init in H1. cbn -[mpd_init] in H1. unfold mpd_init in H1.
               destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O1; discriminate O1. }
      split; [reflexivity|].
      split. { right. right. left. split; [reflexivity|]. split; [exact NID|]. split; [reflexivity|]. deexists 9. split; [reflexivity| exact I]. }
      split; [| assumption].
      eapply heap_presx_trans; [exact PXA|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. destruct Ho as [Ho _]. split; [exact Ho|]. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia.
    - (* [comment removed for export] *)
      assert (IDR : 1 <= id <= 13).
      { rewrite ?unsigned_lit_wrap in K1. clear -K1 IDB. assert (id = 0 \/ 1 <= id) as [->|C] by lia.
        - exfalso. apply K1. vm_compute. reflexivity.
        - rewrite Z.mod_small in K1 by lia. lia. }
      destruct HH0 as [HH3o _].
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
      assert (HH3 : HEAP usegs L HI h2 (grp_free_LB g LB) m4 mo2).
      { apply (@HEAP_munch usegs L HI h2 _ m3 m4 mo2 _ lo HH3o MU WM ACL).
        intros a Ha NO. cbn in NO. rewrite HTc.
        destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
        - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
        - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
        - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
      assert (PXA4 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m m4).
      { eapply heap_presx_trans; [exact PXA|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. cbn in Ho |- *. destruct Ho as [Ho _]. split; [exact Ho|]. split; [| exact I].
        destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
      clear HH3o PXA MU WM. rename PXA4 into PXA. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK4.
      assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by lia.
      clear K1. replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in * by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case1; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case2; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case3; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case4; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case5; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case6; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case7; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case8; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case9; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case10; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case11; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case12; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
      + (* [comment removed for export] *) do 7 zstep.
      eapply case13; first [exact HH3| exact HTc| exact MF| exact PXA| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| exact DIS| exact TP| exact CA| eassumption| reflexivity| lia
        | match goal with |- ?g => idtac "DISPLEFT" g end].
    all: fail.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GL.
