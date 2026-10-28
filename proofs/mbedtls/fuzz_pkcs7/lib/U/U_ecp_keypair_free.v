(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_ecp_group_free.
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
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_keypair_free () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_zero"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_d"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_X"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_Q"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Y"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_Z"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "kp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "kp_freed"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_keypair_free_post"].


Definition U_ECP_KEYPAIR_FREE : Z := 0x38678.
(* [comment removed for export] *)
Notation ECP_KEYPAIR_FREE_STACK := 96 (only parsing).

(* [comment removed for export] *)
Definition kp_tail_mpds (k : ecp_kp) : list mpd := kp_d k :: pt_mpds (kp_Q k).
Definition kp_free_LB (k : ecp_kp) (LB : list blk) : list blk := lb_free_mpds (kp_tail_mpds k) (grp_free_LB (kp_grp k) LB).
(* [comment removed for export] *)
Definition kp_freed (A : Z) (k : ecp_kp) : ecp_kp := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_free ()) "(0.(1.O2.)(2.(3.O2.+<0.)(4.(5.O1.)))(6.(3.O2.+=0.)(4.(7.(8.O1.)))(4.(9.(8.O1.)))(4.(:.(8.O1.)))))")
(* [comment removed for export] *).

Definition ecp_keypair_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (A : Z) (k : ecp_kp) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_free ()) "Lc,$;.(<.(=.&40.)Lt0,(=.&40.)(<.(=.&40.)Lt1,(=.&40.)(<.(=.&40.)Lt2,(=.&40.)(<.(=.&40.)La0,(=.&40.)(<.(=.&40.)La1,(=.&40.)(<.(=.&40.)La2,(=.&40.)(<.(=.&40.)La3,(=.&40.)(<.(=.&40.)La4,(=.&40.)(<.(=.&40.)La5,(=.&40.)(<.(=.&40.)La6,(=.&40.)(<.(=.&40.)La7,(=.&40.)(<.(=.&40.)Lt3,(=.&40.)(<.(=.&40.)Lt4,(=.&40.)(<.(=.&40.)Lt5,(=.&40.)(<.(=.&40.)Lt6,(=.&40.)(<.P,(=.&40.)(>.(=.&8.))Lm',P,(=.&40.)(>.(=.&8.))(<.$?.Lmo',$?.(<.(10.O1=.O1<.O1;.)Lh',(10.O1=.O1<.O1;.)(11.(12.$;.R13.(13.(14.(15.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(16.O19.)O8.(17.(=.&40.))R3.(18.O1=.))R2.))(11.(19.O1=.R3.)(11.(1:.O1=.R3.O3.(1;.&40.O18.))(11.(1<.O1.R2.)(11.(12.$1=.(1>.O1=.O1<.O1;.R1.)(1>.O1=.O1<.O1;.O7.))(11.(1?.O1=.O1<.O1;.R1.(20.O4.O6.)R3.R2.)(11.(21.O1=.O1:.R3.(20.O4.O6.)O5.(22.O5.O4.))(11.(23.O1=.O1<.(20.O4.O6.)(1;.&40.O18.)(24.(25.$1=.$1=.)(26.$1=.$1=.O5.(3.O5.$27.))(28.(25.$1=.$1=.)))O2.R3.)(29.O1=.O1<.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_keypair_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_free ()) "Pra,(=.&40.)Psp,(=.&40.)Pgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)PF,(2:.&5.(=.&40.))Pfc,(=.&20.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$?.Ph,(10.O6.O5.O4.)PLB,(2;.$2<.)PA,$1=.Pk,$2=.Plo,$1=.P,(1?.O6.O5.O4.R5.R4.R7.R6.)P,(21.O6.O3.R8.R5.R4.R3.)P,(2>.(2?.R4.))P,(30.O5.(20.R5.R7.)(1;.&40.R2:.)(1>.O6.O5.O4.R8.)R6.$27.)P,(31.(32.(3.R7.$27.)(33.O5.))(32.(34.O5.)R7.))P,(1:.O6.R<.R6.(1;.&40.R2<.))P,(32.R7.(35.(35.(1;.&40.R2=.)+60.)(36.O5.)))P,(32.(37.O5.)R8.)P,(32.(1;.&40.R2?.)(1>.O6.O5.O4.R=.))P,(12.$1=.(38.(1;.&40.R30.)+10.)=)P,(32.(34.O5.)(37.O5.))P,(12.(=.&40.)R30.(39.&40.(3:.O5.)))P,(19.O6.R13.)P,(29.O6.O5.R14.)P,(3;.O5.O1.+8.)P,(12.$1=.(38.(1;.&40.R37.)+2.)=)P,(12.(=.&40.)R2?.(39.&40.R13.))(3<.O6.R17.(3=.O6.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.R13.R12.R18.R17.)(14.(15.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(39.&40.O2.)R19.(17.(=.&40.))R18.(18.O6.)))")
(* [comment removed for export] *).

Lemma kp_mpds_grp : forall k d, In d (grp_mpds (kp_grp k)) -> In d (kp_mpds k).
Proof. intros k d H. unfold kp_mpds. apply in_or_app. left. exact H. Qed.
Lemma kp_mpds_tail : forall k d, In d (kp_tail_mpds k) -> In d (kp_mpds k).
Proof. intros k d H. unfold kp_mpds. apply in_or_app. right. exact H. Qed.

Section KF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01f0@L10311432145.143L10311432145.161L10311464405.104L10311465800.179L10313562458.125L1157504822.143 L11774327555.106L11805400866.108L11805629605.112L12288290349.143L12288437416.137L12292529832.133L1267802697.132 L13125901610.125L13127832481.143L13127832481.161L13127999288.179L13192051901.125L13294724630.110L13589623563.202L13594111217.179L1553209355.202 L17408832329.132L18428822264.90 L18430824055.98 L19028994704.98 L20421019718.135L20433961190.106L20433961190.184L2395765163.132 L26891890152.179L28704457138.90 L28814043710.99 L3035426189.104 L30997702686.179L30997800071.143L30997800071.161L30999800332.125L31399144472.179L31568441778.161L32049487064.105L32049487064.179L3305887922.143 L34757725497.125L350054171.104  L3523383040.125 L3523383179.143 L3523383179.161 L3523383179.179 L3525463959.123 L3525477263.104 L3525640587.143 L3525640587.161 L36173660702.132L37708033033.104L3818668784.104 L3830374936.180 L39010876474.202L41679356099.148L42599362260.202L43061838089.104L43650205652.202L44210575460.104L44279828714.107L44622288685.109L44622288685.110L44686383316.202L45739454932.202L4574513722.202 L45798074799.179L45907855535.109L46204166667.202L46748113268.105L47489799475.137L4844695055.161 L48576260313.161L49122613519.143L49528090634.134L49528435006.125L49530044341.143L49530044341.161L49530241034.137L49530535345.104L49698585326.109L49698585326.110L49823506697.137L50543729195.179L50719543317.143L50719543317.161L50721283742.125L51316333854.132L52101695852.114L52101802921.118L54391891673.112L55076832172.136L55978761415.179L56552377779.106L56552377779.179L57459684159.125L57461620148.143L57461620148.161L57461780781.179L57838663734.161L58240582923.202L59229011437.125L59231109119.179L59231269734.143L59231269734.161L59308628179.101L60612838208.179L61300838498.104L63748808489.135L64275732278.112L67436143821.104L67436439241.143L67436439241.161L67438241858.125L9782728975.179 00000B00T00f01801J01V01b02P03;03S03d04R04^04j05605B05N05Z06806H06\06l07807D07P08508A08M08Y08e09109R09b0:30:?0:m0;[0<I0<U0<a0<m0=90=E0=Q0=]0>G0?10?[0@E0@o0AY0BC0Bm0C90CE0CZ0D;0DG0Df0E=0E^0F50FM0G;0H40I00IG0I^0Ij0J60JQ0Ja0Jm0K>0KJ0Kc0Ko0L;0LG0LS0L_0Lk0M70MV0N80NI0NU0O10OJ0Oi0P50Pl0Q^0RQ0Ri0S50SA0SM0Se0T=0TU0Tm0U90UI0U^0V30VH0V]0W00WI0W^0Wo0X\0YJ0Z80Zf0[T0[`S1L2ra2sp1A3DHI2KBS1L2ra2sp1A3DHI2KBS1L2ra2sp1A3DHI2KBS1L2ra2sp1A3DHI2KBS1L2ra2sp1A3DHI2KBS2ra2sp1A2KBS2ra2sp1A2KBS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2KB2SX2K0S1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KB4ACLx1d2I4S2ra2sp1A3POS2KB2K01d2I5S2ra2sp1A2KB1d2B1S1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2KB2SX2K0S2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp2s01A2KB2HB5Ha_st5Hl_stS2ra2sp1A3POS2KBS2ra2sp1A3SPA3SPB2KBS2ra2sp1A3POS2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS1L3HLS2ra2sp1A2lo3SLO3ACL3SPB3POS2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KBS2ra2sp1A3POS2KBS1L2ra2sp1A2ND2KBS2ra2sp1A2KBS2ra2sp1A2KB1L3HLS2lo3SLO3SPA3SPB2AL3POS2SX2K0S2ra2sp1A2KB1L3HLS2lo3SLO3SPA3SPB2AL3POS2SX2K0S1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2KB2SX2K0S2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3ACP3SPB3POS2KB4ACLxS2ra2sp1A2KBS2ra2sp1A2KBS1L2ra2sp1A2lo3ACL2KBS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KBS2ra2sp1A2KBS2ra2sp1A3SPB3POS2KB1d2B12d'2H0S2ra2sp1A3SPB2AL3POS2KBS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KBS2ra2sp1A3SPB2AL3POS2KBS1L2HI2ra2sp1h1A4HTOP2KBS1L3HLS2ra2sp1A2lo3SLO3SPA3SPB2AL3POS2KB2SX2K0S1L3HLS2ra2sp1A2lo3SLO3DHI3SPB3POS2KB4ACLx2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01A2lo3SLO3DHI3SPB3POS2KB4ACLx2HB5Ha_st5Hl_stS2ra2sp1A3SPB2AL3POS2KBS2ra2sp1A3SPB2AL3POS2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KB2HB5Ha_st5Hl_stS2ra2sp1A3POS2KBS2ra2sp1A2KBS2ra2sp1A2KB1d2B1S2ra2sp1A2KBS2ra2sp1A1k2EY3SPB3POS2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A3SPB2KB2HB5Ha_st5Hl_stS2ra2sp2s01A3SPB2KB2HB5Ha_st5Hl_stS2ra2sp1A2KB1d2B2S2ra2sp1A2KBS2ra2sp1A1k2EY3SPB3POS2KB2EZS2ra2sp1A1k2EZ3SPB3POS2KBS2ra2sp1A1k2EX3SPB3POS2KB2EY2EZS2ra2sp1A2KBS2ra2sp1A2KB1a1C1L3HLS2lo2ND3SLO3DHI3SPB3POS2SX4ACLx2K0S1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KB4ACLx1a1b2kk1C2B4S1L2HI3HLS2ra2sp1h1A2lo3SLO4HTOP3SPB3POS2KB2K01a2NOS2ra2sp1A3POS2KB2K01x2HxS2ra2sp1A2KBS2ra2sp1A2KBS2ra2sp1A2KBS1L2HI2ra2sp1h1A4HTOP2KBS1L2HI2ra2sp1h1A4HTOP2KBS1L2HI2ra2sp1h1A4HTOP2KBS1L2HI2ra2sp1h1A4HTOP2KBS2ra2sp1A2KBS2ra2sp1A3POS2KBS1L2ra2sp1A2lo3SLO2KBS1L2ra2sp1A2lo3SLO2KBS1L2ra2sp1A2lo3SLO2KBS1L2ra2sp1A2lo3SLO2KBS2ra2sp1A3POS2KB2K0S2ra2sp1A1k2EZ3SPB3POS2KBS1L2ra2sp1A2lo3SLO2KBS2ra2sp1A2KB1a2HaS1L3HLS2ra2sp1A2lo3SLO3SPB3POS2KB4ACLx1a1n2HnS1L3HLS2ra2sp1A2lo3SLO3SPA3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3SPA3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3SPA3ACP3SPB3POS2KB4ACLxS1L3HLS2ra2sp1A2lo3SLO3SPA3ACP3SPB3POS2KB4ACLxS2ra2sp1A2KB". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND"] Lemma U_ecp_keypair_free_spec : forall MT, ecp_keypair_free_stmt usegs L HI MT U_ECP_KEYPAIR_FREE U_MEMSET_FUNC.
  Proof.
    intros MT. unfold ecp_keypair_free_stmt, U_ECP_KEYPAIR_FREE. intros until lo.
    intros HH K DIS CW ND ST SLO ACL HTOP SPA DHI TP MI SOK CA RA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold ECP_KEYPAIR_SIZE in CW, ND.
    ddestruct K as (G & ED & MD & FD & (EX & EY & EZ & MX & MY & MZ) & FQ).
    dpose G as (_ & AL & POS & _).
    pose proof MZ as (CHZ & _). unfold mpdr_at in CHZ. rewrite EZ in CHZ. pose proof (rw_cells_bound _ _ _ _ CHZ) as KB. cbn [cells_size csize Nat.add length mpi_cells] in KB. clear CHZ.
    set (g := kp_grp k) in *. set (LBg := grp_free_LB g LB).
    assert (SUBg : forall b, In b LBg -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    assert (SUBF : forall b, In b (kp_free_LB k LB) -> In b LB) by (intros b Hb; apply SUBg; eapply lb_free_mpds_sub; exact Hb).
    assert (HBRf : Forall (fun b => block_range L (fst b) (snd b)) (kp_free_LB k LB)) by (eapply block_range_forall_sub; [exact HBR| exact SUBF]).
    pose proof (client_wrange_where2 L _ _ _ A 256 lo CW ltac:(lia) HBRf DHI ACL ltac:(lia)) as SX.
    set (FRL := kp_tail_mpds k) in *.
    assert (INF : forall d, In d [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)] -> In d FRL) by (intros d Hd; exact Hd).
    assert (DISF : mpds_apart FRL) by (eapply mpds_apart_sub; [exact DIS| intros d Hd; apply kp_mpds_tail; exact Hd]).
    assert (FRB : Forall mpd_freeable [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]) by (constructor; [exact FD| exact FQ]).
    assert (KEPT : Forall (fun d : mpd => md_own d <> LHeap) ([] : list mpd)) by constructor.
    assert (EQF : kp_free_LB k LB = lb_free_mpds [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)] LBg) by reflexivity.
    (* [comment removed for export] *)
    assert (NIg : forall d, In d FRL -> md_own d = LHeap -> ~ In (md_p d, 4 * md_n d) (kp_free_LB k LB)).
    { intros d Hd O. unfold kp_free_LB. apply lb_free_mpds_notin; [| exact Hd| exact O]. unfold grp_free_LB. apply lb_free_mpds_nodup. exact NDL. }
    pose proof (free_facts_intro usegs L HI h LB (kp_free_LB k LB) m mo (bv_unsigned sp) _ A 256 FRL HH NDL
                  ltac:(intros d Hd; cbn in Hd; destruct Hd as [<-|[<-|[<-|[<-|[]]]]]; assumption) CW SUBF NIg DHI ltac:(lia) ltac:(lia) DI1 DI2) as FF1.
    assert (ACLx : alloc_ceiling <= lo) by exact ACL.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; pose proof G as (_ & GAL & _); lia|].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep.
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (G1 : ecp_group_at usegs MT m1 LB A g).
    { eapply ecp_group_at_munch; [exact G| exact MU| exact WM| exact (unlock _ MI00)| exact MI| cbn; lia|].
      intros d Hd O. ddestruct (mpdr_blk_facts usegs L m LB d) as (_ & _ & I3 & I4 & _); [| exact O| exact HBR|]; [| cbn; lia].
      ddestruct G as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX' & MY' & MZ') & MN & _).
      unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    assert (LIV : Forall (mpdr_at usegs m1 LB) [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]).
    { eapply (lives_munch usegs L m m1); [| exact MU| exact WM| exact (unlock _ MI00)| exact MI| exact HBR| | intros a n Ha Hn; cbn; lia].
      - repeat apply Forall_cons; try apply Forall_nil; assumption.
      - repeat apply Forall_cons; try apply Forall_nil; rewrite ?ED, ?EX, ?EY, ?EZ; cbn; lia. }
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (PXA : heap_presx usegs L (kp_free_LB k LB) (bv_unsigned sp) [(A, A + 256)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    clear G MD MX MY MZ HH MU WM. rename HH1 into HH.
    (* [comment removed for export] *)
    zstep.
    pose proof (U_ecp_group_free_spec L HI HFREE HLS SW DIMG HND MT) as SG. unfold ecp_group_free_stmt, U_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LB) (g := g); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia;
        first [ exact HH | exact G1 | exact ND' | exact TP | exact MI | exact SOK | exact CA | reflexivity
              | eapply mpds_apart_sub; [exact DIS| intros d Hd; apply kp_mpds_grp; exact Hd]
              | eapply (client_wrange_weak L); [exact CW| intros b Hb; change (In b LBg); unfold kp_free_LB in Hb |- * | lia| lia| lia]; eapply lb_free_mpds_sub; exact Hb
              | match goal with |- stk _ _ _ _ => eassumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold ecp_group_free_post, ECP_GROUP_SIZE in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF & HTc & HH2 & GZ & GZC & PXg & SOK2).
    assert (GIN' : forall d, In d (grp_free_mpds g) -> In d (grp_mpds g)).
    { intros d Hd. unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h g =? 1); [destruct Hd|]. destruct (g_h g =? 2); cbn in Hd |- *; tauto. }
    change (grp_free_LB g LB) with LBg in HH2, GZ, PXg.
    replace (ret_pc (Z_to_bv 64 0x38698)) with (Z_to_bv 64 0x38698) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (LIV2 : Forall (mpdr_at usegs m2 LBg) [kp_d k; pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)]).
    { eapply Forall_impl; [| eapply Forall_and; [exact LIV| ]].
      2:{ instantiate (1 := fun d => In d FRL /\ A + 192 <= md_addr d /\ md_addr d + 16 <= A + 256).
          repeat apply Forall_cons; try apply Forall_nil; rewrite ?ED, ?EX, ?EY, ?EZ; cbn -[FRL]; (split; [apply INF; cbn; tauto| lia]). }
      cbv beta. intros d [Md (Hd & B1 & B2)].
      eapply (mpdr_at_presx usegs L m1 m2); [exact Md| exact PXg| exact MI| exact MI2| | |].
      - eapply (client_range_of_wrange L); [exact CW| intros b Hb; unfold kp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb| lia| lia| lia].
      - cbn. lia.
      - intros O. ddestruct (FF1 d Hd O) as (I1 & I2 & I3 & I4 & I5). split.
        + subst LBg. unfold grp_free_LB. apply lb_free_mpds_keep; [exact I1|]. intros d' Hd' O' E'.
          apply (DIS d d'); [apply kp_mpds_tail; exact Hd| apply kp_mpds_grp, GIN', Hd'| | exact O| exact O'| exact E'].
          * pose proof (grp_mpds_addr _ _ _ _ _ _ _ G1 ltac:(apply GIN'; exact Hd')) as [? ?]. lia.
        + cbn. lia. }
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PXg FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    assert (PXA2 : heap_presx usegs L (kp_free_LB k LB) (bv_unsigned sp) [(A, A + 256)] m m2).
    { eapply heap_presx_trans; [exact PXA|]. eapply (heap_presx_weak usegs L); [exact PXg| | lia|].
      - intros b Hb. unfold kp_free_LB in Hb. eapply lb_free_mpds_sub. exact Hb.
      - intros x Hx. cbn in Hx |- *. split; [lia| exact I]. }
    assert (CH : Forall (fun ac => rw_cells usegs m2 (fst ac) (snd ac)) [(A, [CB 192 (repeat (Z_to_bv 8 0) 192)]); (bv_unsigned sp - 16, [C8 s0; C8 ra])]).
    { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact GZC| replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact FR2]. }
    clear LIV PXA FR FR2 GZ GZC PXg ST MI SOK MK G1 HH. rename LIV2 into LIV. rename PXA2 into PXA. rename HH2 into HH. rename ST2 into ST. rename MI2 into MI. rename SOK2 into SOK.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SPF.
    (* [comment removed for export] *)
    zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (kp_d k)) (X0 := (A + 192)) (A := A) (sz := 256) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := FRL) (LB := LB) (LBf := kp_free_LB k LB);
          [ fs_side (bv_unsigned sp + -16) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_X (kp_Q k); pt_Y (kp_Q k); pt_Z (kp_Q k)] .. | ];
          fs_post (bv_unsigned sp + -16) HI HH LIV CH PXA ST MI SOK MF HTc MK.
    zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_X (kp_Q k))) (X0 := (A + 208)) (A := A) (sz := 256) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := FRL) (LB := LB) (LBf := kp_free_LB k LB);
          [ fs_side (bv_unsigned sp + -16) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Y (kp_Q k); pt_Z (kp_Q k)] .. | ];
          fs_post (bv_unsigned sp + -16) HI HH LIV CH PXA ST MI SOK MF HTc MK.
    zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Y (kp_Q k))) (X0 := (A + 224)) (A := A) (sz := 256) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := FRL) (LB := LB) (LBf := kp_free_LB k LB);
          [ fs_side (bv_unsigned sp + -16) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Z (kp_Q k)] .. | ];
          fs_post (bv_unsigned sp + -16) HI HH LIV CH PXA ST MI SOK MF HTc MK.
    (* [comment removed for export] *)
    fa_get CH 0%nat CQY. fa_get CH 1%nat CQX. fa_get CH 2%nat CD. fa_get CH 3%nat CG. fa_get CH 4%nat FR.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in FR by lia.
    assert (CH' : Forall (fun ac => rw_cells usegs _ (fst ac) (snd ac)) [(A + 224, _ : list cell); (A + 208, _ : list cell); (A + 192, _ : list cell); (A, _ : list cell)])
      by (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact CQY| exact CQX| exact CD| exact CG]).
    clear CH CQY CQX CD CG. rename CH' into CH.
    zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    try (replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)). zstep.
    eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Z (kp_Q k))) (X0 := (A + 240)) (A := A) (sz := 256) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := FRL) (LB := LB) (LBf := kp_free_LB k LB);
          [ fs_side (bv_unsigned sp + -16) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF ([] : list mpd) .. | ];
          fs_post (bv_unsigned sp + -16) HI HH LIV CH PXA ST MI SOK MF HTc MK.
    (* [comment removed for export] *)
    apply aevtM_done. unfold ecp_keypair_free_post.
    deexists 18. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HTc|].
    split; [exact HH|].
    fa_get CH 0%nat CQZ. fa_get CH 1%nat CQY. fa_get CH 2%nat CQX. fa_get CH 3%nat CD. fa_get CH 4%nat CG.
    split. { unfold ecp_keypair_at, kp_freed. cbn [kp_grp kp_d kp_Q md_addr mpd_init].
      split; [apply ecp_group_at_zero; [exact CG| exact AL| exact POS]|].
      split; [reflexivity|]. split; [apply mpdr_at_init; [exact CD| lia| lia]|]. split; [cbn; discriminate|].
      split; [| unfold pt_freeable, pt_mpds; cbn; repeat constructor; cbn; discriminate].
      unfold ecp_point_at, pt_init; cbn [pt_X pt_Y pt_Z md_addr mpd_init].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      replace (A + 208 + 16) with (A + 224) by lia. replace (A + 208 + 32) with (A + 240) by lia.
      split; [| split]; (apply mpdr_at_init; [assumption| lia| lia]). }
    split; [exact PXA| exact SOK].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End KF.
