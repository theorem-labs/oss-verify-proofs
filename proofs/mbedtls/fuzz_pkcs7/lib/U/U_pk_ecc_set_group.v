(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts EcpCurves EcpLoad. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type.
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
Ltac2 gd_tbl_P_pk_ecc_set_group () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_d"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_Q"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "pk_ecc_set_group_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"; "stdpp.bitvector.definitions.bv_swrap"].


Definition U_PK_ECC_SET_GROUP : Z := 0x3ed48.
(* [comment removed for export] *)
Notation PK_ECC_SET_GROUP_STACK := 176 (only parsing).

Definition pk_ecc_set_group_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PKA info C : Z) (k : ecp_kp) (id lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_group ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O22.O21.O20.)Lh',(5.O22.O21.O20.)(1.$6.Lr,$6.(1.$7.Lg',$7.(1.(8.$9.)LNB,(8.$9.)(1.(8.$9.)LLB',(8.$9.)(:.(;.$0.R16.(<.(=.(>.O1<.O1;.O1:.O19.R15.R14.R13.O18.O17.(?.&40.R4.)R12.R11.R10.R?.R>.R=.R<.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R;.R:.R9.R8.)O<.(10.O1<.)O;.(11.(2.&40.))R7.(12.O22.))R6.))(:.(13.O22.R7.)(:.(14.O22.R7.O3.(15.&40.O1;.))(:.(16.O1.R6.)(:.(;.$6.(17.O22.O21.O20.R5.)(17.O22.O21.O20.O:.))(:.(18.O22.O21.O20.R5.R1.R7.R6.)(:.Pb,$9.(19.(1:.$9.R1.R2.)(1;.(1:.$9.R1.R3.)(1:.$9.R1.O9.)))(:.Pb,$9.P,(1:.$9.R1.R3.)(1<.(1:.$9.R2.O9.))(:.(1=.O22.O1?.R7.R1.O6.(1>.R3.(1?.O5.)(20.O5.)))(:.(21.(22.R3.))(:.(;.(8.$9.)(23.R3.)R2.)(:.(24.O1>.O1=.O4.O6.R4.R3.R2.)(:.(25.O22.R7.O8.(26.$27.(28.(?.&40.O7.))(26.$27.(28.(?.&40.O6.))(29.$27.))))(:.(2:.O22.O21.O9.(15.&40.O1;.)(26.(2;.$6.$6.)(2<.$6.$6.O6.(2=.O6.$2>.))(29.(2;.$6.$6.)))O2.R7.)(2?.O22.O21.R7.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_ecc_set_group_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ca : Z -> curve_addrs) (ONE : Z) (ECIS : list Z) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_group ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(30.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O9.O8.O7.)PLB,(8.$9.)PPKA,$6.Pinfo,$6.PC,$6.Pid,$6.Plo,$6.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)Ppd,(2.&40.)PqX,(2.&40.)PqY,(2.&40.)PqZ,(2.&40.)Zk,$31.(32.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)P,(18.O9.O8.O7.R15.R14.R17.R16.)P,(25.O9.R18.R14.(26.$27.(28.(?.&40.R13.))(26.$27.(28.(?.&40.R12.))(29.$27.))))P,(;.$6.(33.R15.+8.)=)P,(34.=R16.)P,(1:.$6.R16.O3.)P,(1;.(35.(2=.R18.+10.)R14.)(35.(15.&40.R3<.)R18.))P,(36.O8.R1:.R15.(17.O9.O8.O7.R1;.)R19.+10.)P,(1;.(35.(2=.R1:.+10.)R18.)(35.(2=.R18.$37.)R1:.))P,(1=.O9.O6.R1?.R1<.R19.R9.)P,(1:.(2;.$6.$6.)(2<.$6.$6.R1:.$37.)R1=.)P,(1;.(35.(2=.R1;.$37.)(38.O8.))(35.(39.O8.)R1;.))P,(:.(35.=R1;.)(34.R1;.(3:.+2.+1?.)))P,(14.O9.R23.R1;.(15.&40.R43.))P,(35.R1<.(3;.(3;.(15.&40.R44.)+;0.)(3<.O8.)))P,(35.(3=.O8.)R1=.)P,(35.(15.&40.R46.)(17.O9.O8.O7.R24.))P,(;.$6.(33.(15.&40.R47.)+10.)=)P,(35.(39.O8.)(3=.O8.))P,(;.(2.&40.)R47.(?.&40.(3>.O8.)))P,(13.O9.R2:.)P,(2?.O9.O8.R2;.)P,(3?.O8.O1.+8.)P,Pe,$6.P,(1:.$6.R1.O3.)(3?.O8.R2.+4.)P,(;.$6.(33.(15.&40.R4?.)+2.)=)P,(;.(2.&40.)R47.(?.&40.R2;.))P,(;.(2.&40.)R47.(?.&40.R29.))(40.O9.R30.(41.O9.O8.O7.O6.O5.O4.R52.R51.R50.R4?.R4;.R4:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R33.R32.R2?.R2>.R2=.R2<.R2;.R1;.R2:.R29.R31.R30.)(=.(>.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R33.(?.&40.O2.)R32.(11.(2.&40.))R31.(12.O9.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma grp_free_LB_init : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_group ()) "PC,$6.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PLB,(8.$9.)(;.(8.$9.)(42.(43.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)R1.)R1.)")
(* [comment removed for export] *).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L24463421501.4L35497647387.4L41412507867.4L61394746517.400000700800?00FS2ty2HTSS2ty2HTS2ty2HT". (* [comment removed for export] *)
Lemma ec_rw_mask : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecc_set_group ()) "Pty,$6.PC,$6.P,(:.(35.+2.R2.)(35.R2.+4.))P,(:.(35.=R2.)(34.R2.(3:.+2.+40.)))(;.$6.(44.(33.(3;.=(45.(46.(33.(47.&20.(2=.R4.-2.))+10000000000000000.)+3.)))+10000000000000000.)R3.)R3.)")
(* [comment removed for export] *).
Proof.
  intros ty C HT HC. change 18446744073709551616 with (2^64). rewrite swrap32_id by lia. rewrite (Z.mod_small (ty + -2)) by lia.
  replace (ty + -2 <? 3) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((0 - 1) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. exact HC.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac post_pure :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in destruct PO as [E PO]; subst ms'; try destruct_ands PO;
  try (lazymatch goal with
       | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).
Tactic Notation "acallp" tactic3(apptac) :=
  lazymatch goal with
  | |- aevtM _ _ _ (MS _ _ _ _ _ _ _) => eapply aevtM_cut_evt; [ eassumption | apptac | post_pure ]
  end.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01k0@D10463954377.111D10463954377.112D10463954377.119D11805467289.109D11805467289.110D11805467289.117D17741411513.112D17741411513.119D27960841145.112D30985055127.150D30987168522.130D37214132146.112D44622288685.111D44622288685.112D44622288685.119D49698585326.111D49698585326.112D49698585326.119D49705053714.109D49705053714.110D49705053714.117D52770595178.110D52776777110.112D62969020522.110D62969020522.117D62979429526.112D62979429526.119D64111535230.111D64111535230.112D64111535230.119D6483018707.109 D6483018707.110 D6485038895.111 D6485038895.112 D65032746031.112D65032746031.119D65039114451.110D65039114451.117D67124814306.111D67124814306.112D8543290594.112 D8543290594.119 L11923857411.106L12276552123.157L12281286367.159L12336065056.3  L13067875843.106L13067875843.112L1421482075.9   L14946231313.116L17281932723.106L17281932723.112L17365417242.0  L19040144861.116L1933154116.109 L21877859751.159L22575730938.4  L22704456131.13 L22706389268.16 L22706555140.12 L23050452915.106L23050452915.156L23487721976.1  L246676609.118  L28008903173.116L28009036723.10 L28153926185.3  L28160330329.10 L29010380273.106L29010380273.112L30210739039.158L31827261670.105L33292817991.107L33915846823.158L34003033819.9  L36436267943.160L36792457560.106L36792457560.156L37214132146.109L39024900950.3  L39465428440.106L39465428440.112L39465428440.116L41672612599.8  L43059266230.103L44145255421.3  L44145258086.6  L46554181236.106L46554181236.112L46668273908.106L48426298203.9  L49778760422.3  L50731662328.1  L52660466946.1  L52695971188.106L53114433108.3  L54394092454.11 L54625441225.0  L55137442761.0  L55393443529.0  L58706232308.106L61322865240.106L61322865240.156L62784354520.106L62784354520.156L64111535230.108L64111535230.109L64111535230.115L64727650420.106L65333173629.5  L66000499105.0  L66070830614.118L66361310168.106L66361310168.156L66467881522.123L67109976068.105L67231147079.2  L67690939509.116L67996112456.1  L6817437210.0   L8556109094.107 R51215806953.116R51216019661.11100000X01Q02>02T02j03@04905205i06V07C07D08@09M0:N0:n0;_0<D0<X0<l0=@0=P0=o0>?0>O0?00?Q0?R0?S0?T0?d0@40@P0A50AQ0Am0B=0BM0CA0D>0E20Ef0F30F@0FM0FU0Fb0Fo0GJ0GK0GX0Ge0Gf0H?0HL0I10I>0IY0J70JB0JO0J\0J_0Jl0KY0L;0LD0La0Ln0M;0MH0MU0Mb0NG0Nb0OG0OT0Oa0Ob0On0P;0PH0PU0Pl0QQ0QY0Qk0R80RE0RR0Rm0S70S:0S=0SJ0SU0T20T30T40T50TB0TO0T\0Ti0U60Um0W50X10X>0XN0XO0X\0Xi0Y60YC0Yh0Z00Z10Z50Z60Z[0[H0\5S1L2HI2ra2sp1h3PKA1C4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp2s01h3PKA1C4HTOP2HB5Ha_st5Hl_st2s12s22s34infoS1L2HI2ra2sp1h3PKA4info1C4HTOP2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2HBS1L3HLS2ra2sp3PKA1C2HBS1L3HLS2ra2sp3PKA1C2HBS1L3HLS2ra2sp3PKA4info1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA4info1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s33PKA1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3ACP3SPR2C0S1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3ACP3SPR2C0FS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3DHI3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3NZP3SLO3ACL3DHI3SPR2C02HB5Ha_st5Hl_st2s12s22s34infoS1L3HLS2ra2sp3PKA4info1C2lo3NZP3SLO3ACL3DHI3SPR2C02HB5Ha_st5Hl_stS2ra2sp3PKA1C3SPR2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C3SPR2HB5Ha_st5Hl_st2s12s22s34infoS2ra2sp3PKA4info1C3SPR2HB5Ha_st5Hl_stS2ra2sp3PKA1C3SPR2HBS2ra2sp3PKA1C3SPR2HBS2ra2sp3PKA1C3SPR2HBS2ra2sp3PKA1C2HBS2ra2sp2s33PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA4info1C2HB5Ha_st5Hl_stS2ra2sp3PKA4info1C2HB5Ha_st5Hl_stFFFS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp2s03PKA1C2HB5Ha_st5Hl_st2s12s2S2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_st2s12s2S1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C02HB5Ha_st5Hl_stS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L1C2CDS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2sp1C2lo3SLO3ACL3CACFS2ra2sp3PKA1CS2ra2sp3PKA1CSS2ra2sp3PKA1C2ty3PC24POSTS2ra2sp3PKA1CS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S1L2sp2lo3SLOS1L2sp2lo3SLO3ACL3DHI1a3Hd1S1L2sp2lo3SLO3ACL1a1B2kk2Hr2BcS1L2sp1a2HsS2ra2sp3PKA1CS2ra2sp3PKA1CS1CS2ra2sp3PKA1CS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3SPR2C03CACS1L3HLS2sp1C2lo3SLO3ACL3SPR2C03CACS2sp1a2HaS1L2HI2sp1h3PKA2lo3DSP1a2Ha1QS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S1L3HLS2sp1C2lo3SLO3ACL3CACS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S2ra2sp3PKA1CS2ra2sp3PKA1CFS2sp3SPA3SPRS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L2sp1C2lo3SLO3ACL3CACS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S1C1a2HaS1C3off2O12O21a2HxS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2sp1C2lo3SLO3ACL3CACS1C3off2O1S1CS1CS2ra2sp3PKA1CS3PKA1C3DPCS1L2HI2sp1h2lo3SLO4HTOP1a3HinSSSS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2ra2sp3PKA1C2lo3NZP2HD3SLO3SPR2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA1C2lo3NZP2HD3SLO3SPR2C02HB5Ha_st5Hl_st2s12s22s34infoS1L3HLS2ra2sp3PKA4info1C2lo3NZP2HD3SLO3SPR2C02HB5Ha_st5Hl_stS2ra2sp3PKA1CS1L2HI2sp1h4HTOPSS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S2sp3SPAFS2spSS1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3SPR2C0S1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3ACP3SPR2C0S1L3HLS2ra2sp3PKA1C2lo3NZP3SLO3ACL3ACP3SPR2C0". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0"] Lemma U_pk_ecc_set_group_spec : pk_ecc_set_group_stmt usegs L HI U_MT U_CA U_ONE U_EC_INFOS U_PK_ECC_SET_GROUP U_MEMSET_FUNC.
  Proof.
    unfold pk_ecc_set_group_stmt, U_PK_ECC_SET_GROUP. intros until qZ. cbv zeta.
    intros HH HPKA ALP NZP EI DSP CWP DPC KP INC CD IDB ST SLO ACL HTOP SPA DHI TP MI SOK CA CA_EC0 RA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    pose proof (proj1 (Forall_forall _ _) HBR0 _ INC) as CBR. cbn in CBR. ddestruct CBR as (C0 & C16 & _ & CAC & CIM).
    unfold ECP_KEYPAIR_SIZE in *.
    pose proof KP as KP0. destruct KP0 as (HG & _). ddestruct HG as (HGD & ALC & _).
    cbn [grp_head_cells grp_init g_id g_idpad kp_grp kp_init] in HGD.
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
    pose proof (munch_refl [(bv_unsigned sp - 176 - hl_stack L, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 40%nat ST. carve_frame 16%nat ST. carve_frame 8%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    assert (EI3 : info = 0 \/ info = U_RSA_INFO \/ In info U_EC_INFOS) by (right; right; exact EI).
    pose proof (U_pk_get_type_spec L CA_RSA0 CA_EC0) as SPT. unfold pk_get_type_stmt, pk_get_type_post, U_PK_GET_TYPE in SPT.
    acallp (eapply SPT with (info := info); rewrite ?(unsigned_lit (bv_unsigned sp + -56)) by plia;
           [exact FR0| clear -SPA; lia| plia| exact EI3| assumption| assumption| vm_compute; reflexivity| reflexivity]).
    match goal with H : info = 0 -> _ |- _ => clear H end. match goal with H : info = U_RSA_INFO -> _ |- _ => clear H end.
    match goal with H : In info U_EC_INFOS -> _ |- _ => pose proof (H EI) as TYB; clear H end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?t) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename t into ty end.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    acallp (eapply SPT with (info := info); rewrite ?(unsigned_lit (bv_unsigned sp + -56)) by plia;
           [exact FR0| clear -SPA; lia| plia| exact EI3| assumption| assumption| vm_compute; reflexivity| reflexivity]).
    match goal with H : info = 0 -> _ |- _ => clear H end. match goal with H : info = U_RSA_INFO -> _ |- _ => clear H end.
    match goal with H : In info U_EC_INFOS -> _ |- _ => pose proof (H EI) as TYB2; clear H end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?t) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename t into ty2 end.
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (ecp_keypair_at_munch usegs U_MT m mx LB C _ _ KP MU WM (proj1 MIbox) ltac:(assumption)
                    ltac:(cbn [disjoint_from]; clear -CAC ACL SLO HLS; lia)
                    ltac:(intros d Hd HO; exfalso; revert Hd HO; unfold kp_mpds, kp_init, grp_mpds, grp_init;
                          cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]; unfold mpd_init;
                          intros Hd HO; decompose [or] Hd; subst; cbn in HO; try discriminate; contradiction)) as KP1 end.
    pose proof KP1 as KP1c. ddestruct KP1c as ((HGD & _) & _). unfold kp_init, kp_grp, grp_head_cells, grp_init, g_id, g_idpad in HGD.
    do 4 zstep. rewrite (ec_rw_mask ty2 C TYB2 ltac:(clear -C0 CAC ACL SLO SPR HLS; lia)).
    zstep. if_cases KN1; zify_cond KN1.
    1-2: try (exfalso; clear -KN1 C0 C16 CAC ACL SLO SPR HLS; rewrite ?unsigned_lit in KN1 by lia; lia).
    zstep. zstep. if_cases KA1; zify_cond KA1.
    1-2: try (exfalso; clear -KA1 C0 C16 CAC ACL SLO SPR HLS; rewrite ?unsigned_lit in KA1 by lia; rewrite ?land_7_mod in KA1; lia).
    zstep. zstep. if_cases KID; zify_cond KID. all: cycle 1.
    1:{ exfalso. clear -KID. apply KID. reflexivity. }
    clear KID HGD.
    do 4 zstep. rewrite (ec_rw_mask ty C TYB ltac:(clear -C0 CAC ACL SLO SPR HLS; lia)).
    zstep. if_cases KN2; zify_cond KN2.
    1-2: try (exfalso; clear -KN2 C0 C16 CAC ACL SLO SPR HLS; rewrite ?unsigned_lit in KN2 by lia; lia).
    zstep. zstep. if_cases KA2; zify_cond KA2.
    1-2: try (exfalso; clear -KA2 C0 C16 CAC ACL SLO SPR HLS; rewrite ?unsigned_lit in KA2 by lia; rewrite ?land_7_mod in KA2; lia).
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (Asn1AuxA.HEAP_munch usegs L HI h LB m m1 mo lo _ (proj1 HHbox) ACL MU WM).
      intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
    assert (HP1 : heap_presx usegs L LB (bv_unsigned sp) [(C, C + 192)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR0 DHI Ha.
      destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
      rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _). destruct b as [B kk]; cbn in Hr, Bc. lia. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. clear MK.
    pose proof KP1 as KP1c. ddestruct KP1c as (HG1 & ED & MD & FD & HQ & FQ).
    pose proof (U_ecp_group_load_spec L HI HFREE HCALLOC HLS SW DIMG HND) as SPL.
    unfold ecp_group_load_stmt, ecp_group_load_post, U_ECP_GROUP_LOAD in SPL.
    eapply aevtM_cut; [ eapply SPL with (lo := lo) (LB := LB) (h := h) (id := id) (g := grp_init C idpad pP pA pB pX pY pZ pN hpad);
      rewrite ?grp_free_LB_init; rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by dlia; try eassumption; try reflexivity | ].
    { (* [comment removed for export] *)
      intros d1 d2 H1 H2 NE O1 O2. exfalso. revert H1 O1. unfold grp_mpds, grp_init.
      cbn [g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
      intros H1 O1; decompose [or] H1; subst; cbn in O1; try discriminate; contradiction. }
    { intros a Ha. right; right. exists (C, 256). split; [exact INC| cbn; unfold ECP_GROUP_SIZE in Ha; clear -Ha; lia]. }
    { unfold ECP_GROUP_SIZE. clear -CD. lia. }
    { clear -SLO. lia. }
    { clear -HTOP. lia. }
    { clear -SPA SPR. lia. }
    clear SPL SPT. rewrite grp_free_LB_init.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in PO by dlia.
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & LEQ & LNEW & HG5 & AP5 & GB5 & RES & HP5 & SOK5). unfold ECP_GROUP_SIZE in HP5.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
    match type of HH5 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB5 end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1.
    clear ST SOK. rename MI into MI1.
    (* [comment removed for export] *)
    assert (FR' : rw_cells usegs m5 (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply heap_presx_rw_cells; [exact HP5| exact FR| |]; cbn [cells_size csize Nat.add disjoint_from];
      [intros a Ha; left; clear -Ha; lia| split; [clear -CAC ACL SLO HLS SPR; lia| exact I]]. }
    assert (FR0' : rw_cells usegs m5 (bv_unsigned sp + -56) [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
    { eapply heap_presx_rw_cells; [exact HP5| exact FR0| |]; cbn [cells_size csize Nat.add disjoint_from];
      [intros a Ha; left; clear -Ha; lia| split; [clear -CAC ACL SLO HLS SPR; lia| exact I]]. }
    assert (FR1' : rw_cells usegs m5 (bv_unsigned sp + -64) [CB 8 junk1]).
    { eapply heap_presx_rw_cells; [exact HP5| exact FR1| |]; cbn [cells_size csize Nat.add disjoint_from];
      [intros a Ha; left; clear -Ha; lia| split; [clear -CAC ACL SLO HLS SPR; lia| exact I]]. }
    clear FR FR0 FR1.
    assert (HPKA5 : rw_cells usegs m5 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)]).
    { eapply heap_presx_rw_cells; [exact HP5| exact HPKA| |]; cbn [cells_size csize Nat.add disjoint_from].
      - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
      - split; [clear -DPC; lia| exact I]. }
    clear HPKA.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR1' ST5 (bv_unsigned sp + -56). release_frame FR0' ST5 (bv_unsigned sp + -40). release_frame FR' ST5 (bv_unsigned sp).
    zstep. zstep.
    apply aevtM_done. unfold pk_ecc_set_group_post.
    lazymatch type of RES with gl_result _ _ _ _ ?r ?g ?nb => deexists 17; dexists r, g, nb, LB5 end.
    split. { reflexivity. }
    split; [exact MI5|]. split; [exact ST5|]. split; [exact MF5|]. split; [exact HT5|]. split; [exact HH5|].
    split; [exact LEQ|]. split; [exact LNEW|].
    split. { (* [comment removed for export] *)
      split; [exact HG5|]. cbn [kp_grp kp_d kp_Q kp_init]. split; [exact ED|]. split; [| split; [exact FD| split; [| exact FQ]]].
      - eapply mpdr_at_LB_any; [| cbn; discriminate].
        eapply mpdr_at_presx; [exact MD| exact HP5| exact MI1| exact MI5| | | cbn; intros; discriminate]; cbn [md_addr mpd_init disjoint_from].
        + intros a Ha. right; right. exists (C, 256). split; [exact INC| cbn; clear -Ha; lia].
        + split; [clear; lia| exact I].
      - (* [comment removed for export] *) ddestruct HQ as (EX & EY & EZ & MX & MY & MZ). cbn [kp_Q kp_init] in *.
        split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
        assert (QQ : forall d off, md_addr d = C + off -> 192 <= off -> off + 16 <= 256 -> md_own d = LNull ->
                       mpdr_at usegs m1 LB d -> mpdr_at usegs m5 LB5 d).
        { intros d off Ha O1 O2 HO Hd. eapply mpdr_at_LB_any; [| rewrite HO; discriminate].
          eapply mpdr_at_presx; [exact Hd| exact HP5| exact MI1| exact MI5| | | rewrite HO; intros; discriminate]; rewrite Ha; cbn [disjoint_from].
          + intros a Hx. right; right. exists (C, 256). split; [exact INC| cbn; clear -Hx O1 O2; lia].
          + split; [clear -O1; lia| exact I]. }
        split; [eapply (QQ _ 208)| split; [eapply (QQ _ 224)| eapply (QQ _ 240)]];
          (cbn [md_addr md_own mpd_init pt_init pt_X pt_Y pt_Z]; first [reflexivity| eassumption| clear; lia]). }
    split; [exact AP5|]. split; [exact GB5|]. split; [exact RES|]. split; [exact HPKA5|]. split; [| exact SOK5].
    eapply heap_presx_trans; [exact HP1|]. unfold ECP_GROUP_SIZE.
    eapply heap_presx_weak; [exact HP5| intros b Hb; exact Hb| clear; lia| intros a Ha; exact Ha].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
