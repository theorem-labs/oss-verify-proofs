(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts RepRsa RepCrt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_rsa_init U_ecp_keypair_init U_asn1_get_sequence_of_A U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free.
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
Ltac2 gd_tbl_P_pk_setup () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "pk_setup_post"].


Definition U_PK_SETUP : Z := 0x29cb4.
Notation PK_SETUP_STACK := 80 (only parsing).

Definition pk_setup_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (RSAI : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (PKA info lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_setup ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1>.O1=.O1<.)Lh',(5.O1>.O1=.O1<.)(1.$6.Lr,$6.(1.$6.LC,$6.(1.$6.LSZ,$6.(7.(8.$0.R16.(9.(:.(;.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(<.O19.)O8.(=.(2.&40.))R6.(>.O1>.))R5.))(7.(?.O1>.R6.)(7.(10.O1>.R6.O3.(11.&40.O18.))(7.(12.O1.R5.)(7.(8.$6.(13.O1>.O1=.O1<.R4.)(13.O1>.O1=.O1<.O7.))(7.(8.(2.&40.)R12.(14.&40.R3.))(7.(15.O1>.O1=.O6.(11.&40.O18.)(16.(17.$6.$6.)(18.$6.$6.O5.(19.O5.+10.))(1:.(17.$6.$6.)))O2.R6.)(1;.(7.(8.$6.R3.-3?80.)(7.(1<.O1>.O1=.O1<.R4.O6.R6.R5.)(1=.O1>.R6.O5.(16.$1>.(1?.(14.&40.=))(16.$1>.(1?.(14.&40.=))(1:.$1>.))))))(7.(8.$6.R3.=)(7.(20.O1=.R2.R1.)(7.PB,$6.Pk,$6.P,(21.(17.$6.$6.)(18.$6.$6.R2.R1.)O6.)(1;.(22.(19.R5.R4.)R3.)(22.(19.R3.R2.)R5.))(7.(1<.O1>.O1=.O1<.R4.(16.(17.$6.$6.)(18.$6.$6.R2.R1.)O6.)R6.R5.)(7.(1=.O1>.R6.O5.(16.$1>.(1?.(14.&40.O4.))(16.$1>.(1?.(14.&40.R2.))(1:.$1>.))))(7.P,(8.$6.O4.O1:.)(7.(8.$6.R2.+>8.)(23.O1>.R7.(16.(17.$6.$6.)(18.$6.$6.R3.+>8.)O6.)R3.(24.R3.)))P,(25.(8.$6.O4.O1:.))(7.(8.$6.R2.+100.)(1.(2.&40.)Lidpad,(2.&40.)(1.(2.&40.)LpP,(2.&40.)(1.(2.&40.)LpA,(2.&40.)(1.(2.&40.)LpB,(2.&40.)(1.(2.&40.)LpX,(2.&40.)(1.(2.&40.)LpY,(2.&40.)(1.(2.&40.)LpZ,(2.&40.)(1.(2.&40.)LpN,(2.&40.)(1.(2.&40.)Lhpad,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.(2.&40.)LqX,(2.&40.)(1.(2.&40.)LqY,(2.&40.)(1.(2.&40.)LqZ,(2.&40.)(26.O1>.O1;.R14.(16.(17.$6.$6.)(18.$6.$6.R10.+100.)O6.)R10.(27.R10.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_setup_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (RSAI : Z) (ECIS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_setup ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(28.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O7.O6.O5.)PLB,(29.$2:.)PPKA,$6.Pinfo,$6.Plo,$6.P,(1<.O7.O6.O5.R5.R4.R7.R6.)P,(1=.O7.R8.R4.(16.$1>.(1?.(14.&40.=))(16.$1>.(1?.(14.&40.=))(1:.$1>.))))P,(8.$6.(2;.R5.+8.)=)P,(1;.(8.$6.R5.O3.)(21.$6.R5.O2.))P,(22.(11.&40.R2;.)R7.)P,(22.(19.R8.+10.)(13.O7.O6.O5.R:.))P,(10.O7.R=.R7.(11.&40.R2=.))P,(22.(2<.O6.)R8.)P,(22.R9.(2=.(2=.(11.&40.R2?.)+50.)(2>.O6.)))P,(8.$6.(2;.(11.&40.R30.)+10.)=)P,(22.(11.&40.R31.)(13.O7.O6.O5.R?.))P,(22.(2?.O6.)(2<.O6.))P,(?.O7.R13.)P,(30.O7.O6.R14.)P,(8.(2.&40.)R33.(14.&40.(31.O6.)))P,(8.$6.(2;.(11.&40.R37.)+2.)=)P,(8.(2.&40.)R2?.(14.&40.R13.))P,(8.(2.&40.)R2?.(14.&40.R13.))(32.O7.R18.(33.O7.O6.O5.O4.O3.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R17.R16.R15.R14.R13.R19.R18.)(:.(;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(14.&40.O1.)R1:.(=.(2.&40.))R19.(>.O7.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable MT : list modp_ent.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA72 : const_at L (U_RSA_INFO + 72) 8.
  Hypothesis CA_EC72 : forall e, In e U_EC_INFOS -> const_at L (e + 72) 8.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02R0@D10463954377.78 D10463954377.79 D10463954377.81 D10463954377.82 D11805467289.76 D11805467289.77 D11805467289.79 D11805467289.80 D1441963205.102 D1441963205.99  D18026384712.115D18026384712.118D18028566964.113D18028566964.116D24880498060.105D24880498060.108D24880498060.114D24880498060.117D26559234903.103D26559234903.106D26559234903.112D26559234903.113D26559234903.115D26559234903.116D26574002091.105D26574002091.108D26574002091.114D26574002091.115D26574002091.117D26574002091.118D27668705378.78 D27668705378.79 D27668705378.81 D27668705378.82 D34299948885.105D34299948885.108D34299948885.114D34299948885.115D34299948885.117D34299948885.118D35754698159.78 D35754698159.79 D35754698159.81 D35754698159.82 D35765334355.76 D35765334355.77 D35765334355.79 D35765334355.80 D38441682923.77 D38441682923.80 D44622288685.78 D44622288685.79 D44622288685.81 D44622288685.82 D45290914114.77 D45290914114.80 D49137842428.103D49137842428.106D49137842428.112D49137842428.113D49137842428.115D49137842428.116D49698585326.78 D49698585326.79 D49698585326.81 D49698585326.82 D49705053714.76 D49705053714.77 D49705053714.79 D49705053714.80 D55287947697.115D55287947697.118D59229011437.77 D60486411898.105D60486411898.108D60486411898.114D60486411898.117D64111535230.78 D64111535230.79 D64111535230.81 D64111535230.82 D65537657969.103D65537657969.106D65537657969.112D65537657969.115D65544099981.105D65544099981.108D65544099981.114D65544099981.117D66160960579.102D66160960579.99 D6699899629.80  D7190686615.96  D7190686615.99  D7192832768.77  D7192832768.80  L13700332227.74 L14800215863.112L14800215863.115L16643836346.10 L19051674851.0  L19742833745.1  L21765854580.77 L21765854580.80 L21887662552.104L21887662552.107L21887662552.112L21887662552.115L21887662552.76 L21887662552.79 L22704456131.13 L22706389268.16 L22706555140.12 L23081464626.77 L27775132660.77 L27775132660.80 L28006808888.111L28006808888.114L29010380273.112L29010380273.115L29010380273.71 L33510041944.104L33510041944.107L33510041944.112L33510041944.115L33510041944.77 L33510041944.80 L34290115814.75 L34290115814.78 L39935455635.103L39935455635.106L39935455635.112L39935455635.115L41562522427.102L41562522427.105L41562522427.111L41562522427.114L41942189128.1  L43059266230.73 L43059266230.76 L4306347747.0   L45606478563.0  L46650398932.67 L49246398130.80 L51303916321.0  L54394092454.11 L54394092454.13 L59308631013.1  L59308632045.1  L59308632045.3  L59626077396.67 L66083662040.104L66083662040.107L66083662040.112L66083662040.115L66083662040.77 L66083662040.80 L66158863482.3  L66518012628.67 L66816528084.67 L9716869748.76  L9716869748.79  00000V01B01h02T02b03003>03L03W03b04>04_04o05?05]06;06[07;07I07W07g08708G08W09109K09g0:C0:_0;@0<70=40=k0>h0?Y0@J0AA0B80Bo0Ck0DE0De0E?0E_0Em0F;0FI0FW0Fn0GE0H@0IA0J<0K=0Km0L]0Lk0M90MI0MY0Mi0N90NW0O;0OY0P=0PO0Pa0Q30QE0R:0S40SH0T70Tf0U[0VP0Vn0WR0X00XT0Xb0Y00Y@0YP0Yj0ZD0Z`0[<0[K0[Z0[n0\V0]>0]f0^N0^^0^k0_80_[0_\0_`0_k0`60`A0`L0`Y0`f0a10a<0a[0b=0bF0bQ0b\0bg0cU0dC0dP0d]0dh0e30e>0eK0eX0ec0en0f90fD0fl0gT0hB0i00i;0iF0iS0i`0id0jL0k40k50k60kA0kL0kM0kn0lW0l[0l_0li0m40m?0mJ0mW0md0mo0n:0nF0nQ0n\0ng0o2S1L2HI2ra2sp1h3PKA4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp2s01h3PKA4HTOP2HB5Ha_st5Hl_st2s1S1L2HI2ra2sp1h3PKA4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp2s01h3PKA4HTOP2HB5Ha_st5Hl_st2s1S2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA4info1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA3SPP2HB5Ha_st5Hl_stS2ra2sp3PKA3SPP2HB5Ha_st5Hl_stS2ra2sp3PKA3SPP1C2HB5Ha_st5Hl_stS2ra2sp3PKA3SPP1C2HB5Ha_st5Hl_stS2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA4info1C2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA2lo3SPP3ACL3SLO3ACP3SPR2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA2lo3SPP3ACL3SLO3ACP3SPR2HB5Ha_st5Hl_st2s1S1L2HI2ra2sp1h3PKA4PTOP3SPR2h53HT52HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA4PTOP3SPR2h53HT52HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA4PTOP3SPR1C2h53HT53HN02HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA4PTOP3SPR1C2h53HT53HN02HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA4PTOP3SPR1C2h53HT53HN02HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA4info4PTOP3SPR1C2h53HT53HN02HB5Ha_st5Hl_stS2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp2s03PKA2HB5Ha_st5Hl_st2s1S2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp2s03PKA2HB5Ha_st5Hl_st2s1S2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA2HBS1L2HI2ra2sp1h3PKA4HTOPS1L2HI2ra2sp1h3PKA4HTOPS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3DHI3ACP3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA2lo3SPP3ACL3SLO3DHI3ACP3SPR2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3DHI3ACP3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s03PKA2lo3SPP3ACL3SLO3DHI3ACP3SPR2HB5Ha_st5Hl_st2s1S1L3HLS2ra2sp3PKA2lo3ALP3SPP3ACL3SLO3SPA3ACP3SPRS1L3HLS2ra2sp3PKA2lo3ALP3SPP3ACL3SLO3SPA3ACP3SPRS2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA3SPR2HB5Ha_st5Hl_stS2ra2sp2s03PKA3SPR2HB5Ha_st5Hl_st2s1S2ra2sp3PKA3SPR2HB5Ha_st5Hl_stS2ra2sp2s03PKA3SPR2HB5Ha_st5Hl_st2s1S2ra2sp3PKA3SPR2HBS2ra2sp3PKA3SPR2HBS2ra2sp3PKA3SPR2HBS2ra2sp3PKA3SPR2HBS1L3HLS2ra2sp3PKA2lo3SPP3SLO3SPR1C3HN02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA4info2lo3SPP3SLO3SPR1C3HN02HB5Ha_st5Hl_stS1L2ra2sp3PKA2lo3SLOS1L3HLS2ra2sp3PKA2lo3SPP3SLO3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA2lo3SPP3SLO3SPR2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA2lo3SPP3SLO3SPR1C3HN02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA2lo3SPP3SLO3SPR1C3HN02HB5Ha_st5Hl_stS2ra2sp3PKA3SPP2HB5Ha_st5Hl_stS2ra2sp2s03PKA3SPP2HB5Ha_st5Hl_st2s1S2ra2sp3PKA3SPP2HB5Ha_st5Hl_stS2ra2sp2s03PKA3SPP2HB5Ha_st5Hl_st2s1S2ra2sp3PKA2HBS2ra2sp3PKA2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA1C2HBS2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp3PKA2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA1C2HB5Ha_st5Hl_stS2ra2sp3PKA3SPPS2ra2sp3PKA3SPPS1L2ra2sp3PKA2lo3SLOS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS2ra2sp3PKA4infoS2ra2sp3PKA1CS2ra2sp3PKA1CS1L3HLS2sp3PKA2lo3SPP3ACL3SLO1C3HNCSS2spS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKAS2ra2sp3PKAS1L3HLS2sp2lo3ACL3SLO3DHI1a3Hd1S1L3HLS2sp2lo3ACL3SLO1a1B2kk2Hr2BcS2sp1a2HsS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3SPR1C3HN03HNCS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3SPR1C3HN03HNCS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPR1C3HN0S1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPR1C3HN0S2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA1CS2ra2sp3PKA1CS2spS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRS1L3HLS2ra2sp3PKA2lo3SPP3ACL3SLO3ACP3SPRSSS2ra2sp3PKAS2ra2sp3PKASS1L2HI3HLS2sp1h2lo3SLO4HTOP1a3HinS1L2HI3HLS2sp1h3PKA2lo3SPP4PTOP3SLO1a3HinS2KFS2KNS1C3HN02KNS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA1CS2ra2sp3PKA1CS2ra2sp3PKAS2ra2sp3PKAS2sp3PKA3SPPS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKAS2ra2sp3PKA". (* [comment removed for export] *)
  #[using="HCALLOC HLS DIMG CA_RSA72 CA_EC72"] Lemma U_pk_setup_spec : pk_setup_stmt usegs L HI MT U_RSA_INFO U_EC_INFOS U_PK_SETUP.
  Proof.
    unfold pk_setup_stmt, U_PK_SETUP. intros until lo. intros HH HPKA ALP HINF SPP PTOP ST ACL SLO SPA HTOP DHI MI SOK TP RA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    assert (NI : info <> 0 /\ 0 <= info < 2^64).
    { destruct HINF as [->|EI]; [unfold U_RSA_INFO; cbn; lia|].
      unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI. destruct EI as [<-|[<-|[<-|[]]]]; cbn; lia. }
    destruct NI as [NI IB].
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    zstep. if_cases KI; zify_cond KI. { exfalso. exact (NI KI). } clear KI.
    zstep. if_cases K0; zify_cond K0.
    1-2: try (exfalso; clear -K0 SPP SLO HLS ACL ACP SPR PKB; rewrite ?unsigned_lit in K0 by lia; lia).
    zstep. zstep. if_cases KA; zify_cond KA.
    1-2: try (exfalso; clear -KA ALP SPP SLO HLS ACL ACP SPR PKB; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; lia).
    zstep. zstep. if_cases KZ; zify_cond KZ. 2:{ exfalso. clear -KZ. apply KZ. reflexivity. } clear KZ.
    destruct HINF as [->|EI].
    - (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
        let a := eval vm_compute in (U_RSA_INFO + 72) in
        let bs := eval vm_compute in (match image_bytes usegs a 8 with Some bs => bs | None => [] end) in
        pose proof (statics_ok_cells usegs L mx a bs SOK CA_RSA72 ltac:(vm_compute; reflexivity)) as TB end.
      cbn [length] in TB. unfold U_RSA_INFO in *.

      zstep. zstep. if_cases KB; zify_cond KB. { exfalso; clear -KB; cbn in KB; try discriminate; lia. }
      zstep. zstep. if_cases KF; zify_cond KF. { exfalso. clear -KF. cbn in KF. lia. } clear KF TB.
      pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 32%nat ST.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HH1 : HEAP usegs L HI h LB m1 mo).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h LB m m1 mo lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
      assert (HP1 : heap_presx usegs L LB (bv_unsigned sp) [(PKA, PKA + 16)] m m1).
      { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR0 DHI Ha.
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _). destruct b as [B kk]; cbn in Hr, Bc. lia. }
      clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof (U_rsa_alloc_wrap_spec L HI HCALLOC HLS DIMG) as SPF. unfold rsa_alloc_wrap_stmt, rsa_alloc_wrap_post, U_RSA_ALLOC_WRAP in SPF.
      eapply aevtM_cut; [ eapply SPF with (lo := lo) (LB := LB) (h := h);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by dlia; try eassumption; try reflexivity; try flia2 | ].
      clear SPF.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO].
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by dlia.
      ddestruct PO as (MI5 & ST5 & MF5 & HT5 & Ha0 & HP5 & RES).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
      match type of Ha0 with ?x = Z_to_bv 64 ?cc => subst x; rename cc into C end.
      match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
      assert (SPP' : bv_unsigned sp + -32 <= PKA) by (clear -SPP; lia).
      clear ST MI.
      heap_transport HP5.
      assert (HPX5 : heap_presx usegs L LB (bv_unsigned sp) [(PKA, PKA + 16)] m m5).
      { eapply heap_presx_trans; [exact HP1|]. eapply heap_presx_of_pres_sub; [exact HP5| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      destruct RES as [[-> HH5] | (HBN & HAPN & HH5 & NEW)].
      + (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1. pose proof (conj HH5 I) as HHbox.
        pose proof (munch_refl [(PKA, PKA + 16)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        release_frame FR ST5 (bv_unsigned sp).
        zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN. cbn in KN. lia. }
        zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        assert (HH9 : HEAP usegs L HI h5 LB m9 mo5).
        { apply (Asn1AuxA.HEAP_munch usegs L HI h5 LB m5 m9 mo5 lo _ (proj1 HHbox) ACL MU WM).
          intros a Ha Hin. cbn [outside] in Hin. rewrite HT5. left. clear -Hin SPP PTOP SLO HLS Ha. lia. }
        apply aevtM_done. unfold pk_setup_post. deexists 15. dexists m9, mo5, h5, (-16256), 0, 0.
        split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
        * eapply heap_presx_trans; [exact HPX5|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
          intros a Ha Hc Ho. exact Ho.
        * left. split; [reflexivity|]. split; [exact HH9| assumption].
      + (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1. pose proof (conj HH5 I) as HHbox.
        pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI). pose proof (conj MI5 I) as MI5box.
        pose proof (munch_refl [(PKA, PKA + 16)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        release_frame FR ST5 (bv_unsigned sp).
        zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. lia. }
        zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        lazymatch type of HH5 with HEAP _ _ _ _ ?lb _ _ =>
        assert (HH9 : HEAP usegs L HI h5 lb m9 mo5);
          [ apply (Asn1AuxA.HEAP_munch usegs L HI h5 lb m5 m9 mo5 lo _ (proj1 HHbox) ACL MU WM);
            intros a Ha Hin; cbn [outside] in Hin; rewrite HT5; left; clear -Hin SPP PTOP SLO HLS Ha; lia |] end.
        apply aevtM_done. unfold pk_setup_post. deexists 15.
        dexists m9, mo5, h5, 0, C, 232.
        split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
        * eapply heap_presx_trans; [exact HPX5|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. exact Ho.
        * right. split; [reflexivity|]. split; [exact HBN|]. split; [exact HAPN|]. split; [exact HH9|]. split; [assumption|].
          split; [intros _; split; [reflexivity|]|intros NE; exfalso; apply NE; reflexivity].
          eapply rsa_at_munch; [exact NEW| exact MU| exact WM| exact (proj1 MI5box)| assumption| cbn [disjoint_from]; clear -HNC ACL SLO HLS SPP; lia|].
          intros d Hd HO. exfalso. unfold rsa_mpds, rsa_fresh, rsa_zero_mpds in Hd. cbn [In r_N r_E map] in Hd.
          destruct Hd as [<-|[<-|Hd]]; [cbn in HO; discriminate| cbn in HO; discriminate|].
          apply in_map_iff in Hd. ddestruct Hd as (o & <- & _). cbn in HO. discriminate.
    - (* [comment removed for export] *)
      assert (TB : ro_cells usegs m (info + 72) [CB 8 [Z_to_bv 8 60; Z_to_bv 8 163; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
      { pose proof (CA_EC72 _ EI) as CAE. revert CAE. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]]; intros CAE;
        (lazymatch goal with |- ro_cells _ ?mx (?e + 72) _ =>
           let a := eval vm_compute in (e + 72) in
           let bs := eval vm_compute in (match image_bytes usegs a 8 with Some bs => bs | None => [] end) in
           pose proof (statics_ok_cells usegs L mx a bs SOK CAE ltac:(vm_compute; reflexivity)) as TB0;
           cbn [length] in TB0; exact TB0 end). }
      assert (NER : info <> U_RSA_INFO).
      { clear -EI. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO, U_RSA_INFO in *. cbn [In] in EI. destruct EI as [<-|[<-|[<-|[]]]]; cbn; lia. }

      assert (AI : 0 <= info < 2^64 /\ info mod 8 = 0).
      { clear -EI. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]]; split; (reflexivity || lia). }
      zstep. zstep. if_cases KB; zify_cond KB.
      1-2: try (exfalso; clear -KB AI; rewrite ?unsigned_lit in KB by lia; rewrite ?land_7_mod in KB; lia).
      zstep. zstep. if_cases KF; zify_cond KF. { exfalso. clear -KF. cbn in KF. lia. } clear KF TB.
      pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 32%nat ST.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HH1 : HEAP usegs L HI h LB m1 mo).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h LB m m1 mo lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
      assert (HP1 : heap_presx usegs L LB (bv_unsigned sp) [(PKA, PKA + 16)] m m1).
      { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR0 DHI Ha.
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _). destruct b as [B kk]; cbn in Hr, Bc. lia. }
      clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      pose proof (U_eckey_alloc_wrap_spec L HI HCALLOC HLS DIMG MT) as SPF. unfold eckey_alloc_wrap_stmt, eckey_alloc_wrap_post, U_ECKEY_ALLOC_WRAP in SPF.
      eapply aevtM_cut; [ eapply SPF with (lo := lo) (LB := LB) (h := h);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by dlia; try eassumption; try reflexivity; try flia2 | ].
      clear SPF.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO].
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by dlia.
      ddestruct PO as (MI5 & ST5 & MF5 & HT5 & Ha0 & HP5 & RES).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
      match type of Ha0 with ?x = Z_to_bv 64 ?cc => subst x; rename cc into C end.
      match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
      assert (SPP' : bv_unsigned sp + -32 <= PKA) by (clear -SPP; lia).
      clear ST MI.
      heap_transport HP5.
      assert (HPX5 : heap_presx usegs L LB (bv_unsigned sp) [(PKA, PKA + 16)] m m5).
      { eapply heap_presx_trans; [exact HP1|]. eapply heap_presx_of_pres_sub; [exact HP5| intros b Hb; exact Hb| clear; lia| clear; lia]. }
      destruct RES as [[-> HH5] | (HBN & HAPN & HH5 & NEW)].
      + (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1. pose proof (conj HH5 I) as HHbox.
        pose proof (munch_refl [(PKA, PKA + 16)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        release_frame FR ST5 (bv_unsigned sp).
        zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN. cbn in KN. lia. }
        zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        assert (HH9 : HEAP usegs L HI h5 LB m9 mo5).
        { apply (Asn1AuxA.HEAP_munch usegs L HI h5 LB m5 m9 mo5 lo _ (proj1 HHbox) ACL MU WM).
          intros a Ha Hin. cbn [outside] in Hin. rewrite HT5. left. clear -Hin SPP PTOP SLO HLS Ha. lia. }
        apply aevtM_done. unfold pk_setup_post. deexists 15. dexists m9, mo5, h5, (-16256), 0, 0.
        split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
        * eapply heap_presx_trans; [exact HPX5|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
          intros a Ha Hc Ho. exact Ho.
        * left. split; [reflexivity|]. split; [exact HH9| assumption].
      + (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1. pose proof (conj HH5 I) as HHbox.
        pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI). pose proof (conj MI5 I) as MI5box.
        pose proof (munch_refl [(PKA, PKA + 16)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        release_frame FR ST5 (bv_unsigned sp).
        zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. lia. }
        zstep. zstep. zstep.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
        lazymatch type of HH5 with HEAP _ _ _ _ ?lb _ _ =>
        assert (HH9 : HEAP usegs L HI h5 lb m9 mo5);
          [ apply (Asn1AuxA.HEAP_munch usegs L HI h5 lb m5 m9 mo5 lo _ (proj1 HHbox) ACL MU WM);
            intros a Ha Hin; cbn [outside] in Hin; rewrite HT5; left; clear -Hin SPP PTOP SLO HLS Ha; lia |] end.
        apply aevtM_done. unfold pk_setup_post. deexists 15.
        dexists m9, mo5, h5, 0, C, 256.
        split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
        * eapply heap_presx_trans; [exact HPX5|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. exact Ho.
        * right. split; [reflexivity|]. split; [exact HBN|]. split; [exact HAPN|]. split; [exact HH9|]. split; [assumption|].
          split; [intros E; exfalso; exact (NER E)| intros _; split; [reflexivity|]].
          ddestruct NEW as (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP).
          dexists idpad, pP, pA, pB, pX, pY, pZ, pN, hpad, pd, qX, qY, qZ.
          eapply ecp_keypair_at_munch; [exact KP| exact MU| exact WM| exact (proj1 MI5box)| assumption| cbn [disjoint_from]; clear -HNC ACL SLO HLS SPP; lia|].
          intros d Hd HO. exfalso. unfold kp_mpds, kp_init, grp_mpds, grp_init in Hd. cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In] in Hd.
          destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; cbn in HO; discriminate.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.