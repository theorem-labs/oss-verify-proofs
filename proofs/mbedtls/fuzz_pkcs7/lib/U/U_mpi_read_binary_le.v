(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_resize_clear U_mpi_core_read_be U_mpi_core_read_le U_mpi_read_binary U_mpi_read_binary_r.
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
Ltac2 gd_tbl_P_mpi_read_binary_le () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_read_binary.mpi_read_binary_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "mpi_read_binary_le_stmt_r"; "mpi_read_binary_le_stmt"].


Definition U_MPI_READ_BINARY_LE : Z := 0x1fdac.

Definition mpi_read_binary_le_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_le ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O5.O4.O3.)PLB,(5.$6.)PdX,$7.PB,$8.Pibs,(5.(0.&8.))Plo,$8.P,(9.O5.O4.O3.R6.R5.R8.R7.)P,(:.O5.R9.R6.R5.)P,(;.(<.$=.(>.R6.)$?.))P,(10.O4.R8.(11.&40.R2;.)(12.O5.O4.O3.R9.)R7.)P,(13.O5.R<.R7.R6.)P,(14.=R8.)P,(14.(15.R9.(16.(17.(0.&8.)R8.)))(18.+2.+3?.))P,(19.O4.R<.R8.R:.(16.(17.(0.&8.)R9.)))P,(1:.(1;.(15.R;.(16.(17.(0.&8.)R:.)))(1<.R<.))(1;.(15.(1<.R<.)+10.)R;.))P,P,(<.$=.(>.R=.)$1=.)(1:.(1;.(15.R=.(16.(17.(0.&8.)R<.)))(1>.R>.))(1;.(15.(1>.R>.)(1?.+4.(20.R>.)))R=.))P,(1:.(1;.(15.R=.(16.(17.(0.&8.)R<.)))R;.)(1;.(11.&40.R32.)R=.))P,(21.O5.R13.R<.(11.&40.R33.))P,(1;.R=.(22.(22.(11.&40.R34.)+50.)(23.O4.)))P,(1;.(24.O4.)R>.)P,(1;.(11.&40.R36.)(12.O5.O4.O3.R14.))P,(<.$8.(25.(11.&40.R37.)+10.)=)P,(1;.(26.O4.)(24.O4.))P,(<.(0.&40.)R37.(27.&40.(28.O4.)))P,(29.O5.R1:.)P,(<.$8.(25.(11.&40.R3<.)+2.)=)P,(2:.O5.O4.R1<.)P,(2;.O4.O1.+8.)P,(<.(0.&40.)R36.(27.&40.(1<.R1:.)))P,(<.(0.&40.)R36.(27.&40.R1:.))P,(<.(0.&40.)R36.(27.&40.(16.(17.(0.&8.)R1:.))))(2<.O5.R20.(2=.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.(16.(17.(0.&8.)R1;.))R1:.R21.R20.)(2>.(2?.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(27.&40.O2.)R22.(30.(0.&40.))R21.(31.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_read_binary_le_stmt_r (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_le ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O5.O4.O3.)PLB,(5.$6.)PdX,$7.PB,$8.Pibs,(5.(0.&8.))Plo,$8.P,(9.O5.O4.O3.R6.R5.R8.R7.)P,(32.O5.R9.R6.(1<.R5.)(27.&40.(33.R5.))(20.R5.)(1>.R5.)(34.R5.)(35.R5.)(>.R5.))P,(;.(<.$=.(>.R6.)$?.))P,(10.O4.R8.(11.&40.R2;.)(12.O5.O4.O3.R9.)R7.)P,(13.O5.R<.R7.R6.)P,(14.=R8.)P,(14.(15.R9.(16.(17.(0.&8.)R8.)))(18.+2.+3?.))P,(19.O4.R<.R8.R:.(16.(17.(0.&8.)R9.)))P,(1:.(1;.(15.R;.(16.(17.(0.&8.)R:.)))(1<.R<.))(1;.(15.(1<.R<.)+10.)R;.))P,P,(<.$=.(>.R=.)$1=.)(1:.(1;.(15.R=.(16.(17.(0.&8.)R<.)))(1>.R>.))(1;.(15.(1>.R>.)(1?.+4.(20.R>.)))R=.))P,(1:.(1;.(15.R=.(16.(17.(0.&8.)R<.)))R;.)(1;.(11.&40.R32.)R=.))P,(21.O5.R13.R<.(11.&40.R33.))P,(1;.R=.(22.(22.(11.&40.R34.)+50.)(23.O4.)))P,(1;.(24.O4.)R>.)P,(1;.(11.&40.R36.)(12.O5.O4.O3.R14.))P,(<.$8.(25.(11.&40.R37.)+10.)=)P,(1;.(26.O4.)(24.O4.))P,(<.(0.&40.)R37.(27.&40.(28.O4.)))P,(29.O5.R1:.)P,(<.$8.(25.(11.&40.R3<.)+2.)=)P,(2:.O5.O4.R1<.)P,(2;.O4.O1.+8.)P,(<.(0.&40.)R36.(27.&40.(1<.R1:.)))P,(<.(0.&40.)R36.(27.&40.R1:.))P,(<.(0.&40.)R36.(27.&40.(16.(17.(0.&8.)R1:.))))(2<.O5.R20.(2=.O5.O4.O3.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.(16.(17.(0.&8.)R1;.))R1:.R21.R20.)(2>.(2?.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(27.&40.O2.)R22.(30.(0.&40.))R21.(31.O5.)))")
(* [comment removed for export] *).

Lemma mpi_read_binary_le_stmt_of_r : ltac2:(CDefT.buildp (gd_tbl_P_mpi_read_binary_le ()) "Psegs,(5.$36.)PL,$37.PHI,(38.R2.R1.)PENTRY,$8.PMSF,$8.P,(39.R5.R4.R3.R2.R1.)(3:.R6.R5.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros segs L HI ENTRY MSF H. unfold mpi_read_binary_le_stmt. intros. eapply H; try eassumption. exact (proj1 H1). Qed.

Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in
      assert (E : c = false) by (unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | reflexivity]);
      rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_zero_any :=
  repeat match goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  end.
Local Ltac rec_checks := zstep; if_false_x; zstep; land_zero_any; zstep; if_false.

Section RB.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0230@D10463954377.94 D10463954377.95 D27668705378.94 D27668705378.95 D67426116409.95 L10311346605.168L10313284974.139L10313566315.138L1083854093.131 L10968046633.92 L11508767299.154L11610259909.164L15032432642.130L16004450953.130L16075621096.89 L16447498622.130L17196195435.92 L17624409962.162L18758812866.92 L18760692967.138L19026868104.168L19028796235.139L19562858013.131L19813155784.132L20317390768.124L20371395153.140L21765854580.90 L21887662552.123L21887662552.128L21887662552.89 L22250863135.140L22253030941.131L23514154262.95 L23587552326.132L27008441484.94 L27008441484.95 L27474501445.140L27775132660.90 L29638086697.132L29644522319.133L2977718986.154 L2977718986.164 L30023472010.140L30572882446.141L30575140364.139L3082205504.157 L3082235176.158 L30845915693.131L30847804975.140L33510041944.123L33510041944.128L33510041944.90 L34290115814.89 L35754698159.94 L35754698159.95 L38407314367.169L38441455198.94 L39939636738.125L39939682334.130L41368264692.152L41368264692.162L41372307913.95 L41416020844.92 L41558440306.131L41560313200.140L41562522430.124L41562522430.129L41930314762.130L42000683143.164L42073265598.169L42973201126.131L43055137673.87 L4391105546.129 L4391369226.129 L44622288685.94 L44622288685.95 L45240522463.131L45290817783.94 L47976175629.140L48074055731.130L49698585326.94 L49698585326.95 L50614963431.132L52101695852.158L52101695852.168L52101704109.160L52101704109.170L52101733636.157L52101733636.167L52101802538.166L52101802538.176L52103796997.169L52616107219.142L53519189168.89 L54379423251.127L54391891673.157L54391985784.169L54398282304.168L54748384003.90 L55715119632.89 L56523337483.154L56870963969.132L5697502143.131 L57339310111.94 L57751195497.168L57751203752.170L58831017767.93 L59308632561.125L60863994103.132L63502481837.97 L65054692228.131L65121243056.89 L65502163868.84 L66083662040.123L66083662040.128L66083662040.90 L6700389208.94  L67171178890.154L7190686615.115 L7193125557.94  L772750287.84   L7947744522.129 L7947907211.94  L7948008202.129 L8313508454.152 L8927195168.129 L9239665441.140 L9716869748.89  L9962237875.123 L9962237875.128 L9962237875.90  00000a01[02T03S04O05605U06406\07B07a08I08^09309409I09e0:U0;10;[0<Z0=N0>C0>`0?50@M0@b0A70AL0Aa0BK0Bg0CO0D>0EC0FQ0GD0GY0H30Ho0IJ0Il0JR0JS0JT0K90Ka0L;0LX0Lm0MB0MW0Ml0NQ0O<0Pj0QK0R40R]0Sk0UL0V;0VP0W90Wi0X>0XS0Xh0YV0Z=0ZU0[>0[[0\80]90^C0^]0_R0`I0a60a_0bQ0c10cN0d20eC0g00gj0i20j30kB0l30lV0lc0m80nT10H12912N12[13413Q14614714814915:15R16516U17V17W17h18=18R18g19E19h1:Y1;J1;o1<L1=61=S1>:1>Y1?A1?V1?k1@@1@US1L2HI2ra2sp1h2dX3ibs3len4HTOP2XB3HB05Ha_st5Hl_stS1L2HI2ra2sp2s01h2dX3ibs3len4HTOP2XB3HB05Ha_st5Hl_st2s12s2S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XB3HB05Ha_st5Hl_stS1L3HLS2ra2sp2s02dX3ibs2lo3len3SLO3SPB2X02XB3HB05Ha_st5Hl_st2s1S1L3HLS2ra2sp2s22dX3ibs2lo3len3SLO3SPB2X02XB3HB05Ha_st5Hl_stS1L4DIMG2ra2sp2dX3ibs3len2XB2p23xs33LX3S1L4DIMG2ra2sp2dX3ibs3len2XB2p2S1L4DIMG2ra2sp2dX3ibs3len2XB2p2S2ra2sp2dX3ibs3len3SPB2X02XB3CTL2p24LEN2S2ra2sp2dX1B3ibs2B03len4BEND3SPB2X02XBS2ra2sp2dX3ibs3len2XB1b3xs33LX3S2ra2sp2dX3ibs3len2XB3CTL2p23NR23xs33LX3S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBFS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len3SPB2X02XBS2ra2sp2dX3ibs3len2XB3CTL2p22N14CTL03XX23xs33LX3S2ra2sp2dX3ibs3len3SPB2X02XBS2ra2sp2dX3ibs3len3SPB2X02XB3CTL2p22N13P20S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB2p22N13P203xs33LX3S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB2p23P20S1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPB2X02XB2XSS2ra2sp2dX3ibs2m23len2XB1i2HiS2ra2sp2dX3ibs3len2XBS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3ACL3SPB2X02XB2XS3CTL2p22N14CTL03P203P243BX23XX2S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len3SPB2X02XB3CTL2p22N13P20S2ra2sp2dX3ibs3len3SPB2X02XBS2ra2sp2s22dX3ibs3len2XB3HB05Ha_st5Hl_stS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB1HS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPB2X02XB2XS3HB05Ha_st5Hl_stS1L3HLS2ra2sp2s02dX1B3ibs2lo3len2BX3BLO3SLO3SPB2X02XB2XS3HB05Ha_st5Hl_st2s12s2S1L2ra2sp2dX3ibs2lo3len3ACL3SPB2X02XB2p22N13P203P24S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XB1a2HaS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPB2X02XB2XS1a2Ha1CS2ra2sp2dX3ibs3len2XB3LX31HS2ra2sp2dX3ibs3len2XB2p23xs33LX31HS2ra2sp2dX3ibs3len3SPB2X02XB2p22N13P20FFS2ra2sp2dX3ibs3len3SPB2X02XB2C03LX31aS2ra2sp2dX3ibs3len3SPB2X02XB2C03LX31a2HaS2ra2sp2dX1B3ibs2B03len2XBS2ra2sp2dX1B3ibs2B03len2XB2p2S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XB3HB05Ha_st5Hl_stS2ra2sp2s02dX3ibs3len2XB3HB05Ha_st5Hl_st2s1S1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3ACL3DHI3SPB2X02XB2XS3CTL2p22N14CTL03P203P253BX23XX23xs33LX31a2Ha1H2H0S1L2HI2ra2sp1h2dX3ibs3len4HTOP2XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XBS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPA3SPB2X02XB2XS3CTL4XAL22C04CTL03LX3S1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3ACL3SPA3SPB2X02XB2XS3CTL2p24XAL22N14CTL03P203P243xs33LX3S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB1HS2ra2sp2dX3ibs3len2XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XB2p23P20S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len3SPB2X02XB2p22N13P203xs33LX3S2ra2sp2dX3ibs3len2XB2p23xs33LX31a1H2H0S2ra2sp2dX3ibs3len2XB2C0S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3SPB2X02XBS2ra2sp2dX3ibs3len2XB3CTL3NR2S2ra2sp2dX3ibs3len2XB3CTL3NR2S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3DHI3SPB2X02XB3HB05Ha_st5Hl_stS1L3HLS2ra2sp2s02dX3ibs2lo3len3SLO3ACL3DHI3SPB2X02XB3HB05Ha_st5Hl_st2s12s2S2ra2sp2dX1B3ibs2B03len2XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPA3ACP3SPB2X02XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB2p22N13P24S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XBS2ra2sp2dX3ibs3len3SPB2XB3HB05Ha_st5Hl_stS2ra2sp2s02dX3ibs3len3SPB2XB3HB05Ha_st5Hl_st2s12s2S2ra2sp2dX1B3ibs3len3SPB2X02XB1HS2ra2sp2dX3ibs3len2XB3LX31a1CS2ra2sp2dX3ibs3len2XB2p23xs33LX31a1CS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3ACL3DHI3SPB2X02XB2XS3CTL2C04CTL03LX31a1CS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3ACL3DHI3SPB2X02XB2XS3CTL2p22N14CTL03P203P243P253BX23xs33LX31a1C1H2H0S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3DHI3SPB2X02XB3LX31a2HaS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3DHI3SPB2X02XB2p22N13P203xs33LX31a2HaS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB3LX31a2B'1k1R3B0'2B4S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3SPB2X02XB2p22N13P203xs33LX31a2B'1k1R3B0'2B4S2ra2sp2dX3ibs3len2XB3CTL2p22N14CTL03xs33LX31a2HoS1L2HI2ra2sp1h2dX3ibs3len2XB2p21a1CS2ra2sp2dX2XBS2ra2sp2dX3ibs3len2XBS1L2HI3HLS2ra2sp1h2dX1B3ibs2lo3len2BX3BLO3SLO3ACL4HTOP3ACP3SPB2X02XB2XS3CTL2C04CTL03LX31a2NOS1L2HI3HLS2ra2sp1h2dX1B3ibs2lo3len2BX3BLO3SLO3ACL4HTOP3SPB2X02XB2XS3CTL2p22N14CTL03P203P243BX23XX23xs33LX31a2NO1H2H0S1L2HI3HLS2ra2sp1h2dX1B3ibs2lo3len2BX3BLO3SLO3ACL4HTOP3SPB2X02XB2XS3CTL2p22N14CTL03P203P243BX23XX23xs33LX31a2NO1HS2ra2sp2dX3ibs3len2XBS2ra2sp2dX2XBS2ra2sp2dX3ibs3len2XB3LX3S2ra2sp2dX3ibs2m23len2XB1i2HiS1L2ra2sp2dX3ibs2lo3len3ACL3ACP2X02XBFFFS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPA3SPB3XAL2X02XB2XS3CTLS2ra2sp2dX3ibs3len2XB2KRS2ra2sp2dX1B3ibs3len3SPB2X02XB1a2HaS1L2HI2ra2sp1h2dX3ibs3len2XB1a1CS1L3HLS2ra2sp2dX1B3ibs2lo3len2BX3BLO3SLO3SPA3SPB3XAL2X02XB2XS3CTLFS2ra2sp2dX3ibs2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS1L2ra2sp2dX3ibs2lo3len3SLO2XBS2ra2sp2dX3ibs3len3SPB2X02XB2C03LX3S1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3ACP3SPB2X02XBS1L3HLS2ra2sp2dX3ibs2lo3len3SLO3ACL3ACP3SPB2X02XBS1L3HLS2ra2sp2dX3ibs2lo3SLO3SPB2X02XBS2ra2sp2dX3ibs3len2XB3CTL3NR2S2ra2sp2dX1B3ibs2B03len4BEND3SPB2X02XB3CTLS2ra2sp2dX3ibs3len2XB3CTL3NR2S2ra2sp2dX3ibs3len3SPB2X02XB3X022C03LX3S2ra2sp2dX3ibs3len3SPB2X02XB2p2S2ra2sp2dX3ibs3len3SPB2X02XB2p23P204P216S2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XBS2ra2sp2dX3ibs3len2XB". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND"] Lemma U_mpi_read_binary_le_spec_r : forall MSF, MSF = U_MEMSET_FUNC -> mpi_read_binary_le_stmt_r usegs L HI U_MPI_READ_BINARY_LE MSF.
  Proof.
    intros MSF ->. unfold mpi_read_binary_le_stmt_r, U_MPI_READ_BINARY_LE. intros until lo.
    intros HH MA NST XW HB B0 BEND BCR BX BXP BLO ST SLO ACL HTOP SPA DHI TP MI RA SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as ND.
    dpose MA as (CH & XAL & X0 & LEN & NR & OWN).
    dpose XW as (XCW & XD & XP).
    unfold MPI_MAX_LIMBS in NR. pose proof (rw_cells_bound _ _ _ _ CH) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    assert (PLO : md_own dX = LHeap -> md_p dX + 4 * md_n dX <= alloc_ceiling).
    { intros HO. rewrite HO in OWN. ddestruct OWN as (_ & PIN & _). pose proof (proj1 (Forall_forall _ _) HBR _ PIN) as (_ & _ & _ & P4 & _). exact P4. }
    clear CH OWN.
    set (len := Z.of_nat (length ibs)) in *.
    pose proof (conj HH I) as HH0. pose proof (conj SOK I) as SOK0.
    carve_frame 32%nat ST.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    replace ((len mod 18446744073709551616) ≫ 2 + Z.b2z (0 <? Z.land (len mod 18446744073709551616) 3)) with (chars_to_limbs4 len)
      by (rewrite Z.mod_small by lia; rewrite Z.shiftr_div_pow2 by lia; change (2^2) with 4; symmetry; apply chars_to_limbs4_eq; lia).
    assert (CTL : 0 <= chars_to_limbs4 len <= len) by (unfold chars_to_limbs4; lia).
    assert (MA1 : mpi_at usegs m1 LB (md_addr dX) (Z_to_bv 64 (md_sg dX)) (md_n dX) (md_p dX) (md_limbs dX) (md_pad dX) (md_own dX)).
    { eapply mpdr_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; split; [lia| exact I]|].
      intros HO. cbn. split; [| exact I]. pose proof (PLO HO). lia. }
    zstep.
    eapply aevtM_cut.
    { eapply (U_mpi_resize_clear_spec L HI HFREE HCALLOC HLS SW DIMG HND) with (dX := dX) (nl := chars_to_limbs4 len) (lo := lo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia.
      split; [intros a Ha; destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] | split; [exact XD| exact XP]]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & mo2 & h2 & LB2 & dX2 & r & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MA2 & OUT2 & PX2 & SOK2 & R2).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2. pose proof (HND _ _ _ _ HH2) as ND2.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2].
    ddestruct R2 as (R2 & ADDR2 & FRESH2).
    (* [comment removed for export] *)
    apply (heap_presx_rw_cells usegs L _ _ _ m1 m2 _ _ PX2) in FR;
      [| cbn [cells_size csize Nat.add]; intros a Ha; left; lia
       | unfold mpd_ivs; destruct (md_own dX) eqn:EO; cbn; (split; [lia|]); [exact I| |exfalso; exact (NST eq_refl)]; split; [|exact I]; pose proof (PLO eq_refl); lia ].
    apply (heap_presx_bytes_at usegs L _ _ _ m1 m2 _ _ PX2) in HB;
      [| intros a Ha; destruct (BCR a ltac:(lia)) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]
       | unfold mpd_ivs; destruct (md_own dX) eqn:EO; cbn; (split; [lia|]); [exact I| |exfalso; exact (NST eq_refl)]; split; [|exact I]; destruct (BXP eq_refl); lia ].
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs dX) m m2).
    { eapply heap_presx_trans; [| eapply heap_presx_weaken; [exact PX2| lia| intros a Ho; exact Ho]].
      eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia]. }
    clear MU WM PX2 MA MA1 HH MI ST SOK.
    destruct R2 as [(-> & SG2 & N2 & LIMBS2 & NULL2)|(-> & SG2 & N2 & LIMBS2 & NULL2)].
    2: { (* [comment removed for export] *)
      unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. zstep; if_cases KR; zify_cond KR; [exfalso; cbn in KR; lia|].
      zstep. zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
      destruct HH0 as [HH0 _]. destruct SOK0 as [SOK0 _].
      apply aevtM_done. unfold mpi_read_binary_post. deexists 16. dexists h2, LB2, dX2, MBEDTLS_ERR_MPI_ALLOC_FAILED.
      split; [reflexivity|]. split; [assumption|]. split; [exact ST2|]. split; [exact MF2|]. split; [exact HT2|].
      split; [exact HH2|]. split; [exact MA2|]. split; [exact OUT2|]. split; [exact HPX2|]. split; [exact SOK2|].
      split; [right; reflexivity|]. split; [intros; discriminate|]. exact FRESH2. }
    (* [comment removed for export] *)
    zstep; if_cases KR; zify_cond KR; [| exfalso; apply KR; reflexivity].
    dpose MA2 as [[CH2 (XAL2 & X02 & LEN2 & NR2 & OWN2)] _].
    destruct dX2 as [X2 sg2 n2 p2 limbs2 pad2 own2]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    subst X2 sg2 n2 limbs2. unfold mpi_cells in CH2. unfold MPI_MAX_LIMBS in NR2.
    rec_checks. zstep. zstep.
    assert (NN : bv_unsigned (zx16 (Z_to_bv 64 (chars_to_limbs4 len))) = chars_to_limbs4 len) by (unfold zx16; rewrite !unsigned_lit by lia; apply Z.mod_small; lia).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST2 (bv_unsigned sp).
    rewrite ?NN.
    zstep.
    replace (zx16 (Z_to_bv 64 (chars_to_limbs4 len))) with (Z_to_bv 64 (chars_to_limbs4 len))
      by (unfold zx16; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    destruct HH0 as [HH0 _]. destruct SOK0 as [SOK0 _].
    dpose OUT2 as (_ & NST2 & _). cbn [md_own] in NST2.
    pose proof U_mpi_core_read_le_spec as SPr. unfold mpi_core_read_le_stmt, U_MPI_CORE_READ_LE in SPr.
    assert (CTL0 : chars_to_limbs4 len = 0 <-> len = 0) by (unfold chars_to_limbs4; lia).
    destruct own2 as [| |]; [| | exfalso; exact (NST2 eq_refl)].
    + (* [comment removed for export] *)
      destruct OWN2 as [-> C0].
      assert (U0 : u32arr usegs m2 0 []).
      { split; [split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]] | split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]. }
      eapply aevtM_cut_evt; [ exact MK2 | eapply SPr with (X := 0) (n := chars_to_limbs4 len) (B := B) (blen := len) (lo := lo) (xs := []) (bs := ibs);
          rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (unfold MPI_CORE_READ_LE_STACK; cbn; lia) | ].
      cbv beta. intros ms' PO. unfold mpi_core_read_le_post in PO.
      ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & xs3 & -> & MU3 & WM3 & MI3 & U3 & LX3 & _ & ST3).
      rewrite ?(unsigned_lit (bv_unsigned sp)) in MU3 by lia.
      assert (xs3 = []) as -> by (destruct xs3; [reflexivity| cbn in LX3; lia]).
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ CH2 MU3 WM3 ltac:(cbn; split; [lia| split; [unfold MPI_CORE_READ_LE_STACK; lia| exact I]])) as CH3.
      apply aevtM_done. unfold mpi_read_binary_post. deexists 16. dexists h2, LB2.
      dexists (mkMPD (md_addr dX) 1 0 0 [] pad2 LNull), (read_be_ret (chars_to_limbs4 len) len).
      assert (R0 : read_be_ret (chars_to_limbs4 len) len = 0) by (unfold read_be_ret; destruct (Z.ltb_spec (chars_to_limbs4 len) (chars_to_limbs4 len)); [lia| reflexivity]).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF2|]. split; [exact HT2|].
      split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU3| exact WM3|].
        intros a Ha NO. cbn in NO. unfold MPI_CORE_READ_LE_STACK in NO. rewrite HT2. left. lia. }
      split. { split; [|left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [rewrite C0 in CH3; exact CH3|]. split; [exact XAL2|]. split; [exact X02|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; reflexivity. }
      split; [rewrite <- C0; exact OUT2|].
      split. { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU3| exact WM3|].
        intros a Ha Hc Ho. cbn. unfold MPI_CORE_READ_LE_STACK. split; [lia|]. split; [|exact I].
        destruct Hc as [C|[C|([B' k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0' & B1 & B2 & B4 & B5); cbn in R, B4; lia]. }
      split. { eapply statics_ok_munch; [exact SOK2| exact MU3|]. intros a Ha NW. cbn. unfold MPI_CORE_READ_LE_STACK. split; [lia|]. split; [lia| exact I]. }
      split; [left; exact R0|]. split; [intros _; cbn; split; [reflexivity| unfold chars_to_limbs; unfold chars_to_limbs4 in C0; lia]|].
      rewrite <- C0. exact FRESH2.
    + (* [comment removed for export] *)
      ddestruct OWN2 as (N1 & PIN2 & PAL2 & U2). rewrite repeat_length in U2 || idtac.
      pose proof (proj1 (Forall_forall _ _) HBR2 _ PIN2) as (P20 & P216 & _ & P24 & P25). cbn in P20, P216, P24, P25.
      assert (BX2 : B + len <= p2 \/ p2 + 4 * chars_to_limbs4 len <= B).
      { eapply (new_limbs_apart_range usegs L HI h2 LB LB2 m2 m2 mo2 lo dX (mkMPD (md_addr dX) 1 (chars_to_limbs4 len) p2 (repeat (Z_to_bv 64 0) (Z.to_nat (chars_to_limbs4 len))) pad2 LHeap) B len);
          try eassumption; try reflexivity; try (cbn; lia); destruct DIMG; lia. }
      assert (XX2 : md_addr dX + 16 <= p2 \/ p2 + 4 * chars_to_limbs4 len <= md_addr dX).
      { eapply (new_limbs_apart_range usegs L HI h2 LB LB2 m2 m2 mo2 (bv_unsigned sp) dX (mkMPD (md_addr dX) 1 (chars_to_limbs4 len) p2 (repeat (Z_to_bv 64 0) (Z.to_nat (chars_to_limbs4 len))) pad2 LHeap) (md_addr dX) 16);
          try eassumption; try reflexivity; try (cbn; lia); try (destruct DIMG; lia).
        intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C]. }
      eapply aevtM_cut_evt; [ exact MK2 | eapply SPr with (X := p2) (n := chars_to_limbs4 len) (B := B) (blen := len) (lo := lo) (xs := repeat (Z_to_bv 64 0) (Z.to_nat (chars_to_limbs4 len))) (bs := ibs);
          rewrite ?unsigned_lit by lia; rewrite ?repeat_length; try eassumption; try reflexivity; try (unfold MPI_CORE_READ_LE_STACK; cbn; lia) | ].
      cbv beta. intros ms' PO. unfold mpi_core_read_le_post in PO.
      ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & xs3 & -> & MU3 & WM3 & MI3 & U3 & LX3 & _ & ST3).
      rewrite ?(unsigned_lit (bv_unsigned sp)) in MU3 by lia. rewrite repeat_length in LX3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ CH2 MU3 WM3 ltac:(cbn; split; [lia| split; [unfold MPI_CORE_READ_LE_STACK; lia| exact I]])) as CH3.
      apply aevtM_done. unfold mpi_read_binary_post. deexists 16. dexists h2, LB2.
      dexists (mkMPD (md_addr dX) 1 (chars_to_limbs4 len) p2 xs3 pad2 LHeap), (read_be_ret (chars_to_limbs4 len) len).
      assert (R0 : read_be_ret (chars_to_limbs4 len) len = 0) by (unfold read_be_ret; destruct (Z.ltb_spec (chars_to_limbs4 len) (chars_to_limbs4 len)); [lia| reflexivity]).
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact MF2|]. split; [exact HT2|].
      split. { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact ACL| exact MU3| exact WM3|].
        intros a Ha NO. cbn in NO. unfold MPI_CORE_READ_LE_STACK in NO. rewrite HT2.
        destruct (Z.le_gt_cases p2 a); [destruct (Z.lt_ge_cases a (p2 + 4 * chars_to_limbs4 len)); [right; right; exists (p2, 4 * chars_to_limbs4 len); split; [exact PIN2| cbn; lia] |]|]; left; lia. }
      split. { split; [|left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
        split; [exact CH3|]. split; [exact XAL2|]. split; [exact X02|]. split; [lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
        split; [exact N1|]. split; [exact PIN2|]. split; [exact PAL2| exact U3]. }
      split; [eapply mpd_out_ext; [exact OUT2| reflexivity| cbn; discriminate| reflexivity]|].
      split. { eapply heap_presx_trans; [exact HPX2|]. eapply heap_presx_of_munch; [exact MU3| exact WM3|].
        intros a Ha Hc Ho. cbn. unfold MPI_CORE_READ_LE_STACK. split; [| split; [|exact I]].
        - eapply (new_limbs_apart usegs L HI h2 LB LB2 m2 m2 mo2 (bv_unsigned sp) dX (mkMPD (md_addr dX) 1 (chars_to_limbs4 len) p2 (repeat (Z_to_bv 64 0) (Z.to_nat (chars_to_limbs4 len))) pad2 LHeap) a);
            try eassumption; try reflexivity; try lia; try (destruct DIMG; lia).
          intros HOX. unfold mpd_ivs in Ho. rewrite HOX in Ho. cbn in Ho. lia.
        - destruct Hc as [C|[C|([B' k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (B0' & B1 & B2 & B4 & B5); cbn in R, B4; lia]. }
      split. { eapply statics_ok_munch; [exact SOK2| exact MU3|]. intros a Ha NW. cbn. unfold MPI_CORE_READ_LE_STACK. split; [destruct DIMG; lia|]. split; [lia| exact I]. }
      split; [left; exact R0|]. split; [intros _; cbn; split; [reflexivity| unfold chars_to_limbs, chars_to_limbs4; reflexivity]|].
      exact FRESH2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="HFREE HCALLOC HLS SW DIMG HND"] Lemma U_mpi_read_binary_le_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_read_binary_le_stmt usegs L HI U_MPI_READ_BINARY_LE MSF.
  Proof. intros MSF E. apply mpi_read_binary_le_stmt_of_r. apply U_mpi_read_binary_le_spec_r. exact E. Qed.
End RB.
