(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free.
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
Ltac2 gd_tbl_P_ecp_group_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_zero"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "ecp_group_free_post"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_tail_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_Tsize"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_T"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"].


Definition U_ECP_GROUP_FREE : Z := 0x3850c.
(* [comment removed for export] *)
Notation ECP_GROUP_FREE_STACK := 80 (only parsing).

(* [comment removed for export] *)
Definition grp_free_LB (g : ecp_grp) (LB : list blk) : list blk := lb_free_mpds (grp_free_mpds g) LB.

Definition ecp_group_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (A : Z) (g : ecp_grp) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1=.O1<.O1;.)Lh',(5.O1=.O1<.O1;.)(6.(7.$0.R13.(8.(9.(:.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(;.O19.)O8.(<.(2.&40.))R3.(=.O1=.))R2.))(6.(>.O1=.R3.)(6.(?.O1=.R3.O3.(10.&40.O18.))(6.(11.O1.R2.)(6.(7.$12.(13.O1=.O1<.O1;.R1.)(13.O1=.O1<.O1;.O7.))(6.(14.O1=.O1<.O1;.R1.(15.O4.O6.)R3.R2.)(6.(16.O1=.O1:.R3.(15.O4.O6.)O5.(17.O5.))(6.(18.O1=.R3.O5.(19.$1:.(1;.#<0.(1<.(2.&8.)(1=.&8.=)#<0.))(1>.$1:.)))(6.(1?.O1=.O1<.(15.O4.O6.)(10.&40.O18.)(19.(20.$12.$12.)(21.$12.$12.O5.(22.O5.$23.))(1>.(20.$12.$12.)))O2.R3.)(24.O1=.O1<.R3.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_group_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O6.O5.O4.)PLB,(26.$27.)PA,$12.Pg,$28.Plo,$12.P,(14.O6.O5.O4.R5.R4.R7.R6.)P,(16.O6.O3.R8.R5.R4.R3.)P,(29.(2:.R4.))P,(2;.O5.(15.R5.R7.)(10.&40.R2:.)(13.O6.O5.O4.R8.)R6.$23.)P,(2<.(2=.(22.R7.$23.)(2>.O5.))(2=.(2?.O5.)R7.))P,(?.O6.R<.R6.(10.&40.R2<.))P,(2=.R7.(30.(30.(10.&40.R2=.)+50.)(31.O5.)))P,(2=.(32.O5.)R8.)P,(2=.(10.&40.R2?.)(13.O6.O5.O4.R=.))P,(7.$12.(33.(10.&40.R30.)+10.)=)P,(2=.(2?.O5.)(32.O5.))P,(7.(2.&40.)R30.(1=.&40.(34.O5.)))P,(>.O6.R13.)P,(24.O6.O5.R14.)P,(35.O5.O1.+8.)P,(7.$12.(33.(10.&40.R37.)+2.)=)P,(7.(2.&40.)R2?.(1=.&40.R13.))(36.O6.R17.(37.O6.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.R13.R12.R18.R17.)(9.(:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(1=.&40.O2.)R19.(<.(2.&40.))R18.(=.O6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section STEP.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Variables ENTRY MSF : Z.
  Hypothesis SPF : mpi_free_stmt segs L HI ENTRY MSF.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L19002156758.125L19028896459.94 L19039005131.123L20493946930.97 L27678321849.97 L33611103159.97 L33958652657.99 L36886158029.97 L37704068853.95 L38147545031.123L55677836971.95 L59231260123.97 L59308585607.100L65240132683.12300000G00[00f01C01O01[02202A02G02Y02b02n03M03bS2sp1A2sz2X02B12B21a2HaS1L3HLS2sp2lo2LO3ACLS1L2sp4ACLsS4segs1L2HI2sp2h02SP4SPle3SPTS2sp2SP4SPleS2sp1A2X02B1S2sp1A2sz2d02X02B12B21HS2sp1A2sz2X02B2S2sp1AS2sp1A2d02X02E02B1S2sp1A2szS1L2sp2lo2LOS1L2sp1A2sz2X02ND2B12B21a2Ha2HdS2sp1A2sz2d02X02E02B2". (* [comment removed for export] *)
  #[using="SPF HLS DIMG"] Lemma free_step : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)PPOST,P,$0.SpPm0,P,(2.&40.)(3.(2.&8.))Pmc,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Ph0,(5.Vsegs,VL,VHI,)Phc,(5.Vsegs,VL,VHI,)PLB,(26.$27.)PLBf,(26.$27.)PLBc,(26.$27.)PSP,$12.PA,$12.Psz,$12.Plo,$12.PFR,(26.$38.)Pd0,$38.Prest,(26.$38.)PCS,(26.(20.$12.(26.$1:.)))PX0,$12.P,(14.Vsegs,VL,VHI,R=.R:.R10.R?.)P,(7.$12.(13.Vsegs,VL,VHI,R>.)(13.Vsegs,VL,VHI,R?.))P,(7.$12.(39.R6.)R3.)P,(3:.(20.$12.$12.)Lb,(20.$12.$12.)(3;.VL,(3<.$12.$12.R1.)(3=.$12.$12.R1.))R?.)P,(3>.R10.)P,(2;.VL,R10.R>.(13.Vsegs,VL,VHI,R13.)R=.R<.)P,(2<.(2=.(22.R>.R=.)(2>.VL,))(2=.(2?.VL,)R>.))P,Pd,$38.P,(3?.$38.R1.R=.)P,(7.$40.(41.R2.)$42.)(6.(3?.(20.$12.$12.)(21.$12.$12.(43.R3.)(44.+4.(45.R3.)))R16.)(6.(2=.+1.(45.R3.))(6.(46.=(43.R3.))(6.(2=.(22.(43.R3.)(44.+4.(45.R3.)))(32.VL,))(2<.(2=.(22.R12.R11.)(43.R3.))(2=.(22.(43.R3.)(44.+4.(45.R3.)))R12.))))))P,(29.R=.)P,Pb,$27.P,(3?.$27.R1.R15.)(3?.$27.R2.R17.)P,Pb,$27.P,(3?.$27.R1.R16.)(3?.$27.R2.(47.R10.R16.))P,Pb,$27.P,(3?.$27.R1.R16.)(3?.$27.R2.R19.)P,P,(7.$40.(41.R10.)$42.)(48.(3?.(20.$12.$12.)(21.$12.$12.(43.R11.)(44.+4.(45.R11.)))R18.))P,(3?.$38.R11.R12.)P,(2=.R16.R?.)P,(2=.(22.R10.+10.)(22.R17.R16.))P,(48.(7.$40.(41.R14.)$49.))P,(3:.$38.(4:.Vsegs,R21.R1;.)(19.$38.R15.R14.))P,(3:.$38.Ld,$38.(6.P,(7.$40.(41.R1.)$42.)(3?.$38.R2.R19.)(6.(2=.R1;.(39.R1.))(6.(2=.(22.(39.R1.)+10.)(22.R1;.R1:.))(2<.(2=.(22.(39.R1.)+10.)R14.)(2=.(22.R14.+10.)(39.R1.))))))R15.)P,(3:.(20.$12.(26.$1:.))Lac,(20.$12.(26.$1:.))(18.Vsegs,R24.(3<.$12.(26.$1:.)R1.)(3=.$12.(26.$1:.)R1.))R15.)P,(3:.(20.$12.(26.$1:.))Lac,(20.$12.(26.$1:.))(6.(2<.(6.(2=.R1=.(3<.$12.(26.$1:.)R1.))(2=.(22.(3<.$12.(26.$1:.)R1.)(4;.(4<.(3=.$12.(26.$1:.)R1.))))(22.R1=.R1<.)))(2=.(10.&40.R47.)(3<.$12.(26.$1:.)R1.)))(2<.(2=.(22.(3<.$12.(26.$1:.)R1.)(4;.(4<.(3=.$12.(26.$1:.)R1.))))R16.)(2=.(22.R16.+10.)(3<.$12.(26.$1:.)R1.))))R16.)P,(1?.Vsegs,VL,R20.R1>.(19.(20.$12.$12.)(21.$12.$12.R1=.(22.R1=.R1<.))(1>.(20.$12.$12.)))R26.R25.)P,(?.Vsegs,R26.R1<.(10.&40.R48.))P,(2=.R1=.(30.(30.(10.&40.R49.)+20.)(31.VL,)))P,(2=.(32.VL,)R1>.)P,(2=.(10.&40.R4;.)R22.)P,(2=.R23.(13.Vsegs,VL,VHI,R28.))P,(7.$12.(33.(10.&40.R4=.)+10.)=)P,(2=.(2?.VL,)(32.VL,))P,(7.(2.&40.)R4=.(1=.&40.(34.VL,)))P,(>.Vsegs,R2>.)P,(24.Vsegs,VL,R2?.)P,(35.VL,VMSF,+8.)P,(7.(2.&40.)R4;.(1=.&40.R22.))P,Pt0',(2.&40.)Pt1',(2.&40.)Pt2',(2.&40.)Pa0',(2.&40.)Pa1',(2.&40.)Pa2',(2.&40.)Pa3',(2.&40.)Pa4',(2.&40.)Pa5',(2.&40.)Pa6',(2.&40.)Pa7',(2.&40.)Pt3',(2.&40.)Pt4',(2.&40.)Pt5',(2.&40.)Pt6',(2.&40.)Pm2,P,(2.&40.)(3.(2.&8.))Pmo2,$4.Ph2,(5.Vsegs,VL,VHI,)P,(14.Vsegs,VL,VHI,R1.(47.R38.R3>.)R3.R2.)P,(7.$12.(13.Vsegs,VL,VHI,R2.)(13.Vsegs,VL,VHI,R43.))P,(11.R45.R4.)P,(3:.$38.(4:.Vsegs,R6.(47.R3;.R41.))R3:.)P,(3:.(20.$12.(26.$1:.))Lac,(20.$12.(26.$1:.))(18.Vsegs,R8.(3<.$12.(26.$1:.)R1.)(3=.$12.(26.$1:.)R1.))(19.(20.$12.(26.$1:.))(21.$12.(26.$1:.)R39.(4=.=(1=.&40.+1.)=(4>.R3<.)))R3:.))P,(1?.Vsegs,VL,R44.R42.(19.(20.$12.$12.)(21.$12.$12.R41.(22.R41.R40.))(1>.(20.$12.$12.)))R4:.R8.)P,(?.Vsegs,R9.R40.(10.&40.R6<.))P,(>.Vsegs,R:.)P,(24.Vsegs,VL,R;.)(36.Vsegs,R;.R4?.(9.(:.R70.R6?.R6>.R6=.R1;.R1:.R19.R69.R68.R18.R17.R16.R15.R14.R13.R12.R11.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R10.R?.R>.R=.)R51.(;.R70.)R50.(<.(2.&40.))R<.(=.Vsegs,)))(36.Vsegs,R32.R35.(9.(:.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.)R37.(1=.&40.VENTRY,)R36.(<.(2.&40.))R33.(=.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until X0. intros HH HTc E0 HBR HAP CW ND FF1 FF2 SUBF SUBf SUBc NI IN B1 B2 OWN LIV LIVS CH CHS PXA ST LO ACL SPle SPT SPA DHI TP MI SOK CA ->.
    intros K. pose proof DIMG as [DI1 DI2]. assert (ACLs : alloc_ceiling <= bv_unsigned sp) by lia.
    pose proof (client_wrange_weak L _ _ _ (bv_unsigned sp) _ _ _ A sz CW ltac:(intros b Hb; exact Hb) SPle ltac:(lia) ltac:(lia)) as CWs.
    pose proof (Forall_inv LIV) as M0. unfold mpdr_at in M0. rewrite E0 in M0.
    eapply aevtM_cut.
    { unfold mpi_free_stmt in SPF. eapply SPF with (lo := lo) (h := hc) (LB := LBc);
        [ exact HH | exact M0 | exact OWN | | | | exact ST | lia | exact ACL | rewrite HTc; lia | exact SPA | exact DHI | exact TP | exact MI | exact SOK | exact CA | reflexivity ].
      - change (mpi_free_LB (md_own d0) (md_p d0) (md_n d0) LBc) with (lb_free_mpd d0 LBc). rewrite HTc.
        eapply (client_wrange_weak L); [exact CW| exact SUBf| lia| lia| lia].
      - intros O. ddestruct (FF1 d0 IN O) as (_ & _ & _ & _ & ?). lia.
      - intros a Ha Hd. exfalso. lia. }
    cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO). injection E as -> ->.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & CHX & PX & SOK2).
    change (mpi_free_LB (md_own d0) (md_p d0) (md_n d0) LBc) with (lb_free_mpd d0 LBc) in HH2, PX.
    change ((X0, X0 + 16) :: mpi_free_X (md_own d0) (md_p d0) (md_n d0)) with (mpd_fp (mkMPD X0 (md_sg d0) (md_n d0) (md_p d0) (md_limbs d0) (md_pad d0) (md_own d0))) in PX.
    assert (EFP : mpd_fp (mkMPD X0 (md_sg d0) (md_n d0) (md_p d0) (md_limbs d0) (md_pad d0) (md_own d0)) = mpd_fp d0) by (unfold mpd_fp; cbn; rewrite E0; reflexivity).
    rewrite EFP in PX. clear EFP.
    apply (K y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 mo2 h2 HH2 ltac:(rewrite HT2; exact HTc) MF2).
    - eapply (lives_after_free segs L LB LBf (bv_unsigned sp) _ A sz FR HBR HAP CWs FF1 FF2 mc m2 LBc d0 rest);
        [exact SUBc| exact SUBf| exact IN| lia| lia| exact PX| exact MI| exact MI2| exact (Forall_inv_tail LIV)|].
      eapply Forall_impl; [| exact LIVS]. cbn. (intros d dd_H; ddestruct dd_H as (Q1 & Q2 & Q3 & Q4)). rewrite E0. auto.
    - apply Forall_cons; [exact CHX|].
      eapply (chunks_after_free segs L LB LBf (bv_unsigned sp) _ A sz FR CWs ACLs FF1 mc m2 LBc d0 CS);
        [exact SUBf| exact IN| lia| lia| exact PX| exact CH|].
      eapply Forall_impl; [| exact CHS]. cbn -[Z.add Z.le Z.of_nat]. intros ac [Q1 Q2]. rewrite E0. auto.
    - eapply heap_presx_trans; [exact PXA|].
      eapply (heap_presx_weak segs L) with (SP1 := bv_unsigned sp) (X1 := [(A, A + sz)]); [| intros b Hb; exact Hb| exact SPle| intros x Hx; exact Hx].
      eapply (heap_presx_free_fp segs L LB); [exact PX| exact SUBf| exact SUBF| exact HBR| exact HAP| | exact DHI| lia| exact DI1| exact DI2| intros a Ha; cbn in Ha; rewrite E0; lia].
      intros O. ddestruct (FF1 d0 IN O) as (I1 & I2 & _). split; [exact I1|]. split; [exact (NI O)| exact I2].
    - exact ST2. - exact MI2. - exact SOK2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End STEP.

(* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fs_post spo HI HH LIV CH PXA ST MI SOK MF HTc MK :=
    clear HH LIV CH PXA ST MI SOK HTc MK;
    let MF2 := fresh "MF" in
    intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? HH HTc MF2 LIV CH PXA ST MI SOK;
    rewrite ?(unsigned_lit spo) in ST by lia;
    pose proof (mo_frame_trans _ _ _ MF MF2) as MF'; clear MF MF2; rename MF' into MF;
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK;
    try (lazymatch goal with |- aevtM _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?r)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 r)) with (Z_to_bv 64 r) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).

  (* [comment removed for export] *)
  Ltac inl := solve [repeat (first [left; reflexivity| right])].
  Ltac fs_side spo ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF restF :=
    rewrite ?(unsigned_lit spo) by lia;
    first
      [ exact HBR | exact HAP | exact CW | exact ND | exact FF1 | exact DISF | exact HH | exact HTc | exact LIV | exact CH | exact PXA
      | exact ST | exact TP | exact MI | exact SOK | exact CA | exact ACLx
      | lazymatch goal with
        | |- forall b, In b _ -> In b _ =>
            first [ exact SUBF | intros b Hb; rewrite EQF in Hb; exact (lb_free_mpds_sub restF _ b Hb)
                  | intros b Hb; do 8 (try (apply lb_free_mpd_sub in Hb)); auto ]
        | |- _ = LHeap -> ~ In _ _ =>
            first [ match goal with NI : forall d, In d _ -> md_own d = LHeap -> ~ In _ _ |- _ => intros O; apply NI; [apply INF; cbn; first [inl| tauto]| exact O] end
                  | intros O; unfold grp_free_LB; apply lb_free_mpds_notin; [exact NDL| apply INF; cbn; first [inl| tauto]| exact O] ]
        | |- In _ _ => apply INF; cbn; first [inl| tauto]
        | |- md_addr _ = _ => eassumption
        | |- _ <> LStatic => refine (proj1 (Forall_forall _ _) FRB _ _); cbn; first [inl| tauto]
        | |- Forall _ _ =>
            repeat apply Forall_cons; try apply Forall_nil;
            first [ (* [comment removed for export] *) split; [ first [ intros _; apply INF; cbn; first [inl| tauto]
                                                   | intros O; exfalso; eapply (proj1 (Forall_forall _ _) KEPT); [| exact O]; cbn; first [inl| tauto] ]
                                           | lia ]
                  | (* [comment removed for export] *) cbn [fst snd cells_size csize Nat.add mpi_cells length]; lia ]
        | |- _ = Z_to_bv 64 _ => reflexivity
        end
      | lia
      | match goal with |- ?g => idtac "UNSOLVED" g end ].

  Ltac fa_nth H n := lazymatch n with O => constr:(Forall_inv H) | S ?k => let H' := constr:(Forall_inv_tail H) in fa_nth H' k end.
  Ltac fa_get H n name := let t := fa_nth H n in pose proof t as name; cbn [fst snd] in name.


Section GF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0@L10313562438.106L1054875524.106 L13596208895.106L24933826451.106L29520290632.106L3033325854.106 L35502191104.134L35502191104.135L35508388771.134L3820768867.106 L40905624765.106L42594554710.105L52101695852.132L52101802921.136L52108543731.133L52108543731.134L52108543731.135L52969527648.133L5451249752.106 L6372771493.105 L6741498870.133 L6741498870.134 L6741498870.135 00001502403;04>05Q06U08:09_0;<0<D0=I0>H0?m0AO0BU0C^0Dd0Ek0G>0H=0IA0JH0KLS1L2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3DHIS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LTS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3SPA3SPBS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POSS1L3HLS2ra2sp1A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO3SPBS1L2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT2NDS1L2HI3HLS2ra2sp2h01A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO4HTOP3SPB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO4HTOP3SPB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO3SPB1a1QS1L2ra2sp1A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3ACLS2ra2sp1A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT2SXS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LTS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a1C1L3HLS2lo3POS2ND2SX2LO3ACL3DHI3SPBS1L3HLS2ra2sp1A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO3ACL3SPB1a1b1k1C2B4S2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C11nS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C21n2C1S2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C21nS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C12C2S1L3HLS2ra2sp1A2lo2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT3POS2LO3SPBS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LTS2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C1S2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C22C1S2ra2sp1A2hc2c12c22c32c42c52c62c72tc2L02L12L22L32L42L52L62L72LT1a2C2". (* [comment removed for export] *)
  #[using="HLS DIMG"] Lemma zero_walk : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Pmo0,$4.Pmo,$4.Ph0,(5.$4?.VL,VHI,)Ph,(5.$4?.VL,VHI,)PMT,(26.$50.)PLB,(26.$27.)PA,$12.Pg,$28.Plo,$12.Phc,(26.$1:.)Pc1,(26.$1:.)Pc2,(26.$1:.)Pc3,(26.$1:.)Pc4,(26.$1:.)Pc5,(26.$1:.)Pc6,(26.$1:.)Pc7,(26.$1:.)Ptc,(26.$1:.)Pfj,(26.(2.&8.))Pxra,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)ZLBf,(26.$27.)(15.R10.R12.)P,(14.$4?.VL,VHI,R15.R1.R19.R17.)P,(7.$12.(13.$4?.VL,VHI,R16.)(13.$4?.VL,VHI,R17.))P,(11.R1:.R19.)P,(1?.$4?.VL,R4.(10.&40.R3=.)(19.(20.$12.$12.)(21.$12.$12.R15.(22.R15.+<0.))(1>.(20.$12.$12.)))R1=.R1<.)P,(18.$4?.R1=.R16.R13.)P,(7.$51.(4<.R14.)#8.)P,(18.$4?.R1?.(22.R18.+8.)R14.)P,(7.$51.(4<.R15.)#10.)P,(18.$4?.R21.(22.R1:.+18.)R15.)P,(7.$51.(4<.R16.)#10.)P,(18.$4?.R23.(22.R1<.+28.)R16.)P,(7.$51.(4<.R17.)#10.)P,(18.$4?.R25.(22.R1>.+38.)R17.)P,(7.$51.(4<.R18.)#10.)P,(18.$4?.R27.(22.R20.+48.)R18.)P,(7.$51.(4<.R19.)#10.)P,(18.$4?.R29.(22.R22.+58.)R19.)P,(7.$51.(4<.R1:.)#10.)P,(18.$4?.R2;.(22.R24.+68.)R1:.)P,(7.$51.(4<.R1;.)#10.)P,(18.$4?.R2=.(22.R26.+78.)R1;.)P,(7.$51.(4<.R1<.)#48.)P,(7.$12.(33.R28.+8.)=)P,(46.=R29.)P,(2=.(22.R2:.+<0.)(52.+2.+40.))P,(18.$4?.R32.(30.(10.&40.R53.)+30.)(19.$1:.(53.R41.)(19.$1:.(53.R42.)(19.$1:.(53.R43.)(19.$1:.(53.R4<.)(19.$1:.(53.R4=.)(19.$1:.(53.R54.)(1>.$1:.))))))))P,(2;.VL,R1;.(10.&40.R54.)(13.$4?.VL,VHI,R30.)R2<.+<0.)P,(2<.(2=.(22.R2=.+<0.)(2>.VL,))(2=.(2?.VL,)R2=.))P,(2<.(2=.(22.R2>.+<0.)R2<.)(2=.(10.&40.R56.)R2>.))P,(?.$4?.R36.R2=.(30.(10.&40.R57.)+30.))P,(2=.=R2>.)P,(2=.R2?.(30.(30.(10.&40.R59.)+50.)(31.VL,)))P,(2=.(32.VL,)R30.)P,(2=.(10.&40.R5;.)(13.$4?.VL,VHI,R37.))P,(7.$12.(33.(10.&40.R5<.)+10.)=)P,(2=.(2?.VL,)(32.VL,))P,(>.$4?.R3=.)P,(24.$4?.VL,R3>.)P,(35.VL,$54.+8.)P,(7.$12.(33.(10.&40.R62.)+2.)=)(36.$4?.R3?.(37.$4?.VL,VHI,R3<.R63.R62.R61.R60.R5<.R5;.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R3>.R3;.R3:.R39.R38.R42.R40.)(9.(:.R2=.(1=.&40.(30.(10.&40.R62.)+30.))R61.R60.R5?.R5>.R5=.(1=.&40.R3:.)R2<.R5:.R59.R58.R57.R56.R55.R54.R53.R2;.R2:.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R44.(1=.&40.+38650.)R43.(<.(2.&40.))R41.(=.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until x3. cbv zeta. intros HH HTQ MF PX H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT LT AL POS AB FR CW ND SX ST LO0 LO ACL HTOP SPA DHI MI SOK CA RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof DIMG as [DI1 DI2].
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (grp_join _ _ _ _ _ _ _ _ _ _ _ _ H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT LT) as J.
    clear H0 H1 H2 H3 H4 H5 H6 H7 HT.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp). zstep.
    pose proof (U_platform_zeroize_spec L) as SPZ. unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE in SPZ.
    eapply aevtM_cut_evt; [exact MK| eapply SPZ with (lo := lo) (n := 192) (A := A); first [exact J| exact ST| exact SOK| exact CA| exact MI| reflexivity| lia] |].
    cbv beta. intros ms' PO. unfold platform_zeroize_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MU' & WM' & MI' & HZ & ST' & SOK').
    apply aevtM_done. unfold ecp_group_free_post.
    deexists 17. exists h. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact MF|]. split; [exact HTQ|].
    split. { apply (@HEAP_munch usegs L HI h _ m m' mo _ lo HH MU' WM' ACL).
             intros a Ha NO. cbn in NO. rewrite HTQ.
             destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
             - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
             - left. destruct (Z_le_dec (bv_unsigned sp - 16) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
             - left. destruct (Z_le_dec (bv_unsigned sp - 16) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    change (Z.to_nat 192) with 192%nat in HZ.
    split. { apply ecp_group_at_zero; [| exact AL| exact POS]. exact HZ. }
    split; [exact HZ|].
    split; [| exact SOK'].
    eapply heap_presx_trans; [exact PX|].
    eapply heap_presx_of_munch; [exact MU'| exact WM'|].
    intros a Ha Hc Ho. cbn in Ho |- *. destruct Ho as [Ho _]. split; [exact Ho|]. split; [| exact I].
    destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
    pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L28331135516.110L52517407388.109L59308628304.11200000i01b02^S2ra2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2ra2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L7S2ra2sp1A2hc2c12c22c32c42c52c62c72L02L12L22L32L42L52L62L72K1". (* [comment removed for export] *)
  #[using="HLS DIMG"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Pmo0,$4.Pmo,$4.Ph0,(5.$4?.VL,VHI,)Ph,(5.$4?.VL,VHI,)PMT,(26.$50.)PLB,(26.$27.)PA,$12.Pg,$28.Plo,$12.Phc,(26.$1:.)Pc1,(26.$1:.)Pc2,(26.$1:.)Pc3,(26.$1:.)Pc4,(26.$1:.)Pc5,(26.$1:.)Pc6,(26.$1:.)Pc7,(26.$1:.)Pfj,(26.(2.&8.))Pxra,(2.&40.)Px1,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)ZLBf,(26.$27.)(15.R?.R11.)P,(14.$4?.VL,VHI,R14.R1.R18.R16.)P,(7.$12.(13.$4?.VL,VHI,R15.)(13.$4?.VL,VHI,R16.))P,(11.R19.R18.)P,(1?.$4?.VL,R4.(10.&40.R3<.)(19.(20.$12.$12.)(21.$12.$12.R14.(22.R14.+<0.))(1>.(20.$12.$12.)))R1<.R1;.)P,(18.$4?.R1<.R15.R12.)P,(7.$51.(4<.R13.)#8.)P,(18.$4?.R1>.(22.R17.+8.)R13.)P,(7.$51.(4<.R14.)#10.)P,(18.$4?.R20.(22.R19.+18.)R14.)P,(7.$51.(4<.R15.)#10.)P,(18.$4?.R22.(22.R1;.+28.)R15.)P,(7.$51.(4<.R16.)#10.)P,(18.$4?.R24.(22.R1=.+38.)R16.)P,(7.$51.(4<.R17.)#10.)P,(18.$4?.R26.(22.R1?.+48.)R17.)P,(7.$51.(4<.R18.)#10.)P,(18.$4?.R28.(22.R21.+58.)R18.)P,(7.$51.(4<.R19.)#10.)P,(18.$4?.R2:.(22.R23.+68.)R19.)P,(7.$51.(4<.R1:.)#10.)P,(18.$4?.R2<.(22.R25.+78.)(55.R24.))P,(7.$12.(56.R25.)=)P,(6.(2=.=(57.R26.))(46.(57.R26.)(52.+2.+40.)))P,(7.$12.(33.R28.+8.)=)P,(46.=R29.)P,(2=.(22.R2:.+<0.)(52.+2.+40.))P,(18.$4?.R32.(30.(10.&40.R53.)+30.)(19.$1:.(53.R41.)(19.$1:.(53.R42.)(19.$1:.(53.R43.)(19.$1:.(53.R4<.)(19.$1:.(53.R4=.)(19.$1:.(53.R54.)(1>.$1:.))))))))P,(2;.VL,R1<.(10.&40.R54.)(13.$4?.VL,VHI,R30.)R2<.+<0.)P,(2<.(2=.(22.R2=.+<0.)(2>.VL,))(2=.(2?.VL,)R2=.))P,(2<.(2=.(22.R2>.+<0.)R2<.)(2=.(10.&40.R56.)R2>.))P,(?.$4?.R36.R2=.(30.(10.&40.R57.)+30.))P,(2=.=R2>.)P,(2=.R2?.(30.(30.(10.&40.R59.)+50.)(31.VL,)))P,(2=.(32.VL,)R30.)P,(2=.(10.&40.R5;.)(13.$4?.VL,VHI,R37.))P,(7.$12.(33.(10.&40.R5<.)+10.)=)P,(2=.(2?.VL,)(32.VL,))P,(>.$4?.R3=.)P,(24.$4?.VL,R3>.)P,(35.VL,$54.+8.)P,(7.$12.(33.(10.&40.R62.)+2.)=)(36.$4?.R3?.(37.$4?.VL,VHI,R3<.R63.R62.R61.R60.R5<.R5;.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R44.R43.R3>.R3;.R3:.R39.R38.R42.R40.)(9.(:.R2>.(1=.&40.(30.(10.&40.R62.)+30.))R61.R60.R5?.R5>.R5=.(1=.&40.R3:.)R2=.R5:.R59.R58.R57.R56.R55.R54.R53.R2<.R2;.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R44.(1=.&40.+38588.)R43.(<.(2.&40.))R41.(=.$4?.)))")
(* [comment removed for export] *).
  Proof.
    intros until x3. cbv zeta. intros HH HTQ MF PX H0 L0 H1 L1 H2 L2 H3 L3 H4 L4 H5 L5 H6 L6 H7 L7 HT TS TB AL POS AB FR CW ND SX ST LO0 LO ACL HTOP SPA DHI MI SOK CA RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof HT as HT'. unfold grp_tail_cells in HT. rewrite TS in HT.
    zstep. zstep. if_cases K0; zify_cond K0.
    all: cycle 1.
    1: zstep; zstep; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia].
    all: eapply zero_walk; try eassumption; reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19934584823.11L27045241335.11L63813863975.12L68235442772.1200000600<00H00NS2hz1HS2hz1HS2hz1c2Hc2H0S2hz1c". (* [comment removed for export] *)
  #[using="Type"] Lemma sx32_small_eq : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_free ()) "Phz,$12.Pc,$12.P,(6.(2=.=R2.)(46.R2.(52.+2.+20.)))P,(6.(2=.=R2.)(46.R2.(52.+2.+1?.)))(58.(7.$12.(10.&40.(59.(1=.&40.R4.)))R3.)(7.$12.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    intros hz c H Hc. rewrite bv_unsigned_sx32, unsigned_lit, Z.mod_small by lia. unfold sxz.
    destruct (Z.ltb_spec hz (2^31)); lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac to_tail sp EQF HH LIV CH PXA ST MI SOK MF HTc :=
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia;
    rewrite <- EQF in HH;
    eapply tail_walk; first [exact HH | exact HTc | exact MF | exact PXA | exact ST | exact MI | exact SOK | eassumption | reflexivity | lia
                             | match goal with |- ?g => idtac "TAILSIDE" g; let t := type of HH in idtac "HH=" t end ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "02;0@L10311321710.208L10311432145.135L10311432145.153L10311432145.171L10311432145.189L10311432145.226L10313562458.117L10375178511.207L1040486801.109 L1040637688.104 L11741095640.116L11805421443.118L12369465871.153L13125901610.117L13127832481.135L13127832481.153L13127832481.171L13127832481.189L13127832481.226L13127871518.208L1425973081.189 L14790846208.117L14790846347.135L14790846347.153L14790846347.171L14790846347.189L14790846347.207L14790846347.226L14790846347.244L14793070132.208L14793173387.135L14793173387.153L14793173387.171L14793173387.189L14793173387.226L19039299958.109L19354909044.117L21405280640.208L21702506767.171L22718396937.208L25382082548.117L25618547375.120L25618547375.121L26924648792.117L28584620424.120L28584620424.121L28704457138.104L28771428281.117L28814043710.110L2926861362.226 L30302804018.171L30997800071.135L30997800071.153L30997800071.171L30997800071.189L30997800071.226L30997830456.208L30999800332.117L31253789366.153L31378126578.112L31378308326.117L31392867444.117L34754648246.189L37414286068.117L43061838089.115L43290005942.135L43442376564.116L43654564952.117L44622288685.120L44622288685.121L453342713.218  L453424633.123  L455442171.254  L46795128758.171L49154214159.135L49628390206.117L49630326197.135L49630326197.153L49630326197.171L49630326197.189L49630326197.226L49630351882.208L49698585326.120L49698585326.121L50719543317.135L50719543317.153L50719543317.171L50719543317.189L50719584170.208L50721283742.117L52101695852.124L52101802921.128L54058763663.244L54391891673.122L54976524414.120L54976524414.121L55328356925.117L56145573170.189L57030511056.218L57030691280.123L57032606418.254L57459684159.117L57461620148.135L57461620148.153L57461620148.171L57461620148.189L57461620148.226L57461637643.208L58107000921.171L58228553743.189L59229011437.117L59231227097.208L59231269734.135L59231269734.153L59231269734.171L59231269734.189L59231269734.226L59244667299.123L59308628179.112L59499841752.117L613087794.135  L62554811791.226L62893530908.110L62893530908.207L64275732278.122L67367291830.226L7401899957.112 L7404240257.111 L7510805464.117 L805885129.135  L805885129.153  L805885129.171  L805885129.189  L805885129.226  L805923702.208  L808409666.117  L8807059875.123 L920885645.208  L9324228402.153 00000B00T00f01801J01\01n02:02F02R02^03L03X03d04004<04H04T04`04l05L06?07207e08X09K0:>0;10;d0<W0=J0>=0?00?c0@V0A;0AG0AS0A_0Ak0B70BR0C90CE0DB0EK0El0F80FH0FT0F`0GZ0HT0IN0JH0KH0LH0MB0MN0MZ0Mf0N20N>0NJ0Nk0O70OC0OO0PH0QM0QY0Qe0R:0RF0RR0R^0Rj0S60SB0SN0SZ0Sf0TE0U00U\0VE0Vk0WN0Wn0X]0YT0ZE0ZQ0[D0\A0]J0]V0]b0]n0^:0^F0^^0_60_N0_f0`>0`V0`n0aN0aZ0ao0bD0bY0bn0cC0cX0cm0d90dL0dX0dd0e00e<0eH0f50fA0fM0fY0fe0g\0hS0iJ0jA0k80ko0lf0m20m>0mJS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo2AL3POS3SLO3SPA3SPB2TB2SX2K0S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A1g3POS2EZ3SPB2TB2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACP3SPB2TB4ACLx1g2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A2lo3POS3SLO3ACL3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2HB5Ha_st5Hl_stS2ra2sp2s01A2TB2HB5Ha_st5Hl_st2s12s22s3S2ra2sp1A2TBS1L3HLS2ra2sp1A2lo2AL3POS3SLO3SPA3SPB2TB2SX2K02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01A2lo2AL3POS3SLO3SPA3SPB2TB2SX2K02HB5Ha_st5Hl_st2s12s22s3S1L3HLS2ra2sp1A2lo3POS3SLO3SPB2TBS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB1L3HLS2lo2AL3POS3SLO3SPA3SPB2SX2K01g2H12H23H2'S2ra2sp1A2TB1L3HLS2lo2AL3POS3SLO3SPA3SPB2SX2K01g2H12H23H2'S2ra2sp1A2TB1L3HLS2lo2AL3POS3SLO3SPA3SPB2SX2K01g2H12H23H2'S2ra2sp1A2TB1L3HLS2lo2AL3POS3SLO3SPA3SPB2SX2K01g2H12H23H2'S2ra2sp1A2TB1L3HLS1g2lo2AL3POS3SLO3SPA3SPB2SX2K02K12H12H23H2'2K2S2ra2sp1A2TB1L3HLS1g2lo2AL3POS3SLO3SPA3SPB2SX2K02K12H12H23H2'2K2S2ra2sp1A2TB1L3HLS2lo2AL3POS3SLO3SPA3SPB2SX2K01g2H12H23H2'S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS3SLO3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS3SLO3DHI3SPB2TB4ACLx2HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01A2lo3POS3SLO3DHI3SPB2TB4ACLx2HB5Ha_st5Hl_st2s12s22s3S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A1g2TB2H13H2'S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A3SPB2TB2HB5Ha_st5Hl_stS2ra2sp2s01A3SPB2TB2HB5Ha_st5Hl_st2s12s22s3S2ra2sp1A1g3POS2EX3SPB2TB2H13H2'2EY2EZ2EN2EPS2ra2sp1A1g3POS2EY3SPB2TB2H13H2'2EZ2EN2EPS2ra2sp1A1g3POS2EZ3SPB2TB2H13H2'2EN2EPS2ra2sp1A1g3POS2EN3SPB2TB2H13H2'2EPS2ra2sp1A1g3POS2EP3SPB2TB2H13H2'S2ra2sp1A1g3POS2EB3SPB2TB2H13H2'2EX2EY2EZ2EN2EPS2ra2sp1A2TB1a1C1L3HLS2lo3POS2ND3SLO3DHI3SPB2SX4ACLx2K0S1L3HLS2ra2sp1A2lo3POS3SLO3SPB2TB4ACLx1a1b1k1C2B4S2ra2sp1A2TBS1L2HI3HLS2ra2sp1h1A2lo3POS3SLO4HTOP3SPB2TB2K01a2NOS1L3HLS2ra2sp1A2lo2AL3POS3SLO3SPA3SPB2TB2SX2K02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01A2lo2AL3POS3SLO3SPA3SPB2TB2SX2K02HB5Ha_st5Hl_st2s12s22s3S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS1L2HI2ra2sp1h1A4HTOP2TBS2ra2sp1A1g3POS2EY3SPB2TB2H13H2'S2ra2sp1A2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS1L2ra2sp1A2lo3SLO2TBS2ra2sp1A2TBS2ra2sp1A3POS2TB2K0S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS3SLO3SPB2TB4ACLx1a1n2HnS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S1L3HLS2ra2sp1A1g2lo3POS3SLO3SPA3ACP3SPB2TB4ACLx2H13H2'S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND"] Lemma U_ecp_group_free_spec : forall MT, ecp_group_free_stmt usegs L HI MT U_ECP_GROUP_FREE U_MEMSET_FUNC.
  Proof.
    intros MT. unfold ecp_group_free_stmt, U_ECP_GROUP_FREE. intros until lo.
    intros HH G DIS CW ND ST SLO ACL HTOP SPA DHI TP MI SOK CA RA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold ECP_GROUP_SIZE in CW, ND.
    ddestruct G as (HD & AL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & Bid & Bpb & Bnb & Bh & Bmp & Btp & Btq & Btd & BT & TS & FRB & KEPT & MODP).
    unfold grp_head_cells in HD. unfold grp_tail_cells in HT.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    assert (HBRf : Forall (fun b => block_range L (fst b) (snd b)) (grp_free_LB g LB))
      by (eapply block_range_forall_sub; [exact HBR| intros b Hb; eapply lb_free_mpds_sub; exact Hb]).
    pose proof (client_wrange_where2 L _ _ _ A 192 lo CW ltac:(lia) HBRf DHI ACL ltac:(lia)) as SX.
    assert (SUBF : forall b, In b (grp_free_LB g LB) -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    (* [comment removed for export] *)
    assert (GIN : forall d, In d (grp_free_mpds g) -> In d (grp_mpds g)).
    { intros d Hd. unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h g =? 1); [destruct Hd|]. destruct (g_h g =? 2); cbn in Hd |- *; tauto. }
    assert (DISF : mpds_apart (grp_free_mpds g)) by (eapply mpds_apart_sub; [exact DIS| exact GIN]).
    assert (ALLM : forall d, In d (grp_mpds g) -> mpdr_at usegs m LB d).
    { intros d Hd. unfold grp_mpds, pt_mpds in Hd. cbn in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    pose proof (free_facts_intro usegs L HI h LB (grp_free_LB g LB) m mo (bv_unsigned sp) _ A 192 (grp_free_mpds g) HH NDL
                  ltac:(intros d Hd; apply ALLM, GIN, Hd) CW SUBF
                  ltac:(intros d Hd O; unfold grp_free_LB; apply lb_free_mpds_notin; assumption) DHI ltac:(lia) ltac:(lia) DI1 DI2) as FF1.
    assert (ACLx : alloc_ceiling <= lo) by exact ACL.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep. zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; lia|].
    (* [comment removed for export] *)
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (LIV : Forall (mpdr_at usegs m1 LB) [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g]).
    { eapply (lives_munch usegs L m m1); [| exact MU| exact WM| exact (unlock _ MI00)| exact MI| exact HBR| | intros a n Ha Hn; cbn; lia].
      - repeat apply Forall_cons; try apply Forall_nil; assumption.
      - repeat apply Forall_cons; try apply Forall_nil; rewrite ?EP, ?EA, ?EB, ?EX, ?EY, ?EZ, ?EN; cbn; lia. }
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (PXA : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    pose proof (eq_refl (heap_top usegs L HI h)) as HTc. pose proof (mo_frame_refl mo) as MF.
    clear MP MA MB MX MY MZ MN ALLM HH MU WM. rename HH1 into HH.
    match goal with F : rw_cells usegs m1 (bv_unsigned sp + -48) ?cs |- _ => match type of HT with rw_cells _ _ _ ?tcs =>
      assert (CH : Forall (fun ac => rw_cells usegs m1 (fst ac) (snd ac)) [(A, [C4 (Z_to_bv 64 (g_id g)); C4 (g_idpad g)]); (A + 120, tcs); (bv_unsigned sp - 48, cs)])
        by (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact HD| exact HT| replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact F]);
      clear HD F end end.
    (* [comment removed for export] *)
    zstep. clear HT. zstep. zstep.
    if_cases K1; zify_cond K1.
    all: cycle 1.
    { (* [comment removed for export] *)
      assert (H1 : (g_h g =? 1) = false).
      { apply Z.eqb_neq. intros E. apply K1. apply (proj2 (sx32_small_eq (g_h g) 1 Bh ltac:(lia))). exact E. }
      destruct (Z.eq_dec (g_h g) 2) as [H2|H2].
      - (* [comment removed for export] *)
        pose proof H2 as H2'. apply Z.eqb_eq in H2'.
        unfold grp_free_mpds, grp_kept_mpds in FRB, KEPT. rewrite H1, H2' in FRB, KEPT. cbn [app pt_mpds] in FRB, KEPT.
        assert (INF : forall d, In d [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] -> In d (grp_free_mpds g)).
        { intros d Hd. unfold grp_free_mpds. rewrite H1, H2'. exact Hd. }
        assert (EQF : grp_free_LB g LB = lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] LB).
        { unfold grp_free_LB, grp_free_mpds. rewrite H1, H2'. reflexivity. }
        pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SPF.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_A g)) (X0 := (A + 24)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_B g)) (X0 := (A + 40)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_X (g_G g))) (X0 := (A + 56)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Y (g_G g); pt_Z (g_G g)] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Y (g_G g))) (X0 := (A + 72)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Z (g_G g)] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Z (g_G g))) (X0 := (A + 88)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF ([] : list mpd) .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        (* [comment removed for export] *)
        fa_get CH 6%nat HT.
        zstep. clear HT. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; apply K2; apply (proj2 (sx32_small_eq (g_h g) 2 Bh ltac:(lia))); exact H2].
        (* [comment removed for export] *)
        fa_get CH 0%nat CZ. fa_get CH 1%nat CY. fa_get CH 2%nat CX. fa_get CH 3%nat CB_. fa_get CH 4%nat CA_. fa_get CH 5%nat CHD. fa_get CH 6%nat CTL. fa_get CH 7%nat CFR.
        pose proof (proj1 (Forall_inv LIV)) as CN. rewrite EN in CN. pose proof (proj1 (Forall_inv (Forall_inv_tail LIV))) as CP. rewrite EP in CP.
        change (lb_free_mpd (pt_Z (g_G g)) (lb_free_mpd (pt_Y (g_G g)) (lb_free_mpd (pt_X (g_G g)) (lb_free_mpd (g_B g) (lb_free_mpd (g_A g) LB)))))
          with (lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g)] LB) in HH.
        to_tail sp EQF HH LIV CH PXA ST MI SOK MF HTc.
      - (* [comment removed for export] *)
        pose proof H2 as H2'. apply Z.eqb_neq in H2'.
        unfold grp_free_mpds, grp_kept_mpds in FRB, KEPT. rewrite H1, H2' in FRB, KEPT. cbn [app pt_mpds] in FRB, KEPT.
        assert (INF : forall d, In d [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] -> In d (grp_free_mpds g)).
        { intros d Hd. unfold grp_free_mpds. rewrite H1, H2'. exact Hd. }
        assert (EQF : grp_free_LB g LB = lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] LB).
        { unfold grp_free_LB, grp_free_mpds. rewrite H1, H2'. reflexivity. }
        pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SPF.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_A g)) (X0 := (A + 24)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_B g)) (X0 := (A + 40)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_X (g_G g))) (X0 := (A + 56)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Y (g_G g))) (X0 := (A + 72)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [pt_Z (g_G g); g_N g; g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (pt_Z (g_G g))) (X0 := (A + 88)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [g_N g; g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        (* [comment removed for export] *)
        fa_get CH 6%nat HT.
        zstep. clear HT. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; apply H2; apply (proj1 (sx32_small_eq (g_h g) 2 Bh ltac:(lia))); exact K2|].
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_N g)) (X0 := (A + 104)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF [g_P g] .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        zstep. zstep. eapply (free_step usegs L HI _ _ SPF HLS DIMG) with (d0 := (g_P g)) (X0 := (A + 8)) (A := A) (sz := 192) (SP := bv_unsigned sp) (h0 := h) (m0 := m) (lo := lo)
          (FR := grp_free_mpds g) (LB := LB) (LBf := grp_free_LB g LB);
          [ fs_side (bv_unsigned sp + -48) ACLx HBR HAP NDL CW ND FF1 DISF SUBF INF FRB KEPT HH HTc LIV CH PXA ST TP MI SOK CA EQF ([] : list mpd) .. | ];
          fs_post (bv_unsigned sp + -48) HI HH LIV CH PXA ST MI SOK MF HTc MK.
        (* [comment removed for export] *)
        fa_get CH 0%nat CP. fa_get CH 1%nat CN. fa_get CH 2%nat CZ. fa_get CH 3%nat CY. fa_get CH 4%nat CX. fa_get CH 5%nat CB_. fa_get CH 6%nat CA_.
        fa_get CH 7%nat CHD. fa_get CH 8%nat CTL. fa_get CH 9%nat CFR.
        change (lb_free_mpd (g_P g) (lb_free_mpd (g_N g) (lb_free_mpd (pt_Z (g_G g)) (lb_free_mpd (pt_Y (g_G g)) (lb_free_mpd (pt_X (g_G g)) (lb_free_mpd (g_B g) (lb_free_mpd (g_A g) LB)))))))
          with (lb_free_mpds [g_A g; g_B g; pt_X (g_G g); pt_Y (g_G g); pt_Z (g_G g); g_N g; g_P g] LB) in HH.
        to_tail sp EQF HH LIV CH PXA ST MI SOK MF HTc. }
    (* [comment removed for export] *)
    assert (H1 : g_h g = 1) by (apply (proj1 (sx32_small_eq (g_h g) 1 Bh ltac:(lia))); exact K1).
    assert (EQF : grp_free_LB g LB = LB).
    { unfold grp_free_LB, grp_free_mpds. rewrite (proj2 (Z.eqb_eq _ _) H1). reflexivity. }
    fa_get CH 0%nat CHD. fa_get CH 1%nat CTL. fa_get CH 2%nat CFR.
    fa_get LIV 0%nat LA. fa_get LIV 1%nat LB_. fa_get LIV 2%nat LX. fa_get LIV 3%nat LY. fa_get LIV 4%nat LZ. fa_get LIV 5%nat LN. fa_get LIV 6%nat LP.
    apply proj1 in LA. apply proj1 in LB_. apply proj1 in LX. apply proj1 in LY. apply proj1 in LZ. apply proj1 in LN. apply proj1 in LP.
    rewrite EA in LA. rewrite EB in LB_. rewrite EX in LX. rewrite EY in LY. rewrite EZ in LZ. rewrite EN in LN. rewrite EP in LP.
    replace (A + 56 + 16) with (A + 72) in LY by lia. replace (A + 56 + 32) with (A + 88) in LZ by lia.
    to_tail sp EQF HH LIV CH PXA ST MI SOK MF HTc.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GF.
