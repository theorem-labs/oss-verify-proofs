(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_mpi_init U_mpi_addsub U_mpi_lset U_mpi_grow U_mpi_core_bitlen U_mpi_bitlen U_ecp_group_init U_ecp_group_free U_ecp_defs U_ecp_statics U_ecp_group_load.
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
Ltac2 gd_tbl_P_ecp_group_load_mx () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.curve_addrs"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.grp_mxi"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.EcpLoad.mx_field"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.ecp_group_load_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_P"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.heap1"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_N"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.cN"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.mx_nbits"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.ca_modp"].


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grp_mxi_heap : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx ()) "Pid,$0.Pca,$1.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.Pd,$3.P,(4.$3.R1.(5.(6.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)))P,(7.$8.(9.R2.)$:.)(;.(7.$3.R3.R6.)(;.(7.$3.R3.R5.)(7.$3.R3.R4.)))")
(* [comment removed for export] *).
Proof.
  intros until d. intros Hd O. unfold grp_mpds, grp_mxi, pt_mpds in Hd. cbn -[smpd mpd_init] in Hd. unfold smpd, mpd_init in Hd.
  destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O; try discriminate O; auto.
Qed.

Lemma grp_mxi_apart : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx ()) "Pid,$0.Pca,$1.PA,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.P,(<.(=.R:.+18.)R3.)P,(<.(=.R;.+38.)R3.)P,(<.(=.R<.+58.)R3.)P,P,(7.$8.(9.R6.)$:.)P,(7.$8.(9.R6.)$:.)(>.(7.$0.(?.R8.)(?.R7.)))P,P,(7.$8.(9.R7.)$:.)P,(7.$8.(9.R6.)$:.)(>.(7.$0.(?.R9.)(?.R7.)))P,P,(7.$8.(9.R7.)$:.)P,(7.$8.(9.R7.)$:.)(>.(7.$0.(?.R9.)(?.R8.)))(10.(5.(6.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)))")
(* [comment removed for export] *).
Proof.
  intros until dZ. intros [EA _] [EX _] [EZ _] NAX NAZ NXZ d1 d2 H1 H2 NE O1 O2.
  destruct (grp_mxi_heap _ _ _ _ _ _ _ _ _ _ _ _ _ H1 O1) as [->|[->| ->]];
  destruct (grp_mxi_heap _ _ _ _ _ _ _ _ _ _ _ _ _ H2 O2) as [->|[->| ->]]; try (exfalso; apply NE; reflexivity); auto using not_eq_sym.
Qed.

(* [comment removed for export] *)
Ltac presx_all segs L PX CW SUB :=
  lazymatch type of PX with heap_presx _ _ _ _ _ ?m _ =>
    repeat match goal with H : rw_cells segs m ?a ?cs |- _ =>
      let H' := fresh in
      pose proof (heap_presx_rw_cells segs L _ _ _ _ _ _ _ PX H
                    ltac:(first [ eapply (client_range_of_wrange L); [exact CW| exact SUB| lia| cbn; lia| cbn; lia]
                                | cbn; intros xx Hxx; left; lia ])
                    ltac:(cbn; lia)) as H';
      clear H; rename H' into H
    end
  end.

Section MX.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L10311464405.107L11554870423.107L12292903720.134L20904604443.107L22218202372.132L22220297151.107L25483224503.136L32435371120.132L35204911163.107L35204930595.126L35866125198.107L37708033033.107L37738322224.134L3818668784.107 L41560557296.133L59695185539.132L61300838498.10700000?00h01O01X01a01j02802A02f03K03o04804A04S05005905JS1L2ra2sp1A3DHIS1L3HLS2ra2sp1A2lo2LO3ACL3SPA3ACP3SPB3POSS1L3HLS2ra2sp1A2lo2LO2SX3SPA3SPB2AL3POSS2ra2sp1AS2ra2sp1AS2ra2sp1AS2ra2sp1A1a2HaS2ra2sp1AS1L3HLS2ra2sp1A2lo2LO3ACL3ACP3SPB3POSS1L3HLS2ra2sp1A2lo2LO3ACL3ACP3SPB3POSS1L2HI2ra2sp2h01h1A3HTQ4HTOP3SPB3POSS2ra2sp1AS2ra2sp1AS1L2ra2sp1A2lo3ACLS1L3HLS2ra2sp1A2lo2LO3SPB3POSS2ra2sp1AS1L2ra2sp1A2lo2LO". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND"] Lemma mx_fail : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(11.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(12.(2.&8.))Pm,P,(2.&40.)(12.(2.&8.))Pmo0,$13.Pmo,$13.Ph0,(14.$15.VL,VHI,)Ph,(14.$15.VL,VHI,)PLB,(16.$17.)PLBc,(16.$17.)PA,$0.Pg,$18.Pid,$0.Plo,$0.Pr,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpB,(2.&40.)PpY,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)Pxra,(2.&40.)Pxs1,(2.&40.)PdA,$3.PdX,$3.PdZ,$3.Pfj,(16.(2.&8.))ZLBf,(16.$17.)(19.R10.R13.)Zgc,$18.(6.R10.(1:.R10.)R12.R=.R<.R;.R:.R9.R8.R5.R4.R3.)P,(;.(7.$0.R11.+9.)(7.$0.R11.+=.))P,(7.$0.R10.$1;.)P,(1<.$15.VL,VHI,R18.R16.R1<.R1:.)P,(7.$0.(1=.$15.VL,VHI,R19.)(1=.$15.VL,VHI,R1:.))P,(1>.R1=.R1<.)P,(1?.$15.VL,R7.(20.&40.R3?.)(21.(22.$0.$0.)(23.$0.$0.R18.(=.R18.+<0.))(24.(22.$0.$0.)))R20.R1?.)P,(25.$15.$26.R20.R1:.R19.R7.)P,(10.(5.R8.))P,Pb,$17.(27.(4.$17.R1.R1=.)(;.(4.$17.R1.(28.R:.))(4.$17.R1.R;.)))P,Pb,$17.P,(4.$17.R1.(28.R;.))(>.(4.$17.R2.R=.))P,(29.$15.R24.(2:.(20.&40.R44.)+20.)(21.$2;.(2<.#8.R=.)(21.$2;.(2=.R3=.)(21.$2;.(2=.R3>.)(21.$2;.(2=.R45.)(24.$2;.))))))P,(2>.$15.R25.R1;.(2:.(20.&40.R45.)+20.))P,(2?.=R1<.)P,(2?.R1=.(2:.(2:.(20.&40.R47.)+70.)(30.VL,)))P,(;.(2?.(=.R21.+<0.)R1>.)(2?.(20.&40.R48.)R21.))P,(31.VL,R11.(20.&40.R49.)(1=.$15.VL,VHI,R26.)R22.+<0.)P,(;.(2?.(=.R23.+<0.)(32.VL,))(2?.(33.VL,)R23.))P,(2?.(34.VL,)R21.)P,(2?.(20.&40.R4<.)(1=.$15.VL,VHI,R29.))P,(2?.(33.VL,)(34.VL,))P,(35.$15.R2>.)P,(36.$15.VL,R2?.)P,(7.$0.(37.(20.&40.R51.)+2.)=)P,(7.(2.&40.)R4?.(38.&40.(39.VL,)))P,(3:.VL,$3;.+8.)P,(7.$0.(37.(20.&40.R53.)+10.)=)(3<.$15.R32.(3=.$15.VL,VHI,$26.$1:.$3>.R55.R54.R53.R52.R4>.R4=.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R37.R36.R31.R2?.R2=.R2<.R2;.R2:.R35.R33.)(3?.(40.R22.(38.&40.(2:.(20.&40.R54.)+20.))R53.R52.R51.R50.R4?.(38.&40.R2=.)R21.(38.&40.R29.)R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.)R37.(38.&40.+3<450.)R36.(41.(2.&40.))R34.(42.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros IDC Er HH HTQ MF PX G DIS IFF FRESH FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA TP CA SPA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. pose proof DIMG as [DI1 DI2].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as NDc.
    dpose G as (_ & AL & POS & _).
    set (gc := grp_mxi id (U_CA id) A idpad pP pB pY pN hpad dA dX dZ) in *.
    (* [comment removed for export] *)
    assert (HEAPIN : forall d, In d (grp_mpds gc) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) LBc).
    { intros d Hd O. dpose G as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX' & MY' & MZ') & MN & _).
      assert (M : mpdr_at usegs m LBc d).
      { unfold grp_mpds, pt_mpds in Hd. cbn -[gc] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
      destruct (mpdr_blk_facts _ L _ _ _ M O HBR) as (I1 & _). exact I1. }
    assert (KEEPf : forall b, In b (grp_free_LB g LB) -> In b (grp_free_LB gc LBc)).
    { intros [B k] Hb. unfold grp_free_LB. apply lb_free_mpds_keep; [apply (proj2 (IFF _)); right; exact Hb|].
      intros d Hd O E. subst B.
      assert (GINd : In d (grp_mpds gc)).
      { unfold grp_free_mpds in Hd. unfold grp_mpds. destruct (g_h gc =? 1); [destruct Hd|]. destruct (g_h gc =? 2); cbn -[gc] in Hd |- *; clear -Hd; tauto. }
      pose proof (HEAPIN d GINd O) as INc.
      assert (INb : In (md_p d, k) LBc) by (apply (proj2 (IFF _)); right; exact Hb).
      assert (k = 4 * md_n d).
      { clear -NDc INc INb. induction LBc as [|[C j] LBc IH]; [destruct INc|]. cbn in NDc. apply List.NoDup_cons_iff in NDc as [Hni ND'].
        destruct INc as [E1|INc]; destruct INb as [E2|INb].
        - congruence.
        - injection E1; intros; subst. exfalso. apply Hni. apply in_map_iff. exists (md_p d, k). auto.
        - injection E2; intros; subst. exfalso. apply Hni. apply in_map_iff. exists (md_p d, 4 * md_n d). auto.
        - apply IH; assumption. }
      subst k. apply (FRESH (md_p d, 4 * md_n d)); [| exact Hb].
      unfold grp_blocks. apply in_flat_map. exists d. split; [exact GINd|]. unfold mpd_blk. rewrite O. left. reflexivity. }
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (U_ecp_group_free_spec L HI HFREE HLS SW DIMG HND U_MT) as SG. unfold ecp_group_free_stmt, U_ECP_GROUP_FREE, ECP_GROUP_SIZE in SG.
    eapply aevtM_cut.
    { eapply SG with (lo := lo) (h := h) (LB := LBc) (g := gc); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH | exact G | exact DIS | exact ND | exact TP | exact MI | exact SOK | exact CA | reflexivity
              | rewrite HTQ; eapply (client_wrange_weak L); [exact CW| exact KEEPf| lia| lia| lia]
              | match goal with |- stk _ _ _ _ => eassumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold ecp_group_free_post, ECP_GROUP_SIZE in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & mo2 & h2 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & GZ & GZC & PXg & SOK2).
    replace (ret_pc (Z_to_bv 64 0x3c45c)) with (Z_to_bv 64 0x3c45c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PXg FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    clear FR ST MI SOK MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    pose proof (munch_refl ([] : list ivl) m2) as MU2. pose proof (wmono_refl usegs m2) as WM2.
    zstep. zstep. zstep. zstep. zstep. release_frame FR2 ST2 (bv_unsigned sp). zstep.
    replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp). zstep.
    apply aevtM_done. unfold ecp_group_load_post.
    deexists 16. dexists h2, r, (grp_zero A), [], (grp_free_LB gc LBc).
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact (mo_frame_trans _ _ _ MF MF2)|]. split; [rewrite HT2; exact HTQ|].
    split; [exact HH2|].
    split. { intros b. split; [| intros [[]|Hb]; apply KEEPf; exact Hb]. intros Hb. right.
             assert (INc : In b LBc) by (unfold grp_free_LB in Hb; eapply lb_free_mpds_sub; exact Hb).
             destruct (proj1 (IFF b) INc) as [Hg|Hf]; [| exact Hf]. exfalso.
             unfold grp_blocks in Hg. apply in_flat_map in Hg. ddestruct Hg as (d & Hd & Hbd).
             unfold mpd_blk in Hbd. destruct (md_own d) eqn:O; try (destruct Hbd; fail). destruct Hbd as [<-|[]].
             unfold grp_free_LB in Hb. eapply (lb_free_mpds_notin _ LBc d); [exact NDc| | exact O| exact Hb].
             unfold grp_free_mpds, grp_mpds in *. subst gc. cbn -[smpd mpd_init] in Hd |- *. unfold smpd, mpd_init in Hd.
             destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O; try discriminate O; tauto. }
    split; [intros b Hb; destruct Hb|].
    split; [exact GZ|].
    split. { intros d1 d2 H1 H2 NE O1 O2. exfalso. unfold grp_mpds, grp_zero, pt_mpds, pt_zero in H1. cbn -[mpd_zero] in H1. unfold mpd_zero in H1.
             destruct H1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn in O1; discriminate O1. }
    split; [reflexivity|].
    split. { right. right. right. auto. }
    split; [| exact SOK2].
    eapply heap_presx_trans; [exact PX|].
    eapply (heap_presx_weak usegs L); [exact PXg| exact KEEPf| lia| intros x Hx; exact Hx].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02D0@L10311463514.170L10311464784.121L10313283409.154L10375254250.195L10375289852.157L1040637868.170 L10679787817.157L10679955253.195L11554870040.170L11554870802.121L11583727142.154L11606534197.113L11799439267.157L11803469603.158L11803469604.196L11803470500.197L11805421443.157L11805421443.195L11805647263.157L11805647263.195L11805648021.157L11805648021.195L11805648787.157L11805648787.195L11805649674.157L11805650053.157L11805650053.195L11805650561.157L11805650561.195L1224772295.170 L13595959528.154L19039446859.170L19445133702.197L22217840259.196L22217840260.158L22217841411.197L22217841412.159L22218202371.191L22219853880.157L22219853880.195L22219855154.157L22219855154.195L22219855412.157L22219855412.195L22219856557.157L22219857186.157L22219857186.195L22219857702.157L22219857702.195L22220086820.157L22220086820.195L22220296506.121L22220297264.170L22222394884.157L22224490883.195L22575452390.154L22718431801.195L22718433583.157L24934068612.154L28379259168.157L28379259430.157L28379260716.157L28379260978.157L28379262393.157L28769543853.195L28769775035.157L29010565666.149L29428309718.154L30303296953.170L30432942177.154L31255887241.158L31255887246.196L32435371127.191L34063995495.114L34754565024.157L34754565675.157L34754566453.157L34754567231.157L34754567993.157L34754943031.121L34756743694.197L35159187972.170L35204911806.121L35204913076.170L35204930595.142L35204930595.189L35866124555.121L37071243961.157L37071245106.195L37311119420.154L37622523289.161L37622523289.193L37703839285.195L37708112016.157L3818668149.121 L3818669439.170 L3820486772.154 L39484547269.191L3965196495.157 L3969832554.195 L40151132471.196L40829474284.170L40905867946.154L41073274087.154L41558460109.192L42558922028.195L42558952240.157L43289959072.157L43289960235.195L43401321387.158L43401321388.196L44279992808.157L44284370765.195L45122568817.154L46795029053.170L46795177525.157L47197190670.121L4741077216.154 L48448356305.121L48965534006.157L48965536288.195L49500901851.170L51518040679.114L54867022662.157L54873200736.195L55330566207.157L55330667305.195L56039687843.159L56039687843.197L56145933747.121L56147672970.197L59231106797.170L59308585607.124L59308585607.173L59695185540.191L6056531214.191 L62763497140.191L64314372888.121L64525773856.157L64525774630.195L64631256620.157L6701995239.121 L67367210041.157L67367210815.195L7315428753.154 L8358581904.151 L9326323722.196 L9326323725.158 00000J00\00n01I01\02002<02P03D04004104^05Z05f06:06N06Z06n07:07N07Z07n08:08N08Z08f09j09k0:?0;50;I0<50<M0<a0<m0=A0=M0=a0=m0>A0>M0>a0>m0?A0?M0?Y0?m0@90@M0@Y0@m0A90AM0AY0Am0BA0BU0Ba0C10C=0CI0CU0Ca0Cm0DA0DM0DN0Da0E50E60EB0EV0Ej0F60FB0FN0FZ0Ff0G20G>0GR0Gj0HR0IB0Ij0JZ0KA0KM0Ka0L:0LK0Ld0M80MD0MY0N60NK0NL0NX0Nl0O@0OT0Of0P=0Pe0Q90QE0QQ0Qe0R80RS0R_0S30SJ0S^0Sj0T:0T;0TR0T^0U20UQ0U]0U^0U_0Uk0V?0VR0Vm0W90WM0Wi0Xn0Z;0ZO0ZP0ZQ0Z]0Zi0[=0[I0[]0[i0\=0\>0\J0\^0\jS1L2ra2sp1A3DHI2TB2dZ1r2PZS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS2ra2sp1A2PA3APA2TB2dZ1r2PZS2ra2sp1A2PA3APA2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TB2dZ1r2PZS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TBFS2ra2sp1A2id2PA2PX3IDC3NAX3APA3APX3POS3SPB2TBS1L3HLS2ra2sp1A2lo2PA2PX3NAX3APA3APX2AL3POS2LO2SX3SPA3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo2PA2PX3NAX3APA3APX2AL3POS2LO2SX3SPA3SPB2TB2dZ1r2PZFS2ra2sp1A2TB2dZ1r2PZS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TB2h22dZ1r3HT22PZS2ra2sp1A3SPA3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZ3APZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS1L2ra2sp1A2lo2LO2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBFS2ra2sp1A2lo3LO02TBS2ra2sp1A2TB2dZ1r2PZFS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A3POS2TB2dZ1r2PZS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dZ1r2PZS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dZ1r2PZS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS1L2HI2ra2sp2h01A4HTOP2TBS2ra2sp1A2TB1x2HxS2ra2sp1A2TB2dZ1r2PZ1x2HxS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS1L2ra2sp1A2lo3ACL2TBS1L2ra2sp1A2lo3ACL2TB2dZ1r2PZS1L2ra2sp1A2lo3ACL2TBFS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2lo2SX2TBS2ra2sp1A3POS2RA3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3SPB2TB2dZ1r2PZS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2PX3APX2TBS2ra2sp1A2PX3APX2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS2ra2sp1A3POS2TBFS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2AL3POS3SPB2TB2dZ1r2PZS2ra2sp1A2TBFFS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB2xx3HxxS2ra2sp1A2TB2dZ1r2PZ2xx3HxxS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS1L2ra2sp1A2lo2LO2TB2dZ1r2PZS1L3HLS2ra2sp1A2lo2PA2PX3NAX3APA3APX3POS2LO2ND3ACL3DHI3SPB2TB1a2Ha2HdS1L3HLS2ra2sp1A2lo2PA2PX3NAX3APA3APX3POS2LO2ND3ACL3DHI3SPB2TB2dZ1r2PZ1a2Ha2HdS2ra2sp1A2TB2dZ1r2PZFFS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TBS1L2ra2sp1A2lo2LO2TBS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZFS2ra2sp1A2TBS2ra2sp1A2TB2dZ1r2PZS2ra2sp1A2TB". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND"] Lemma mx_third : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(11.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(12.(2.&8.))Pm,P,(2.&40.)(12.(2.&8.))Pmo0,$13.Pmo,$13.Ph0,(14.$15.VL,VHI,)Ph,(14.$15.VL,VHI,)PLB,(16.$17.)PLBc,(16.$17.)PA,$0.Pg,$18.Pid,$0.Plo,$0.Pidpad,(2.&40.)PpP,(2.&40.)PpA,(2.&40.)PpB,(2.&40.)PpX,(2.&40.)PpY,(2.&40.)PpZ,(2.&40.)PpN,(2.&40.)Phpad,(2.&40.)Pxra,(2.&40.)Pxs1,(2.&40.)PwA,(2.&40.)PwX,(2.&40.)PPA,$0.PPX,$0.Pfj,(16.(2.&8.))ZLBf,(16.$17.)(19.R13.R16.)Zca,$1.(1:.R13.)P,(;.(7.$0.R14.+9.)(7.$0.R14.+=.))P,(1<.$15.VL,VHI,R1:.R18.R1>.R1<.)P,(7.$0.(1=.$15.VL,VHI,R1;.)(1=.$15.VL,VHI,R1<.))P,(1>.R1?.R1>.)P,(1?.$15.VL,R6.(20.&40.R42.)(21.(22.$0.$0.)(23.$0.$0.R1:.(=.R1:.+<0.))(24.(22.$0.$0.)))R22.R21.)P,Pb,$17.(27.(4.$17.R1.R1=.)(;.(4.$17.R1.(21.(22.$0.$0.)(23.$0.$0.R;.+4.)(21.(22.$0.$0.)(23.$0.$0.R:.+4.)(24.(22.$0.$0.)))))(4.$17.R1.R8.)))P,(>.(4.(22.$0.$0.)(23.$0.$0.R;.+4.)R8.))P,(>.(4.(22.$0.$0.)(23.$0.$0.R;.+4.)R9.))P,(>.(7.$0.R=.R<.))P,(;.(2?.(=.R1?.+<0.)R>.)(2?.(=.R>.+4.)R1?.))P,(;.(2?.(=.R20.+<0.)R>.)(2?.(=.R>.+4.)R20.))P,(29.$15.R28.R21.(21.$2;.(43.(38.&40.R1?.))(21.$2;.(43.R1=.)(24.$2;.))))P,(7.$0.(37.R22.+8.)=)P,(44.=R23.)P,(29.$15.R2;.(=.R24.+8.)(45.(46.R?.)(38.&40.+1.)(47.(48.(2.&40.)(49.R22.)))R1?.))P,(4:.$15.R2<.R26.(4;.(=.R25.+18.)R14.R16.R1?.))P,(29.$15.R2=.(=.R26.+28.)(45.=(38.&40.+1.)=R1?.))P,(4:.$15.R2>.R28.(4;.(=.R27.+38.)R15.R17.R1?.))P,(29.$15.R2?.(=.R28.+48.)(45.=(38.&40.+1.)=R1?.))P,(29.$15.R30.(=.R29.+58.)(45.=(38.&40.+1.)=R1?.))P,(29.$15.R31.(=.R2:.+68.)(45.(4<.R15.)(38.&40.+1.)(47.(48.(2.&40.)(4=.R28.)))R1?.))P,(29.$15.R32.(=.R2;.+78.)(21.$2;.(2=.(38.&40.(4>.(49.R29.)(47.(48.(2.&40.)(49.R29.))))))(21.$2;.(2=.(38.&40.(4?.R29.)))(21.$2;.(43.(38.&40.+2.))(21.$2;.(43.R1?.)(21.$2;.(2=.(38.&40.(50.R16.)))(21.$2;.(2=.(38.&40.=))(21.$2;.(2=.(38.&40.=))(21.$2;.(2=.(38.&40.=))(21.$2;.(2=.(38.&40.=))(21.$2;.(2=.(38.&40.=))(24.$2;.))))))))))))P,(29.$15.R33.(2:.(20.&40.R54.)+20.)(21.$2;.(2<.#8.R19.)(21.$2;.(2=.R4=.)(21.$2;.(2=.R4>.)(21.$2;.(2=.R55.)(24.$2;.))))))P,(2>.$15.R34.R2:.(2:.(20.&40.R55.)+20.))P,(2?.=R2;.)P,(2?.R2<.(2:.(2:.(20.&40.R57.)+70.)(30.VL,)))P,(;.(2?.(=.R30.+<0.)R2=.)(2?.(20.&40.R58.)R30.))P,(31.VL,R1=.(20.&40.R59.)(1=.$15.VL,VHI,R35.)R31.+<0.)P,(;.(2?.(=.R32.+<0.)(32.VL,))(2?.(33.VL,)R32.))P,(2?.(34.VL,)R30.)P,(2?.(20.&40.R5<.)(1=.$15.VL,VHI,R38.))P,(2?.(33.VL,)(34.VL,))P,(35.$15.R3=.)P,(36.$15.VL,R3>.)P,(7.$0.(37.(20.&40.R61.)+2.)=)P,(7.(2.&40.)R5?.(38.&40.(39.VL,)))P,(3:.VL,$3;.+8.)P,(7.$0.(37.(20.&40.R63.)+10.)=)(3<.$15.R41.(3=.$15.VL,VHI,$26.$1:.$3>.R65.R64.R63.R62.R5>.R5=.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R46.R45.R40.R3>.R3<.R3;.R3:.R39.R44.R42.)(3?.(40.R2?.(38.&40.(2:.(20.&40.R64.)+20.))R63.R62.R61.R60.R5?.(38.&40.R3<.)R2>.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.)R46.(38.&40.+3<440.)R45.(41.(2.&40.))R43.(42.$15.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros IDC HH HTQ MF PXA IFF FPA FPX NAX APA APX HD AL POS HP MA HB MX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA TP CA SPA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. pose proof DIMG as [DI1 DI2].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (U_curve_statics m id MI ltac:(lia)) as CS. pose proof (lock MI) as MI00.
    assert (SUBc : forall b, In b (grp_free_LB g LB) -> In b LBc) by (intros b Hb; apply (proj2 (IFF b)); right; exact Hb).
    assert (MPB : 0 <= ca_modp (U_CA id) < 2^64 /\ In (ca_modp (U_CA id), (ca_P (U_CA id), cP id)) U_MT).
    { destruct IDC as [-> | ->]; cbn -[c9_P c13_P]; (split; [lia| auto 20]). }
    destruct MPB as [MB MODP].
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := h) (LB := LBc) (dX := mpd_init (A + 88) pZ) (z := 1); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH | exact TP | exact MI | exact SOK | exact CA | reflexivity
              | apply mpd_of_mpdr; [apply mpdr_at_init; [exact HZ| lia| lia]| left; reflexivity]
              | cbn; discriminate
              | split; [rewrite HTQ; eapply (client_wrange_weak L); [exact CW| exact SUBc| lia| cbn; lia| cbn; lia]| split; [intros a Ha Hd; exfalso; cbn in Ha; lia| cbn; discriminate]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | lia ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & mo2 & h2 & LB2 & dZ & r & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MZ2 & OUT & PXl & SOK2 & LR).
    replace (ret_pc (Z_to_bv 64 0x3c44c)) with (Z_to_bv 64 0x3c44c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mpd_ivs md_addr md_own mpd_init] in PXl.
    ddestruct OUT as (EZa & OZ & OUT1 & OUT2 & OUT3). cbn [md_addr mpd_init mpd_blk md_own] in EZa, OUT1, OUT2, OUT3.
    assert (SUB2 : forall b, In b LBc -> In b LB2) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    assert (SUBf2 : forall b, In b (grp_free_LB g LB) -> In b LB2) by (intros b Hb; apply SUB2, SUBc, Hb).
    presx_all usegs L PXl CW SUBc.
    assert (MA2 : mpd_at usegs m2 LB2 (heap1 (A + 24) PA wA pA)).
    { apply mpd_of_mpdr; [| left; reflexivity]. eapply mpdr_at_LB_mono; [| exact SUB2].
      eapply (mpdr_at_presx usegs L m m2); [exact (mpdr_of_mpd _ _ _ _ MA)| exact PXl| exact MI| exact MI2| | cbn; lia|].
      - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUBc| lia| lia| lia].
      - cbn. intros _. split; [apply (proj2 (IFF _)); left; cbn; auto| lia]. }
    assert (MX2 : mpd_at usegs m2 LB2 (heap1 (A + 56) PX wX pX)).
    { apply mpd_of_mpdr; [| left; reflexivity]. eapply mpdr_at_LB_mono; [| exact SUB2].
      eapply (mpdr_at_presx usegs L m m2); [exact (mpdr_of_mpd _ _ _ _ MX)| exact PXl| exact MI| exact MI2| | cbn; lia|].
      - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUBc| lia| lia| lia].
      - cbn. intros _. split; [apply (proj2 (IFF _)); left; cbn; auto| lia]. }
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PXA|]. eapply (heap_presx_weak usegs L); [exact PXl| exact SUBc| lia|]. intros x Hx. cbn in Hx |- *. split; [lia| exact I]. }
    clear MA MX PXA ST MI SOK MK HH MU WM. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      ddestruct LR as ([(Er & Zn & Zo & Zl & Zs & Zpd) | [Er EdZ]] & EaZ & FRZ); [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; cbv in K0; discriminate].
      cbn [md_n mpd_init md_addr] in Zn, EaZ. change (if 1 <? 0 then -1 else 1) with 1 in Zs.
      destruct (lset_heap1 dZ (A + 88) Zn Zo Zl Zs EaZ) as [wZ EdZ].
      pose proof MZ2 as MZb. rewrite EdZ in MZ2. set (PZ := md_p dZ) in *. set (pdZ := md_pad dZ) in *.
      assert (INZ : In (PZ, 4) LB2) by (dpose MZ2 as [[_ (_ & _ & _ & _ & (_ & IN & _))] _]; exact IN).
      assert (FPZ : ~ In (PZ, 4) LBc).
      { intros C. destruct (FRZ (PZ, 4)) as [[]|NI]; [| exact (NI C)]. rewrite EdZ. cbn. left. reflexivity. }
      assert (APZ : A + 192 <= PZ \/ PZ + 4 <= A).
      { destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2].
        eapply (client_apart_block L (grp_free_LB g LB) LB2); [exact CW| exact SUBf2| exact HBR2| exact HAP2| exact INZ| intros C; apply FPZ, SUBc, C| lia| lia| exact DHI| lia| exact DI1| exact DI2]. }
      zstep. zstep.
      (* [comment removed for export] *)
      pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SF. unfold mpi_free_stmt, U_MPI_FREE in SF.
      eapply aevtM_cut.
      { eapply SF with (lo := lo) (h := h2) (LB := LB2) (X := A + 72) (own := LNull) (P := 0) (n := 0) (limbs := []); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
          first [ exact HH2 | exact TP | exact MI2 | exact SOK2 | exact CA | reflexivity
                | exact (mpdr_at_init _ _ LB2 _ _ HY ltac:(lia) ltac:(lia))
                | cbn; discriminate
                | cbn [mpi_free_LB]; rewrite HT2, HTQ; eapply (client_wrange_weak L); [exact CW| exact SUBf2| lia| lia| lia]
                | intros a Ha Hd; exfalso; lia
                | match goal with |- stk _ _ _ _ => eassumption end
                | lia
                | match goal with |- ?gg => idtac "MFREELEFT" gg end ]. }
      cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
      ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & mo3 & h3 & E & PO). injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
      ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & HY3 & PXf & SOK3).
      cbn [mpi_free_LB mpi_free_X] in HH3, PXf.
      replace (ret_pc (Z_to_bv 64 0x3c46c)) with (Z_to_bv 64 0x3c46c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      clear HY. presx_all usegs L PXf CW SUBf2.
      assert (MA3 : mpdr_at usegs m3 LB2 (heap1 (A + 24) PA wA pA)).
      { eapply (mpdr_at_presx usegs L m2 m3); [exact (mpdr_of_mpd _ _ _ _ MA2)| exact PXf| exact MI2| exact MI3| | cbn; lia|].
        - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUBf2| lia| lia| lia].
        - cbn. intros _. split; [apply SUB2; apply (proj2 (IFF _)); left; cbn; auto| lia]. }
      assert (MX3 : mpdr_at usegs m3 LB2 (heap1 (A + 56) PX wX pX)).
      { eapply (mpdr_at_presx usegs L m2 m3); [exact (mpdr_of_mpd _ _ _ _ MX2)| exact PXf| exact MI2| exact MI3| | cbn; lia|].
        - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUBf2| lia| lia| lia].
        - cbn. intros _. split; [apply SUB2; apply (proj2 (IFF _)); left; cbn; auto| lia]. }
      assert (MZ3 : mpdr_at usegs m3 LB2 (heap1 (A + 88) PZ wZ pdZ)).
      { eapply (mpdr_at_presx usegs L m2 m3); [exact (mpdr_of_mpd _ _ _ _ MZ2)| exact PXf| exact MI2| exact MI3| | cbn; lia|].
        - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUBf2| lia| lia| lia].
        - cbn. intros _. split; [exact INZ| lia]. }
      clear MA2 MX2 MZ2 ST2 MI2 SOK2 MK MU WM. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
      zstep. zstep. zstep. zstep. zstep. release_frame FR ST3 (bv_unsigned sp). zstep.
      replace (bv_unsigned sp - 32 + 32) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp). zstep.
      apply aevtM_done. unfold ecp_group_load_post.
      deexists 16. dexists h3, 0, (grp_mx id (U_CA id) A idpad pP pA pB pX pY pdZ pN hpad PA PX PZ wA wX wZ), [(PA, 4); (PX, 4); (PZ, 4)], LB2.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|].
      split; [exact (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF2 MF3))|]. split; [rewrite HT3, HT2; exact HTQ|].
      split; [exact HH3|].
      split. { intros b. split.
               - intros Hb. destruct (OUT1 b Hb) as [Hc|Hz]; [| rewrite EdZ in Hz; cbn in Hz; left; cbn; clear -Hz; tauto].
                 destruct (proj1 (IFF b) Hc) as [H2b|Hf]; [left; cbn in H2b |- *; clear -H2b; tauto| right; exact Hf].
               - intros [[<-|[<-|[<-|[]]]]|Hf]; [apply SUB2; apply (proj2 (IFF _)); left; cbn; auto ..| exact INZ| apply SUBf2; exact Hf]. }
      split. { intros b [<-|[<-|[<-|[]]]]; [exact FPA| exact FPX| intros C; apply FPZ, SUBc, C]. }
      split. { unfold grp_mx. eapply grp_mxi_at; try eassumption; try lia.
               - eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI3].
               - apply mx_field_heap1. - apply mx_field_heap1. - apply mx_field_heap1. }
      split. { assert (NZA : PA <> PZ) by (intros E; apply FPZ; rewrite <- E; apply (proj2 (IFF _)); left; cbn; auto).
               assert (NZX : PX <> PZ) by (intros E; apply FPZ; rewrite <- E; apply (proj2 (IFF _)); left; cbn; auto).
               unfold grp_mx. apply grp_mxi_apart; [apply mx_field_heap1| apply mx_field_heap1| apply mx_field_heap1| cbn; intros; assumption..]. }
      split; [reflexivity|].
      split. { right. left. split; [reflexivity|]. split; [exact IDC|]. deexists 15. split; reflexivity. }
      split; [| exact SOK3].
      eapply heap_presx_trans; [exact PX2|]. eapply (heap_presx_weak usegs L); [exact PXf| exact SUBf2| lia|]. intros x Hx. unfold ECP_GROUP_SIZE in Hx. cbn in Hx |- *.
      destruct Hx as [Hx _]. split; [lia| exact I].
    - (* [comment removed for export] *)
      ddestruct LR as ([(Er & _) | [Er EdZ]] & EaZ & FRZ); [exfalso; subst r; apply K0; reflexivity|].
      subst r. subst dZ.
      assert (BLK : grp_blocks (grp_mxi id (U_CA id) A idpad pP pB pY pN hpad (heap1 (A + 24) PA wA pA) (heap1 (A + 56) PX wX pX) (mpd_init (A + 88) pZ)) = [(PA, 4); (PX, 4)]) by reflexivity.
      eapply (mx_fail) with (dA := heap1 (A + 24) PA wA pA) (dX := heap1 (A + 56) PX wX pX) (dZ := mpd_init (A + 88) pZ)
                            (idpad := idpad) (pP := pP) (pB := pB) (pY := pY) (pN := pN) (hpad := hpad);
        first [ exact IDC| reflexivity| exact HH2| rewrite HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF MF2)| exact PX2| exact FR| exact ST2| exact CW| exact ND| exact MI2| exact SOK2| exact TP| exact CA| lia
              | eapply grp_mxi_at; first [exact IDC| exact MODP| exact MB| exact HD| exact HP| exact HB| exact HY| exact HN| exact HT| exact (mpdr_of_mpd _ _ _ _ MA2)| exact (mpdr_of_mpd _ _ _ _ MX2)| exact (mpdr_of_mpd _ _ _ _ MZ2)
                                         | apply mx_field_heap1| apply mx_field_init| lia
                                         | eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI2] ]
              | apply grp_mxi_apart; [apply mx_field_heap1| apply mx_field_heap1| apply mx_field_init| cbn; intros; first [assumption| discriminate]..]
              | rewrite BLK; intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [exact (proj1 (IFF b) Hc)| cbn in Hz; destruct Hz]| intros Hb; apply SUB2; exact (proj2 (IFF b) Hb)]
              | rewrite BLK; intros b [<-|[<-|[]]]; [exact FPA| exact FPX]
              | match goal with |- ?gg => idtac "TOFAIL" gg end].
  all: fail.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MX.
