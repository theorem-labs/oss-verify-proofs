(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02ae181dde614b28 2 13 1 1 8 3 2 1 30 1 31 1 6 0 1 23 1 24 1 29 1 32 1 33 8 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P0446255ee447cff7 1 2 8 2 0 1 27 1 8 2 16 1 28 1 2 29 1 30 1P05f463fc19d988af 0 7 0 1 6 1 9 4 12 1 20 1 21 1 22 1P073f87b9e242e920 0 5 0 1 27 1 28 1 33 1 34 1P07a9c19a6c635fb3 0 2 0 1 13 1P08f1ea715dc9e34a 0 5 0 1 21 1 22 1 27 1 28 1P09a8e35d649c6bc3 0 2 0 1 10 1P09d41790f57a8b80 1 1 8 2 16 1 28 1 3 0 1 27 1 29 8P0e993eed8cd11b31 2 13 1 1 8 3 2 1 30 1 31 1 6 0 1 23 1 24 1 29 1 32 1 33 8 1 1 8 3 1 1 29 1 32 1 4 0 2 30 2 31 2 33 16P0f03f8befbd85993 2 21 1 1 8 3 1 1 36 1 37 1 6 0 1 29 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 2 36 2 37 2 39 16P123bcdce30185438 0 2 0 1 13 1P1bd7e9692876cad2 2 21 1 1 8 3 1 1 36 1 37 1 6 0 1 29 1 30 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 2 36 2 37 2 39 16P1ccae46819e09e70 0 5 0 1 22 1 23 1 28 1 29 1P1d067021236eaa8e 2 14 1 1 8 3 1 1 31 1 32 1 6 0 1 24 1 25 1 30 1 33 1 34 8 1 1 8 3 2 1 30 1 33 1 4 0 2 31 2 32 2 34 16P20424f50596c5c26 2 14 1 1 8 3 1 1 31 1 32 1 6 0 1 24 1 25 1 30 1 33 1 34 8 1 1 8 3 2 1 30 1 33 1 4 0 2 31 2 32 2 34 16P22277e219aad1e84 0 2 0 1 9 1P242e50988fe69f49 0 2 0 1 13 1P33de30ab6c29c3de 0 5 0 1 21 1 22 1 27 1 28 1P3453e164f097efa4 0 4 0 8 3 8 27 8 28 8N00223ec0760ebe5eN047a2b386174d34aN09ca205b58520006N0ab50dcd30f0d9b6N0b1bbe34f09e510bN0fa32cb622fc1242N10d4549c5ed2d667N1625e848c13b684bN1a50385eadd778fbN1fea2d54793d342fN245f6a67137c33b9N3044dae47e658792"%lxh.
Ltac2 gd_tbl_P_mpi_free () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "zeroize_and_free_post"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "mpi_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "mpi_free_X"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "mpi_free_post"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"].


Definition U_ZEROIZE_AND_FREE : Z := 0x25a0c.
Definition U_MPI_FREE : Z := 0x1f4a8.
Definition U_FREE : Z := 0x3fa98.
Definition U_MEMSET : Z := 0x46e44.

(* [comment removed for export] *)
Notation ZEROIZE_AND_FREE_STACK := 16 (only parsing).
Notation MPI_FREE_STACK := 32 (only parsing).

(* [comment removed for export] *)
Lemma statics_ok_heap_pres segs L LB SP m m' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "P,(0.O6.O5.O2.)P,(1.O6.O5.O4.O3.O2.O1.)P,Pa,$2.P,(3.O5.R1.)(4.O5.R2.)(0.O6.O5.O1.)")
(* [comment removed for export] *).
Proof.
  intros (H0 & H1 & HP) PR SW. split; [exact H0|]. split; [exact H1|]. intros a Ha HE.
  destruct (PR a ltac:(lia) ltac:(right; left; split; [exact Ha| intros HS; exact (HE (SW _ HS))])) as [E _].
  rewrite E. exact (HP a Ha HE).
Qed.

Definition zeroize_and_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (buf len lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "Lc,$5.(6.(7.&40.)Lt0,(7.&40.)(6.(7.&40.)Lt1,(7.&40.)(6.(7.&40.)Lt2,(7.&40.)(6.(7.&40.)La0,(7.&40.)(6.(7.&40.)La1,(7.&40.)(6.(7.&40.)La2,(7.&40.)(6.(7.&40.)La3,(7.&40.)(6.(7.&40.)La4,(7.&40.)(6.(7.&40.)La5,(7.&40.)(6.(7.&40.)La6,(7.&40.)(6.(7.&40.)La7,(7.&40.)(6.(7.&40.)Lt3,(7.&40.)(6.(7.&40.)Lt4,(7.&40.)(6.(7.&40.)Lt5,(7.&40.)(6.(7.&40.)Lt6,(7.&40.)(6.P,(7.&40.)(8.(7.&8.))Lm',P,(7.&40.)(8.(7.&8.))(6.$9.Lmo',$9.(6.(:.O1<.O1;.O1:.)Lh',(:.O1<.O1;.O1:.)(;.(<.$5.R13.(=.(>.(?.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(10.O19.)O8.(11.(7.&40.))R3.(12.O1<.))R2.))(;.(13.O1<.R3.)(;.(14.O1<.R3.O3.(15.&40.O18.))(;.(16.O1.R2.)(;.(<.$2.(17.O1<.O1;.O1:.R1.)(17.O1<.O1;.O1:.O7.))(;.(18.O1<.O1;.O1:.R1.(19.O5.O6.)R3.R2.)(;.(1:.O1<.O1;.(19.O5.O6.)(15.&40.O18.)(1;.(1<.$2.$2.)(1=.$2.$2.O5.(1>.O5.O4.))(1?.(1<.$2.$2.)))O2.R3.)(0.O1<.O1;.R3.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition zeroize_and_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(20.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(8.(7.&8.))Pmo,$9.Ph,(:.O5.O4.O3.)PLB,(21.$22.)Pbuf,$2.Plen,$2.Plo,$2.Pjunk,(21.(7.&8.))P,(18.O5.O4.O3.R6.R5.R8.R7.)P,(23.(<.$2.R5.=)(;.(24.(1<.$2.$2.)(1=.$2.$2.R5.R4.)R6.)(25.O5.R9.R5.(1;.$26.(27.(28.R4.)R2.)(1?.$26.)))))P,(;.(29.=R5.)(2:.R5.(2;.+2.+40.)))P,(14.O5.R;.R5.(15.&40.R2;.))P,(29.R6.(2<.(2<.(15.&40.R2<.)+10.)(2=.O4.)))P,(29.(2>.O4.)R7.)P,(29.(15.&40.R2>.)(17.O5.O4.O3.R<.))P,(<.$2.(2?.(15.&40.R2?.)+10.)=)P,(29.(30.O4.)(2>.O4.))P,(<.(7.&40.)R2?.(31.&40.(32.O4.)))P,(13.O5.R12.)P,(0.O5.O4.R13.)P,(33.O4.O1.+8.)P,(<.(7.&40.)R2=.(31.&40.R11.))P,(<.(7.&40.)R2=.(31.&40.R11.))(34.O5.R16.(35.O5.O4.O3.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.R15.R14.R13.R12.R11.R17.R16.)(>.(?.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(31.&40.O2.)R18.(11.(7.&40.))R17.(12.O5.)))")
(* [comment removed for export] *).

Lemma outside_dec W a : outside W a \/ ~ outside W a.
Proof. induction W as [|[lo hi] W IH]; cbn; [left; exact I|]. destruct IH as [IH|IH]; [| right; tauto]. destruct (Z.lt_ge_cases a lo); [left; split; [lia| exact IH]|]. destruct (Z.lt_ge_cases a hi); [right; lia| left; split; [lia| exact IH]]. Qed.

(* [comment removed for export] *)
Lemma HEAP_munch segs L (HI : heap_iface segs L) h LB m m' mo W SP : ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "P,(18.O:.O9.O8.O7.O6.O5.O3.)P,(36.O2.O5.O4.)P,(37.O:.O5.O4.)P,(29.(2>.O9.)O1.)P,Pa,$2.P,(;.(29.=R1.)(2:.R1.(2;.+2.+40.)))P,(38.(39.O2.R2.))(3:.O9.O6.O1.(17.O:.O9.O8.O7.)R3.)(18.O:.O9.O8.O7.O6.O4.O3.)")
(* [comment removed for export] *).
Proof.
  intros HH MU WM HSP HW. eapply (heap_frame segs L HI); [exact HH| exact HSP| | exact WM].
  intros a Ha NC. apply MU. rewrite wa_unsigned by lia.
  destruct (outside_dec W a) as [O|NO]; [exact O| exfalso; exact (NC (HW a Ha NO))].
Qed.

Section ZF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  Lemma lb_remove_0 h LB m mo : HEAP usegs L HI h LB m mo -> lb_remove 0 LB = LB.
  Proof.
    intros HH. flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _. clear HH.
    induction LB as [|[A n] LB IH]; [reflexivity|]. inversion BR as [|x l B1 B2]; subst. cbn [lb_remove fst].
    flat constr:(B1) 2%nat. flclear B1. intros B0 _. cbn in B0. destruct (Z.eqb_spec A 0); [lia|]. f_equal. exact (IH B2).
  Qed.

  Lemma U_zeroize_and_free_spec : zeroize_and_free_stmt usegs L HI U_ZEROIZE_AND_FREE U_MEMSET_FUNC.
  Proof.
    unfold zeroize_and_free_stmt, U_ZEROIZE_AND_FREE. intros until junk. intros HH HB LEN ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    assert (BR : buf = 0 \/ (0 < buf /\ buf + len <= alloc_ceiling /\ (buf + len <= hl_img_lo L \/ hl_img_hi L <= buf) /\ In (buf, len) LB /\ rw_cells usegs m buf [CB (Z.to_nat len) junk])).
    { destruct HB as [HB|[HB CH]]; [left; exact HB| right]. flat constr:((proj1 (Forall_forall _ _) HBR _ HB)) 5%nat. intros B1 _ _ B4 B5. cbn in B1, B4, B5. auto 6. }
    clear HB. pose proof ACL as ACLN. pose proof alloc_ceiling_bounds as ACB. 
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      assert (buf = 0) as -> by (destruct BR as [->|(B1 & B4 & _)]; [reflexivity| rewrite Z.mod_small in K0 by (pose proof alloc_ceiling_bounds; lia); lia]).
      zstep. replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
      eapply aevtM_cut_evt; [exact MK| eapply (heap_free_null usegs L HI); reflexivity|]. cbv beta. intros ms' ->.
      finish; rewrite ?(lb_remove_0 h LB m mo HH); first [apply mo_frame_refl| reflexivity| exact HH| apply heap_presx_refl].
    - destruct BR as [->|(B1 & B4 & B5 & HIN & CH)]; [exfalso; apply K0; reflexivity|].
      zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in K1 by lia. subst len.
        zstep. replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
        eapply aevtM_cut; [eapply (heap_free usegs L HI) with (A := buf) (n := 0) (lo := lo); try eassumption; try reflexivity; try lia|].
        cbv beta. intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as -> ->.
        destruct_ands PO. flat constr:(PO) 3%nat. flclear PO. intros h' HT' HH'.
        finish; try eassumption; [eapply heap_presx_of_pres; eassumption| eapply statics_ok_heap_pres; eassumption].
      + (* [comment removed for export] *)
        rewrite ?unsigned_lit in K1 by lia.
        pose proof (statics_ok_cells usegs L _ U_MEMSET_FUNC (le8 (Z_to_bv 64 U_MEMSET)) SOK CA ltac:(vm_compute; reflexivity)) as [_ MSFB].
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (MSFC : ro_cells usegs mx U_MEMSET_FUNC [C8 (Z_to_bv 64 U_MEMSET)]) by (split; [cbn; auto| exact MSFB]) end. clear MSFB.
        unfold U_MEMSET_FUNC, U_MEMSET in MSFC. flat constr:(CA) 3%nat. intros CA1 CA2 _. unfold U_MEMSET_FUNC in CA1, CA2.
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (munch_refl [(buf, buf + len); (bv_unsigned sp - 16, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
        carve_frame 16%nat ST.
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. clear MSFC.
        eapply aevtM_cut_evt; [exact MK| eapply U_memset_spec; rewrite ?unsigned_lit by lia; [| eassumption]; eassumption |].
        cbv beta. intros ms' PO. unfold memset_post in PO.
        flat constr:(PO) 20%nat. flclear PO. intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m2 -> MU2 WM2 MI2 RW2.
        rewrite ?unsigned_lit in MU2, RW2 by lia. rewrite Z.mod_0_l in RW2 by lia.
        replace (ret_pc (Z_to_bv 64 0x25a38)) with (Z_to_bv 64 0x25a38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (rw_cells_transport usegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn; lia)) as FR2.
        assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -16)) by (eapply stk_transport; [exact ST| exact MU2| exact WM2| intros x Hx; left; cbn; lia]).
        assert (HH2 : HEAP usegs L HI h LB m2 mo).
        { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU2| exact WM2| exact ACL|].
          intros a Ha NO. right; right. exists (buf, len). split; [exact HIN|]. cbn in NO |- *. lia. }
        assert (SOK2 : statics_ok usegs L m2).
        { eapply statics_ok_munch; [exact SOK| exact MU2|]. intros a Ha _. cbn. lia. }
        clear FR ST HH SOK CH MI.
        zstep. zstep. zstep. zstep. release_frame FR2 ST2 (bv_unsigned sp).
        zstep. replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
        eapply aevtM_cut; [eapply (heap_free usegs L HI) with (A := buf) (n := len) (lo := lo); try eassumption; try reflexivity; try lia|].
        cbv beta. intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as -> ->.
        destruct_ands PO. flat constr:(PO) 3%nat. flclear PO. intros h' HT' HH'.
        finish; try eassumption.
        * (* [comment removed for export] *) eapply heap_presx_trans; [| eapply heap_presx_of_pres; eassumption].
          eapply heap_presx_of_munch; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]; intros xx Hxx; cbn in Hxx |- *; lia]| eapply wmono_trans; eassumption|].
          intros a Ha Hc Ho. cbn in Ho |- *. destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|].
          apply lb_remove_sub in Hb. flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4' _. cbn in C, B4'. lia.
        * eapply statics_ok_heap_pres; [exact SOK2| eassumption| exact SW].
  Qed.
End ZF.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mpi_free_LB (own : limb_own) (P n : Z) (LB : list blk) : list blk :=
  match own with LHeap => lb_remove P LB | _ => LB end.
Definition mpi_free_X (own : limb_own) (P n : Z) : list (Z * Z) :=
  match own with LHeap => [(P, P + 4 * n)] | _ => [] end.

Definition mpi_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (X P n : Z) (pad : word) (own : limb_own) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "Lc,$5.(6.(7.&40.)Lt0,(7.&40.)(6.(7.&40.)Lt1,(7.&40.)(6.(7.&40.)Lt2,(7.&40.)(6.(7.&40.)La0,(7.&40.)(6.(7.&40.)La1,(7.&40.)(6.(7.&40.)La2,(7.&40.)(6.(7.&40.)La3,(7.&40.)(6.(7.&40.)La4,(7.&40.)(6.(7.&40.)La5,(7.&40.)(6.(7.&40.)La6,(7.&40.)(6.(7.&40.)La7,(7.&40.)(6.(7.&40.)Lt3,(7.&40.)(6.(7.&40.)Lt4,(7.&40.)(6.(7.&40.)Lt5,(7.&40.)(6.(7.&40.)Lt6,(7.&40.)(6.P,(7.&40.)(8.(7.&8.))Lm',P,(7.&40.)(8.(7.&8.))(6.$9.Lmo',$9.(6.(:.O1?.O1>.O1=.)Lh',(:.O1?.O1>.O1=.)(;.(<.$5.R13.(=.(>.(?.O1<.O1;.O1:.O19.R12.R11.R10.O18.O17.R?.R>.R=.R<.R;.R:.R9.R8.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R7.R6.R5.R4.)O<.(10.O1<.)O;.(11.(7.&40.))R3.(12.O1?.))R2.))(;.(13.O1?.R3.)(;.(14.O1?.R3.O3.(15.&40.O1;.))(;.(16.O1.R2.)(;.(<.$2.(17.O1?.O1>.O1=.R1.)(17.O1?.O1>.O1=.O:.))(;.(18.O1?.O1>.O1=.R1.(3;.O4.O7.O6.O9.)R3.R2.)(;.(25.O1?.R3.O8.(3<.=(31.&40.+1.)=O5.))(;.(1:.O1?.O1>.(3;.O4.O7.O6.O9.)(15.&40.O1;.)(1;.(1<.$2.$2.)(1=.$2.$2.O8.(1>.O8.+10.))(3=.O4.O7.O6.))O2.R3.)(0.O1?.O1>.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(20.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(8.(7.&8.))Pmo,$9.Ph,(:.O5.O4.O3.)PLB,(21.$22.)PX,$2.Psw,(7.&40.)Pn,$2.PP,$2.Plimbs,(21.(7.&40.))Ppad,(7.&40.)Pown,$3>.Plo,$2.P,(18.O5.O4.O3.R:.R9.R<.R;.)P,(3?.O5.R=.R:.R9.R8.R7.R6.R5.R4.R3.)P,(38.(<.$3>.R4.$40.))P,(41.O4.(3;.R5.R8.R9.R<.)(15.&40.R2?.)(17.O5.O4.O3.R=.)R;.+10.)P,P,(<.$3>.R6.$42.)(23.(29.(1>.R=.+10.)R:.)(29.(1>.R:.(43.+4.R;.))R=.))P,Pa,$2.P,(;.(29.R>.R1.)(2:.R1.(1>.R>.+10.)))P,(;.(29.(44.O4.)R2.)(2:.R2.(30.O4.)))(4.O4.R3.)P,(14.O5.R12.R7.(15.&40.R32.))P,(29.R8.(2<.(2<.(15.&40.R33.)+20.)(2=.O4.)))P,(29.(2>.O4.)R9.)P,(29.(15.&40.R35.)(17.O5.O4.O3.R13.))P,(<.$2.(2?.(15.&40.R36.)+10.)=)P,(29.(30.O4.)(2>.O4.))P,(<.(7.&40.)R36.(31.&40.(32.O4.)))P,(13.O5.R19.)P,(0.O5.O4.R1:.)P,(33.O4.O1.+8.)P,(<.(7.&40.)R34.(31.&40.R18.))(34.O5.R1<.(45.O5.O4.O3.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1;.R1:.R19.R16.R17.R14.R13.R12.R1=.R1<.)(>.(?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(31.&40.O2.)R1>.(11.(7.&40.))R1=.(12.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma client_wrange_where L LB SP top A k lo : ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "P,(41.O7.O6.O5.O4.O3.O2.)P,(2:.=O2.)P,(46.(1<.$2.$2.)Lb,(1<.$2.$2.)(47.O7.(48.$2.$2.R1.)(49.$2.$2.R1.))O6.)P,(29.(30.O7.)(2>.O7.))P,(29.(2>.O7.)O1.)P,(29.(1>.O1.O2.)O5.)(23.(29.(1>.O3.O2.)O1.)(29.O5.O3.))")
(* [comment removed for export] *).
Proof.
  intros CW K BR DHI CLO LK.
  assert (LOW : forall a, client_waddr L LB SP top a -> SP <= a \/ a < alloc_ceiling).
  { intros a [C|[C|([B n] & Hb & C)]]; [left; lia| right; lia|]. right. flat constr:((proj1 (Forall_forall _ _) BR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in C, B4. lia. }
  destruct (LOW _ (CW A ltac:(lia))) as [H|H]; [right; exact H|].
  destruct (LOW _ (CW (A + k - 1) ltac:(lia))) as [H'|H']; [exfalso; lia| left; lia].
Qed.

Lemma heap_presx_weaken segs L LB SP1 SP2 X1 X2 m m' : ltac2:(CDefT.buildp (gd_tbl_P_mpi_free ()) "P,(1:.O9.O8.O7.O6.O4.O2.O1.)P,(29.O6.O5.)P,Pa,$2.P,(39.O3.R1.)(39.O4.R2.)(1:.O9.O8.O7.O5.O3.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros HP LE HX a Ha Hc Ho. apply HP; [exact Ha| | apply HX; exact Ho].
  destruct Hc as [C|C]; [left; lia| right; exact C].
Qed.

Section MF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.

  Lemma U_mpi_free_spec : mpi_free_stmt usegs L HI U_MPI_FREE U_MEMSET_FUNC.
  Proof.
    unfold mpi_free_stmt, U_MPI_FREE. intros until lo. intros HH MA NST XCW XP XD ST SLO ACL HTOP SPA DHI TP MI SOK CA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP.
    flat constr:(MA) 6%nat. flclear MA. intros CH XAL X0 LEN NR OWN. unfold mpi_cells in CH.
    pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    assert (HBR' : Forall (fun b => block_range L (fst b) (snd b)) (mpi_free_LB own P n LB)).
    { destruct own; [exact HBR| |exact HBR]. apply Forall_forall; intros b Hb; apply (proj1 (Forall_forall _ _) HBR); eapply lb_remove_sub; exact Hb. }
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR' DHI ACL ltac:(lia)) as XS.
    unfold MPI_MAX_LIMBS in NR.
    (* [comment removed for export] *)
    assert (OWF : (own = LNull /\ P = 0 /\ n = 0) \/ (own = LHeap /\ 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr usegs m P limbs /\ 0 < P /\ P + 4 * n <= alloc_ceiling)).
    { destruct own as [| |]; [left| right| exfalso; exact (NST eq_refl)].
      - flat constr:(OWN) 2%nat. flclear OWN. intros P0 N0. split; [reflexivity|]. split; [exact P0| exact N0].
      - flat constr:(OWN) 4%nat. flclear OWN. intros N1 PIN PAL PCH. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
        split; [reflexivity|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|]. split; [exact PCH|]. split; [exact P0| exact P4]. }
    clear OWN.
    assert (PRNG : 0 <= P /\ P + 4 * n <= alloc_ceiling) by (destruct OWF as [(_ & -> & ->)|(_ & _ & _ & _ & _ & P0 & P4)]; lia).
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x25a0c] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    { (* [comment removed for export] *)
      assert (PZ : P = 0) by flia. destruct OWF as [(-> & _ & ->)|(_ & _ & _ & _ & _ & P0 & _)]; [| exfalso; lia]. cbn [mpi_free_LB mpi_free_X] in *.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      lazymatch goal with Hm : munch _ m m5, Hw : wmono _ m m5, Hc : rw_cells _ m5 X _ |- _ => rename Hm into MU; rename Hw into WM; rename Hc into CH5 end.
      apply aevtM_done. unfold mpi_free_post. flexi 17%nat. exists h. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [apply mo_frame_refl|]. split; [reflexivity|].
      split. { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU| exact WM| exact ACL|].
               intros a Ha NO. cbn in NO. destruct (Z.le_gt_cases X a); destruct (Z.lt_ge_cases a (X + 16));
                 first [destruct (XCW a ltac:(lia)) as [C|C]; [left; lia| right; exact C] | left; lia]. }
      split. { exact (rw_cells_split_C4 usegs m5 X [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 pad] CH5). }
      split. { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *.
               destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|]. flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in C, B4. lia. }
      eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn.
      assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))). (flsplit; repeat split); try exact I; flia. }
    (* [comment removed for export] *)
    assert (PNZ : P <> 0) by (intros EP; flia).
    destruct OWF as [(_ & -> & _)|(-> & N1 & PIN & PAL & U32 & P0 & P4)]; [exfalso; exact (PNZ eq_refl)|]. cbn [mpi_free_LB mpi_free_X] in *.
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros _ _ _ _ P5. cbn in P5.
    clear CH ST MI. lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with Hm : munch _ m m1, Hw : wmono _ m m1, Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -16) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
      rename Hm into MU01; rename Hw into WM01; rename Hc into CH; rename Hf into FR; rename Hs into ST1; rename Hi into MI1 end.
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact MU01| exact WM01| exact ACL|].
      pose proof (client_wrange_mono L _ LB _ _ _ _ XCW ltac:(intros b Hb; eapply lb_remove_sub; exact Hb)) as XCWf.
      intros a Ha NO. cbn in NO. destruct (Z.le_gt_cases X a); destruct (Z.lt_ge_cases a (X + 16));
        first [destruct (XCWf a ltac:(lia)) as [C|C]; [left; lia| right; exact C] | left; lia]. }
    assert (SOK1 : statics_ok usegs L m1) by (eapply statics_ok_munch; [exact SOK| exact MU01|]; intros a Ha NW; cbn; flia).
    pose proof (u32arr_cells usegs _ _ _ (u32arr_transport usegs _ _ _ _ _ U32 MU01 WM01 ltac:(cbn; flia))) as PCH. clear U32.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. clear MK.
    eapply aevtM_cut.
    { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := P) (len := 4 * n) (lo := lo) (junk := u32s limbs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by lia; try eassumption; try reflexivity; try lia.
      right. split; [exact PIN|]. replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia. exact PCH. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2' mo2 h2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by lia.
    flat constr:(PO) 7%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 PX2 SOK2.
    replace (ret_pc (Z_to_bv 64 0x1f4d8)) with (Z_to_bv 64 0x1f4d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 FR ltac:(cbn; intros a Ha; left; lia) ltac:(cbn; lia)) as FR2.
    pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ PX2 CH ltac:(cbn; intros a Ha; destruct (XCW a ltac:(lia)) as [C|C]; [left; lia| right; exact C]) ltac:(cbn; pose proof (XP eq_refl); lia)) as CH2.
    clear FR CH PCH HH HH1 SOK SOK1 ST1 MI1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK2).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch goal with Hm : munch _ m2 m5, Hw : wmono _ m2 m5, Hc : rw_cells _ m5 X _ |- _ => rename Hm into MU; rename Hw into WM; rename Hc into CH5 end.
    apply aevtM_done. unfold mpi_free_post. flexi 17%nat. exists h2. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [exact MF2|]. split; [exact HT2|].
    split. { eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HH2| exact MU| exact WM| exact ACL|].
             intros a Ha NO. cbn in NO. rewrite HT2. destruct (XCW a ltac:(lia)) as [C|C]; [left; lia| right; exact C]. }
    split. { exact (rw_cells_split_C4 usegs m5 X [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) [C4 pad] CH5). }
    split. { eapply heap_presx_trans; [| eapply heap_presx_trans; [eapply heap_presx_weaken; [exact PX2| lia| intros a Ho; cbn in Ho |- *; tauto]|]].
             - (* [comment removed for export] *) eapply heap_presx_of_munch; [exact MU01| exact WM01|]. intros a Ha Hc Ho. cbn in Ho |- *.
               destruct Hc as [C|[C|([B k] & Hb & C)]]; [lia| lia|]. flat constr:((proj1 (Forall_forall _ _) HBR' _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in C, B4. lia.
             - eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn in Ho |- *. lia. }
    eapply statics_ok_munch; [exact SOK2| exact MU|]. intros a Ha NW. cbn.
    assert (O1 : ~ (X <= a < X + 16)) by (intros HX; exact (NW (XD a HX Ha))). (flsplit; repeat split); try exact I; flia.
  Qed.
End MF.
