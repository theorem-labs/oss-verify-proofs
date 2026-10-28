(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_core_bitlen U_mpi_bitlen U_ecp_group_free U_ecp_defs U_ecp_statics U_ecp_group_load.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_group_load_c2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.ecp_group_load_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section GL.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Let sw_tail := sw_tail L HI HLS DIMG.
  (* [comment removed for export] *)
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
    end.



  (* [comment removed for export] *)
  Lemma case5 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_c2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+5.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)(29.$5.R2?.(2:.$5.VL,VHI,$2;.$2<.$2=.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R2>.R2<.R2;.R2:.+5.R29.R32.R30.)(2>.(2?.R1?.(19.&40.(1=.(10.&40.R52.)+20.))R51.R50.R4?.R4>.R4=.(19.&40.R2;.)(19.&40.+5.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(19.&40.+3;<=<.)R33.(30.(0.&40.))R31.(31.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PX HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (U_curve_statics m 5 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH. pose proof (lock MI) as MI00.
    clear HCALLOC HFREE.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx (bv_unsigned sp + -32) _, Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOK MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK MI; rename SOK' into SOK; rename Hi into MI
      end end.
    splitat HD 2%nat HP. splitat HP 3%nat HA. splitat HA 3%nat HB. splitat HB 3%nat HX. splitat HX 3%nat HY. splitat HY 3%nat HZ. splitat HZ 3%nat HN. splitat HN 3%nat HT.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    (* [comment removed for export] *)
    apply mpi_cells_of_sn in HP; [| lia]. change (1114113 mod 2 ^ 16) with 1 in HP. change (1114113 / 2 ^ 16) with 17 in HP.
    apply mpi_cells_of_sn in HA; [| lia]. change (1 mod 2 ^ 16) with 1 in HA. change (1 / 2 ^ 16) with 0 in HA.
    apply mpi_cells_of_sn in HB; [| lia]. change (1114113 mod 2 ^ 16) with 1 in HB. change (1114113 / 2 ^ 16) with 17 in HB.
    apply mpi_cells_of_sn in HX; [| lia]. change (1114113 mod 2 ^ 16) with 1 in HX. change (1114113 / 2 ^ 16) with 17 in HX.
    apply mpi_cells_of_sn in HY; [| lia]. change (1114113 mod 2 ^ 16) with 1 in HY. change (1114113 / 2 ^ 16) with 17 in HY.
    apply mpi_cells_of_sn in HZ; [| lia]. change (65537 mod 2 ^ 16) with 1 in HZ. change (65537 / 2 ^ 16) with 1 in HZ.
    apply mpi_cells_of_sn in HN; [| lia]. change (1114113 mod 2 ^ 16) with 1 in HN. change (1114113 / 2 ^ 16) with 17 in HN.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 5)) (cP 5) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 104) (ca_N (U_CA 5)) (cN 5) pN) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HN| lia| lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 6 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HH2 : HEAP usegs L HI h (grp_free_LB g LB) m2 mo).
    { apply (@HEAP_munch usegs L HI h _ m m2 mo _ lo HH MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    eapply (sw_tail) with (id := 5); first [exact HH2| exact HTQ| exact MF| exact PX2| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| eassumption| reflexivity| lia
      | match goal with |- ?g => idtac "CASELEFT" g end].
  all: fail.
  Qed.

  (* [comment removed for export] *)
  Lemma case6 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_c2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+6.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)(29.$5.R2?.(2:.$5.VL,VHI,$2;.$2<.$2=.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R2>.R2<.R2;.R2:.+6.R29.R32.R30.)(2>.(2?.R1?.(19.&40.(1=.(10.&40.R52.)+20.))R51.R50.R4?.R4>.R4=.(19.&40.R2;.)(19.&40.+6.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(19.&40.+3<178.)R33.(30.(0.&40.))R31.(31.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PX HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (U_curve_statics m 6 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH. pose proof (lock MI) as MI00.
    clear HCALLOC HFREE.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx (bv_unsigned sp + -32) _, Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOK MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK MI; rename SOK' into SOK; rename Hi into MI
      end end.
    splitat HD 2%nat HP. splitat HP 3%nat HA. splitat HA 3%nat HB. splitat HB 3%nat HX. splitat HX 3%nat HY. splitat HY 3%nat HZ. splitat HZ 3%nat HN. splitat HN 3%nat HT.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    (* [comment removed for export] *)
    apply mpi_cells_of_sn in HP; [| lia]. change (524289 mod 2 ^ 16) with 1 in HP. change (524289 / 2 ^ 16) with 8 in HP.
    apply mpi_cells_of_sn in HA; [| lia]. change (524289 mod 2 ^ 16) with 1 in HA. change (524289 / 2 ^ 16) with 8 in HA.
    apply mpi_cells_of_sn in HB; [| lia]. change (524289 mod 2 ^ 16) with 1 in HB. change (524289 / 2 ^ 16) with 8 in HB.
    apply mpi_cells_of_sn in HX; [| lia]. change (524289 mod 2 ^ 16) with 1 in HX. change (524289 / 2 ^ 16) with 8 in HX.
    apply mpi_cells_of_sn in HY; [| lia]. change (524289 mod 2 ^ 16) with 1 in HY. change (524289 / 2 ^ 16) with 8 in HY.
    apply mpi_cells_of_sn in HZ; [| lia]. change (65537 mod 2 ^ 16) with 1 in HZ. change (65537 / 2 ^ 16) with 1 in HZ.
    apply mpi_cells_of_sn in HN; [| lia]. change (524289 mod 2 ^ 16) with 1 in HN. change (524289 / 2 ^ 16) with 8 in HN.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 6)) (cP 6) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 104) (ca_N (U_CA 6)) (cN 6) pN) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HN| lia| lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 6 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HH2 : HEAP usegs L HI h (grp_free_LB g LB) m2 mo).
    { apply (@HEAP_munch usegs L HI h _ m m2 mo _ lo HH MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    eapply (sw_tail) with (id := 6); first [exact HH2| exact HTQ| exact MF| exact PX2| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| eassumption| reflexivity| lia
      | match goal with |- ?g => idtac "CASELEFT" g end].
  all: fail.
  Qed.

  (* [comment removed for export] *)
  Lemma case7 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_c2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+7.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)(29.$5.R2?.(2:.$5.VL,VHI,$2;.$2<.$2=.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R2>.R2<.R2;.R2:.+7.R29.R32.R30.)(2>.(2?.R1?.(19.&40.(1=.(10.&40.R52.)+20.))R51.R50.R4?.R4>.R4=.(19.&40.R2;.)(19.&40.+7.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(19.&40.+3<238.)R33.(30.(0.&40.))R31.(31.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PX HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (U_curve_statics m 7 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH. pose proof (lock MI) as MI00.
    clear HCALLOC HFREE.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx (bv_unsigned sp + -32) _, Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOK MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK MI; rename SOK' into SOK; rename Hi into MI
      end end.
    splitat HD 2%nat HP. splitat HP 3%nat HA. splitat HA 3%nat HB. splitat HB 3%nat HX. splitat HX 3%nat HY. splitat HY 3%nat HZ. splitat HZ 3%nat HN. splitat HN 3%nat HT.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    (* [comment removed for export] *)
    apply mpi_cells_of_sn in HP; [| lia]. change (786433 mod 2 ^ 16) with 1 in HP. change (786433 / 2 ^ 16) with 12 in HP.
    apply mpi_cells_of_sn in HA; [| lia]. change (786433 mod 2 ^ 16) with 1 in HA. change (786433 / 2 ^ 16) with 12 in HA.
    apply mpi_cells_of_sn in HB; [| lia]. change (786433 mod 2 ^ 16) with 1 in HB. change (786433 / 2 ^ 16) with 12 in HB.
    apply mpi_cells_of_sn in HX; [| lia]. change (786433 mod 2 ^ 16) with 1 in HX. change (786433 / 2 ^ 16) with 12 in HX.
    apply mpi_cells_of_sn in HY; [| lia]. change (786433 mod 2 ^ 16) with 1 in HY. change (786433 / 2 ^ 16) with 12 in HY.
    apply mpi_cells_of_sn in HZ; [| lia]. change (65537 mod 2 ^ 16) with 1 in HZ. change (65537 / 2 ^ 16) with 1 in HZ.
    apply mpi_cells_of_sn in HN; [| lia]. change (786433 mod 2 ^ 16) with 1 in HN. change (786433 / 2 ^ 16) with 12 in HN.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 7)) (cP 7) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 104) (ca_N (U_CA 7)) (cN 7) pN) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HN| lia| lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 6 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HH2 : HEAP usegs L HI h (grp_free_LB g LB) m2 mo).
    { apply (@HEAP_munch usegs L HI h _ m m2 mo _ lo HH MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    eapply (sw_tail) with (id := 7); first [exact HH2| exact HTQ| exact MF| exact PX2| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| eassumption| reflexivity| lia
      | match goal with |- ?g => idtac "CASELEFT" g end].
  all: fail.
  Qed.

  (* [comment removed for export] *)
  Lemma case8 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_c2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+8.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)(29.$5.R2?.(2:.$5.VL,VHI,$2;.$2<.$2=.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R2>.R2<.R2;.R2:.+8.R29.R32.R30.)(2>.(2?.R1?.(19.&40.(1=.(10.&40.R52.)+20.))R51.R50.R4?.R4>.R4=.(19.&40.R2;.)(19.&40.+8.)R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(19.&40.+3<014.)R33.(30.(0.&40.))R31.(31.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PX HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (U_curve_statics m 8 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH. pose proof (lock MI) as MI00.
    clear HCALLOC HFREE.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx (bv_unsigned sp + -32) _, Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOK MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK MI; rename SOK' into SOK; rename Hi into MI
      end end.
    splitat HD 2%nat HP. splitat HP 3%nat HA. splitat HA 3%nat HB. splitat HB 3%nat HX. splitat HX 3%nat HY. splitat HY 3%nat HZ. splitat HZ 3%nat HN. splitat HN 3%nat HT.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    (* [comment removed for export] *)
    apply mpi_cells_of_sn in HP; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HP. change (1048577 / 2 ^ 16) with 16 in HP.
    apply mpi_cells_of_sn in HA; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HA. change (1048577 / 2 ^ 16) with 16 in HA.
    apply mpi_cells_of_sn in HB; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HB. change (1048577 / 2 ^ 16) with 16 in HB.
    apply mpi_cells_of_sn in HX; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HX. change (1048577 / 2 ^ 16) with 16 in HX.
    apply mpi_cells_of_sn in HY; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HY. change (1048577 / 2 ^ 16) with 16 in HY.
    apply mpi_cells_of_sn in HZ; [| lia]. change (65537 mod 2 ^ 16) with 1 in HZ. change (65537 / 2 ^ 16) with 1 in HZ.
    apply mpi_cells_of_sn in HN; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HN. change (1048577 / 2 ^ 16) with 16 in HN.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 8)) (cP 8) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 3 zstep.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 104) (ca_N (U_CA 8)) (cN 8) pN) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HN| lia| lia| eapply static_limbs_any_mem; [exact STN| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    do 6 zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (HH2 : HEAP usegs L HI h (grp_free_LB g LB) m2 mo).
    { apply (@HEAP_munch usegs L HI h _ m m2 mo _ lo HH MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
      destruct Hc as [C|[C|([b k] & Hb & C)]]; [lia| lia|]. cbn in C.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    eapply (sw_tail) with (id := 8); first [exact HH2| exact HTQ| exact MF| exact PX2| exact HD| exact HP| exact HA| exact HB| exact HX| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST| exact CW| exact SOK| eassumption| reflexivity| lia
      | match goal with |- ?g => idtac "CASELEFT" g end].
  all: fail.
  Qed.
End GL.
