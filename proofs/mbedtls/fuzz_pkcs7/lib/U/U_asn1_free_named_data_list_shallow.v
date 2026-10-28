(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_asn1_free_named_data_list_shallow () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove_all"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Logic.True"; "Stdlib.Lists.List.NoDup"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "asn1_free_named_data_list_shallow_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "U_FREE"; "asn1_free_named_data_list_shallow_stmt"; "U_ASN1_FREE_NAMED_DATA_LIST_SHALLOW"].


Definition U_ASN1_FREE_NAMED_DATA_LIST_SHALLOW : Z := 0x1efe0.
Definition U_FREE : Z := 0x3fa98.

Definition asn1_free_named_data_list_shallow_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (nodes : list Z) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_free_named_data_list_shallow ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1;.O1:.O19.)Lh',(5.O1;.O1:.O19.)(6.(7.$0.R13.(8.(9.(:.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(;.O18.)O7.(<.(2.&40.))R3.(=.O1;.))R2.))(6.(>.O1;.R3.)(6.(?.O1;.R3.O3.(10.&40.O17.))(6.(11.O1.R2.)(6.(7.$12.(13.O1;.O1:.O19.R1.)(13.O1;.O1:.O19.O6.))(6.(14.O1;.O1:.O19.R1.(15.O4.O5.)R3.R2.)(16.O1;.O1:.(15.O4.O5.)(10.&40.O17.)O2.R3.)))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition asn1_free_named_data_list_shallow_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_free_named_data_list_shallow ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(17.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(18.$19.)Pa,$12.Pnodes,(18.$12.)Plo,$12.P,(14.O4.O3.O2.R5.R4.R7.R6.)P,(1:.O4.L,(18.$1;.)$1<.R8.R5.R4.R3.)P,(1=.$12.R4.)P,(?.O4.R:.R4.(10.&40.R2:.))P,(1>.R5.(1?.(1?.(10.&40.R2;.)+10.)(20.O3.)))P,(1>.(21.O3.)R6.)P,(1>.(10.&40.R2=.)(13.O4.O3.O2.R;.))P,(7.$12.(22.(10.&40.R2>.)+10.)=)P,(1>.(23.O3.)(21.O3.))P,(7.(2.&40.)R2>.(24.&40.(25.O3.)))P,(>.O4.R11.)P,(7.(2.&40.)R2:.(24.&40.R>.))(26.O4.R12.(27.O4.O3.O2.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.R11.R10.R>.R=.R13.R12.)(9.(:.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(24.&40.O1.)R14.(<.(2.&40.))R13.(=.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (lo : Z).
  Hypothesis SLO : lo <= bv_unsigned sp - 16 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.

  Notation POST := (asn1_free_named_data_list_shallow_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).

  (* [comment removed for export] *)
  #[using="HFREE SLO HLS ACL ACP HTOP TP SPB"] Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_free_named_data_list_shallow ()) "Prest,(18.$12.)Pa,$12.Phc,(5.$28.VL,VHI,)PLBc,(18.$19.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.P,(29.(7.(18.$12.)R16.(2:.$12.)))P,(1=.$12.R17.)P,(1:.$28.L,(18.$1;.)$1<.R4.R15.R17.R18.)P,(14.$28.VL,VHI,R17.R16.R5.R4.)P,(7.$12.(13.$28.VL,VHI,R18.)(13.$28.VL,VHI,Vh,))P,(16.$28.VL,R18.(10.&40.Vsp,)Vm,R7.)P,(11.Vmo,R7.)P,(2;.$28.R9.(2<.(10.&40.Vsp,)-10.)(2=.$1;.(2>.Vs0,)(2=.$1;.(2>.Vra,)(2:.$1;.))))P,(?.$28.R:.Vlo,(2<.(10.&40.Vsp,)-10.))P,(>.$28.R;.)(26.$28.R;.(27.$28.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,R1=.R20.Vlo,Vm,Vmo,)(9.(:.R1<.(24.&40.(2<.(10.&40.Vsp,)-10.))Vgp,Vtp,R1;.R1:.R19.R18.Vs1,(24.&40.R1?.)R17.R16.R15.R14.R13.R12.R11.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(24.&40.+1>??0.)Vfc,(<.(2.&40.))R<.(=.$28.)))")
(* [comment removed for export] *).
  Proof.
    induction rest as [|a' rest IH]; intros a hc LBc x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc
      HNE HND HC HH HT HP MF FR ST MI; [congruence|].
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nxt & post & H1 & H2 & HNODE & _ & HNX & HC').
    unfold NAME_NEXT in HNX. unfold NAME_SIZE in H2, HIN.
    pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite H2 in NB.
    assert (A7 : Z.land a 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    zstep. rewrite ?A7. zstep. first [ if_false | idtac ].
    zstep. zstep.
    replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
    eapply aevtM_cut; [ eapply (heap_free usegs L HI) with (A := a) (n := 64) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by plia; try eassumption; try reflexivity; try plia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by plia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m1; rename mox into mo1 end.
    ddestruct PO as (h1 & HT1 & HH1).
    match goal with H : heap_pres _ _ _ _ mm m1 |- _ => rename H into HPc end.
    match goal with H : stk _ m1 _ _ |- _ => rename H into ST1 end.
    match goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
    match goal with H : mo_frame moc mo1 |- _ => rename H into MF1 end.
    clear MK ST MI. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
    (* [comment removed for export] *)
    apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HPc) in FR; [| simpl_sizes; apply client_range_stack; lia].
    assert (HCR : name_chain usegs (fun _ => True) m1 (lb_remove a LBc) nxt rest).
    { eapply chain_free_other; [exact HC'| | exact HPc| unfold NAME_SIZE; lia].
      intros y Hy Hya. subst y. apply NoDup_cons_iff in HND. exact (proj1 HND Hy). }
    assert (HP1 : heap_pres usegs L (lb_remove a LBc) (bv_unsigned sp) m m1).
    { eapply heap_pres_trans_sub; [exact HP| eapply heap_pres_sp_mono; [exact HPc| lia] | intros b Hb; eapply lb_remove_sub; exact Hb]. }
    clear HPc HP HC HC' HNX HNODE.
    pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HCR) as NXB.
    zstep. zstep. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KN by lia.
      destruct (chain_nonnull usegs _ _ _ _ _ _ _ HCR KN) as (a2 & rest2 & ER).
      eapply (IH nxt h1 (lb_remove a LBc)); try eassumption; try lia.
      + rewrite ER; congruence.
      + inversion HND; assumption.
      + eapply mo_frame_trans; eassumption.
    - rewrite ?unsigned_lit in KN by lia.
      pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- KN; exact HCR)) as ER. subst rest.
      zstep. zstep. zstep. zstep.
      release_frame FR ST1 (bv_unsigned sp).
      rewrite HT in HT1.
      finish. eapply mo_frame_trans; eassumption. exact HT1. exact HH1.
  Qed.
End Walk.

Lemma U_asn1_free_named_data_list_shallow_spec : ltac2:(CDefT.buildp (gd_tbl_P_asn1_free_named_data_list_shallow ()) "PL,$2?.PHI,(30.$28.R1.)P,(7.$12.(31.R2.)$32.)P,(1>.=(20.R3.))(33.$28.R4.R3.$34.)")
(* [comment removed for export] *).
Proof.
  intros L HI HFREE HLS. unfold asn1_free_named_data_list_shallow_stmt, U_ASN1_FREE_NAMED_DATA_LIST_SHALLOW.
  intros until lo. intros HH HC HND ST SLO ACL HTOP SPA DHI TP MI ->.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. pose proof (proj1 ST) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HC) as AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  zstep. if_cases K0; zify_cond K0.
  { (* [comment removed for export] *)
    rewrite ?unsigned_lit in K0 by lia.
    pose proof (chain_null_inv usegs _ _ _ _ _ _ ltac:(rewrite <- K0; exact HC)) as ER. subst nodes.
    zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
    all: try apply mo_frame_refl; try reflexivity; try eassumption.
    all: eapply heap_pres_of_munch; [eassumption| eassumption| exact HBR| exact DHI|]; intros x; cbn [outside]; lia. }
  rewrite ?unsigned_lit in K0 by lia.
  destruct (chain_nonnull usegs _ _ _ _ _ _ _ HC K0) as (ahd & rest & ER).
  eapply loop_walk with (rest := nodes) (LBc := LB) (hc := h); try eassumption; try lia.
  - rewrite ER; congruence.
  - eapply chain_munch; [exact HC| exact MU| exact WM|].
    intros x Hx. pose proof (chain_nodes_in usegs _ _ _ _ _ _ _ HC x Hx) as HIN.
    rewrite Forall_forall in HBR. destruct (HBR _ HIN) as (_ & _ & _ & HCE & _). cbn [fst snd] in HCE.
    cbn [disjoint_from]. unfold NAME_SIZE in *. lia.
  - eapply heap_pres_of_munch; [exact MU| exact WM| exact HBR| exact DHI|].
    intros x. cbn [outside]. lia.
  - apply mo_frame_refl.
Qed.
