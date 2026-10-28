(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_rsa_init U_rsa_free U_asn1_get_sequence_of_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_wrap_rsa () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "rsa_alloc_wrap_post"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.U.U_rsa_free.rsa_free_LB"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "rsa_free_wrap_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"].


Definition U_RSA_ALLOC_WRAP : Z := 0x2a17c.
Definition U_RSA_FREE_WRAP : Z := 0x2a1b4.
Notation RSA_ALLOC_WRAP_STACK := 32 (only parsing).
Notation RSA_FREE_WRAP_STACK := 64 (only parsing).

Definition rsa_alloc_wrap_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_rsa ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1:.O19.O18.)Lh',(5.O1:.O19.O18.)(1.$6.LC,$6.(7.(8.$0.R14.(9.(:.(;.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(<.O17.)O6.(=.(2.&40.))R4.(>.O1:.))R3.))(7.(?.O1:.R4.)(7.(10.O1:.R4.O3.(11.&40.O16.))(7.(12.O1.R3.)(7.(8.$6.(13.O1:.O19.O18.R2.)(13.O1:.O19.O18.O5.))(7.(8.(2.&40.)R10.(14.&40.R1.))(7.(15.O1:.O19.O4.(11.&40.O16.)O2.R4.)(16.(7.(8.$6.R1.=)(17.O1:.O19.O18.R2.O4.R4.R3.))(7.(18.O19.R1.+>8.)(7.PB,$6.Pk,$6.P,(19.(1:.$6.$6.)(1;.$6.$6.R2.R1.)O4.)(16.(1<.(1=.R4.+>8.)R3.)(1<.(1=.R3.R2.)R4.))(7.(17.O1:.O19.O18.R2.(1>.(1:.$6.$6.)(1;.$6.$6.R1.+>8.)O4.)R4.R3.)(1?.O1:.R4.(1>.(1:.$6.$6.)(1;.$6.$6.R1.+>8.)O4.)R1.(20.R1.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_alloc_wrap_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_rsa ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O4.O3.O2.)PLB,(22.$23.)Plo,$6.P,(17.O4.O3.O2.R3.R2.R5.R4.)P,(10.O4.R6.R2.(11.&40.R26.))P,(1<.R3.(24.(24.(11.&40.R27.)+20.)(25.O3.)))P,(1<.(26.O3.)R4.)P,(1<.(11.&40.R29.)(13.O4.O3.O2.R7.))P,(8.$6.(27.(11.&40.R2:.)+10.)=)P,(1<.(28.O3.)(26.O3.))P,(8.(2.&40.)R2:.(14.&40.(29.O3.)))P,(?.O4.R=.)P,(8.$6.(27.(11.&40.R2?.)+2.)=)(2:.O4.R>.(2;.O4.O3.O2.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R=.R<.R;.R?.R>.)(:.(;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(14.&40.O1.)R10.(=.(2.&40.))R?.(>.O4.)))")
(* [comment removed for export] *).

Definition rsa_free_wrap_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (C : Z) (r : rsa_st) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_rsa ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1<.O1;.O1:.)Lh',(5.O1<.O1;.O1:.)(7.(8.$0.R13.(9.(:.(;.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(<.O19.)O8.(=.(2.&40.))R3.(>.O1<.))R2.))(7.(?.O1<.R3.)(7.(10.O1<.R3.O3.(11.&40.O18.))(7.(12.O1.R2.)(7.(8.$6.(13.O1<.O1;.O1:.R1.)(13.O1<.O1;.O1:.O7.))(7.(17.O1<.O1;.O1:.R1.(2<.O5.(2=.O4.O6.))R3.R2.)(7.(15.O1<.O1;.(2<.O5.(2=.O4.O6.))(11.&40.O18.)O2.R3.)(2>.O1<.O1;.R3.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_free_wrap_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_rsa ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O5.O4.O3.)PLB,(22.$23.)PC,$6.Pr,$2?.Plo,$6.P,(17.O5.O4.O3.R5.R4.R7.R6.)P,(1?.O5.R8.R5.R4.R3.)P,(10.O5.R9.R3.(11.&40.R29.))P,(1<.R4.(24.(24.(11.&40.R2:.)+40.)(25.O4.)))P,(1<.(26.O4.)R5.)P,(1<.(11.&40.R2<.)(13.O5.O4.O3.R:.))P,(8.$6.(27.(11.&40.R2=.)+10.)=)P,(1<.(28.O4.)(26.O4.))P,(8.(2.&40.)R2=.(14.&40.(29.O4.)))P,(?.O5.R10.)P,(2>.O5.O4.R11.)P,(30.O4.O1.+8.)P,(8.$6.(27.(11.&40.R34.)+2.)=)P,(8.(2.&40.)R2<.(14.&40.R10.))(2:.O5.R14.(31.O5.O4.O3.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R13.R12.R11.R10.R?.R15.R14.)(:.(;.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(14.&40.O2.)R16.(=.(2.&40.))R15.(>.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma rsa_at_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_rsa ()) "Psegs,(22.$32.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(22.$23.)PC,$6.Pr,$2?.PW,(22.$33.)P,(1?.R7.R6.R4.R3.R2.)P,(34.R2.R7.R6.)P,(35.R9.R8.R7.)P,(?.R:.R9.)P,(?.R;.R9.)P,(36.R6.R8.+>8.)P,Pd,$37.P,(19.$37.R1.(38.R:.R9.))P,(8.$39.(3:.R2.)$3;.)(36.R:.(3<.R3.)(3=.+4.(3>.R3.)))(1?.R>.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB C r W RA MU WM MI MI' DC DL.
  ddestruct RA as (HD & HT & AN & AE & FN & FE & LEN & ALL & CAL & C0 & CB & CIN & PN & PE & PNE).
  unfold rsa_at. repeat match goal with |- _ /\ _ => split end; try assumption.
  all: lazymatch goal with
       | |- rw_cells _ _ _ (rsa_head_cells _) => eapply rw_cells_transport; [exact HD| exact MU| exact WM|]; cbn [cells_size csize Nat.add rsa_head_cells];
                                eapply disjoint_from_sub; [exact DC| lia| cbn; lia]
       | |- rw_cells _ _ _ rsa_tail_cells => eapply rw_cells_transport; [exact HT| exact MU| exact WM|]; cbn [cells_size csize Nat.add rsa_tail_cells];
                                eapply disjoint_from_sub; [exact DC| lia| unfold RSA_CTX_SIZE in *; cbn; lia]
       | |- Forall _ _ => rewrite Forall_forall in ALL |- *; intros d Hd; eapply mpdr_at_munch; [apply ALL; exact Hd| exact MU| exact WM| exact MI| exact MI'| |];
            [ destruct (rsa_mpds_addr _ _ d (conj AN AE) Hd) as (A1 & A2 & _); eapply disjoint_from_sub; [exact DC| lia| lia]
            | intros HO; apply DL; [exact Hd| exact HO] ]
       | |- _ => clear -LEN; lia
       end.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_gone : forall (LB : list blk) C B k, List.NoDup (map fst LB) -> In (B, k) (lb_remove C LB) -> B <> C.
Proof.
  induction LB as [|[x y] rest IH]; cbn; intros C B k ND HIn; [destruct HIn|].
  inversion ND as [|x' l' Hx Hl]; subst.
  destruct (Z.eqb_spec x C) as [->|NE].
  - intros ->. apply Hx. apply in_map_iff. exists (C, k). split; [reflexivity| exact HIn].
  - destruct HIn as [E|HIn]; [injection E as -> ->; exact NE| eapply IH; eauto].
Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  #[using="HCALLOC HLS DIMG"] Lemma U_rsa_alloc_wrap_spec : rsa_alloc_wrap_stmt usegs L HI U_RSA_ALLOC_WRAP.
  Proof.
    unfold rsa_alloc_wrap_stmt, U_RSA_ALLOC_WRAP. intros until lo. intros HH ST SLO ACL HTOP SPA DHI TP MI RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    pose proof (conj HH I) as HHbox.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 232) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2 | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match goal with H : heap_pres _ _ _ _ _ m2 |- _ => rename H into HPc end.
    match goal with H : stk _ m2 _ _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
    match goal with H : mo_frame mo mo2 |- _ => rename H into MF2 end.
    (* [comment removed for export] *)
    assert (HP2 : heap_pres usegs L LB (bv_unsigned sp) m m2).
    { eapply heap_pres_trans_sub; [| eapply heap_pres_sp_mono; [exact HPc| clear; lia] | intros b Hb; exact Hb].
      eapply heap_pres_of_munch; [exact MU| exact WM| exact HBR0| exact DHI|]. intros a. cbn [outside]. clear -ACL SLO HLS. lia. }
    clear ST MI MK HH HHbox MU WM. heap_transport HPc. clear HPc.
    ddestruct PO as (h2 & HT2 & [[-> HH2] | (N & -> & HBN & HH2 & HNEW)]).
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN. cbn in KN. lia. }
      zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      apply aevtM_done. unfold rsa_alloc_wrap_post. deexists 15. dexists m2, mo2, h2, 0.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
      left. split; [reflexivity| exact HH2].
    - (* [comment removed for export] *)
      change (1 * 232) with 232 in HBN, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI).
      destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [_ HAP]. cbn [blocks_apart] in HAP. destruct HAP as [HAPN _].
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. pose proof (conj HH2 I) as HHbox.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. cbn in KN. lia. }
      pose proof (munch_refl [(N, N + 232); (bv_unsigned sp - 32, bv_unsigned sp + -16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep.
      pose proof U_rsa_init_spec as SPI. unfold rsa_init_stmt, U_RSA_INIT in SPI.
      acallx_sp (bv_unsigned sp + -16)
        (eapply SPI with (A := N) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2).
      clear SPI.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : rw_cells _ m3 N _ |- _ => rename H into HZ end.
      match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
      assert (HH3 : HEAP usegs L HI h2 ((N, 232) :: LB) m3 mo2).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h2 ((N, 232) :: LB) m2 m3 mo2 lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. rewrite HT2.
        destruct (outside_dec [(N, N + 232)] a) as [O1|O1]; cbn [outside] in O1.
        2:{ right. right. exists (N, 232). split; [left; reflexivity| cbn; clear -O1; lia]. }
        left. clear -Hin O1 SLO HLS HTOP Ha. lia. }
      assert (HP3 : heap_pres usegs L LB (bv_unsigned sp) m m3).
      { eapply heap_pres_trans_sub; [exact HP2| | intros b Hb; exact Hb].
        intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by (clear -Ha; lia). cbn [outside].
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]].
        - clear -Hs HNC ACL SLO HLS. lia.
        - clear -Hd1 Hd2 HNI DI1 DI2 DHI ACL SLO HLS. lia.
        - destruct b as [B k]. cbn in Hr. pose proof (HAPN B k Hb) as AP.
          rewrite Forall_forall in HBR0. destruct (HBR0 _ Hb) as (_ & _ & _ & Bc & _). cbn in Bc. clear -Hr AP Bc ACL SLO HLS. lia. }
      clear HHbox MU WM HP2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
      zstep. zstep. zstep. zstep. zstep.
      release_frame FR ST3 (bv_unsigned sp).
      apply aevtM_done. unfold rsa_alloc_wrap_post. deexists 15. dexists m3, mo2, h2, N.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
      right. split; [exact HBN|]. split; [exact HAPN|]. split; [exact HH3|].
      apply rsa_at_of_zero; [exact HZ| exact HN16| exact HN0| left; reflexivity].
  Qed.

  #[using="HFREE HLS SW DIMG HND"] Lemma U_rsa_free_wrap_spec : rsa_free_wrap_stmt usegs L HI U_RSA_FREE_WRAP U_MEMSET_FUNC.
  Proof.
    unfold rsa_free_wrap_stmt, U_RSA_FREE_WRAP. intros until lo. intros HH RA ST SLO ACL HTOP SPA DHI TP MI SOK CA RAE ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    pose proof RA as RAc. ddestruct RAc as (_ & _ & _ & _ & _ & _ & _ & _ & CAL & C0 & CB & CIN & _). unfold RSA_CTX_SIZE in CB, CIN.
    pose proof (proj1 (Forall_forall _ _) HBR0 _ CIN) as (_ & _ & _ & CCE & CIM). cbn [fst snd] in CCE, CIM.
    pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep.
    assert (HH1 : forall mx, munch [(bv_unsigned sp - 16, bv_unsigned sp)] m mx -> wmono usegs m mx -> HEAP usegs L HI h LB mx mo).
    { intros mx MUx WMx. apply (Asn1AuxA.HEAP_munch usegs L HI h LB m mx mo lo _ (proj1 HHbox) ACL MUx WMx).
      intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => specialize (HH1 mx MU WM); rename mx into m1 end.
    assert (HP1 : heap_pres usegs L LB (bv_unsigned sp) m m1).
    { eapply heap_pres_of_munch; [exact MU| exact WM| exact HBR0| exact DHI|]. intros a. cbn [outside]. clear -ACL SLO HLS. lia. }
    assert (RA1 : rsa_at usegs m1 LB C r).
    { eapply rsa_at_munch; [exact RA| exact MU| exact WM| exact (proj1 MIbox)| assumption| cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia|].
      intros d Hd HO. ddestruct RA as (_ & _ & _ & _ & _ & _ & _ & ALL & _). rewrite Forall_forall in ALL.
      ddestruct (ALL d Hd) as (_ & _ & _ & _ & _ & HOW). rewrite HO in HOW. ddestruct HOW as (_ & HIn & _).
      pose proof (proj1 (Forall_forall _ _) HBR0 _ HIn) as (_ & _ & _ & Pc & _). cbn [fst snd] in Pc.
      cbn [disjoint_from]. clear -Pc ACL SLO HLS. lia. }
    clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (U_rsa_free_spec L HI HFREE HLS SW DIMG HND) as SPF. unfold rsa_free_stmt, U_RSA_FREE in SPF.
    eapply aevtM_cut; [ eapply SPF with (C := C) (r := r) (lo := lo) (LB := LB) (h := h);
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2 | ].
    clear SPF.
    intros ms' mo' PO. unfold rsa_free_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia.
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & CIN5 & HPX5 & SOK5).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HH5 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h5; set (LB5 := lb) in * end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH5) as [HBR5 HAP5].
    unfold RSA_CTX_SIZE in CIN5, HPX5.
    apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX5) in FR;
      [| apply client_range_stack; simpl_sizes; clear; lia | simpl_sizes; cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia ].
    zstep. zstep. zstep. zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
    eapply aevtM_cut; [ eapply (heap_free usegs L HI) with (A := C) (n := 232) (lo := lo) (LB := LB5);
      try eassumption; try reflexivity | ].
    { clear -SLO HLS; lia. }
    { rewrite HT5. exact HTOP. }
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'. destruct_ands PO.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
    match goal with H : heap_pres _ _ _ _ m5 m6 |- _ => rename H into HP6 end.
    match goal with H : exists h', _ |- _ => destruct H as (h6 & HT6 & HH6) end.
    apply aevtM_done. unfold rsa_free_wrap_post. deexists 15. dexists m6, mo6, h6.
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply mo_frame_trans; eassumption.
    - etransitivity; eassumption.
    - (* [comment removed for export] *)
      eapply heap_pres_trans_sub; [exact HP1| | intros b Hb; apply lb_remove_sub in Hb; subst LB5; unfold rsa_free_LB in Hb; do 2 apply lb_free_mpd_sub in Hb; exact Hb].
      eapply heap_pres_trans_sub with (LB1 := lb_remove C LB5); [| exact HP6| intros b Hb; exact Hb].
      intros a Ha Hc. apply HPX5; [exact Ha| |].
      + destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; clear -Hs; lia| right; left; exact Hd| right; right].
        exists b. split; [eapply lb_remove_sub; exact Hb| exact Hr].
      + cbn [outside]. split; [| exact I].
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [clear -Hs CCE ACL SLO HLS; lia| clear -Hd1 Hd2 CIM DI1 DI2; lia|].
        destruct b as [B k]. cbn in Hr.
        assert (NE : B <> C) by (eapply lb_remove_gone; [exact (HND _ _ _ _ HH5)| exact Hb]).
        pose proof (blocks_apart_in2 _ _ _ _ _ HAP5 CIN5 (lb_remove_sub _ _ _ Hb) ltac:(intros E; exact (NE (eq_sym E)))) as AP.
        clear -AP Hr. lia.
    - eapply statics_ok_heap_pres; [exact SOK5| exact HP6| exact SW].
  Qed.
End Walk.
