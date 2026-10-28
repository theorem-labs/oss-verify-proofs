(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_ecp_group_free U_ecp_keypair_init U_ecp_keypair_free U_asn1_get_sequence_of_A U_pk_wrap_rsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_wrap_eckey () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "eckey_alloc_wrap_post"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_free.kp_free_LB"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "eckey_free_wrap_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"].


Definition U_ECKEY_ALLOC_WRAP : Z := 0x2a33c.
Definition U_ECKEY_FREE_WRAP : Z := 0x2a374.
Notation ECKEY_ALLOC_WRAP_STACK := 48 (only parsing).
Notation ECKEY_FREE_WRAP_STACK := 112 (only parsing).

Definition eckey_alloc_wrap_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_eckey ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1;.O1:.O19.)Lh',(5.O1;.O1:.O19.)(1.$6.LC,$6.(7.(8.$0.R14.(9.(:.(;.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(<.O17.)O6.(=.(2.&40.))R4.(>.O1;.))R3.))(7.(?.O1;.R4.)(7.(10.O1;.R4.O3.(11.&40.O16.))(7.(12.O1.R3.)(7.(8.$6.(13.O1;.O1:.O19.R2.)(13.O1;.O1:.O19.O5.))(7.(8.(2.&40.)R10.(14.&40.R1.))(7.(15.O1;.O1:.O4.(11.&40.O16.)O2.R4.)(16.(7.(8.$6.R1.=)(17.O1;.O1:.O19.R2.O4.R4.R3.))(7.(18.O1:.R1.+100.)(7.PB,$6.Pk,$6.P,(19.(1:.$6.$6.)(1;.$6.$6.R2.R1.)O4.)(16.(1<.(1=.R4.+100.)R3.)(1<.(1=.R3.R2.)R4.))(7.(17.O1;.O1:.O19.R2.(1>.(1:.$6.$6.)(1;.$6.$6.R1.+100.)O4.)R4.R3.)(1.(2.&40.)Lidpad,(2.&40.)(1.(2.&40.)LpP,(2.&40.)(1.(2.&40.)LpA,(2.&40.)(1.(2.&40.)LpB,(2.&40.)(1.(2.&40.)LpX,(2.&40.)(1.(2.&40.)LpY,(2.&40.)(1.(2.&40.)LpZ,(2.&40.)(1.(2.&40.)LpN,(2.&40.)(1.(2.&40.)Lhpad,(2.&40.)(1.(2.&40.)Lpd,(2.&40.)(1.(2.&40.)LqX,(2.&40.)(1.(2.&40.)LqY,(2.&40.)(1.(2.&40.)LqZ,(2.&40.)(1?.O1;.O18.R11.(1>.(1:.$6.$6.)(1;.$6.$6.R>.+100.)O4.)R>.(20.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.)))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition eckey_alloc_wrap_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_eckey ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O5.O4.O3.)PLB,(22.$23.)Plo,$6.P,(17.O5.O4.O3.R3.R2.R5.R4.)P,(10.O5.R6.R2.(11.&40.R26.))P,(1<.R3.(24.(24.(11.&40.R27.)+30.)(25.O4.)))P,(1<.(26.O4.)R4.)P,(1<.(11.&40.R29.)(13.O5.O4.O3.R7.))P,(8.$6.(27.(11.&40.R2:.)+10.)=)P,(1<.(28.O4.)(26.O4.))P,(8.(2.&40.)R2:.(14.&40.(29.O4.)))P,(?.O5.R=.)P,(8.$6.(27.(11.&40.R2?.)+2.)=)(2:.O5.R>.(2;.O5.O4.O3.O2.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R=.R<.R;.R?.R>.)(:.(;.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(14.&40.O1.)R10.(=.(2.&40.))R?.(>.O5.)))")
(* [comment removed for export] *).

Definition eckey_free_wrap_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (A : Z) (k : ecp_kp) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_eckey ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1<.O1;.O1:.)Lh',(5.O1<.O1;.O1:.)(7.(8.$0.R13.(9.(:.(;.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(<.O19.)O8.(=.(2.&40.))R3.(>.O1<.))R2.))(7.(?.O1<.R3.)(7.(10.O1<.R3.O3.(11.&40.O18.))(7.(12.O1.R2.)(7.(8.$6.(13.O1<.O1;.O1:.R1.)(13.O1<.O1;.O1:.O7.))(7.(17.O1<.O1;.O1:.R1.(2<.O5.(2=.O4.O6.))R3.R2.)(7.(15.O1<.O1;.(2<.O5.(2=.O4.O6.))(11.&40.O18.)O2.R3.)(2>.O1<.O1;.R3.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition eckey_free_wrap_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (MT : list modp_ent) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_eckey ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O6.O5.O4.)PLB,(22.$23.)PA,$6.Pk,$2?.Plo,$6.P,(17.O6.O5.O4.R5.R4.R7.R6.)P,(1?.O6.O3.R8.R5.R4.R3.)P,(30.(31.R4.))P,(19.(1:.$6.$6.)(1;.$6.$6.R6.+100.)(2=.R5.R7.))P,(10.O6.R;.R5.(11.&40.R2;.))P,(1<.R6.(24.(24.(11.&40.R2<.)+70.)(25.O5.)))P,(1<.(26.O5.)R7.)P,(1<.(11.&40.R2>.)(13.O6.O5.O4.R<.))P,(8.$6.(27.(11.&40.R2?.)+10.)=)P,(1<.(28.O5.)(26.O5.))P,(8.(2.&40.)R2?.(14.&40.(29.O5.)))P,(?.O6.R12.)P,(2>.O6.O5.R13.)P,(32.O5.O1.+8.)P,(8.$6.(27.(11.&40.R36.)+2.)=)P,(8.(2.&40.)R2>.(14.&40.R12.))(2:.O6.R16.(33.O6.O5.O4.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.R15.R14.R13.R12.R11.R17.R16.)(:.(;.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(14.&40.O2.)R18.(=.(2.&40.))R17.(>.O6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma ecp_keypair_at_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_wrap_eckey ()) "Psegs,(22.$34.)PMT,(22.$35.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(22.$23.)PA,$6.Pk,$2?.PW,(22.$36.)P,(1?.R8.R7.R6.R4.R3.R2.)P,(37.R2.R7.R6.)P,(38.R:.R8.R7.)P,(?.R;.R9.)P,(?.R<.R9.)P,(39.R6.R8.+100.)P,Pd,$3:.P,(19.$3:.R1.(31.R9.))P,(8.$3;.(3<.R2.)$3=.)(39.R:.(3>.R3.)(3?.+4.(40.R3.)))(1?.R?.R>.R<.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  (intros segs MT m m' LB A k W dd_H; ddestruct dd_H as (HG & ED & MD & FD & HQ & FQ); intros MU WM MI MI' D DL).
  split; [| split; [exact ED| split; [| split; [exact FD| split; [| exact FQ]]]]].
  - eapply ecp_group_at_munch; [exact HG| exact MU| exact WM| exact MI| exact MI'| eapply disjoint_from_sub; [exact D| lia| lia]|].
    intros d Hd HO. apply DL; [| exact HO]. unfold kp_mpds. apply in_or_app. left. exact Hd.
  - eapply mpdr_at_munch; [exact MD| exact MU| exact WM| exact MI| exact MI'| rewrite ED; eapply disjoint_from_sub; [exact D| lia| lia]|].
    intros HO. apply DL; [| exact HO]. unfold kp_mpds. apply in_or_app. right. left. reflexivity.
  - eapply ecp_point_at_munch; [exact HQ| exact MU| exact WM| exact MI| exact MI'| eapply disjoint_from_sub; [exact D| lia| lia]|].
    intros d Hd HO. apply DL; [| exact HO]. unfold kp_mpds. apply in_or_app. right. right. exact Hd.
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

  #[using="HCALLOC HLS DIMG"] Lemma U_eckey_alloc_wrap_spec : forall MT, eckey_alloc_wrap_stmt usegs L HI MT U_ECKEY_ALLOC_WRAP.
  Proof.
    intros MT. unfold eckey_alloc_wrap_stmt, U_ECKEY_ALLOC_WRAP. intros until lo. intros HH ST SLO ACL HTOP SPA DHI TP MI RA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    pose proof (conj HH I) as HHbox.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 260448) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 256) (lo := lo);
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
    assert (HP2 : heap_pres usegs L LB (bv_unsigned sp) m m2).
    { eapply heap_pres_trans_sub; [| eapply heap_pres_sp_mono; [exact HPc| clear; lia] | intros b Hb; exact Hb].
      eapply heap_pres_of_munch; [exact MU| exact WM| exact HBR0| exact DHI|]. intros a. cbn [outside]. clear -ACL SLO HLS. lia. }
    clear ST MI MK HH HHbox MU WM. heap_transport HPc. clear HPc.
    ddestruct PO as (h2 & HT2 & [[-> HH2] | (N & -> & HBN & HH2 & HNEW)]).
    - pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      zstep. if_cases KN; zify_cond KN. 2:{ exfalso. clear -KN. cbn in KN. lia. }
      zstep. zstep. zstep. zstep.
      release_frame FR ST2 (bv_unsigned sp).
      apply aevtM_done. unfold eckey_alloc_wrap_post. deexists 15. dexists m2, mo2, h2, 0.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
      left. split; [reflexivity| exact HH2].
    - change (1 * 256) with 256 in HBN, HH2, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
      pose proof HBN as HBNc. ddestruct HBNc as (HN0 & HN16 & _ & HNC & HNI).
      destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [_ HAP]. cbn [blocks_apart] in HAP. destruct HAP as [HAPN _].
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. pose proof (conj HH2 I) as HHbox.
      zstep. if_cases KN; zify_cond KN. { exfalso. clear -KN HN0. rewrite ?unsigned_lit in KN by lia. cbn in KN. lia. }
      pose proof (munch_refl [(N, N + 256); (bv_unsigned sp - 48, bv_unsigned sp + -16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
      zstep. zstep.
      pose proof (U_ecp_keypair_init_spec MT) as SPI. unfold ecp_keypair_init_stmt, ecp_keypair_init_post, U_ECP_KEYPAIR_INIT, ECP_KEYPAIR_SIZE in SPI.
      acallx_sp (bv_unsigned sp + -16)
        (eapply SPI with (A := N) (lo := lo) (LB := (N, 256) :: LB); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia;
         try eassumption; try reflexivity; try flia2).
      clear SPI.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : ecp_keypair_at _ _ m3 _ N _ |- _ => rename H into HKP end.
      match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
      assert (HH3 : HEAP usegs L HI h2 ((N, 256) :: LB) m3 mo2).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h2 ((N, 256) :: LB) m2 m3 mo2 lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. rewrite HT2.
        destruct (outside_dec [(N, N + 256)] a) as [O1|O1]; cbn [outside] in O1.
        2:{ right. right. exists (N, 256). split; [left; reflexivity| cbn; clear -O1; lia]. }
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
      apply aevtM_done. unfold eckey_alloc_wrap_post. deexists 15. dexists m3, mo2, h2, N.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
      right. split; [exact HBN|]. split; [exact HAPN|]. split; [exact HH3|]. deexists 13. exact HKP.
  Qed.

  #[using="HFREE HLS SW DIMG HND"] Lemma U_eckey_free_wrap_spec : forall MT, eckey_free_wrap_stmt usegs L HI MT U_ECKEY_FREE_WRAP U_MEMSET_FUNC.
  Proof.
    intros MT. unfold eckey_free_wrap_stmt, U_ECKEY_FREE_WRAP. intros until lo. intros HH KP APT CIN5 ST SLO ACL HTOP SPA DHI TP MI SOK CA RAE ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    assert (CIN : In (A, 256) LB) by (unfold kp_free_LB, grp_free_LB in CIN5; do 2 apply lb_free_mpds_sub in CIN5; exact CIN5).
    pose proof (proj1 (Forall_forall _ _) HBR0 _ CIN) as (A0 & A16 & _ & CCE & CIM). cbn [fst snd] in A0, A16, CCE, CIM.
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
    assert (KP1 : ecp_keypair_at usegs MT m1 LB A k).
    { eapply ecp_keypair_at_munch; [exact KP| exact MU| exact WM| exact (proj1 MIbox)| assumption| cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia|].
      intros d Hd HO.
      assert (HIn : In (md_p d, 4 * md_n d) LB).
      { ddestruct KP as (HG & _ & MD & _ & (_ & _ & _ & MX & MY & MZ) & _).
        unfold kp_mpds in Hd. apply in_app_or in Hd.
        assert (R : forall d', mpdr_at usegs m LB d' -> md_own d' = LHeap -> In (md_p d', 4 * md_n d') LB)
          by ((intros d' dd_H; ddestruct dd_H as (_ & _ & _ & _ & _ & HOW); intros HO'); rewrite HO' in HOW; ddestruct HOW as (_ & HIn & _); exact HIn).
        destruct Hd as [Hd|[<-|Hd]].
        - ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & GX & GY & GZ) & MN & _).
          unfold grp_mpds in Hd. cbn [app In pt_mpds] in Hd.
          destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; eapply R; eassumption.
        - eapply R; eassumption.
        - cbn [In pt_mpds] in Hd. destruct Hd as [<-|[<-|[<-|[]]]]; eapply R; eassumption. }
      pose proof (proj1 (Forall_forall _ _) HBR0 _ HIn) as (_ & _ & _ & Pc & _). cbn [fst snd] in Pc.
      cbn [disjoint_from]. clear -Pc ACL SLO HLS. lia. }
    clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (U_ecp_keypair_free_spec L HI HFREE HLS SW DIMG HND MT) as SPF.
    unfold ecp_keypair_free_stmt, ecp_keypair_free_post, U_ECP_KEYPAIR_FREE, ECP_KEYPAIR_SIZE in SPF.
    eapply aevtM_cut; [ eapply SPF with (A := A) (k := k) (lo := lo) (LB := LB) (h := h);
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2 | ].
    1: { intros a Ha; right; right; exists (A, 256); split; [exact CIN5| cbn; clear -Ha; lia]. }
    clear SPF.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia.
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & KP5 & HPX5 & SOK5).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HH5 with HEAP _ _ _ ?hh ?lb _ _ => rename hh into h5; set (LB5 := lb) in * end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH5) as [HBR5 HAP5].
    apply (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX5) in FR;
      [| apply client_range_stack; simpl_sizes; clear; lia | simpl_sizes; cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia ].
    zstep. zstep. zstep. zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    replace (Z_to_bv 64 260760) with (Z_to_bv 64 (hl_free L)) by (rewrite HFREE; reflexivity).
    eapply aevtM_cut; [ eapply (heap_free usegs L HI) with (A := A) (n := 256) (lo := lo) (LB := LB5);
      try eassumption; try reflexivity | ].
    { clear -SLO HLS; lia. }
    { rewrite HT5. exact HTOP. }
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO].
    injection E as E1 E2. subst ms' mo'. destruct_ands PO.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
    match goal with H : heap_pres _ _ _ _ m5 m6 |- _ => rename H into HP6 end.
    match goal with H : exists h', _ |- _ => destruct H as (h6 & HT6 & HH6) end.
    apply aevtM_done. unfold eckey_free_wrap_post. deexists 15. dexists m6, mo6, h6.
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply mo_frame_trans; eassumption.
    - etransitivity; eassumption.
    - eapply heap_pres_trans_sub; [exact HP1| | intros b Hb; apply lb_remove_sub in Hb; subst LB5; unfold kp_free_LB, grp_free_LB in Hb; do 2 apply lb_free_mpds_sub in Hb; exact Hb].
      eapply heap_pres_trans_sub with (LB1 := lb_remove A LB5); [| exact HP6| intros b Hb; exact Hb].
      intros a Ha Hc. apply HPX5; [exact Ha| |].
      + destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; clear -Hs; lia| right; left; exact Hd| right; right].
        exists b. split; [eapply lb_remove_sub; exact Hb| exact Hr].
      + cbn [outside]. split; [| exact I].
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [clear -Hs CCE ACL SLO HLS; lia| clear -Hd1 Hd2 CIM DI1 DI2; lia|].
        destruct b as [B kk]. cbn in Hr.
        assert (NE : B <> A) by (eapply lb_remove_gone; [exact (HND _ _ _ _ HH5)| exact Hb]).
        pose proof (blocks_apart_in2 _ _ _ _ _ HAP5 CIN5 (lb_remove_sub _ _ _ Hb) ltac:(intros E; exact (NE (eq_sym E)))) as AP.
        clear -AP Hr. lia.
    - eapply statics_ok_heap_pres; [exact SOK5| exact HP6| exact SW].
  Qed.
End Walk.
