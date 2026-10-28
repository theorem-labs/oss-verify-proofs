(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts RepRsa RepCrt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_ecp_group_free U_ecp_keypair_free U_rsa_free U_asn1_get_sequence_of_A U_pk_wrap_rsa U_pk_wrap_eckey.
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
Ltac2 gd_tbl_P_pk_free () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.app"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.fst"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.pk_rep_c"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "pk_free_c_post"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpd"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpds"; "Stdlib.Lists.List.NoDup"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_free_mpds"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_PLATFORM_ZEROIZE"].


Definition U_PK_FREE : Z := 0x29c28.
Definition U_RSA_INFO : Z := 0x48d18.
Definition U_ECKEY_INFO : Z := 0x48d78.
Definition U_ECKEYDH_INFO : Z := 0x48dd8.
Definition U_ECDSA_INFO : Z := 0x48e38.
Definition U_EC_INFOS : list Z := [U_ECKEY_INFO; U_ECKEYDH_INFO; U_ECDSA_INFO].
Notation PK_FREE_STACK' := 256 (only parsing).

Definition pk_free_c_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LBo LB : list blk) (PKA : Z) (owned : list blk) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1=.O1<.O1;.)Lh',(5.O1=.O1<.O1;.)(1.(6.$7.)LLBo',(6.$7.)(8.(9.$0.R14.(:.(;.(<.O1:.O19.O18.O17.R13.R12.R11.O16.O15.R10.R?.R>.R=.R<.R;.R:.R9.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R8.R7.R6.R5.)O:.(=.O1:.)O9.(>.(2.&40.))R4.(?.O1=.))R3.))(8.(10.O1=.R4.)(8.(11.O1=.O1<.R4.)(8.(12.O1=.R4.O3.(13.&40.O19.))(8.(14.O1.R3.)(8.(9.$15.(16.O1=.O1<.O1;.R2.)(16.O1=.O1<.O1;.O8.))(8.(17.O1=.O1<.O1;.R2.(18.$7.R1.O6.)R4.R3.)(8.Pb,$7.P,(19.$7.R1.R2.)(19.$7.R2.O7.)(8.Pb,$7.P,(19.$7.R1.O7.)P,(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)O4.)))(19.$7.R3.R4.)(8.(1>.O1=.R4.O5.(1?.$20.(21.(22.&40.=))(1?.$20.(21.(22.&40.=))(23.$20.))))(8.(24.O1=.O1<.(18.$7.R1.O6.)(13.&40.O19.)(1?.(1=.$15.$15.)(25.$15.$15.O5.(26.O5.+10.))(23.(1=.$15.$15.)))O2.R4.)Pb,$7.P,(19.$7.R1.R2.)(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)O4.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pk_free_c_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (RSAI : Z) (ECIS : list Z) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O7.O6.O5.)PLBo,(6.$7.)PLB,(6.$7.)PPKA,$15.Pinfo,$15.Pctx,$15.Powned,(6.$7.)Plo,$15.P,(17.O7.O6.O5.R8.(18.$7.R7.R6.)R:.R9.)P,(1>.O7.R;.R6.(1?.$20.(21.(22.&40.R5.))(1?.$20.(21.(22.&40.R4.))(23.$20.))))P,(9.$15.(28.R7.+8.)=)P,(29.O7.O4.O3.O2.R=.(18.$7.R:.R9.)R8.R7.R6.R5.)P,Pb,$7.P,(19.$7.R1.R7.)(19.$7.R2.R=.)P,(2:.(13.&40.R2?.)R:.)P,(2:.(26.R;.+10.)(16.O7.O6.O5.R>.))P,(12.O7.R11.R8.(13.&40.R31.))P,(2:.(2;.O6.)R9.)P,(2:.R:.(2<.(2<.(13.&40.R33.)+100.)(2=.O6.)))P,(9.$15.(28.(13.&40.R34.)+10.)=)P,(2:.(13.&40.R35.)(16.O7.O6.O5.R13.))P,(2:.(2>.O6.)(2;.O6.))P,(10.O7.R17.)P,(11.O7.O6.R18.)P,(9.(2.&40.)R37.(22.&40.(2?.O6.)))P,(9.(2.&40.)R32.(22.&40.R15.))(30.O7.R1:.(31.O7.O6.O5.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R19.R18.R17.R16.R13.R12.R1;.R1:.)(;.(<.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(22.&40.O1.)R1<.(>.(2.&40.))R1;.(?.O7.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_notin_id : forall a (LB : list blk), ~ In a (map fst LB) -> lb_remove a LB = LB.
Proof.
  induction LB as [|[x y] r IH]; cbn; intros H; [reflexivity|].
  destruct (Z.eqb_spec x a) as [->|NE]; [exfalso; apply H; left; reflexivity|]. rewrite IH; [reflexivity|]. intros Hin. apply H. right. exact Hin.
Qed.

Lemma lb_remove_app : forall a (X LB : list blk), ~ In a (map fst LB) -> lb_remove a (X ++ LB) = lb_remove a X ++ LB.
Proof.
  induction X as [|[x y] r IH]; cbn; intros LB H; [apply lb_remove_notin_id; exact H|].
  destruct (Z.eqb_spec x a) as [->|NE]; [reflexivity|]. cbn. rewrite IH; [reflexivity| exact H].
Qed.

Lemma lb_free_mpd_app : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pd,$32.PX,(6.$7.)PLB,(6.$7.)P,P,(9.$33.(34.R3.)$35.)(1:.(19.$15.(36.R4.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R2.)))(9.(6.$7.)(37.R4.(18.$7.R3.R2.))(18.$7.(37.R4.R3.)R2.))")
(* [comment removed for export] *).
Proof. intros d X LB H. unfold lb_free_mpd. destruct (md_own d) eqn:E; try reflexivity. apply lb_remove_app. apply H. reflexivity. Qed.

Lemma lb_free_mpds_app : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pds,(6.$32.)PX,(6.$7.)PLB,(6.$7.)P,Pd,$32.P,(19.$32.R1.R4.)P,(9.$33.(34.R2.)$35.)(1:.(19.$15.(36.R3.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R4.)))(9.(6.$7.)(38.R4.(18.$7.R3.R2.))(18.$7.(38.R4.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  induction ds as [|d r IH]; cbn; intros X LB H; [reflexivity|].
  rewrite lb_free_mpd_app by (apply H; left; reflexivity). apply IH. intros d' Hd'. apply H. right. exact Hd'.
Qed.

Lemma map_fst_lb_remove_sub : forall a (LB : list blk) x, In x (map fst (lb_remove a LB)) -> In x (map fst LB).
Proof. intros a LB x H. apply in_map_iff in H. ddestruct H as ([B k] & <- & Hb). apply in_map_iff. exists (B, k). split; [reflexivity| eapply lb_remove_sub; exact Hb]. Qed.

Lemma NoDup_lb_remove : forall a (LB : list blk), List.NoDup (map fst LB) -> List.NoDup (map fst (lb_remove a LB)).
Proof.
  induction LB as [|[x y] r IH]; cbn; intros H; [constructor|].
  inversion H as [|x' l' Hx Hl]; subst. destruct (Z.eqb_spec x a) as [->|NE]; [exact Hl|].
  cbn. constructor; [| apply IH; exact Hl]. intros Hin. apply Hx. eapply map_fst_lb_remove_sub. exact Hin.
Qed.

Lemma NoDup_lb_free_mpd : forall d (LB : list blk), List.NoDup (map fst LB) -> List.NoDup (map fst (lb_free_mpd d LB)).
Proof. intros d LB H. unfold lb_free_mpd. destruct (md_own d); try exact H. apply NoDup_lb_remove. exact H. Qed.

Lemma NoDup_lb_free_mpds : forall ds (LB : list blk), List.NoDup (map fst LB) -> List.NoDup (map fst (lb_free_mpds ds LB)).
Proof. induction ds as [|d r IH]; cbn; intros LB H; [exact H|]. apply IH. apply NoDup_lb_free_mpd. exact H. Qed.

Lemma NoDup_app_notin_Z : forall (l1 l2 : list Z) a, List.NoDup (l1 ++ l2) -> In a l1 -> ~ In a l2.
Proof.
  induction l1 as [|x r IH]; cbn; intros l2 a H Ha Hb; [destruct Ha|].
  apply List.NoDup_cons_iff in H. destruct H as [Hx Hl].
  destruct Ha as [->|Ha]; [apply Hx; apply in_or_app; right; exact Hb| exact (IH _ _ Hl Ha Hb)].
Qed.

Lemma NoDup_app_notin : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "PLBo,(6.$7.)PLB,(6.$7.)Pa,$15.P,(39.$15.(1<.(1=.$15.$15.)$15.(1;.$15.$15.)(18.$7.R3.R2.)))P,(19.$15.R2.(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R4.))(1:.(19.$15.R3.(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R4.)))")
(* [comment removed for export] *).
Proof. intros LBo LB a H Ha. rewrite map_app in H. eapply NoDup_app_notin_Z; eauto. Qed.

(* [comment removed for export] *)
Lemma lb_free_mpd_gone : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pd,$32.PLB,(6.$7.)PB,$15.Pk,$15.P,(39.$15.(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R3.))P,(19.(1=.$15.$15.)(25.$15.$15.R3.R2.)(37.R5.R4.))P,(9.$33.(34.R6.)$35.)(1:.(9.$15.R5.(36.R7.)))")
(* [comment removed for export] *).
Proof. intros d LB B k ND H HO. unfold lb_free_mpd in H. rewrite HO in H. eapply lb_remove_gone; [exact ND| exact H]. Qed.

Lemma lb_free_mpds_gone : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pds,(6.$32.)PLB,(6.$7.)PB,$15.Pk,$15.Pd,$32.P,(39.$15.(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R4.))P,(19.(1=.$15.$15.)(25.$15.$15.R4.R3.)(38.R6.R5.))P,(19.$32.R3.R7.)P,(9.$33.(34.R4.)$35.)(1:.(9.$15.R7.(36.R5.)))")
(* [comment removed for export] *).
Proof.
  induction ds as [|d0 r IH]; cbn; intros LB B k d ND H Hd HO; [destruct Hd|].
  destruct Hd as [<-|Hd].
  - apply lb_free_mpds_sub in H. eapply lb_free_mpd_gone; eauto.
  - eapply IH; [apply NoDup_lb_free_mpd; exact ND| exact H| exact Hd| exact HO].
Qed.

(* [comment removed for export] *)
Lemma kp_tail_sub : forall k d, In d (kp_tail_mpds k) -> In d (kp_mpds k).
Proof. intros k d H. unfold kp_tail_mpds in H. unfold kp_mpds. apply in_or_app. right. exact H. Qed.
Lemma grp_free_sub : forall g d, In d (grp_free_mpds g) -> In d (grp_mpds g).
Proof.
  intros g d H. unfold grp_free_mpds in H. unfold grp_mpds.
  destruct (g_h g =? 1); [destruct H|]. destruct (g_h g =? 2); cbn [app In pt_mpds] in H |- *; tauto.
Qed.
Lemma grp_sub_kp : forall k d, In d (grp_mpds (kp_grp k)) -> In d (kp_mpds k).
Proof. intros k d H. unfold kp_mpds. apply in_or_app. left. exact H. Qed.

(* [comment removed for export] *)
Lemma grp_heap_in_free : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Psegs,(6.$3:.)PMT,(6.$3;.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PA,$15.Pg,$3<.Pd,$32.P,(3=.R7.R6.R5.R4.R3.R2.)P,(19.$32.R2.(3>.R3.))P,(9.$33.(34.R3.)$35.)(19.$32.R4.(3?.R5.))")
(* [comment removed for export] *).
Proof.
  intros segs MT m LB A g d HG Hd HO.
  ddestruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REST).
  assert (KEPT : Forall (fun d => md_own d <> LHeap) (grp_kept_mpds g)) by tauto.
  rewrite Forall_forall in KEPT.
  unfold grp_free_mpds, grp_kept_mpds in *. unfold grp_mpds in Hd.
  destruct (g_h g =? 1) eqn:E1.
  { exfalso. apply (KEPT d); [| exact HO]. unfold grp_mpds. exact Hd. }
  destruct (g_h g =? 2) eqn:E2.
  - cbn [app In pt_mpds] in Hd |- *.
    destruct Hd as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; first [subst d; tauto | exfalso; apply (KEPT d); [cbn; rewrite <- E; tauto| exact HO]].
  - cbn [app In pt_mpds] in Hd |- *. destruct Hd as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; subst d; tauto.
Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variable MT : list modp_ent.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_MSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis CA_RSA : const_at L (U_RSA_INFO + 80) 8.
  Hypothesis CA_EC : forall e, In e U_EC_INFOS -> const_at L (e + 80) 8.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L19203991648.9 L35503824862.13L38948636245.0 L47769292825.9 L52101696360.3 L52101792632.11L52103791535.10L5451249235.5  00000Q01;01<01]01f02G02f037S1L3HLS2sp3PKA2lo3SPP3ACL3SLO3DHIS1L2HI3HLS2sp2h03PKA2lo3SPP4PTOP3SLO1a3HinSS1L3HLS2sp3PKA2lo3SPP3ACL3SLO3ACPS2sp1a2HsS1L3HLS2sp2lo3ACL3SLO1a1B1k2Hr2BcS1L3HLS2sp2lo3ACL3SLO3DHI1a3Hd1S1L3HLS2sp2lo3SLO". (* [comment removed for export] *)
  #[using="HLS DIMG CA_MSF"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_free ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pm0,P,(2.&40.)(3.(2.&8.))Pmo0,$4.Ph0,(5.$40.VL,VHI,)PLBo,(6.$7.)PLB,(6.$7.)PLBo',(6.$7.)Powned,(6.$7.)PPKA,$15.Plo,$15.Pcs,(6.$20.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$40.VL,VHI,)P,(17.$40.VL,VHI,R1.(18.$7.R8.R9.)R3.R2.)P,(9.$15.(16.$40.VL,VHI,R2.)(16.$40.VL,VHI,R<.))P,(1>.$40.R5.R8.R6.)P,(9.$41.(42.R7.)#10.)P,(9.$15.(28.R:.+8.)=)P,(2:.(13.&40.R30.)R;.)P,(2:.(26.R<.+10.)(16.$40.VL,VHI,R11.))P,(12.$40.R:.R<.(13.&40.R32.))P,(2:.(2;.VL,)R=.)P,(2:.R>.(2<.(2<.(13.&40.R34.)+100.)(2=.VL,)))P,(9.$15.(28.(13.&40.R35.)+10.)=)P,(2:.(2>.VL,)(2;.VL,))P,(10.$40.R?.)P,(11.$40.VL,R10.)P,(14.R1:.R10.)P,Pb,$7.P,(19.$7.R1.R18.)(19.$7.R2.R1;.)P,Pb,$7.P,(19.$7.R1.R1;.)P,(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R19.)))(19.$7.R3.R1;.)P,Pb,$7.P,(19.$7.R1.R1:.)(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)R1:.)))P,(24.$40.VL,(18.$7.R1:.R1;.)(13.&40.R3=.)(1?.(1=.$15.$15.)(25.$15.$15.R18.(26.R18.+10.))(23.(1=.$15.$15.)))R1?.R15.)(30.$40.R15.(31.$40.VL,VHI,R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R1>.R1=.R1<.R19.R1:.R18.R20.R1?.)(;.(<.R3?.R3>.R3=.R3<.R2=.R2<.R2;.R3;.R3:.(22.&40.R19.)(22.&40.+10.)R2:.R29.R28.R27.R26.R25.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R24.R23.R22.R21.)R2?.(22.&40.$43.)R2>.(>.(2.&40.))R16.(?.$40.)))")
(* [comment removed for export] *).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 mo0 h0 LBo LB LBo' owned PKA lo cs mm moc hc
      HH HT HPKA HSZ ALP SPP PTOP ST ACL SLO SPA DHI MI SOK MF SUB KEPT GONE HPX.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2].
    destruct (rw_cells_forget _ _ _ _ HPKA) as [jk HPK]. rewrite HSZ in HPK. clear HPKA.
    pose proof (U_platform_zeroize_spec L) as SPZ. unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE in SPZ.
    eapply aevtM_cut_evt; [exact MK| eapply SPZ with (A := PKA) (n := 16) (lo := lo);
        rewrite ?unsigned_lit by (clear -SPR SPP PTOP; lia); try eassumption; try reflexivity |].
    { clear; lia. }
    { clear -SPP SLO HLS ACL ACP; lia. }
    { clear -SLO HLS; lia. }
    { right; exact SPP. }
    { right. clear -SPP SLO HLS ACL DHI; lia. }
    clear SPZ.
    cbn beta. intros ms' PO. unfold platform_zeroize_post in PO. destruct_exs PO.
    ddestruct PO as (-> & MU & WM & MI' & HZ & ST' & SOK').
    lazymatch type of MI' with mem_inv _ ?mx => rename mx into m9 end.
    change (Z.to_nat 16) with 16%nat in HZ.
    apply (rw_cells_zeros usegs m9 PKA 16 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in HZ; [| cbn; repeat split; reflexivity | reflexivity].
    assert (HH9 : HEAP usegs L HI hc (LBo' ++ LB) m9 moc).
    { apply (Asn1AuxA.HEAP_munch usegs L HI hc (LBo' ++ LB) mm m9 moc lo _ HH ACL MU WM).
      intros a Ha Hin. cbn [outside] in Hin. rewrite HT. left. clear -Hin SPP PTOP SLO HLS Ha. lia. }
    apply aevtM_done. unfold pk_free_c_post. deexists 15. dexists m9, moc, hc, LBo'.
    split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
    eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. cbn [outside] in Ho |- *. split; [exact (proj1 Ho)|]. split; [| exact I].
    destruct Hc as [Hs|[[Hd1 Hd2]|Hb]]; [clear -Hs; lia| clear -Hd1 Hd2 DHI ACL SLO HLS; lia|].
    ddestruct Hb as (b & Hb & Hr). rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _).
    destruct b as [B k]; cbn in Hr, Bc. clear -Hr Bc ACL SLO HLS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01K0@D10463954377.100D10463954377.101D10463954377.102D10463954377.99 D11805467289.100D11805467289.97 D11805467289.98 D11805467289.99 D13294724630.100D13294724630.102D13296972522.100D13296972522.98 D15282083212.108D17614736195.124D17614736195.130D2213593069.102 D22575734509.108D34074246853.124D34074246853.130D3523383040.102 D3523383040.108 D3525463959.120 D3525463959.126 D36801578553.100D36801578553.102D44208477419.102D44208477419.108D44622288685.100D44622288685.101D44622288685.102D44622288685.99 D45907855535.101D45907855535.99 D45914037331.97 D45914037331.99 D49698585326.100D49698585326.101D49698585326.102D49698585326.99 D49705053714.100D49705053714.97 D49705053714.98 D49705053714.99 D58146298210.101D58146298210.99 D64111535230.100D64111535230.101D64111535230.102D64111535230.99 D67438241858.102D67438241858.108L11774327555.97 L11774327555.99 L11805783156.8  L15282083212.108L16811460530.100L17600056186.3  L20433961190.96 L20433961190.98 L20643752190.8  L22704456131.14 L22706389268.17 L22706555140.13 L29010380273.80 L31401241659.123L31401241659.129L32049487064.124L32049487064.130L32049487064.96 L32049487064.98 L34299519794.98 L36012194261.80 L38330469153.0  L3834310201.124 L3834310201.130 L43059266230.94 L43059266230.96 L45993986129.1  L46748113268.96 L46748113268.98 L49530003784.1  L49953061438.79 L54394092454.11 L56552377779.124L56552377779.130L56552377779.97 L56552377779.99 L56828088003.91 L59308628179.11 L59308631013.1  L59308631400.1  00000Z01D01n02X02g03603E03T04204P04_04n04o05?05O05d06906E06Q07=07f08R09;0:10:d0;<0;T0<R0=M0>H0?F0?d0@B0@Q0@`0AB0Ad0BF0Bh0C;0CN0Ca0D40Dg0E]0F?0Fa0GC0Ge0HU0IB0IN0IZ0J40J50JA0JM0JY0Je0KB0Ka0LC0LL0LT0L`0Ll0M80MD0MP0M\0Mh0Mi0Mj0NN0No0OS0P40P80PD0PP0PT0P`0QA0QM0QY0Qe0R10RB0Rf0Rj0RnS1L2HI2sp2s01h3PKA3ctx4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA3ctx4HTOP2HB5Ha_st5Hl_stS1L2HI2sp2s01h3PKA3ctx4HTOP2HB5Ha_st5Hl_stS1L2HI2ra2sp1h3PKA3ctx4HTOP2HB5Ha_st5Hl_stS2sp3PKA3ctx2HBS2sp3PKA3ctx2HBS2sp3PKA3ctx2HBS2sp3PKA3ctx2HBS2sp2s03PKA3ctx2HB5Ha_st5Hl_stS2sp2s03PKA3ctx2HB5Ha_st5Hl_stS2sp3PKA3ctx2HBS2sp3PKA3ctx2HBFS2sp3PKA3ctx3SPPS2sp3PKA3ctx3SPPS1L2sp3PKA3ctx2lo3SLOS1L2sp3PKA3ctx2lo3SLOS2sp3PKA3ctxS2sp3PKA3ctxS1L3HLS2sp3PKA3ctx2lo3ACL3SLO3ACP3SPR3PKB2C0S1L3HLS2sp3PKA3ctx2lo3ACL3SLO3ACP3SPR3PKBS1L3HLS2sp3PKA3ctx2lo3ACL3SLO3ACP3SPR3PKB2C0S1L3HLS2sp3PKA3ctx2lo3ACL3SLO3ACP3SPR3PKBS1L3HLS2sp2s03PKA3ctx2lo3SLO3SPR3PKB2C02HB5Ha_st5Hl_stS1L3HLS2sp2s03PKA3ctx2lo3SLO3SPR3PKB2HB5Ha_st5Hl_stS1L2HI2sp1h3PKA3ctx4HTOPS1L2HI2sp1h3PKA3ctx4HTOPS1L3HLS2sp2s03PKA3ctx2lo3ACL3SLO3DHI3SPR3PKB2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA3ctx2lo3ACL3SLO3DHI3SPR3PKB2HB5Ha_st5Hl_stS1L3HLS2sp2s03PKA3ctx2lo3ACL3SLO3DHI3SPR3PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA3ctx2lo3ACL3SLO3DHI3SPR3PKB2C02HB5Ha_st5Hl_stS2ra2sp3PKA3ctx2HB5Ha_st5Hl_stS2ra2sp3PKA3ctx2HB5Ha_st5Hl_stS2sp3PKA3ctx2HBS2sp3PKA3ctx2HBS2sp2s03PKA3ctx3SPR2HB5Ha_st5Hl_stS2ra2sp3PKA3ctx3SPR2HB5Ha_st5Hl_stS2sp2s03PKA3ctx3SPR2HB5Ha_st5Hl_stS2ra2sp3PKA3ctx3SPR2HB5Ha_st5Hl_stS2sp3PKA3ctx3SPR2HBS2sp3PKA3ctx3SPR2HBS2sp3PKA3ctx3SPR2HBS2sp3PKA3ctx3SPR2HBS1L3HLS2ra2sp3PKA3ctx2lo3SLO3SPR3PKB2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA3ctx2lo3SLO3SPR3PKB2C02HB5Ha_st5Hl_stS2sp2s03PKA3ctx3SPP2HB5Ha_st5Hl_stS2ra2sp3PKA3ctx3SPP2HB5Ha_st5Hl_stS2sp2s03PKA3ctx3SPP2HB5Ha_st5Hl_stS2ra2sp3PKA3ctx3SPP2HB5Ha_st5Hl_stS1L3HLS2sp3PKA3ctx2lo3ACL3SLO3SPA3ACP3SPR3PKB2C0S1L3HLS2sp3PKA3ctx2lo3ACL3SLO3SPA3ACP3SPR3PKBS2sp3PKA3ctxS2sp3PKA3ctxS1L3HLS2sp2lo3ACL3SLO1d2PcFS2sp3PKA3ctxS2sp3PKA3SPPS2sp3PKA3ctxS2sp3PKA3ctxS1L3HLS2sp3ctx2lo3ACL3SLO3CCES1L3HLS2sp2lo3ACL3SLO3DHI1a3Hd1S1L3HLS2sp2lo3ACL3SLO1a1B2kk2Hr2BcS2sp1a2HsS2sp3PKAS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxFSS1L3HLS2sp3PKA3ctx2lo3SLO3SPR3PKB2C0S1L3HLS2sp3PKA3ctx2lo3SLO3SPR3PKBS1L3HLS2sp3PKA3ctx2lo3SLO3SPR3PKB2C0S1L3HLS2sp3PKA3ctx2lo3SLO3SPR3PKBS2spS2sp3PKA3ctxS2sp3PKA3ctxS2spS2sp3PKA3PKBS1L2HI3HLS2sp1h2lo3SLO4HTOP1a3HinS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA3ctxS2sp3PKA4info3ctxS1L3HLS2sp3PKA2lo3SPP3ACL3SLO3ACP2K0S2KFS2KI". (* [comment removed for export] *)
  #[using="HFREE HLS SW DIMG HND CA_MSF CA_RSA CA_EC"] Lemma U_pk_free_spec : pk_free_c_stmt usegs L HI U_RSA_INFO U_EC_INFOS MT U_PK_FREE.
  Proof.
    unfold pk_free_c_stmt, U_PK_FREE. intros until lo. intros HH HPKA ALP REP OWN SPP PTOP ST ACL SLO SPA HTOP DHI MI SOK TP ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof DIMG as [DI1 DI2]. pose proof (HND _ _ _ _ HH) as NDL.
    pose proof (rw_cells_bound _ _ _ _ HPKA) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    zstep. if_cases K0; zify_cond K0.
    1-2: try (exfalso; clear -K0 SPP SLO HLS ACL ACP PKB; rewrite ?unsigned_lit in K0 by lia; lia).
    zstep. zstep. if_cases KA; zify_cond KA.
    1-2: try (exfalso; clear -KA ALP SPP SLO HLS ACL ACP PKB; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; lia).
    zstep. zstep. if_cases KI; zify_cond KI.
    { (* [comment removed for export] *)
      destruct REP as [(-> & -> & ->)|[(-> & _)|(EI & _)]].
      2:{ exfalso. clear -KI. unfold U_RSA_INFO in KI. cbn in KI. lia. }
      2:{ exfalso. clear -KI EI. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
          destruct EI as [<-|[<-|[<-|[]]]]; cbn in KI; lia. }
      zstep. zstep.
      eapply tail_walk with (LBo' := LBo); try eassumption; try reflexivity.
      - apply mo_frame_refl.
      - intros b Hb; exact Hb.
      - intros b Hb _; exact Hb.
      - intros b _ Hin. exact Hin.
      - apply heap_presx_refl. }
    assert (NI : info <> 0) by (intros ->; apply KI; reflexivity).
    destruct REP as [(E0 & _)|[(-> & _ & _ & r & RA & EO)|(EI & _ & _ & k & KP & CIN & APT & PNE & AL16 & CB256 & EO)]]; [exfalso; exact (NI E0)| |].
    - (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
        let a := eval vm_compute in (U_RSA_INFO + 80) in
        let bs := eval vm_compute in (match image_bytes usegs a 8 with Some bs => bs | None => [] end) in
        pose proof (statics_ok_cells usegs L mx a bs SOK CA_RSA ltac:(vm_compute; reflexivity)) as TB end.
      cbn [length] in TB. unfold U_RSA_INFO in *.
      zstep. zstep. if_cases KB; zify_cond KB. { exfalso; clear -KB; cbn in KB; try discriminate; lia. }
      zstep. zstep. if_cases KF; zify_cond KF. { exfalso. clear -KF. lia. } clear KF TB.
      pose proof (map_fst_iff _ _ EO) as EOf.
      pose proof RA as RAc. ddestruct RAc as (_ & _ & _ & _ & _ & _ & _ & ALL & CAL & C0 & CBr & CINr & _). unfold RSA_CTX_SIZE in CBr, CINr.
      pose proof (proj1 (Forall_forall _ _) HBR0 _ CINr) as (_ & _ & _ & CCE & CIM). cbn [fst snd] in CCE, CIM.
      pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
      pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 16%nat ST.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HH1 : HEAP usegs L HI h (LBo ++ LB) m1 mo).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h (LBo ++ LB) m m1 mo lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
      assert (RA1 : rsa_at usegs m1 (LBo ++ LB) ctx r).
      { eapply rsa_at_munch; [exact RA| exact MU| exact WM| exact (proj1 MIbox)| assumption| cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia|].
        intros d Hd HO. rewrite Forall_forall in ALL. ddestruct (ALL d Hd) as (_ & _ & _ & _ & _ & HOW). rewrite HO in HOW. ddestruct HOW as (_ & HIn & _).
        pose proof (proj1 (Forall_forall _ _) HBR0 _ HIn) as (_ & _ & _ & Pc & _). cbn [fst snd] in Pc.
        cbn [disjoint_from]. clear -Pc ACL SLO HLS. lia. }
      assert (HP1 : heap_presx usegs L (LBo ++ LB) (bv_unsigned sp) [(PKA, PKA + 16)] m m1).
      { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR0 DHI Ha.
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _). destruct b as [B kk]; cbn in Hr, Bc. lia. }
      clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      (* [comment removed for export] *)
      assert (NOL : forall a, In a (map fst ((ctx, 232) :: rsa_limb_blocks r)) -> ~ In a (map fst LB)).
      { intros a Ha. eapply NoDup_app_notin; [exact NDL|]. apply in_map_iff in Ha. ddestruct Ha as (b & <- & Hb).
        apply in_map_iff. exists b. split; [reflexivity| apply OWN; apply EO; exact Hb]. }
      assert (LEQ : lb_remove ctx (rsa_free_LB r (LBo ++ LB)) = lb_remove ctx (rsa_free_LB r LBo) ++ LB).
      { unfold rsa_free_LB. rewrite !lb_free_mpd_app. 1: apply lb_remove_app.
        - apply NOL. left. reflexivity.
        - intros HO. apply NOL. right. unfold rsa_limb_blocks. rewrite map_app. apply in_or_app. left. unfold mpd_blk. rewrite HO. left. reflexivity.
        - intros HO. apply NOL. right. unfold rsa_limb_blocks. rewrite map_app. apply in_or_app. right. unfold mpd_blk. rewrite HO. left. reflexivity. }
      assert (SUB' : forall b, In b (lb_remove ctx (rsa_free_LB r LBo) ++ LB) -> In b (LBo ++ LB)).
      { intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
        apply lb_remove_sub in Hb. unfold rsa_free_LB in Hb. do 2 apply lb_free_mpd_sub in Hb. exact Hb. }
      pose proof (U_rsa_free_wrap_spec L HI HFREE HLS SW DIMG HND) as SPF. unfold rsa_free_wrap_stmt, U_RSA_FREE_WRAP in SPF.
      eapply aevtM_cut; [ eapply SPF with (C := ctx) (r := r) (lo := lo) (LB := LBo ++ LB) (h := h);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2 | ].
      clear SPF.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO].
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia.
      ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & HP5 & SOK5).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
      match type of HH5 with HEAP _ _ _ ?hh _ _ _ => rename hh into h5 end.
      rewrite LEQ in HH5, HP5.
      pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1.
      assert (SPP' : bv_unsigned sp + -16 <= PKA) by (clear -SPP; lia).
      clear ST MI HH1.
      heap_transport HP5.
      zstep. zstep. zstep. zstep.
      release_frame FR ST5 (bv_unsigned sp).
      zstep. zstep.
      eapply tail_walk; try eassumption.
      + reflexivity.
      + intros b Hb. apply lb_remove_sub in Hb. unfold rsa_free_LB in Hb. do 2 apply lb_free_mpd_sub in Hb. exact Hb.
      + intros [B kk] Hb Hn0. cbn [fst] in Hn0. assert (Hn : ~ In B (map fst ((ctx, 232) :: rsa_limb_blocks r))) by (intros X; exact (Hn0 (proj2 (EOf B) X))).
        cbn [map fst] in Hn. apply In_lb_remove_keep; [| intros ->; apply Hn; left; reflexivity].
        unfold rsa_free_LB. apply lb_free_mpd_keep; [apply lb_free_mpd_keep; [exact Hb|]|];
          intros HO E; apply Hn; right; unfold rsa_limb_blocks; rewrite map_app; apply in_or_app;
          [right| left]; unfold mpd_blk; rewrite HO; left; cbn; symmetry; exact E.
      + intros [B kk] Hb Hin0. cbn [fst] in Hin0. pose proof (proj1 (EOf B) Hin0) as Hin. cbn [fst map] in Hin.
        assert (ND1 : List.NoDup (map fst LBo)) by (rewrite map_app in NDL; exact (List.NoDup_app_remove_r _ _ NDL)).
        destruct Hin as [E|Hin].
        * symmetry in E. revert E. eapply lb_remove_gone; [| exact Hb]. unfold rsa_free_LB. do 2 apply NoDup_lb_free_mpd. exact ND1.
        * apply lb_remove_sub in Hb. unfold rsa_free_LB in Hb. unfold rsa_limb_blocks in Hin. rewrite map_app in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin|Hin].
          -- unfold mpd_blk in Hin. destruct (md_own (r_N r)) eqn:HO; cbn in Hin; try tauto. destruct Hin as [E|[]].
             revert E. apply not_eq_sym. eapply lb_free_mpd_gone; [apply NoDup_lb_free_mpd; exact ND1| exact Hb| exact HO].
          -- unfold mpd_blk in Hin. destruct (md_own (r_E r)) eqn:HO; cbn in Hin; try tauto. destruct Hin as [E|[]].
             apply lb_free_mpd_sub in Hb. revert E. apply not_eq_sym. eapply lb_free_mpd_gone; [exact ND1| exact Hb| exact HO].
      + eapply heap_presx_trans; [| eapply heap_presx_of_pres_sub; [exact HP5| intros b Hb; exact Hb| clear; lia| clear; lia]].
        intros a Ha Hc Ho. apply HP1; [exact Ha| | exact Ho].
        destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right; exists b; split; [apply SUB'; exact Hb| exact Hr]].
    - (* [comment removed for export] *)
      assert (TB : ro_cells usegs m (info + 80) [CB 8 [Z_to_bv 8 116; Z_to_bv 8 163; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
      { pose proof (CA_EC _ EI) as CAE. revert CAE. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]]; intros CAE;
        (lazymatch goal with |- ro_cells _ ?mx (?e + 80) _ =>
           let a := eval vm_compute in (e + 80) in
           let bs := eval vm_compute in (match image_bytes usegs a 8 with Some bs => bs | None => [] end) in
           pose proof (statics_ok_cells usegs L mx a bs SOK CAE ltac:(vm_compute; reflexivity)) as TB0;
           cbn [length] in TB0; exact TB0 end). }
      assert (AI : 0 <= info < 2^64 /\ info mod 8 = 0).
      { clear -EI. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]]; split; (reflexivity || lia). }
      zstep. zstep. if_cases KB; zify_cond KB.
      1-2: try (exfalso; clear -KB AI; rewrite ?unsigned_lit in KB by lia; rewrite ?land_7_mod in KB; lia).
      zstep. zstep. if_cases KF; zify_cond KF. { exfalso. clear -KF. cbn in KF. lia. } clear KF TB.
      pose proof (map_fst_iff _ _ EO) as EOf.
      pose proof (proj1 (Forall_forall _ _) HBR0 _ CIN) as (_ & _ & _ & CCE & CIM). cbn [fst snd] in CCE, CIM.
      pose proof (conj HH I) as HHbox. pose proof (conj MI I) as MIbox.
      pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      carve_frame 16%nat ST.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      assert (HH1 : HEAP usegs L HI h (LBo ++ LB) m1 mo).
      { apply (Asn1AuxA.HEAP_munch usegs L HI h (LBo ++ LB) m m1 mo lo _ (proj1 HHbox) ACL MU WM).
        intros a Ha Hin. cbn [outside] in Hin. left. clear -Hin SLO HLS HTOP Ha. lia. }
      assert (OWNB : forall d, In d (kp_mpds k) -> md_own d = LHeap -> In (md_p d, 4 * md_n d) (LBo ++ LB)).
      { intros d Hd HO. destruct (kp_mpds_mpdr usegs MT _ _ _ _ _ KP Hd) as (_ & _ & _ & _ & _ & HOW). rewrite HO in HOW. ddestruct HOW as (_ & HIn & _). exact HIn. }
      assert (KP1 : ecp_keypair_at usegs MT m1 (LBo ++ LB) ctx k).
      { eapply ecp_keypair_at_munch; [exact KP| exact MU| exact WM| exact (proj1 MIbox)| assumption| cbn [disjoint_from]; clear -CCE ACL SLO HLS; lia|].
        intros d Hd HO. pose proof (proj1 (Forall_forall _ _) HBR0 _ (OWNB d Hd HO)) as (_ & _ & _ & Pc & _). cbn [fst snd] in Pc.
        cbn [disjoint_from]. clear -Pc ACL SLO HLS. lia. }
      assert (HP1 : heap_presx usegs L (LBo ++ LB) (bv_unsigned sp) [(PKA, PKA + 16)] m m1).
      { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn [outside]. clear -ACL SLO HLS Hc HBR0 DHI Ha.
        destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
        rewrite Forall_forall in HBR0. ddestruct (HBR0 b Hb) as (_ & _ & _ & Bc & _). destruct b as [B kk]; cbn in Hr, Bc. lia. }
      clear MU WM HHbox. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
      (* [comment removed for export] *)
      assert (NOL : forall a, In a (map fst ((ctx, 256) :: kp_blocks k)) -> ~ In a (map fst LB)).
      { intros a Ha. eapply NoDup_app_notin; [exact NDL|]. apply in_map_iff in Ha. ddestruct Ha as (b & <- & Hb).
        apply in_map_iff. exists b. split; [reflexivity| apply OWN; apply EO; exact Hb]. }
      assert (NOLd : forall d, In d (kp_mpds k) -> md_own d = LHeap -> ~ In (md_p d) (map fst LB)).
      { intros d Hd HO. apply NOL. right. rewrite kp_blocks_eq. apply in_map_iff. exists (md_p d, 4 * md_n d). split; [reflexivity|].
        apply in_flat_map_mpd_blk; [exact Hd| exact HO]. }
      assert (CINF : forall X, In (ctx, 256) X -> In (ctx, 256) (kp_free_LB k X)).
      { intros X HX. unfold kp_free_LB, grp_free_LB. apply lb_free_mpds_keep; [apply lb_free_mpds_keep; [exact HX|]|];
          intros d Hd HO E; refine (PNE d _ HO (eq_sym E)); first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]. }
      assert (LEQ : lb_remove ctx (kp_free_LB k (LBo ++ LB)) = lb_remove ctx (kp_free_LB k LBo) ++ LB).
      { unfold kp_free_LB, grp_free_LB. rewrite !lb_free_mpds_app. 1: apply lb_remove_app.
        - apply NOL. left. reflexivity.
        - intros d Hd HO. apply NOLd; [first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]| exact HO].
        - intros d Hd HO. apply NOLd; [first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd]| exact HO]. }
      assert (SUBo : forall b, In b (lb_remove ctx (kp_free_LB k LBo)) -> In b LBo).
      { intros b Hb. apply lb_remove_sub in Hb. unfold kp_free_LB, grp_free_LB in Hb. do 2 apply lb_free_mpds_sub in Hb. exact Hb. }
      assert (SUB' : forall b, In b (lb_remove ctx (kp_free_LB k LBo) ++ LB) -> In b (LBo ++ LB)).
      { intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply SUBo; exact Hb| right; exact Hb]. }
      pose proof (U_eckey_free_wrap_spec L HI HFREE HLS SW DIMG HND MT) as SPF. unfold eckey_free_wrap_stmt, U_ECKEY_FREE_WRAP in SPF.
      eapply aevtM_cut; [ eapply SPF with (A := ctx) (k := k) (lo := lo) (LB := LBo ++ LB) (h := h);
        rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by dlia; try eassumption; try reflexivity; try flia2 | ].
      { apply CINF. exact CIN. }
      clear SPF.
      intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO].
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in PO by dlia.
      ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & HP5 & SOK5).
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
      match type of HH5 with HEAP _ _ _ ?hh _ _ _ => rename hh into h5 end.
      rewrite LEQ in HH5, HP5.
      pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5. clear MK1.
      assert (SPP' : bv_unsigned sp + -16 <= PKA) by (clear -SPP; lia).
      clear ST MI HH1.
      heap_transport HP5.
      zstep. zstep. zstep. zstep.
      release_frame FR ST5 (bv_unsigned sp).
      zstep. zstep.
      assert (ND1 : List.NoDup (map fst LBo)) by (rewrite map_app in NDL; exact (List.NoDup_app_remove_r _ _ NDL)).
      eapply tail_walk; try eassumption.
      + reflexivity.
      + intros [B kk] Hb Hn0. cbn [fst] in Hn0. assert (Hn : ~ In B (map fst ((ctx, 256) :: kp_blocks k))) by (intros X; exact (Hn0 (proj2 (EOf B) X))).
        cbn [map fst] in Hn. apply In_lb_remove_keep; [| intros ->; apply Hn; left; reflexivity].
        unfold kp_free_LB, grp_free_LB. apply lb_free_mpds_keep; [apply lb_free_mpds_keep; [exact Hb|]|];
          intros d Hd HO E; apply Hn; right; rewrite kp_blocks_eq; apply in_map_iff; exists (md_p d, 4 * md_n d); (split; [cbn; symmetry; exact E|]);
          (apply in_flat_map_mpd_blk; [| exact HO]); first [apply grp_sub_kp; apply grp_free_sub; exact Hd| apply kp_tail_sub; exact Hd].
      + intros [B kk] Hb Hin0. cbn [fst] in Hin0. pose proof (proj1 (EOf B) Hin0) as Hin. cbn [fst map] in Hin. destruct Hin as [E|Hin].
        * symmetry in E. revert E. eapply lb_remove_gone; [| exact Hb]. unfold kp_free_LB, grp_free_LB. do 2 apply NoDup_lb_free_mpds. exact ND1.
        * apply lb_remove_sub in Hb. rewrite kp_blocks_eq in Hin. apply in_map_iff in Hin. ddestruct Hin as (b & Eb & Hbk). cbn in Eb.
          destruct (flat_map_mpd_blk_inv _ _ Hbk) as (d & Hd & HO & ->). cbn in Eb. subst B.
          unfold kp_free_LB, grp_free_LB in Hb. unfold kp_mpds in Hd. apply in_app_or in Hd. destruct Hd as [Hd|Hd].
          -- (* [comment removed for export] *)
             apply lb_free_mpds_sub in Hb.
             refine (lb_free_mpds_gone _ _ _ _ d ND1 Hb _ HO eq_refl).
             destruct KP as (HG & _). eapply grp_heap_in_free; [exact HG| exact Hd| exact HO].
          -- refine (lb_free_mpds_gone _ _ _ _ d _ Hb _ HO eq_refl); [apply NoDup_lb_free_mpds; exact ND1| exact Hd].
      + eapply heap_presx_trans; [| eapply heap_presx_of_pres_sub; [exact HP5| intros b Hb; exact Hb| clear; lia| clear; lia]].
        intros a Ha Hc Ho. apply HP1; [exact Ha| | exact Ho].
        destruct Hc as [Hs|[Hd|(b & Hb & Hr)]]; [left; exact Hs| right; left; exact Hd| right; right; exists b; split; [apply SUB'; exact Hb| exact Hr]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
