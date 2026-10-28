(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_ecp_group_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_rsa_free () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.mpd_z"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "rsa_free_LB"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "rsa_free_post"].


Definition U_RSA_FREE : Z := 0x2a7ec.
(* [comment removed for export] *)
Notation RSA_FREE_STACK := 48 (only parsing).

(* [comment removed for export] *)
Definition rsa_free_seq (C : Z) (r : rsa_st) : list mpd := ltac2:(CDefT.buildp (gd_tbl_P_rsa_free ()) "(0.$1.(2.(3.O2.+<0.))(0.$1.(2.(3.O2.+=0.))(0.$1.(2.(3.O2.+90.))(0.$1.(2.(3.O2.+30.))(0.$1.(2.(3.O2.+50.))(0.$1.(2.(3.O2.+40.))(0.$1.(4.O1.)(0.$1.(5.O1.)(0.$1.(2.(3.O2.+;0.))(0.$1.(2.(3.O2.+:0.))(0.$1.(2.(3.O2.+80.))(0.$1.(2.(3.O2.+70.))(0.$1.(2.(3.O2.+60.))(6.$1.))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rsa_free_LB (r : rsa_st) (LB : list blk) : list blk := lb_free_mpd (r_N r) (lb_free_mpd (r_E r) LB).

Lemma rsa_free_LB_eq : forall C r LB, lb_free_mpds (rsa_free_seq C r) LB = rsa_free_LB r LB.
Proof. reflexivity. Qed.

Lemma rsa_free_seq_mpds : forall C r d, In d (rsa_free_seq C r) <-> In d (rsa_mpds C r).
Proof. intros C r d. unfold rsa_free_seq, rsa_mpds, rsa_zero_mpds, rsa_zero_offs. cbn [map In]. tauto. Qed.

Lemma rsa_free_seq_heap : forall C r d, In d (rsa_free_seq C r) -> md_own d = LHeap -> d = r_N r \/ d = r_E r.
Proof.
  intros C r d H O. unfold rsa_free_seq in H. cbn [In] in H.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
    first [subst d; cbn in O; discriminate | subst d; auto | destruct H].
Qed.

Lemma rsa_free_LB_keep : ltac2:(CDefT.buildp (gd_tbl_P_rsa_free ()) "Pr,$7.PLB,(8.$9.)PB,$:.Pk,$:.P,(;.(<.$:.$:.)(=.$:.$:.R2.R1.)R3.)P,P,(>.$?.(10.(5.R5.))$11.)(12.(>.$:.(13.(5.R6.))R4.))P,P,(>.$?.(10.(4.R6.))$11.)(12.(>.$:.(13.(4.R7.))R5.))(;.(<.$:.$:.)(=.$:.$:.R5.R4.)(14.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros r LB B k H HN HE. unfold rsa_free_LB.
  apply lb_free_mpd_keep; [apply lb_free_mpd_keep; [exact H|]|]; intros O E; [apply (HE O)| apply (HN O)]; congruence.
Qed.

Lemma rsa_free_LB_sub : forall r LB b, In b (rsa_free_LB r LB) -> In b LB.
Proof. intros r LB b H. unfold rsa_free_LB in H. do 2 apply lb_free_mpd_sub in H. exact H. Qed.

Definition rsa_free_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (C : Z) (r : rsa_st) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_free ()) "Lc,$15.(16.(17.&40.)Lt0,(17.&40.)(16.(17.&40.)Lt1,(17.&40.)(16.(17.&40.)Lt2,(17.&40.)(16.(17.&40.)La0,(17.&40.)(16.(17.&40.)La1,(17.&40.)(16.(17.&40.)La2,(17.&40.)(16.(17.&40.)La3,(17.&40.)(16.(17.&40.)La4,(17.&40.)(16.(17.&40.)La5,(17.&40.)(16.(17.&40.)La6,(17.&40.)(16.(17.&40.)La7,(17.&40.)(16.(17.&40.)Lt3,(17.&40.)(16.(17.&40.)Lt4,(17.&40.)(16.(17.&40.)Lt5,(17.&40.)(16.(17.&40.)Lt6,(17.&40.)(16.P,(17.&40.)(18.(17.&8.))Lm',P,(17.&40.)(18.(17.&8.))(16.$19.Lmo',$19.(16.(1:.O1<.O1;.O1:.)Lh',(1:.O1<.O1;.O1:.)(1;.(>.$15.R13.(1<.(1=.(1>.O19.O18.O17.O16.R12.R11.R10.O15.O14.R?.R>.R=.R<.R;.R:.R9.R8.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R7.R6.R5.R4.)O9.(1?.O19.)O8.(20.(17.&40.))R3.(21.O1<.))R2.))(1;.(22.O1<.R3.)(1;.(23.O1<.R3.O3.(24.&40.O18.))(1;.(25.O1.R2.)(1;.(>.$:.(26.O1<.O1;.O1:.R1.)(26.O1<.O1;.O1:.O7.))(1;.(27.O1<.O1;.O1:.R1.(14.O4.O6.)R3.R2.)(1;.(;.(<.$:.$:.)(=.$:.$:.O5.$28.)(14.O4.O6.))(1;.(29.O1<.O1;.(14.O4.O6.)(24.&40.O18.)(0.(<.$:.$:.)(=.$:.$:.O5.(3.O5.$28.))(6.(<.$:.$:.)))O2.R3.)(2:.O1<.O1;.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_free_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_free ()) "Pra,(17.&40.)Psp,(17.&40.)Pgp,(17.&40.)Ptp,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Ps0,(17.&40.)Ps1,(17.&40.)Pa0,(17.&40.)Pa1,(17.&40.)Pa2,(17.&40.)Pa3,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)Ps2,(17.&40.)Ps3,(17.&40.)Ps4,(17.&40.)Ps5,(17.&40.)Ps6,(17.&40.)Ps7,(17.&40.)Ps8,(17.&40.)Ps9,(17.&40.)Ps10,(17.&40.)Ps11,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)PF,(2;.&5.(17.&40.))Pfc,(17.&20.)Pm,P,(17.&40.)(18.(17.&8.))Pmo,$19.Ph,(1:.O5.O4.O3.)PLB,(8.$9.)PC,$:.Pr,$7.Plo,$:.P,(27.O5.O4.O3.R5.R4.R7.R6.)P,(2<.O5.R8.R5.R4.R3.)P,(23.O5.R9.R3.(24.&40.R29.))P,(2=.R4.(2>.(2>.(24.&40.R2:.)+30.)(2?.O4.)))P,(2=.(30.O4.)R5.)P,(2=.(24.&40.R2<.)(26.O5.O4.O3.R:.))P,(>.$:.(31.(24.&40.R2=.)+10.)=)P,(2=.(32.O4.)(30.O4.))P,(>.(17.&40.)R2=.(33.&40.(34.O4.)))P,(22.O5.R10.)P,(2:.O5.O4.R11.)P,(35.O4.O1.+8.)P,(>.$:.(31.(24.&40.R34.)+2.)=)P,(>.(17.&40.)R2<.(33.&40.R10.))(36.O5.R14.(37.O5.O4.O3.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R13.R12.R11.R10.R?.R15.R14.)(1=.(1>.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(33.&40.O2.)R16.(20.(17.&40.))R15.(21.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Ltac rs_in := cbn [In rsa_free_seq]; repeat (first [left; reflexivity | right]).
Ltac rs_side spo ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA restF :=
  rewrite ?(unsigned_lit spo) by lia;
  first
    [ exact HBR | exact HAP | exact CW | exact ND | exact FF1 | exact DISF | exact HH | exact HTc | exact LIV | exact CH | exact PXA
    | exact ST | exact TP | exact MI | exact SOK | exact CA | exact ACLx
    | lazymatch goal with
      | |- forall b, In b _ -> In b _ =>
          first [ intros b Hb; exact (lb_free_mpds_sub restF _ b Hb)
                | intros b Hb; do 14 (try (apply lb_free_mpd_sub in Hb)); exact Hb ]
      | |- _ = LHeap -> ~ In _ _ =>
          match goal with NI : forall d, In d _ -> md_own d = LHeap -> ~ In _ _ |- _ => intros O; apply NI; [rs_in| exact O] end
      | |- In _ _ => rs_in
      | |- md_addr _ = _ => first [exact AN | exact AE | reflexivity]
      | |- _ <> LStatic => first [exact OWNN | exact OWNE | cbn; discriminate]
      | |- Forall _ _ =>
          repeat apply Forall_cons; try apply Forall_nil;
          first [ (* [comment removed for export] *) split; [ intros _; rs_in | cbn [md_addr mpd_z]; rewrite ?AN, ?AE; lia ]
                | (* [comment removed for export] *) cbn [fst snd cells_size csize Nat.add mpi_cells length rsa_head_cells rsa_tail_cells]; lia ]
      | |- _ = Z_to_bv 64 _ => reflexivity
      end
    | cbn [md_addr mpd_z]; rewrite ?AN, ?AE; lia
    | match goal with |- ?g => idtac "UNSOLVED" g end ].

(* [comment removed for export] *)
Ltac rs_step SPF xC xr xd xX :=
  lazymatch goal with
  | HH : HEAP ?segs ?L ?HI _ ?LBc _ _, PXA : heap_presx _ _ ?xLBf ?xSP _ ?xm0 _,
    HTc : heap_top _ _ _ _ = heap_top _ _ _ ?xh0, ST : stk _ _ ?xlo _, HLS : 0 <= hl_stack _, DIMG : hl_img_lo _ <= hl_data_lo _ /\ _ |- _ =>
      eapply (free_step segs L HI _ _ SPF HLS DIMG) with (d0 := xd) (X0 := xX) (A := xC) (sz := 232) (SP := xSP) (h0 := xh0) (m0 := xm0) (lo := xlo)
        (FR := rsa_free_seq xC xr) (LBf := xLBf)
  end.

Ltac rs_free1 SPF xC xr spo d X rest ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI :=
  rs_step SPF xC xr d X;
  [ rs_side spo ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA rest .. | ];
  fs_post spo HI HH LIV CH PXA ST MI SOK MF HTc MK.

Section RF.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  #[using="HFREE HLS SW DIMG HND"] Lemma U_rsa_free_spec : rsa_free_stmt usegs L HI U_RSA_FREE U_MEMSET_FUNC.
  Proof.
    unfold rsa_free_stmt, U_RSA_FREE. intros until lo.
    intros HH RA_ ST SLO ACL HTOP SPA DHI TP MI SOK CA RA ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as NDL. pose proof DIMG as [DI1 DI2].
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    ddestruct RA_ as (HD & HT & AN & AE & [OWNN _] & [OWNE _] & LEN & ALL & CAL & C0 & CB & CIN & PN & PE & PNE).
    unfold RSA_CTX_SIZE in CB, CIN. unfold rsa_head_cells in HD. unfold rsa_tail_cells in HT.
    pose proof (proj1 (Forall_forall _ _) HBR _ CIN) as (_ & _ & _ & C4_ & C5_). cbn [fst snd] in C4_, C5_.
    set (LBf := lb_free_mpds (rsa_free_seq C r) LB).
    assert (SUBF : forall b, In b LBf -> In b LB) by (intros b Hb; eapply lb_free_mpds_sub; exact Hb).
    assert (HBRf : Forall (fun b => block_range L (fst b) (snd b)) LBf) by (eapply block_range_forall_sub; [exact HBR| exact SUBF]).
    assert (CINf : In (C, 232) LBf).
    { subst LBf. rewrite rsa_free_LB_eq. apply rsa_free_LB_keep; [exact CIN| exact PN| exact PE]. }
    assert (CW : client_wrange L LBf (bv_unsigned sp) (heap_top usegs L HI h) C 232).
    { intros a Ha. right; right. exists (C, 232). split; [exact CINf| cbn; lia]. }
    assert (ND : C + 232 <= hl_data_lo L \/ hl_data_hi L <= C) by lia.
    assert (ALLM : forall d, In d (rsa_free_seq C r) -> mpdr_at usegs m LB d).
    { intros d Hd. apply (proj1 (Forall_forall _ _) ALL). apply (proj1 (rsa_free_seq_mpds C r d)). exact Hd. }
    assert (NI : forall d, In d (rsa_free_seq C r) -> md_own d = LHeap -> ~ In (md_p d, 4 * md_n d) LBf).
    { intros d Hd O. subst LBf. apply lb_free_mpds_notin; assumption. }
    assert (DISF : mpds_apart (rsa_free_seq C r)).
    { intros d1 d2 H1 H2 NE O1 O2.
      destruct (rsa_free_seq_heap _ _ _ H1 O1) as [-> | ->]; destruct (rsa_free_seq_heap _ _ _ H2 O2) as [-> | ->];
        [exfalso; apply NE; reflexivity| exact (PNE O1 O2)| intros E; exact (PNE O2 O1 (eq_sym E))| exfalso; apply NE; reflexivity]. }
    pose proof (free_facts_intro usegs L HI h LB LBf m mo (bv_unsigned sp) _ C 232 (rsa_free_seq C r) HH NDL ALLM CW SUBF NI DHI ltac:(lia) ltac:(lia) DI1 DI2) as FF1.
    assert (ACLx : alloc_ceiling <= lo) by exact ACL.
    assert (SX : C + 232 <= lo \/ bv_unsigned sp <= C) by lia.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zstep. zstep; if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; change 7 with (Z.ones 3) in K1; rewrite Z.land_ones in K1 by lia; change (2 ^ 3) with 8 in K1; lia|].
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (lock MI) as MI00. pose proof (conj HH I) as HH0. clear HH.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    destruct HH0 as [HH _].
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (LIV : Forall (mpdr_at usegs m1 LB) (rsa_free_seq C r)).
    { eapply (lives_munch usegs L m m1); [| exact MU| exact WM| exact (unlock _ MI00)| exact MI| exact HBR| | intros a n Ha Hn; cbn; lia].
      - apply Forall_forall. exact ALLM.
      - unfold rsa_free_seq. repeat apply Forall_cons; try apply Forall_nil; cbn [md_addr mpd_z]; rewrite ?AN, ?AE; cbn; lia. }
    assert (HH1 : HEAP usegs L HI h LB m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia. }
    assert (PXA : heap_presx usegs L LBf (bv_unsigned sp) [(C, C + 232)] m m1).
    { eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C_|[C_|([b k] & Hb & C_)]]; [lia| lia|]. cbn in C_. pose proof (proj1 (Forall_forall _ _) HBRf _ Hb) as (_ & _ & _ & B4 & _). cbn in B4. lia. }
    pose proof (eq_refl (heap_top usegs L HI h)) as HTc. pose proof (mo_frame_refl mo) as MF.
    clear ALL ALLM HH MU WM. rename HH1 into HH.
    match goal with F : rw_cells usegs m1 (bv_unsigned sp + -16) ?cs |- _ =>
      assert (CH : Forall (fun ac => rw_cells usegs m1 (fst ac) (snd ac))
                     [(C, [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_len r))]); (C + 224, [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]); (bv_unsigned sp - 16, cs)])
        by (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [exact HD| exact HT| replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; exact F]);
      clear HD HT F end.
    pose proof (U_mpi_free_spec L HI HFREE HLS SW DIMG) as SPF.
    zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 192)) (C + 192)
      [mpd_z (C + 208); mpd_z (C + 144); mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 208)) (C + 208)
      [mpd_z (C + 144); mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 144)) (C + 144)
      [mpd_z (C + 48); mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 48)) (C + 48)
      [mpd_z (C + 80); mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 80)) (C + 80)
      [mpd_z (C + 64); r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 64)) (C + 64)
      [r_E r; r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rewrite <- AE. rs_free1 SPF C r (bv_unsigned sp + -16) (r_E r) (md_addr (r_E r))
      [r_N r; mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rewrite <- AN. rs_free1 SPF C r (bv_unsigned sp + -16) (r_N r) (md_addr (r_N r))
      [mpd_z (C + 176); mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 176)) (C + 176)
      [mpd_z (C + 160); mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 160)) (C + 160)
      [mpd_z (C + 128); mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 128)) (C + 128)
      [mpd_z (C + 112); mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    zstep. zstep. rs_free1 SPF C r (bv_unsigned sp + -16) (mpd_z (C + 112)) (C + 112)
      [mpd_z (C + 96)] ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    (* [comment removed for export] *)
    fa_get CH 14%nat CFR. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) in CFR by lia.
    zstep. zstep. zstep. release_frame CFR ST (bv_unsigned sp). zstep.
    lazymatch type of CH with Forall ?P ?CS =>
      let pre := eval cbn [removelast] in (removelast CS) in
      let P' := eval pattern (bv_unsigned sp - 16) in P in
      assert (CH' : Forall P pre) by (apply (proj1 (proj1 (Forall_app P pre [(bv_unsigned sp - 16, [C8 s0; C8 ra])]) CH)));
      clear CH; rename CH' into CH end.
    zstep. rs_free1 SPF C r (bv_unsigned sp) (mpd_z (C + 96)) (C + 96) ([] : list mpd) ACLx HBR HAP CW ND FF1 DISF OWNN OWNE AN AE HH HTc LIV CH PXA ST TP MI SOK CA MF MK HI.
    (* [comment removed for export] *)
    apply aevtM_done. unfold rsa_free_post. deexists 17.
    lazymatch goal with HH : HEAP _ _ _ ?h2 _ _ _ |- _ => exists h2 end.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HTc|].
    subst LBf. rewrite rsa_free_LB_eq in PXA, CINf.
    split. { lazymatch type of HH with HEAP _ _ _ _ ?l _ _ => change l with (lb_free_mpds (rsa_free_seq C r) LB) in HH end.
             rewrite rsa_free_LB_eq in HH. exact HH. }
    split; [exact CINf|]. split; [exact PXA| exact SOK].
  Qed.
End RF.
