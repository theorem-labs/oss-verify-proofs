(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX HeapIface Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts RepRsa RepCrt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_rsa_free U_ecp_group_free U_ecp_keypair_free.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RepPk () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "WithSegs.agree_on"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.iff"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_limb_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_kp"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_mpds"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_blocks"; "WithSegs.pk_rep_c"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.in_block"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.PKC"; "pk_rep_c"; "pk_rep_c_null"; "pk_rep_c_null_inv"; "pk_rep_c_blocks"; "pk_rep_c_frame"].


Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition agree_on (m m' : mem) (A n : Z) : Prop := forall a, A <= a < A + n -> m' (wa a) = m (wa a).

#[using="Type"] Lemma agree_on_sub : forall m m' A n a k, agree_on m m' A n -> A <= a -> a + k <= A + n -> agree_on m m' a k.
Proof. intros m m' A n a k H H1 H2 x Hx. apply H. lia. Qed.

#[using="Type"] Lemma bytes_at_agree : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pbs,(3.(0.&8.))P,(4.Vsegs,R4.R2.R1.)P,(5.R5.R4.R3.(6.(7.(0.&8.)R2.)))(4.Vsegs,R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' A bs (H0 & H1 & H) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_agree : forall m m' A n, wr_at segs m A n -> agree_on m m' A n -> wr_at segs m' A n.
Proof.
  intros m m' A n (H0 & H1 & H) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (AG (A + i)) by lia. exact H.
Qed.

#[using="Type"] Lemma rw_cells_agree : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pcs,(3.$8.)P,(9.Vsegs,R4.R2.R1.)P,(5.R5.R4.R3.(6.(:.R2.)))(9.Vsegs,R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' A cs [[Hwf Hb] Hw] AG. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; [exact Hb|]. rewrite cells_bytes_length by exact Hwf. exact AG.
  - eapply wr_at_agree; eauto.
Qed.

#[using="Type"] Lemma u32arr_agree : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))P,(;.Vsegs,R4.R2.R1.)P,(5.R5.R4.R3.(<.+4.(6.(7.(0.&40.)R2.))))(;.Vsegs,R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' A ws [Hb Hw] AG. split.
  - eapply bytes_at_agree; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul. intros a Ha. apply AG. lia.
  - eapply wr_at_agree; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_ro_any : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PP,$2.Pbs,(3.(0.&8.))P,(4.Vsegs,R4.R2.R1.)P,Pi,$2.P,(=.(>.=R1.)(?.R1.(6.(7.(0.&8.)R3.))))(10.$11.(12.Vsegs,(13.(14.R5.R2.)))$15.)P,(16.Vsegs,R6.)P,(16.Vsegs,R6.)(4.Vsegs,R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros m m' P bs (H0 & H1 & H) RO MI MI'. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). unfold mrd.
  assert (E : m (wa (P + Z.of_nat i)) = None).
  { destruct (m (wa (P + Z.of_nat i))) as [b|] eqn:Em; [| reflexivity]. exfalso.
    pose proof (MI _ _ Em) as R. rewrite (RO (Z.of_nat i)) in R by lia. discriminate. }
  assert (E' : m' (wa (P + Z.of_nat i)) = None).
  { destruct (m' (wa (P + Z.of_nat i))) as [b|] eqn:Em; [| reflexivity]. exfalso.
    pose proof (MI' _ _ Em) as R. rewrite (RO (Z.of_nat i)) in R by lia. discriminate. }
  rewrite E, E'. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpdr_at_agree : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PLB,(3.$17.)PLB',(3.(18.$2.$2.))Pd,$19.P,(1:.Vsegs,R5.R3.R1.)P,(16.Vsegs,R6.)P,(16.Vsegs,R6.)P,(5.R8.R7.(1;.R4.)+10.)P,P,(10.$1<.(1=.R5.)$1>.)(=.(5.R:.R9.(1?.R6.)(<.+4.(20.R6.)))(21.(18.$2.$2.)(22.$2.$2.(1?.R6.)(<.+4.(20.R6.)))R7.))(1:.Vsegs,R9.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB' d (HR & HAL & HPOS & HL & HN & HO) MI MI' AG AH.
  split; [| split; [exact HAL| split; [exact HPOS| split; [exact HL| split; [exact HN|]]]]].
  - eapply rw_cells_agree; [exact HR|]. cbn [cells_size csize Nat.add mpi_cells]. exact AG.
  - destruct (md_own d); [exact HO| |].
    + destruct HO as (H1 & H2 & H3 & H4). destruct (AH eq_refl) as [AGL HIN]. split; [exact H1|]. split; [exact HIN|]. split; [exact H3|].
      eapply u32arr_agree; [exact H4|]. rewrite HL. exact AGL.
    + destruct HO as (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [| exact H5].
      eapply bytes_at_ro_any; [exact H4| | exact MI| exact MI']. intros i Hi. apply H5. rewrite u32s_length, Nat2Z.inj_mul, HL in Hi. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma in_flat_map_mpd_blk : forall d ds, In d ds -> md_own d = LHeap -> In (md_p d, 4 * md_n d) (flat_map mpd_blk ds).
Proof. intros d ds Hd HO. apply in_flat_map. exists d. split; [exact Hd|]. unfold mpd_blk. rewrite HO. left. reflexivity. Qed.

#[using="Type"] Lemma flat_map_mpd_blk_inv : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pb,$17.Pds,(3.$19.)P,(21.$17.R2.(23.$19.$17.$24.R1.))(25.$19.Ld,$19.(=.(21.$19.R1.R3.)(=.(10.$1<.(1=.R1.)$1>.)(10.$17.R4.(22.$2.$2.(1?.R1.)(<.+4.(20.R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros b ds H. apply in_flat_map in H. destruct H as (d & Hd & Hb). exists d. split; [exact Hd|].
  unfold mpd_blk in Hb. destruct (md_own d); cbn in Hb; [destruct Hb| | destruct Hb]. destruct Hb as [<-|[]]. split; reflexivity.
Qed.

#[using="Type"] Lemma map_fst_iff : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pl1,(3.$17.)Pl2,(3.$17.)P,Pb,$17.(26.(21.$17.R1.R3.)(21.$17.R1.R2.))Pa,$2.(26.(21.$2.R1.(27.(18.$2.$2.)$2.(28.$2.$2.)R4.))(21.$2.R1.(27.(18.$2.$2.)$2.(28.$2.$2.)R3.)))")
(* [comment removed for export] *).
Proof.
  intros l1 l2 H a. rewrite !in_map_iff. split; intros (b & E & Hb); exists b; split; [exact E| apply H; exact Hb| exact E| apply H; exact Hb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pk_rep_c (RSAI : Z) (ECIS : list Z) (MT : list modp_ent)
    (m : mem) (LB : list blk) (PKA info ctx : Z) (owned : list blk) : Prop := ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "(29.(=.(10.$2.O3.=)(=.(10.$2.O2.=)(10.(3.$17.)O1.(2:.$17.))))(29.(=.(10.$2.O3.O9.)(=.(2;.(10.$2.O9.=))(=.(16.Vsegs,O6.)(25.$2<.Lr,$2<.(=.(2=.Vsegs,O6.O5.O2.R1.)Pb,$17.(26.(21.$17.R1.O1.)(21.$17.R1.(2>.(18.$2.$2.)(22.$2.$2.O2.+>8.)(2?.R2.)))))))))(=.(21.$2.O3.O8.)(=.(2;.(10.$2.O3.=))(=.(16.Vsegs,O6.)(25.$30.Lk,$30.(=.(31.Vsegs,O7.O6.O5.O2.R1.)(=.(21.(18.$2.$2.)(22.$2.$2.O2.+100.)O5.)(=.(32.(33.R1.))(=.Pd,$19.P,(21.$19.R1.(33.R2.))P,(10.$1<.(1=.R2.)$1>.)(2;.(10.$2.(1?.R3.)O2.))(=.(10.$2.(34.O2.+10.)=)(=.(>.(14.O2.+100.)(35.+2.+40.))Pb,$17.(26.(21.$17.R1.O1.)(21.$17.R1.(2>.(18.$2.$2.)(22.$2.$2.O2.+100.)(36.R2.))))))))))))))))")
(* [comment removed for export] *).

Variable RSAI : Z.
Variable ECIS : list Z.
Variable MT : list modp_ent.

#[using="Type"] Lemma pk_rep_c_null : forall m LB PKA, pk_rep_c RSAI ECIS MT m LB PKA 0 0 [].
Proof. intros. left. repeat split; reflexivity. Qed.

#[using="Type"] Lemma pk_rep_c_null_inv : forall m LB PKA ctx owned, pk_rep_c RSAI ECIS MT m LB PKA 0 ctx owned -> owned = [].
Proof. intros m LB PKA ctx owned [(_ & _ & E)|[(E & NE & _)|(_ & NE & _)]]; [exact E| exfalso; apply NE; symmetry; exact E| exfalso; apply NE; reflexivity]. Qed.

#[using="Type"] Lemma rsa_limb_blocks_in : forall m LB C r b, rsa_at segs m LB C r -> In b (rsa_limb_blocks r) -> In b LB.
Proof.
  intros m LB C r b RA Hb. destruct RA as (_ & _ & _ & _ & _ & _ & _ & ALL & _).
  unfold rsa_limb_blocks in Hb. apply in_app_or in Hb.
  assert (R : forall d, mpdr_at segs m LB d -> In b (mpd_blk d) -> In b LB).
  { intros d (_ & _ & _ & _ & _ & HOW) Hbd. unfold mpd_blk in Hbd. destruct (md_own d); cbn in Hbd; [destruct Hbd| | destruct Hbd].
    destruct Hbd as [<-|[]]. destruct HOW as (_ & HIn & _). exact HIn. }
  rewrite Forall_forall in ALL.
  destruct Hb as [Hb|Hb]; (eapply R; [apply ALL| exact Hb]); unfold rsa_mpds; cbn; auto.
Qed.

#[using="Type"] Lemma kp_mpds_mpdr : forall m LB A k d, ecp_keypair_at segs MT m LB A k -> In d (kp_mpds k) -> mpdr_at segs m LB d.
Proof.
  intros m LB A k d (HG & _ & MD & _ & (_ & _ & _ & MX & MY & MZ) & _) Hd.
  unfold kp_mpds in Hd. apply in_app_or in Hd. destruct Hd as [Hd|[<-|Hd]].
  - destruct HG as (_ & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & GX & GY & GZ) & MN & _).
    unfold grp_mpds in Hd. cbn [app In pt_mpds] in Hd. destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption.
  - exact MD.
  - cbn [In pt_mpds] in Hd. destruct Hd as [<-|[<-|[<-|[]]]]; assumption.
Qed.

#[using="Type"] Lemma kp_blocks_eq : forall k, kp_blocks k = flat_map mpd_blk (kp_mpds k).
Proof.
  intros k. unfold kp_blocks, kp_mpds, grp_blocks, pt_blocks. rewrite flat_map_app. cbn [flat_map]. reflexivity.
Qed.

#[using="Type"] Lemma kp_blocks_in : forall m LB A k b, ecp_keypair_at segs MT m LB A k -> In b (kp_blocks k) -> In b LB.
Proof.
  intros m LB A k b KP Hb. rewrite kp_blocks_eq in Hb. destruct (flat_map_mpd_blk_inv _ _ Hb) as (d & Hd & HO & ->).
  destruct (kp_mpds_mpdr _ _ _ _ _ KP Hd) as (_ & _ & _ & _ & _ & HOW). rewrite HO in HOW. destruct HOW as (_ & HIn & _). exact HIn.
Qed.

#[using="Type"] Lemma pk_rep_c_blocks : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))PLB,(3.$17.)PPKA,$2.Pinfo,$2.Pctx,$2.Powned,(3.$17.)P,(37.VRSAI,VECIS,VMT,R6.R5.R4.R3.R2.R1.)Pb,$17.P,(21.$17.R1.R3.)(21.$17.R2.R8.)")
(* [comment removed for export] *).
Proof.
  intros m LB PKA info ctx owned [(_ & _ & ->)|[(_ & _ & _ & r & RA & EO)|(_ & _ & _ & k & KP & CIN & _ & _ & _ & _ & EO)]] b Hb; [destruct Hb| |]; apply EO in Hb.
  - destruct Hb as [<-|Hb]; [| eapply rsa_limb_blocks_in; eauto]. destruct RA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CIN & _). exact CIN.
  - destruct Hb as [<-|Hb]; [exact CIN| eapply kp_blocks_in; eauto].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma agree_of_blocks : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Powned,(3.$17.)Pm,Px,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))PA,$2.Pn,$2.P,Pa,$2.P,(38.R6.R1.)(10.(1.(0.&8.))A1.R5.(13.R2.)A1.R6.(13.R2.))P,(21.(18.$2.$2.)(22.$2.$2.R3.R2.)R6.)(5.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros owned m m' A n H HIn a Ha. apply H. exists (A, n). split; [exact HIn| cbn; lia]. Qed.

#[using="Type"] Lemma mpdr_at_frame_in : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PLB,(3.$17.)PLB',(3.$17.)Powned,(3.$17.)Pd,$19.PC,$2.Psz,$2.P,(1:.Vsegs,R8.R6.R3.)P,(16.Vsegs,R9.)P,(16.Vsegs,R9.)P,Pb,$17.P,(21.$17.R1.R8.)(21.$17.R2.R:.)P,Pa,$2.P,(38.R9.R1.)(10.(1.(0.&8.))A1.R=.(13.R2.)A1.R>.(13.R2.))P,(21.(18.$2.$2.)(22.$2.$2.R7.R6.)R9.)P,(>.R8.(1;.R9.))P,(>.(14.(1;.R:.)+10.)(14.R9.R8.))P,P,(10.$1<.(1=.R;.)$1>.)(21.(18.$2.$2.)(22.$2.$2.(1?.R<.)(<.+4.(20.R<.)))R=.)(1:.Vsegs,R10.R>.R<.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB' owned d C sz MD MI MI' HS HA HIn H1 H2 HB.
  eapply mpdr_at_agree; [exact MD| exact MI| exact MI'| |].
  - eapply agree_on_sub; [eapply agree_of_blocks; [exact HA| exact HIn]| exact H1| exact H2].
  - intros HO. split; [eapply agree_of_blocks; [exact HA| apply HB; exact HO]| apply HS; apply HB; exact HO].
Qed.

#[using="Type"] Lemma pk_rep_c_frame : ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PLB,(3.$17.)PLB',(3.$17.)PPKA,$2.Pinfo,$2.Pctx,$2.Powned,(3.$17.)P,(37.VRSAI,VECIS,VMT,R8.R6.R4.R3.R2.R1.)P,(16.Vsegs,R8.)P,Pb,$17.P,(21.$17.R1.R4.)(21.$17.R2.R9.)P,Pa,$2.P,(38.R5.R1.)(10.(1.(0.&8.))A1.R<.(13.R2.)A1.R=.(13.R2.))(37.VRSAI,VECIS,VMT,R;.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros m m' LB LB' PKA info ctx owned REP MI' HS HA.
  destruct REP as [Z0|[(EI & NE & MI & r & RA & EO)|(EI & NE & MI & k & KP & CIN & APT & PNE & AL16 & CB & EO)]].
  - left. exact Z0.
  - right; left. split; [exact EI|]. split; [exact NE|]. split; [exact MI'|]. exists r. split; [| exact EO].
    destruct RA as (HD & HT & AN & AE & FN & FE & LEN & ALL & CAL & C0 & CBr & CINr & PN & PE & PNE).
    assert (AG : agree_on m m' ctx 232) by (eapply agree_of_blocks; [exact HA| apply EO; left; reflexivity]).
    unfold rsa_at. repeat match goal with |- _ /\ _ => split end; try assumption.
    + eapply rw_cells_agree; [exact HD|]. cbn [cells_size csize Nat.add rsa_head_cells]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + eapply rw_cells_agree; [exact HT|]. cbn [cells_size csize Nat.add rsa_tail_cells]. eapply agree_on_sub; [exact AG| lia| unfold RSA_CTX_SIZE in *; cbn; lia].
    + clear -LEN; lia. + clear -LEN; lia.
    + rewrite Forall_forall in ALL |- *. intros d Hd.
      destruct (rsa_mpds_addr ctx r d (conj AN AE) Hd) as (A1 & A2 & _).
      eapply mpdr_at_frame_in with (owned := owned) (C := ctx) (sz := 232);
        [apply ALL; exact Hd| exact MI| exact MI'| exact HS| exact HA| apply EO; left; reflexivity| lia| lia|].
      intros HO. apply EO. right. unfold rsa_limb_blocks, rsa_mpds, rsa_zero_mpds in *. cbn [In] in Hd.
      destruct Hd as [<-|[<-|Hd]].
      * apply in_or_app. left. unfold mpd_blk. rewrite HO. left. reflexivity.
      * apply in_or_app. right. unfold mpd_blk. rewrite HO. left. reflexivity.
      * exfalso. apply in_map_iff in Hd. destruct Hd as (o & <- & _). cbn in HO. discriminate.
    + apply HS. apply EO. left. reflexivity.
  - right; right. split; [exact EI|]. split; [exact NE|]. split; [exact MI'|]. exists k.
    assert (AG : agree_on m m' ctx 256) by (eapply agree_of_blocks; [exact HA| apply EO; left; reflexivity]).
    assert (MF : forall d, In d (kp_mpds k) -> mpdr_at segs m' LB' d).
    { intros d Hd. pose proof (kp_mpds_mpdr _ _ _ _ _ KP Hd) as MD.
      destruct KP as (HG & ED & _ & _ & (EX & EY & EZ & _) & _).
      destruct HG as (_ & _ & _ & EP & EA & EB & EN & _ & _ & _ & (GX & GY & GZ & _) & _).
      assert (HR : ctx <= md_addr d /\ md_addr d + 16 <= ctx + 256).
      { unfold kp_mpds, grp_mpds in Hd. cbn [app In pt_mpds] in Hd.
        destruct Hd as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; lia. }
      eapply mpdr_at_frame_in with (owned := owned) (C := ctx) (sz := 256);
        [exact MD| exact MI| exact MI'| exact HS| exact HA| apply EO; left; reflexivity| lia| lia|].
      intros HO. apply EO. right. rewrite kp_blocks_eq. apply in_flat_map_mpd_blk; [exact Hd| exact HO]. }
    destruct KP as (HG & ED & MD & FD & (EX & EY & EZ & MX & MY & MZ) & FQ).
    split; [| split; [apply HS; apply EO; left; reflexivity| split; [exact APT| split; [exact PNE| split; [exact AL16| split; [exact CB| exact EO]]]]]].
    split; [| split; [exact ED| split; [apply MF; unfold kp_mpds; apply in_or_app; right; left; reflexivity| split; [exact FD| split; [| exact FQ]]]]].
    + destruct HG as (HDc & AL & POS & EP & EA & EB & EN & MP & MA & MB & (GX & GY & GZ & PX & PY & PZ) & MN & HTc & REST).
      unfold ecp_group_at. repeat match goal with |- _ /\ _ => split end; try assumption;
        try (apply MF; unfold kp_mpds, grp_mpds; cbn [app In pt_mpds]; tauto).
      all: lazymatch goal with
           | |- rw_cells _ _ _ (grp_head_cells _) =>
               eapply rw_cells_agree; [exact HDc|]; cbn [cells_size csize Nat.add grp_head_cells]; eapply agree_on_sub; [exact AG| lia| cbn; lia]
           | |- rw_cells _ _ _ (grp_tail_cells _) =>
               eapply rw_cells_agree; [exact HTc|]; cbn [cells_size csize Nat.add grp_tail_cells]; eapply agree_on_sub; [exact AG| lia| cbn; lia]
           | |- ecp_point_at _ _ _ _ _ =>
               split; [exact GX|]; split; [exact GY|]; split; [exact GZ|];
               split; [| split]; apply MF; unfold kp_mpds, grp_mpds; cbn [app In pt_mpds]; tauto
           | |- _ => clear -REST; tauto
           end.
    + split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [| split]; apply MF; unfold kp_mpds; cbn [app In pt_mpds]; apply in_or_app; right; right; cbn; tauto.
Qed.

End WithSegs.

(* [comment removed for export] *)
Definition PKC_inst (segs : list Segment) (RSAI : Z) (ECIS : list Z) (MT : list modp_ent) : pk_class segs := ltac2:(CDefT.buildp (gd_tbl_RepPk ()) "(39.O4.(3:.O4.O3.O2.O1.)(3;.O4.O3.O2.O1.)(3<.O4.O3.O2.O1.)(3=.O4.O3.O2.O1.)(3>.O4.O3.O2.O1.))")
(* [comment removed for export] *).
