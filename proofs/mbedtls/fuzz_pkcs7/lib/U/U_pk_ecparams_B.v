(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_pk_ecparams_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_ecparams_B () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.ecp_ids_state"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_sinv.ecp_ids_lok"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.lb_ext"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "EP.ctx_now"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_d"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_Q"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.ecparams_result"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.kp_grp"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_GROUP_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Definition U_PK_USE_ECPARAMS : Z := 0x2964c.

(* [comment removed for export] *)
Lemma kp_init_presx : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "Psegs,(0.$1.)PL,$2.PMT,(0.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))PLB,(0.$6.)PLB',(0.$6.)PSP,$7.PX,(0.$8.)PC,$7.Pidpad,(4.&40.)PpP,(4.&40.)PpA,(4.&40.)PpB,(4.&40.)PpX,(4.&40.)PpY,(4.&40.)PpZ,(4.&40.)PpN,(4.&40.)Phpad,(4.&40.)Pqd,(4.&40.)PqX,(4.&40.)PqY,(4.&40.)PqZ,(4.&40.)P,(9.(:.(;.R16.)(<.R16.))(:.(=.R16.)(>.R16.)))P,(?.R18.R16.R15.R13.R?.(10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.))P,(11.R19.R18.R14.R12.R11.R16.R15.)P,(12.R1:.R17.)P,(12.R1;.R17.)P,(13.(14.$7.$7.)(15.$7.$7.R13.+100.)R17.)P,(16.R15.R14.+100.)(?.R1>.R1<.R1:.R18.R15.(10.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.))")
(* [comment removed for export] *).
Proof.
  (intros segs L MT m m' LB LB' SP X C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ DIMG dd_H; ddestruct dd_H as (HG & ED & MD & FD & HQ & FQ); intros PX MI MI' INC DX).
  assert (NOH : forall d, In d (kp_mpds (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ)) -> md_own d = LHeap -> False).
  { intros d Hd HO. revert Hd HO. unfold kp_mpds, kp_init, grp_mpds, grp_init.
    cbn [kp_grp kp_d kp_Q g_P g_A g_B g_G g_N pt_mpds pt_init pt_X pt_Y pt_Z app In]. unfold mpd_init.
    intros Hd HO; decompose [or] Hd; subst; cbn in HO; try discriminate; contradiction. }
  assert (CR : forall off n, 0 <= off -> off + n <= 256 -> client_range L LB SP (C + off) n).
  { intros off n H1 H2 a Ha. right; right. exists (C, 256). split; [exact INC| cbn; lia]. }
  assert (TR : forall d off, In d (kp_mpds (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ)) -> md_addr d = C + off -> 0 <= off -> off + 16 <= 256 ->
                 mpdr_at segs m LB d -> mpdr_at segs m' LB' d).
  { intros d off Hd Ha O1 O2 Md. eapply mpdr_at_LB_any; [| intros O; exact (NOH d Hd O)].
    eapply mpdr_at_presx; [exact Md| exact PX| exact MI| exact MI'| | | intros O; exfalso; exact (NOH d Hd O)]; rewrite Ha.
    - apply CR; assumption.
    - eapply disjoint_from_sub; [exact DX| lia| lia]. }
  split; [| split; [exact ED| split; [| split; [exact FD| split; [| exact FQ]]]]].
  - eapply (ecp_group_at_presx segs L); [exact HG| exact PX| exact MI| exact MI'| rewrite <- (Z.add_0_r C) at 1; apply (CR 0 192); lia| eapply disjoint_from_sub; [exact DX| lia| lia]|].
    intros d Hd HO. exfalso. apply (NOH d); [| exact HO]. unfold kp_mpds. apply in_app_iff. left. exact Hd.
  - eapply (TR _ 192); [| | | | exact MD]; [unfold kp_mpds; apply in_app_iff; right; left; reflexivity| reflexivity| lia| lia].
  - ddestruct HQ as (EX & EY & EZ & MX & MY & MZ). cbn [kp_Q kp_init] in *.
    split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
    split; [eapply (TR _ 208); [| | | | exact MX]| split; [eapply (TR _ 224); [| | | | exact MY]| eapply (TR _ 240); [| | | | exact MZ]]];
      (cbn [md_addr md_own mpd_init pt_init pt_X pt_Y pt_Z]; first [reflexivity| clear; lia| unfold kp_mpds; apply in_app_iff; right; right; cbn; auto]).
Qed.

Lemma gl_result_range : forall ca ONE id C r g NB, gl_result ca ONE id C r g NB -> -2^31 < r <= 0.
Proof.
  intros ca ONE id C r g NB H. unfold gl_result, MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, MBEDTLS_ERR_MPI_ALLOC_FAILED in H.
  decompose [and or ex] H; subst; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma ecp_ids_state_presx : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "Psegs,(0.$1.)PL,$2.PLB,(0.$6.)PSP,$7.PX,(0.$8.)PIDONE,$7.PIDS,$7.Pm,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))P,(17.R9.R4.R3.R2.)P,(11.R:.R9.R8.R7.R6.R3.R2.)P,(18.R:.R6.R5.)P,(16.R8.R7.+1.)P,(16.R9.R7.+38.)(17.R>.R9.R8.R6.)")
(* [comment removed for export] *).
Proof.
  (intros segs L LB SP X IDONE IDS m m' dd_H; ddestruct dd_H as (b & ibs & R1 & R2 & IMP); intros PX dd_H; ddestruct dd_H as (I1 & I2 & I3 & I4); intros D1 D2). dexists b, ibs.
  pose proof R2 as [[WF _] _]. cbn in WF. destruct WF as [LEN _].
  split; [| split; [| exact IMP]].
  - eapply heap_presx_rw_cells; [exact PX| exact R1| | exact D1]. cbn. intros a Ha. right; left. destruct (I4 a ltac:(lia)) as [_ NS]. split; [lia| exact NS].
  - eapply heap_presx_rw_cells; [exact PX| exact R2| | exact D2].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. right; left.
    destruct (I4 a ltac:(lia)) as [_ NS]. split; [lia| exact NS].
Qed.

Section EP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST usegs L HI) (LB : list blk)
            (PKA info C lo PAR LEN P BUF : Z) (tg pd : word) (bs : list byte)
            (idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ : word).
  Notation K := (kp_init C idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ).
  Hypothesis HH0 : HEAP usegs L HI h0 LB m0 mo0.
  Hypothesis HPKA0 : rw_cells usegs m0 PKA [C8 (Z_to_bv 64 info); C8 (Z_to_bv 64 C)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis NZP : 0 < PKA.
  Hypothesis EI : In info U_EC_INFOS.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis CWP : client_wrange L LB lo (heap_top usegs L HI h0) PKA 16.
  Hypothesis DPC : PKA + 16 <= C \/ C + 256 <= PKA.
  Hypothesis PKD : PKA + 16 <= hl_data_lo L \/ hl_data_hi L <= PKA.
  Hypothesis KP0 : ecp_keypair_at usegs U_MT m0 LB C K.
  Hypothesis INC : In (C, 256) LB.
  Hypothesis CD : C + 256 <= hl_data_lo L \/ hl_data_hi L <= C.
  Hypothesis HPAR0 : rw_cells usegs m0 PAR (buf_cells tg pd LEN P).
  Hypothesis ALR : PAR mod 8 = 0.
  Hypothesis NZR : 0 < PAR.
  Hypothesis DSR : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis RD : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis RC : PAR + 24 <= C \/ C + 256 <= PAR.
  Hypothesis HBS0 : bytes_at usegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis LEN0 : 0 <= LEN.
  Hypothesis PL : P + LEN <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis IDS0 : ecp_ids_state usegs U_ECP_IDS_DONE U_ECP_IDS m0.
  Hypothesis SOK0 : statics_ok usegs L m0.
  Hypothesis CA : const_at L U_MEMSET_FUNC 8.
  Hypothesis CAT : const_at L U_OID_EC_GRP_TBL 440.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.
  Hypothesis SLO : lo <= bv_unsigned sp - 688 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h0.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis MI0 : mem_inv usegs m0.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.
  Hypothesis IDL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.

  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation X0 := [(C, C + ECP_GROUP_SIZE); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation POST := (pk_use_ecparams_post usegs L HI U_MT U_CA U_ONE U_ECP_IDS_DONE U_ECP_IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PKA info C K lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -104)
                        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  Definition ctx_now (h : HST usegs L HI) (LBi T : list blk) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "(9.(19.$1:.VL,VHI,O5.O4.O2.O1.)(9.(1;.$7.(1<.$1:.VL,VHI,O5.)(1<.$1:.VL,VHI,Vh0,))(9.(1=.Vmo0,O1.)(9.(12.$1:.O2.)(9.(1>.$1:.VL,O2.)(9.(1?.VLB,O3.O4.)(17.$1:.$20.$21.O2.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="HI m0 mo0 h0 LB HH0 INC INB"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "(9.(22.+1000.(23.VL,))(9.(22.=VC,)(9.(1;.$7.(24.VC,+10.)=)(9.(:.(25.VC,+100.)(23.VL,))(9.(26.(:.(25.VC,+100.)(;.VL,))(:.(>.VL,)VC,))(9.(:.(25.VBUF,(27.(28.(4.&8.)Vbs,)))(23.VL,))(26.(:.(25.VBUF,(27.(28.(4.&8.)Vbs,)))(;.VL,))(:.(>.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof alloc_ceiling_pos as ACP. destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0 & C16 & _ & CAC & CIM). cbn in C0, C16, CAC, CIM.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC & BIM). cbn in BAC, BIM. auto 10.
  Qed.

  (* [comment removed for export] *)
  #[using="HI mo0 h0 lo BUF bs HH0 HPKA0 DSP CWP PKD INC INB IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "Pm,P,(4.&40.)(5.(4.&8.))P,(11.$1:.VL,VLB,(29.&40.Vsp,)(2:.(14.$7.$7.)(15.$7.$7.$20.(25.$20.+1.))(2:.(14.$7.$7.)(15.$7.$7.$21.(25.$21.+38.))(2;.(14.$7.$7.))))Vm0,R1.)(2<.$1:.R2.VPKA,(2:.$2=.(2>.(2?.&40.Vinfo,))(2:.$2=.(2>.(2?.&40.VC,))(2;.$2=.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. pose proof ep_basics as (ACP & _). eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.

  (* [comment removed for export] *)
  #[using="HLS PAR bs NZP DSP DPC NZR DSR RC SLO"] Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "Ph,(30.$1:.VL,VHI,)PLBi,(0.$6.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$31.Pr,$7.Pg',$32.PNB,(0.$6.)Px1,(4.&40.)Px5,(4.&40.)Px6,(4.&40.)Px7,(4.&40.)Px8,(4.&40.)Px9,(4.&40.)Px11,(4.&40.)Px12,(4.&40.)Px13,(4.&40.)Px14,(4.&40.)Px15,(4.&40.)Px16,(4.&40.)Px17,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px26,(4.&40.)Px27,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)P,(33.R22.R21.R1<.R20.R1?.)P,(?.$1:.$34.R21.R22.VC,(35.R1>.(36.(10.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))(37.(10.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))))P,(38.(39.R1?.))P,(1;.(0.$6.)(3:.R20.)R1?.)P,(3;.$3<.$3=.VC,(3>.(10.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,))R22.R21.R20.)P,(9.(22.(3?.(40.+2.+1?.))R23.)(:.R23.=))P,(2<.$1:.R26.VPKA,(2:.$2=.(2>.(2?.&40.Vinfo,))(2:.$2=.(2>.(2?.&40.VC,))(2;.$2=.))))P,(11.$1:.VL,VLB,(29.&40.Vsp,)(2:.(14.$7.$7.)(15.$7.$7.VC,(25.VC,$41.))(2:.(14.$7.$7.)(15.$7.$7.$20.(25.$20.+1.))(2:.(14.$7.$7.)(15.$7.$7.$21.(25.$21.+38.))(2;.(14.$7.$7.)))))Vm0,R27.)P,(2<.$1:.R28.(25.(29.&40.Vsp,)-68.)(2:.$2=.(2>.Vs11,)(2:.$2=.(2>.Vs10,)(2:.$2=.(2>.Vs9,)(2:.$2=.(2>.Vs8,)(2:.$2=.(2>.Vs7,)(2:.$2=.(2>.Vs6,)(2:.$2=.(2>.Vs5,)(2:.$2=.(2>.Vs4,)(2:.$2=.(2>.Vs3,)(2:.$2=.(2>.Vs2,)(2:.$2=.(2>.Vs1,)(2:.$2=.(2>.Vs0,)(2:.$2=.(2>.Vra,)(2;.$2=.)))))))))))))))P,(42.$1:.R29.Vlo,(25.(29.&40.Vsp,)-68.))(43.$1:.R29.(44.$1:.VL,VHI,$34.$3<.$3=.$20.$21.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(10.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(45.(46.R25.(2?.&40.(25.(29.&40.Vsp,)-200.))Vgp,Vtp,R24.R23.R22.R21.R20.(2?.&40.R28.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(2?.&40.+29;>0.)Vfc,(47.(4.&40.))R2:.(48.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros KP AP GB RES RR HPKA PX FR ST).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    do 14 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply aevtM_done. unfold pk_use_ecparams_post.
    deexists 17. dexists r, g', NB, LBi.
    split. { reflexivity. }
    destruct EXT as [EXT1 EXT2].
    split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HT|]. split; [exact HH|].
    split; [exact EXT1|]. split; [exact EXT2|]. split; [exact KP|]. split; [exact AP|]. split; [exact GB|].
    split; [exact RES|]. split; [exact RR|]. split; [exact HPKA|]. split; [exact PX|]. exact (conj SOK IDS).
  Qed.

  (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL"] Lemma setgrp_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_B ()) "Ph,(30.$1:.VL,VHI,)PLBi,(0.$6.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$31.Pid,$7.Px1,(4.&40.)Px5,(4.&40.)Px6,(4.&40.)Px7,(4.&40.)Px10,(4.&40.)Px11,(4.&40.)Px12,(4.&40.)Px13,(4.&40.)Px14,(4.&40.)Px15,(4.&40.)Px16,(4.&40.)Px17,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px26,(4.&40.)Px27,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)P,(33.R1?.R1>.(2;.$6.)R1=.R1<.)P,(11.$1:.VL,VLB,(29.&40.Vsp,)(2:.(14.$7.$7.)(15.$7.$7.$20.(25.$20.+1.))(2:.(14.$7.$7.)(15.$7.$7.$21.(25.$21.+38.))(2;.(14.$7.$7.))))Vm0,R1>.)P,(9.(:.=R1=.)(22.R1=.(40.+2.+1?.)))P,(2<.$1:.R20.(25.(29.&40.Vsp,)-68.)(2:.$2=.(2>.Vs11,)(2:.$2=.(2>.Vs10,)(2:.$2=.(2>.Vs9,)(2:.$2=.(2>.Vs8,)(2:.$2=.(2>.Vs7,)(2:.$2=.(2>.Vs6,)(2:.$2=.(2>.Vs5,)(2:.$2=.(2>.Vs4,)(2:.$2=.(2>.Vs3,)(2:.$2=.(2>.Vs2,)(2:.$2=.(2>.Vs1,)(2:.$2=.(2>.Vs0,)(2:.$2=.(2>.Vra,)(2;.$2=.)))))))))))))))P,(42.$1:.R21.Vlo,(25.(29.&40.Vsp,)-68.))(43.$1:.R21.(44.$1:.VL,VHI,$34.$3<.$3=.$20.$21.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(10.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(45.(46.R1?.(2?.&40.(25.(29.&40.Vsp,)-200.))Vgp,Vtp,R1>.R1=.R1<.(2?.&40.VPKA,)(2?.&40.R20.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(2?.&40.+29;=4.)Vfc,(47.(4.&40.))R22.(48.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros PX IDB FR ST).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. dpose ep_basics as (ACP & C0 & C16 & CAC & CIM & BAC & BIM). pose proof DIMG as [DI1 DI2].
    pose proof (ctx_pka m PX) as HPKA.
    assert (KP : ecp_keypair_at usegs U_MT m LBi C K).
    { eapply kp_init_presx; [exact DIMG| exact KP0| exact PX| exact MI0| exact MI| exact INC|].
      cbn. ddestruct IDL as (I1 & I2 & I3 & _). clear -CIM DI1 DI2 I1 I2 I3. repeat split; lia. }
    zstep. rewrite Z.add_0_r, (swrap32_id id) by (clear -IDB; lia).
    zstep. zstep.
    carve_frame 408%nat ST.
    pose proof (U_pk_ecc_set_group_spec L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0) as SPG.
    unfold pk_ecc_set_group_stmt, pk_ecc_set_group_post, U_PK_ECC_SET_GROUP in SPG.
    eapply aevtM_cut; [ eapply SPG with (lo := lo) (LB := LBi) (h := h) (id := id);
      rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by dlia; try eassumption; try reflexivity | ].
    { clear -DSP. lia. }
    { rewrite HT. eapply (client_wrange_weak L); [exact CWP| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| lia| lia| lia]. }
    { eapply lb_ext_sub; [exact EXT| exact INC]. }
    { clear -SLO. lia. }
    { rewrite HT. clear -HTOP. lia. }
    { clear -SPA SPR. lia. }
    clear SPG.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by dlia.
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & LEQ & LNEW & KP5 & AP5 & GB5 & RES & HPKA5 & HP5 & SOK5). unfold ECP_GROUP_SIZE in HP5.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
    match type of HH5 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB5 end.
    lazymatch type of RES with gl_result _ _ _ _ ?r ?g ?nb => rename r into r5; rename g into g5; rename nb into NB5 end.
    (* [comment removed for export] *)
    assert (FR' : FRS m5).
    { eapply heap_presx_rw_cells; [exact HP5| exact FR| |]; cbn [cells_size csize Nat.add disjoint_from];
      [intros a Ha; left; clear -Ha; lia| split; [clear -CAC ACL SLO HLS SPR; lia| exact I]]. }
    match goal with FRJ : rw_cells usegs m (bv_unsigned sp + -512) [CB 408 ?j] |- _ =>
      assert (FRJ' : rw_cells usegs m5 (bv_unsigned sp + -512) [CB 408 j])
        by (eapply heap_presx_rw_cells; [exact HP5| exact FRJ| |]; cbn [cells_size csize Nat.add disjoint_from];
            [intros a Ha; left; clear -Ha; lia| split; [clear -CAC ACL SLO HLS SPR; lia| exact I]]); clear FRJ end.
    release_frame FRJ' ST5 (bv_unsigned sp + -104).
    eapply exit_walk; [ | exact KP5| exact AP5| exact GB5| left; exists id; split; [exact IDB| exact RES]| exact (gl_result_range _ _ _ _ _ _ _ RES)| exact HPKA5| | exact FR'| exact ST5].
    - (* [comment removed for export] *)
      split; [exact HH5|]. split; [rewrite HT5; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF5]|]. split; [exact MI5|]. split; [exact SOK5|].
      split.
      + pose proof EXT as [EXT1 EXT2]. split.
        * intros b. rewrite (LEQ b), (EXT1 b). clear. cbn. tauto.
        * intros b Hb HL. apply (LNEW b Hb). eapply lb_ext_sub; [exact EXT| exact HL].
      + eapply ecp_ids_state_presx; [exact IDS| exact HP5| exact IDL| |]; cbn; ddestruct IDL as (I1 & I2 & I3 & _);
          (split; [clear -I1 I2 I3 CD; lia| exact I]).
    - (* [comment removed for export] *)
      eapply heap_presx_trans; [eapply heap_presx_weak; [exact PX| intros b Hb; exact Hb| clear; lia| intros a Ha; exact (proj2 Ha)]|].
      eapply heap_presx_weak; [exact HP5| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| clear; lia|].
      intros a Ha. cbn in Ha |- *. unfold ECP_GROUP_SIZE in Ha. split; [exact (proj1 Ha)| exact I].
  Qed.
End EP.
