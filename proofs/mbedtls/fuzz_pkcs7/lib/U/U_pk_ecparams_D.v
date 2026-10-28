(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Arr MpiCoreAux MpiWalkAux Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C.
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
Ltac2 gd_tbl_P_pk_ecparams_D () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Logic.iff"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.EcpCurves.curve_addrs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.gl_result"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "IDWS"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.ecp_ids_state"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_B.ctx_now"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_blocks"; "RocqVerifyHarness.AgentSubmission.Spec.PkTmp.tmp_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
Lemma in_lb_remove_iff : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "PLB,(0.$1.)PP,$2.Pb,$1.P,(3.$2.(4.(5.$2.$2.)$2.(6.$2.$2.)R3.))(7.(8.$1.R2.(9.R3.R4.))(:.(8.$1.R2.R4.)(;.(<.$2.(6.$2.$2.R2.)R3.))))")
(* [comment removed for export] *).
Proof.
  intros LB P [B k] ND. split.
  - intros H. split; [exact (In_lb_remove _ _ _ H)|]. cbn. intros ->. exact (lb_remove_notin _ _ _ ND H).
  - intros [H NE]. apply In_lb_remove_keep; [exact H| exact NE].
Qed.

Lemma gl_free_set : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Pca,P,$2.$=.PONE,$2.Pid,$2.PA,$2.Pr,$2.Pg,$>.PNB,(0.$1.)PLB,(0.(5.$2.$2.))P,(?.R8.R7.R6.R5.R4.R3.R2.)P,(3.$2.(4.(5.$2.$2.)$2.(6.$2.$2.)R2.))P,Pb,$1.P,(8.$1.R1.R5.)(8.$1.R2.R5.)Pb,$1.(7.(8.$1.R1.(10.R7.R5.))(:.(8.$1.R1.R5.)(;.(8.$1.R1.R6.))))")
(* [comment removed for export] *).
Proof.
  intros ca ONE id A r g NB LB GL ND SUB b.
  destruct GL as [(_ & _ & _ & -> & (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & ->))
              |[(_ & _ & (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & PA & PX & PZ & wA & wX & wZ & -> & ->))
              |[(_ & _ & -> & (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & -> & _))
              |(_ & _ & -> & ->)]]].
  - unfold grp_free_LB, grp_free_mpds, grp_sw. cbn. tauto.
  - unfold grp_free_LB, grp_free_mpds, grp_mx, grp_mxi. cbn -[lb_remove In].
    rewrite (in_lb_remove_iff _ PZ b) by (apply nodup_lb_remove, nodup_lb_remove, ND).
    rewrite (in_lb_remove_iff _ PX b) by (apply nodup_lb_remove, ND).
    rewrite (in_lb_remove_iff _ PA b) by exact ND.
    destruct b as [B k]. cbn. split.
    + (intros dd_H; ddestruct dd_H as (((H & N1) & N2) & N3)). split; [exact H|]. intros [E|[E|[E|[]]]]; injection E as <- <-; [apply N1| apply N2| apply N3]; reflexivity.
    + intros [H N].
      assert (K : forall P, In (P, 4) [(PA, 4); (PX, 4); (PZ, 4)] -> B <> P).
      { intros P HP ->. apply N. pose proof (nodup_fst_same _ _ _ _ ND H (SUB _ HP)) as ->. exact HP. }
      split; [split; [split; [exact H|]|]|]; apply K; cbn; auto.
  - unfold grp_free_LB, grp_free_mpds, grp_init. cbn. tauto.
  - unfold grp_free_LB, grp_free_mpds, grp_zero. cbn. tauto.
Qed.

(* [comment removed for export] *)
Lemma gl_signs : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Pca,P,$2.$=.PONE,$2.Pid,$2.PA,$2.Pg,$>.PNB,(0.$1.)P,(?.R6.R5.R4.R3.=R2.R1.)Pd,$11.P,(8.$11.R1.(12.R4.))(<.$2.(13.R2.)+1.)")
(* [comment removed for export] *).
Proof.
  intros ca ONE id A g NB GL d Hd. unfold gl_result, MBEDTLS_ERR_ECP_FEATURE_UNAVAILABLE, MBEDTLS_ERR_MPI_ALLOC_FAILED in GL.
  destruct GL as [(_ & _ & _ & _ & (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & ->))
              |[(_ & _ & (idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & PA & PX & PZ & wA & wX & wZ & -> & _))
              |[(E & _)|(E & _)]]]; [| | discriminate E| discriminate E].
  - unfold grp_mpds, grp_sw in Hd. cbn -[smpd mpd_init In] in Hd. cbn [In app] in Hd.
    destruct (has_A id); decompose [or] Hd; subst; try reflexivity; try contradiction.
  - unfold grp_mpds, grp_mx, grp_mxi in Hd. cbn -[smpd mpd_init heap1 In] in Hd. cbn [In app] in Hd.
    decompose [or] Hd; subst; try reflexivity; try contradiction.
Qed.


(* [comment removed for export] *)
Definition IDWS : list word := map (Z_to_bv 64) ecp_ids.
Lemma ids_bytes_u32s : ecp_ids_bytes = u32s IDWS.
Proof. vm_compute. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L19384548599.4L23520446711.4L25776931255.4L31361301943.4L3369585847.4 L34080721719.4L36457724599.4L39417606391.4L46056173815.4L50465617719.4L58319665399.4L59071483127.4L62950335111.4L7821186295.4 L8208711057.7 00000900B00K00T00]00f00o01801A01J01S01\01e01n02;S1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j2Ek2CJS1j1w1k2Ek2CJ". (* [comment removed for export] *)
Lemma ids_nth : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Pj,$2.Pw,(14.&40.)P,(<.(15.(14.&40.))(16.(14.&40.)$17.(18.R2.))(19.(14.&40.)R1.))P,(1:.=R3.)(1;.$2.Lid,$2.(:.(<.(14.&40.)R4.(1<.&40.R1.))(:.(:.(1:.=R1.)(1:.R1.+=.))(:.(7.(<.$2.R1.=)(<.$2.R5.+=.))(1:.R5.+=.)))))")
(* [comment removed for export] *).
Proof.
  intros j w H Hj. unfold IDWS in H.
  assert (CJ : (Z.to_nat j < 14)%nat). { pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite H; discriminate)) as HL. cbn in HL. exact HL. }
  remember (Z.to_nat j) as k eqn:Ek.
  do 14 (destruct k as [|k]; [cbn in H; injection H as <-; eexists; split; [reflexivity|]; lia|]). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ecp_ids_state_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Psegs,(0.$1=.)PIDONE,$2.PIDS,$2.PW,(0.$1>.)Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))P,(1?.R6.R5.R4.R2.)P,(20.R4.R3.R2.)P,(21.R8.R4.R3.)P,(22.R6.R8.+1.)P,(22.R7.R8.+38.)(1?.R;.R:.R9.R6.)")
(* [comment removed for export] *).
Proof.
  (intros segs IDONE IDS W m m' dd_H; ddestruct dd_H as (b & ibs & R1 & R2 & IMP); intros MU WM D1 D2). dexists b, ibs.
  split; [eapply rw_cells_transport; [exact R1| exact MU| exact WM| exact D1]|].
  split; [eapply rw_cells_transport; [exact R2| exact MU| exact WM| exact D2]| exact IMP].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L25080995374.2L38557618280.200000600<S1z2HzS1z2Hz". (* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  (* [comment removed for export] *)
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis CAC : C + 256 <= alloc_ceiling.
  Hypothesis C0 : 0 < C.
  Hypothesis C16 : C mod 16 = 0.
  Hypothesis CIM : C + 256 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis BAC : BUF + Z.of_nat (length bs) <= alloc_ceiling.
  Hypothesis BIM : BUF + Z.of_nat (length bs) <= hl_img_lo L \/ hl_img_hi L <= BUF.

  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation X0 := [(C, C + ECP_GROUP_SIZE); (U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_ECP_IDS, U_ECP_IDS + 56)].
  Notation POST := (pk_use_ecparams_post usegs L HI U_MT U_CA U_ONE U_ECP_IDS_DONE U_ECP_IDS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PKA info C K lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -104)
                        [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  (* [comment removed for export] *)
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "(:.(23.+1000.(24.VL,))(:.(23.=VC,)(:.(<.$2.(25.VC,+10.)=)(:.(1:.(26.VC,+100.)(24.VL,))(:.(27.(1:.(26.VC,+100.)(28.VL,))(1:.(29.VL,)VC,))(:.(1:.(26.VBUF,(2:.(2;.(14.&8.)Vbs,)))(24.VL,))(27.(1:.(26.VBUF,(2:.(2;.(14.&8.)Vbs,)))(28.VL,))(1:.(29.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Pm,P,(14.&40.)(15.(14.&8.))P,(2<.$2=.VL,VLB,(2>.&40.Vsp,)(2?.(5.$2.$2.)(30.$2.$2.$31.(26.$31.+1.))(2?.(5.$2.$2.)(30.$2.$2.$32.(26.$32.+38.))(33.(5.$2.$2.))))Vm0,R1.)(34.$2=.R2.VPKA,(2?.$35.(36.(1<.&40.Vinfo,))(2?.$35.(36.(1<.&40.VC,))(33.$35.))))")
(* [comment removed for export] *).
  Proof.
    intros m PX. eapply heap_presx_rw_cells; [exact PX| exact HPKA0| |]; cbn [cells_size csize Nat.add disjoint_from].
    - intros a Ha. destruct (CWP a Ha) as [Q|[Q|Q]]; [left; clear -Q DSP Ha; lia| right; left; exact Q| right; right; exact Q].
    - ddestruct IDL as (I1 & I2 & I3 & _). clear -PKD I1 I2 I3. split; [lia| split; [lia| exact I]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  #[using="IDL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 IDL). Qed.
  #[using="L IDL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 IDL)). Qed.
  #[using="IDL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 IDL))). Qed.
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Pa,$2.P,(27.(:.(1:.$31.R1.)(23.R1.(26.$31.+1.)))(:.(1:.$32.R1.)(23.R1.(26.$32.+38.))))(:.(37.VL,R2.)(;.(38.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.

  Notation G := (bv_unsigned sp + -504).
  Notation REF := (bv_unsigned sp + -296).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L28467717136.4  L35502338560.9  L37666267916.16 L52615561274.128L55346310259.12 L59263549952.4  L6492794257.6   L6494891585.6   L6495045014.8   L6497577422.127 00000600Q00o01G01]01f02:02M02c03>S1L2H1S1L2HI2sp2h02lo4HTOP1a1g2g0S1L2lo1u1v1A1n2HA4DHI'4ACL'2Q1S2ra2sp3PKA1C3PAR2bs1a1lS2sp2lo1u1v1a2Ha2Q12Q2S1L2H02H1S1L2lo3ACL3DHI1a3Hd1S1L2lo3ACL3DHI1a2HaS1L2lo3ACL1a1B1k2Hr2B4S2ra2sp3PKA1C2lo3PAR2bs1a1l". (* [comment removed for export] *)
  #[using="ra PKA C PAR bs ACL HTOP DHI IDL"] Lemma ctx_munch : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Ph,(39.$2=.VL,VHI,)PLBi,(0.$1.)PT,(0.$1.)Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))Pmo,$3:.PW,(0.$1>.)P,(3;.VL,VHI,Vmo0,Vh0,VLB,R7.R6.R5.R4.R2.)P,(2<.$2=.VL,VLB,(2>.&40.Vsp,)(2?.(5.$2.$2.)(30.$2.$2.$31.(26.$31.+1.))(2?.(5.$2.$2.)(30.$2.$2.$32.(26.$32.+38.))(33.(5.$2.$2.))))Vm0,R5.)P,(20.R3.R6.R5.)P,(21.$2=.R7.R6.)P,(3<.$2=.R7.)P,(3=.(5.$2.$2.)Liv,(5.$2.$2.)(:.(1:.Vlo,(6.$2.$2.R1.))(1:.(3>.$2.$2.R1.)(2>.&40.Vsp,)))R6.)(:.(3;.VL,VHI,Vmo0,Vh0,VLB,R=.R<.R;.R9.R8.)(2<.$2=.VL,VLB,(2>.&40.Vsp,)(2?.(5.$2.$2.)(30.$2.$2.$31.(26.$31.+1.))(2?.(5.$2.$2.)(30.$2.$2.$32.(26.$32.+38.))(33.(5.$2.$2.))))Vm0,R9.))")
(* [comment removed for export] *).
  Proof.
    (intros h LBi T m m' mo W dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros PX MU WM MI' HW).
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    assert (OUTW : forall a, (a < lo \/ bv_unsigned sp <= a) -> outside W a).
    { intros a Ha. clear -HW Ha. induction W as [|[u v] W IH]; cbn; [exact I|]. inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2.
      split; [lia| apply IH; exact Q3]. }
    split; [| eapply heap_presx_trans; [exact PX|]].
    - split; [| split; [exact HT| split; [exact MF| split; [exact MI'| split; [| split; [exact EXT|]]]]]].
      + apply (Asn1AuxA.HEAP_munch usegs L HI h LBi m m' mo lo _ HH ACL MU WM).
        intros a Ha NO. left. rewrite HT. destruct (Z_lt_ge_dec a lo); [exfalso; apply NO, OUTW; left; lia|].
        destruct (Z_le_gt_dec (bv_unsigned sp) a); [exfalso; apply NO, OUTW; right; lia|]. clear -g g0 HTOP. lia.
      + eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha _. apply OUTW. left. clear -Ha DHI ACL. lia.
      + assert (DW : forall A n, A + n <= hl_data_hi L -> disjoint_from W A n).
        { intros A n HA. pose proof DHI as DHI'. pose proof ACL as ACL'. clear -HW HA DHI' ACL'.
          induction W as [|[u v] W IH]; cbn; [exact I|]. inversion HW as [|? ? [Q1 Q2] Q3]; subst. cbn in Q1, Q2.
          split; [lia| apply IH; exact Q3]. }
        eapply ecp_ids_state_munch; [exact IDS| exact MU| exact WM| apply DW| apply DW]; generalize IL1 IL2 IL3; clear; intros; lia.
    - destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR' _].
      eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha Hc _. apply OUTW.
      destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [right; exact Hs| left; clear -Hd1 DHI ACL; lia| left].
      pose proof (proj1 (Forall_forall _ _) HBR' _ (lb_ext_sub _ _ _ _ EXT Hb)) as (_ & _ & _ & B4 & _). destruct b as [B k]; cbn in Hr, B4. clear -Hr B4 ACL. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Notation CTX := (ctx_now L HI mo0 h0 LB).
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0110@D11805467289.199D40000057555.199D49705053714.199L13499167864.188L14351168243.6  L14368737793.5  L14946148648.188L14948428072.188L15925965075.7  L15928000268.7  L15928144661.3  L15928147222.4  L18731979229.1  L18933043916.4  L18994852257.0  L19011089568.7  L20361976943.7  L21135888065.0  L24494512233.6  L26036618712.190L26239071453.1  L27901888243.12 L28142564996.0  L30392002547.6  L33082966091.6  L35411708365.6  L38732773782.8  L39459941448.1  L40147641242.6  L41588182622.3  L44200638400.2  L44200755144.3  L45272789334.2  L46132990536.1  L48011564883.1  L48062193029.6  L48062193029.9  L48063759353.7  L49425788764.198L49664744988.1  L51165391420.199L52955663349.7  L53516959912.188L53519239336.188L5537256425.5   L59308549609.3  L59427879996.189L59538322464.6  L61033050697.3  L61033053258.4  L61033397840.7  L61035294799.7  L61120265865.3  L61303247072.7  L62912532084.190L63106620870.10 L6430512117.7   L66572612610.3  L7109062493.1   L8064411869.1   L8322245898.4   L9786670416.7   L9788617045.4   L9788620630.3   L9788961615.7   00000G00^01901U01j02;02<02=02>02?02@02A02E02I02J02c03803903=03Q03U03k03l04A04V04\05905:05J05W05`05i05o06306706806906O07\07`09009109E09Y09]09f09g09h09i09j09k09l0:70:D0:X0;70;;0;E0;I0;M0;Y0;Z0;[0;c0;dS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs2HBS2ra2sp3PKA1C3PAR2bs3SPR2HBS2ra2sp3PKA1C3PAR2bs3idj3IJBS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOFFFFFFS2spS2r1SS1L3HLS2sp2lo3SLO3ACL3DHIS1L3HLS2sp2lo3SLO3ACLSS2spS2ra2sp3PKA1C3PAR2bsS2spS1L2HI2sp2h04HTOP1a2HaSS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS1a2HaS1L3HLS2sp2lo3SLO3ACL3SPR3ACPFS1L1a1H2H02H12HaS3idj3IJB3NZJS3idj3IJBS3idj3IJBS1j2JBS2spS2spFFS1L2HI2sp2h04HTOP1h2HTS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02tj2WFS2spS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3DSP3DPC3NZR3DSR2RC3SLO3ACL3ACP3CAC2C02mj2l22WFFS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2spS1j2JB2NJFFFFFFS2sp2a'3Ha'S1L2sp2lo3SLOS2ra2sp3PKA1C3PAR2bsS1L2sp2lo2H02H13DHI3ACL3SLO3HLSS2spS2r12RR2HqS2spS2spS2r12RR1q2HqFFS2sp3SPAF". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM"] Lemma tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_D ()) "Ph,(39.$2=.VL,VHI,)PLBi,(0.$1.)Pm,P,(14.&40.)(15.(14.&8.))Pmo,$3:.Pgref,$>.Pidg,$2.Prg,$2.Pj,$2.Pr1,$2.PdN,$11.PdP,$11.PdA,$11.PdB,$11.PdX,$11.PdY,$11.PdZ,$11.Pscj,(0.(14.&8.))Phj,(0.(14.&8.))Ptj,(0.(14.&8.))Pmj,(0.(14.&8.))Pl1,(0.(14.&8.))Pl2,(0.(14.&8.))Ppb,(14.&40.)Pnb,(14.&40.)Px1,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px10,(14.&40.)Px11,(14.&40.)Px12,(14.&40.)Px13,(14.&40.)Px14,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Px19,(14.&40.)Px20,(14.&40.)Px21,(14.&40.)Px22,(14.&40.)Px23,(14.&40.)Px24,(14.&40.)Px25,(14.&40.)Px26,(14.&40.)Px27,(14.&40.)Px28,(14.&40.)Px29,(14.&40.)Px30,(14.&40.)Px31,(14.&40.)P,(3;.VL,VHI,Vmo0,Vh0,VLB,R31.R30.(3?.$1.(40.(2?.$11.R28.(2?.$11.R27.(2?.$11.R26.(2?.$11.R25.(2?.$11.R24.(2?.$11.R23.(2?.$11.R22.(33.$11.)))))))))(41.R2=.))R2?.R2>.)P,(2<.$2=.VL,VLB,(2>.&40.Vsp,)(2?.(5.$2.$2.)(30.$2.$2.$31.(26.$31.+1.))(2?.(5.$2.$2.)(30.$2.$2.$32.(26.$32.+38.))(33.(5.$2.$2.))))Vm0,R30.)P,(42.$2=.R31.R32.(26.(2>.&40.Vsp,)-1?8.)+<0.(2?.$11.R2:.(2?.$11.R29.(2?.$11.R28.(2?.$11.R27.(2?.$11.R26.(2?.$11.R25.(2?.$11.R24.(33.$11.)))))))))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+68.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+8.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+18.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+28.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+38.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+48.))P,(<.$2.(43.R2;.)(26.(26.(2>.&40.Vsp,)-1?8.)+58.))P,Pb,$1.P,(8.$1.R1.(41.R38.))(;.(8.$1.R2.(40.(2?.$11.R34.(2?.$11.R33.(2?.$11.R32.(2?.$11.R31.(2?.$11.R30.(2?.$11.R2?.(2?.$11.R2>.(33.$11.)))))))))))P,(44.$2=.$45.R3:.R3;.(26.(2>.&40.Vsp,)-128.)R38.)P,(46.(12.R39.))P,(?.$47.$48.R39.(26.(2>.&40.Vsp,)-128.)R38.R3:.(41.R3:.))P,(49.$2=.R3=.$32.(4:.$17.))P,(:.(1:.=R39.)(1:.R39.+=.))P,(:.(23.(4;.(4<.+2.+1?.))R39.)(1:.R39.=))P,(34.$2=.R40.(26.(2>.&40.Vsp,)-200.)(2?.$35.(4=.#8.R32.)(33.$35.)))P,(34.$2=.R41.(26.(2>.&40.Vsp,)-1?8.)(2?.$35.(4=.#8.R32.)(33.$35.)))P,(34.$2=.R42.(26.(26.(2>.&40.Vsp,)-1?8.)+78.)(2?.$35.(36.R2>.)(2?.$35.(36.R2=.)(2?.$35.(4=.#38.R32.)(33.$35.)))))P,(34.$2=.R43.(26.(2>.&40.Vsp,)-138.)(2?.$35.(4=.#8.R32.)(2?.$35.(4=.#4.R31.)(2?.$35.(4=.#4.R30.)(33.$35.)))))P,(34.$2=.R44.(26.(2>.&40.Vsp,)-68.)(2?.$35.(36.Vs11,)(2?.$35.(36.Vs10,)(2?.$35.(36.Vs9,)(2?.$35.(36.Vs8,)(2?.$35.(36.Vs7,)(2?.$35.(36.Vs6,)(2?.$35.(36.Vs5,)(2?.$35.(36.Vs4,)(2?.$35.(36.Vs3,)(2?.$35.(36.Vs2,)(2?.$35.(36.Vs1,)(2?.$35.(36.Vs0,)(2?.$35.(36.Vra,)(33.$35.)))))))))))))))P,(4>.$2=.R45.Vlo,(26.(2>.&40.Vsp,)-200.))(4?.$2=.R45.(50.$2=.VL,VHI,$45.$47.$48.$31.$32.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(51.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(52.(53.R30.(1<.&40.(26.(2>.&40.Vsp,)-200.))Vgp,Vtp,R2?.R2>.R2=.(1<.&40.VPKA,)(1<.&40.(26.$32.(54.+4.R41.)))R2<.R2;.R2:.R29.R28.R27.R26.R25.(1<.&40.R40.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)VF,(1<.&40.+29;7<.)Vfc,(55.(14.&40.))R46.(56.$2=.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. (intros dd_H; ddestruct dd_H as (HH & HT & MF & MI & SOK & EXT & IDS); intros PX TOK EN EP EA EB EX EY EZ RT HG AP GL HIDS JB RR FR0 FRH FRT FRM FR ST).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBRc HAPc]. pose proof (HND _ _ _ _ HH) as NDc.
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof (U_ecp_group_free_spec L HI HFREE HLS SW DIMG HND U_MT) as SGF. unfold ecp_group_free_stmt, ecp_group_free_post, U_ECP_GROUP_FREE in SGF.
    eapply aevtM_cut.
    { eapply SGF with (lo := lo) (h := h) (LB := LBi) (A := REF) (g := gref);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH | exact HG | exact AP | exact TP | exact CA | eassumption
              | rewrite HT; intros a Ha; left; clear -Ha SLO HLS HTOP ACL ACP; unfold ECP_GROUP_SIZE in Ha; lia
              | unfold ECP_GROUP_SIZE; clear -DHI ACL SLO HLS; lia
              | clear -SLO; lia | clear -HTOP HT; lia | clear -SPA SPR; lia
              | reflexivity | f_equal; clear; lia
              | match goal with |- ?g => idtac "GFLEFT" g end ]. }
    clear SGF.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & HG2 & FRR2 & PX2 & SOK2). unfold ECP_GROUP_SIZE in PX2.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    (* [comment removed for export] *)
    pose proof (gl_free_set _ _ _ _ _ _ _ LBi GL NDc ltac:(intros b Hb; apply (proj2 (proj1 EXT b)); left; apply in_app_iff; right; exact Hb)) as FS.
    set (LBf := grp_free_LB gref LBi) in *.
    assert (EXT2 : lb_ext LB (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) LBf).
    { destruct EXT as [E1 E2]. split.
      - intros b. rewrite (FS b), (E1 b), in_app_iff. split.
        + (intros dd_H; ddestruct dd_H as [[[HT'|HR]|HL] NR]); [left; exact HT'| exfalso; exact (NR HR)| right; exact HL].
        + intros [HT'|HL]; [split; [left; left; exact HT'| intros HR; exact (RT _ HR HT')]| split; [right; exact HL| intros HR; apply (E2 b); [apply in_app_iff; right; exact HR| exact HL]]].
      - intros b HT'. apply E2. apply in_app_iff. left. exact HT'. }
    assert (TOK2 : tmp_ok usegs m2 LBf G 192 [dN; dP; dA; dB; dX; dY; dZ]).
    { eapply (tmp_ok_presx usegs L); [exact TOK| exact PX2| exact MI| exact MI2| clear; lia| clear -ACL SLO HLS; lia| | | exact HBRc].
      - intros d Hd Od. apply (proj2 (FS _)). pose proof (tmp_ok_in usegs _ _ _ _ _ _ TOK Hd) as [MDd _].
        destruct (mpdr_blk_facts usegs L _ _ _ MDd Od HBRc) as (Id & _). split; [exact Id|].
        intros HR. apply (RT _ HR). apply in_tmp_blocks. exists d. split; [exact Hd|]. rewrite (mpd_blk_heap _ Od). left; reflexivity.
      - repeat constructor; cbn; clear -ACL SLO HLS ACP; lia. }
    assert (PXn : heap_presx usegs L LB (bv_unsigned sp) XS m0 m2).
    { eapply heap_presx_trans; [exact PX|].
      eapply (presx_caller usegs L LB LBf LBi); [exact PX2| intros b Hb; eapply lb_ext_sub; [exact EXT2| exact Hb]| clear; lia| clear -ACL SLO HLS; lia
        | exact HBRc| exact HAPc| exact NDc| intros b Hb; eapply lb_ext_sub; [exact EXT| exact Hb]| | exact DHI| exact DI1| exact DI2].
      intros iv [<-|[]]. left. cbn. clear -ACL SLO HLS. lia. }
    pose proof (ecp_ids_state_presx usegs L _ _ _ _ _ _ _ IDS PX2 IDL
                  ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia) ltac:(cbn; generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia)) as IDS2.
    assert (HIDS2 : bytes_at usegs m2 U_ECP_IDS (u32s IDWS)).
    { eapply heap_presx_bytes_at; [exact PX2| exact HIDS| |]; rewrite <- ids_bytes_u32s; cbn [length ecp_ids_bytes].
      - intros a Ha. right; left. destruct (IL4 a ltac:(right; generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia)) as [_ NS]. split; [generalize IL1 IL2 IL3 Ha; clear; cbn; intros; lia| exact NS].
      - cbn. generalize IL1 IL2 IL3 DHI ACL SLO HLS; clear; intros; lia. }
    (* [comment removed for export] *)
    repeat match goal with
    | Hc : rw_cells usegs m ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; intros a' Ha'; left; clear -Ha'; lia
                  | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; split; [clear; lia| exact I] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end.
    clear HH MI SOK ST TOK PX IDS HIDS HG AP HBRc HAPc MK.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    (* [comment removed for export] *)
    destruct (nth_error IDWS (Z.to_nat j)) as [w|] eqn:NJ; [| exfalso; apply nth_error_None in NJ; cbn in NJ; clear -NJ JB; lia].
    ddestruct (ids_nth j w NJ ltac:(clear -JB; lia)) as (idj & -> & IJB & IJZ & _).
    pose proof (u32ro_read usegs m2 U_ECP_IDS IDWS j _ (wa (U_ECP_IDS + 4 * j)) HIDS2 NJ ltac:(clear -JB; lia) eq_refl) as RDJ.
    zstep. clear RDJ. rewrite (sx32_small idj) by (clear -IJB; lia).
    (* [comment removed for export] *)
    assert (CTX2 : CTX h2 LBf (tmp_blocks [dN; dP; dA; dB; dX; dY; dZ]) m2 mo2).
    { split; [exact HH2|]. split; [rewrite HT2; exact HT|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
      split; [exact MI2|]. split; [exact SOK2|]. split; [exact EXT2| exact IDS2]. }
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 _].
    clear HH2 HT2 MF2 SOK2 EXT2 IDS2 FS HIDS2 NJ HG2 EXT RT GL HT MF NDc.
    pose proof (munch_refl [(bv_unsigned sp + -304, bv_unsigned sp + -300)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    destruct (ctx_munch _ _ _ _ _ _ _ CTX2 PXn MU WM ltac:(assumption) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as [CTX3 PX3].
    pose proof (tmp_ok_munch usegs L _ _ _ _ _ _ _ TOK2 MU WM (proj1 (proj2 (proj2 (proj2 CTX2)))) ltac:(assumption) ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) HBR2) as TOK3.
    clear CTX2 PXn MU WM TOK2 MK2. pose proof (heap_mok _ _ HI _ _ _ _ (proj1 CTX3)) as MK3.
    (* [comment removed for export] *)
    assert (FRT' : rw_cells usegs m3 (G + 120) [CB 72 (le8 pb ++ le8 nb ++ tj)]).
    { pose proof FRT as [[WF _] _]. cbn in WF. eapply rw_cells_reshape; [exact FRT| cbn; rewrite ?app_length, ?length_le8; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity]. }
    assert (FRM' : rw_cells usegs m3 (bv_unsigned sp + -312) [CB 16 (mj ++ le4 (Z_to_bv 64 idj) ++ l2)]).
    { pose proof FRM as [[WF _] _]. cbn in WF. eapply rw_cells_reshape; [exact FRM| cbn; rewrite ?app_length, ?length_le4; cbn; split; [lia| exact I]| cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity]. }
    clear FRT FRM.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    - (* [comment removed for export] *)
      assert (NZ : r1 <> 0) by (intros ->; apply KR; reflexivity).
      eapply cleanup_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs) (r2 := r1)
                              (dN := dN) (dP := dP) (dA := dA) (dB := dB) (dX := dX) (dY := dY) (dZ := dZ);
        try eassumption; try reflexivity.
      intros Z0. exfalso. exact (NZ Z0).
    - (* [comment removed for export] *)
      assert (Z0 : r1 = 0).
      { clear -KR RR. apply Z.mod_divide in KR; [| lia]. destruct KR as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
      subst r1. clear KR.
      destruct (Z.eq_dec idj 0) as [EJ|NZJ].
      + rewrite EJ in *. zstep. zstep. zstep. zstep. zstep.
        match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
          replace (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 (-0x4E80)) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply cleanup_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs) (r2 := -0x4E80)
                                (dN := dN) (dP := dP) (dA := dA) (dB := dB) (dX := dX) (dY := dY) (dZ := dZ);
          try eassumption; try reflexivity.
        all: first [clear; cbn; lia| intros Z0; exfalso; clear -Z0; cbn in Z0; lia].
      + zstep. zstep. zstep. zstep. zstep.
        replace (0 <? idj) with true by (symmetry; apply Z.ltb_lt; clear -IJB NZJ; lia).
        match goal with |- context [Z_to_bv 64 (Z.land ?a ?b)] =>
          replace (Z_to_bv 64 (Z.land a b)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply cleanup_walk with (PKA := PKA) (info := info) (C := C) (lo := lo) (PAR := PAR) (bs := bs) (r2 := 0)
                                (dN := dN) (dP := dP) (dA := dA) (dB := dB) (dX := dX) (dY := dY) (dZ := dZ);
          try eassumption; try reflexivity.
        all: first [clear; cbn; lia| intros _; exists idj; split; [reflexivity| clear -IJB NZJ; lia]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
