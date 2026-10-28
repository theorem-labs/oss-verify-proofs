(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Arr MpiCoreAux MpiWalkAux Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E U_pk_ecparams_F U_pk_ecparams_G U_asn1_get_tag U_asn1_get_int U_asn1_get_mpi U_mpi_read_binary U_mpi_read_binary_proof U_mpi_lset U_pk_ecparams_H U_pk_ecparams_I.
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
Local Ltac pnull K :=
  exfalso;
  repeat match type of K with context [?a <? ?b] =>
    first [ let E := fresh "E" in assert (E : (a <? b) = true) by (apply Z.ltb_lt; lia); rewrite E in K; clear E
          | let E := fresh "E" in assert (E : (a <? b) = false) by (apply Z.ltb_ge; lia); rewrite E in K; clear E ] end;
  vm_compute in K; first [ discriminate K | lia ].
Ltac2 gd_tbl_P_pk_ecparams_J () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_H.SPINV"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].



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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
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
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
(* [comment removed for export] *).
  Proof. exact (proj2 (proj2 (proj2 IDL))). Qed.
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.

  Notation G := (bv_unsigned sp + -504).
  Notation REF := (bv_unsigned sp + -296).
  Notation CTX := (ctx_now L HI mo0 h0 LB).
  Notation DS7 dN dP dA dB dX dY dZ := ([dN; dP; dA; dB; dX; dY; dZ] : list mpd) (only parsing).


  Notation LSTATE := (LSTATE sp gp tp F fc PKA).
  Notation LINV := (LINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo).
  Notation ctx_munch' := (ctx_munch L HI ra sp m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP DHI IDL).
  Notation tail_from_linv' := (tail_from_linv L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation iter_head' := (iter_head L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation cmp_chain' := (cmp_chain L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation idloop_walk' := (idloop_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation cleanup_walk' := (cleanup_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation linv_frame' := (linv_frame L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR bs ACL HTOP SPA DHI IDL).



  Notation PEND := (P + LEN).
  Ltac inlist := cbn; repeat (first [ left; reflexivity | right ]).
  (* [comment removed for export] *)
  Ltac dj7 EN EP EA EB EX EY EZ :=
    let d := fresh "d" in let Hd := fresh "Hd" in
    intros d Hd; cbn in Hd; decompose [or] Hd; try contradiction; subst d; rewrite ?EN, ?EP, ?EA, ?EB, ?EX, ?EY, ?EZ; cbn;
    generalize SLO HLS ACL; clear; intros; repeat split; lia.

  Notation SPINV' := (SPINV L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB lo LEN P).
  Notation spinv_munch' := (spinv_munch L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 mo0 h0 LB PKA C lo PAR LEN P bs ACL HTOP DHI IDL).
  Notation spinv_update' := (spinv_update L HI HLS DIMG HND sp m0 mo0 h0 LB lo SLO ACL DHI IDL).
  Notation ctx_bytes' := (ctx_bytes L DIMG sp m0 LB BUF bs HBS0 INB IDL BIM).
  Notation tmp_apart_LB' := (tmp_apart_LB L HI HLS ra sp LB PKA C lo PAR bs NZP DSP DPC NZR DSR RC SLO ACL ACP CAC C0).
  Notation tmp_upd7' := (tmp_upd7 sp).
  Notation tmp_writable' := (tmp_writable L HI sp h0 lo ACL HTOP DHI).
  Notation specC2_walk' := (specC2_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM).
  Notation spec_err' := (spec_err L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).
  Notation spec_erradd' := (spec_erradd L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC INB CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM).

(* [comment removed for export] *)
  Ltac tmp_post m1 m2 d Ed CX1 PX1 TOK1 HH1 HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2 CXo PXo TOKo :=
    let EAD := fresh "EAD" in let HBR1 := fresh "HBR1" in let MDd := fresh "MDd" in let NSd := fresh "NSd" in
    pose proof (proj1 OUT) as EAD;
    destruct (spinv_update' _ _ m1 _ _ _ m2 _ _ d _ _ CX1 PX1 TOK1 ltac:(inlist) HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CXo & PXo & TOKo);
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _];
    pose proof (proj1 (tmp_ok_in usegs _ _ _ _ _ d TOK1 ltac:(inlist))) as MDd;
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) d ltac:(inlist))) as NSd;
    rewrite (mpd_ivs_fp d NSd) in PX2;
    repeat match goal with
    | Hc : rw_cells usegs m1 ?a ?cs |- _ =>
        first [ apply (heap_presx_rw_cells usegs L _ _ _ m1 m2 a cs PX2) in Hc;
                [ | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; let a' := fresh "a'" in let Ha' := fresh "Ha'" in intros a' Ha'; left; clear -Ha'; lia
                  | first [ (* [comment removed for export] *) eapply (fp_disjoint_stack usegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                              | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia]
                          | split; [cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; clear; lia
                                   | eapply (fp_disjoint_stack usegs L d m1); [exact MDd| exact HBR1| clear -ACL SLO HLS; lia
                                     | rewrite Ed; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mpi_cells length]; clear; lia] ] ] ]
              | let t := type of Hc in idtac "DROPCHUNK" t; clear Hc ]
    end;
    clear HBR1 MDd NSd.

  Notation specC_walk' := (specC_walk L HI HFREE HCALLOC HLS SW DIMG HND CA_RSA0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PKA info C lo PAR LEN P BUF bs idpad pP pA pB pX pY pZ pN hpad qd qX qY qZ HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM).

  (* [comment removed for export] *)
  Ltac gt_call SGT FRP FRL HBS MI p ed tg KEEP :=
    acallx (eapply SGT with (PP := REF) (LENP := bv_unsigned sp + -304) (P := p) (END := ed) (BUF := BUF) (bs := bs) (tag := tg);
            first [ exact FRP | exact FRL | exact HBS | exact MI | reflexivity
                  | KEEP
                  | clear -BAC ACL SLO HLS; lia
                  | clear -SPA SPR; lia | clear -ACL ACP SLO HLS; lia | clear -BUF0; lia
                  | clear; lia
                  | f_equal; clear; lia
                  | match goal with |- ?g => idtac "GTLEFT" g end ]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L1229126065.151 L19349569929.0  L31165788229.151L46369226564.0  00001H01I02_02`S1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2BP2PL3B634BUF03SLO3ACL3ACP2C03BAC2EC3ECBSS1L3HLS2ra2sp3PKA1C2lo3PAR3LEN1P3BUF2bs3NZP3NZR2BP2PL3B634BUF03SLO3ACL3ACP2C03BAC1p2PBS". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specB3_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.PdN,$23.PdP,$23.PdA,$23.PdB,$23.PdX,$23.PdY,$23.PdZ,$23.Pp,$4.Plnw,(=.&40.)Pvw,(=.&40.)Ppb,(=.&40.)Pnb,(=.&40.)Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Ppj,(20.(=.&8.))Prj,(20.(=.&8.))PpX,(=.&40.)PpY,(=.&40.)PpZ,(=.&40.)PEC,$4.Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(24.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,VLEN,VP,R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)P,(3.$23.R29.(25.(7.(7.(11.&40.Vsp,)-1?8.)+38.)R1<.))P,(3.$23.R29.(25.(7.(7.(11.&40.Vsp,)-1?8.)+48.)R1<.))P,(3.$23.R29.(25.(7.(7.(11.&40.Vsp,)-1?8.)+58.)R1<.))P,(0.(6.VP,R1<.)(6.R1<.(7.VP,VLEN,)))(26.$10.R32.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.(2=.R1<.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R1;.R1:.R19.(1;.&40.VPKA,)(1;.&40.(7.VP,VLEN,))(1;.&40.R2:.)R18.R17.R16.R15.R14.R13.R12.(1;.&40.(7.(11.&40.Vsp,)-1?0.))(1;.&40.R1=.)R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(1;.&40.+2992<.)Vfc,(2>.(=.&40.))R33.(2?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI DXI DYI DZI ECB.
    dpose SI as (CX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _).
    pose proof CX as (HH & _). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. if_cases KE; zify_cond KE.
    { (* [comment removed for export] *) zstep. zstep. zstep. eapply spec_err'; [exact SI| clear; lia| clear; lia]. }
    rewrite ?Z.mod_small in KE by (clear -PB ECB BP PL B63 BUF0 LEN0; lia).
    eapply specC_walk'; [exact SI| exact DXI| exact DYI| exact DZI].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02a0@D11805467289.226D11805467289.262D13897687993.212D13897687993.257D18360801976.212D18360801976.257D2090238905.264 D22162838905.214D22518009273.212D22518009273.257D24006757689.212D24006757689.257D27373842873.212D27373842873.257D34020630390.212D34020630390.257D36953774137.212D36953774137.257D3986801849.212 D3986801849.257 D4371694009.212 D4371694009.257 D44622288685.264D46200682742.212D46200682742.257D47763733816.212D47763733816.257D49001417753.259D49698585326.264D49705053714.226D49705053714.262D5082246559.264 D52101704109.215D52101704109.260D53269563319.212D53269563319.257D55610685700.264D58526514487.212D58526514487.257D59953809465.212D59953809465.257D68578355769.212D68578355769.257D9383801913.212 D9383801913.257 D9919893866.226 D9919893866.262 D9926296982.264 L11328196705.15 L11423978205.16 L11920359492.17 L12632560433.6  L13302926971.6  L1386329760.225 L14351168243.6  L14368737793.5  L14429712647.1  L15928130581.31 L16093294955.6  L16269778262.3  L16270054593.9  L16270152278.18 L16271922246.13 L16808181456.12 L16810735808.17 L16859315579.6  L17679132023.31 L18933043916.4  L19649668203.6  L19730642225.6  L20032160929.18 L20034454193.13 L20361976947.6  L20380073089.5  L20393681974.31 L20905600099.17 L21101674529.12 L24850858691.8  L25583011654.12 L25730154902.214L26387515891.6  L26820190404.31 L27265566716.16 L27300246154.15 L27668012539.3  L28379935446.3  L28380020182.18 L28380183361.9  L28382051270.13 L28456411139.217L28456411139.253L28877807824.13 L28897400179.6  L29015421609.5  L29558833075.208L29558833075.217L29558833075.252L29558833075.253L29742945110.252L30392002547.6  L30944687130.6  L34347336241.6  L36036252426.11 L36650009439.3  L37808070763.6  L37905822001.6  L38237953557.5  L38574091387.6  L38732773782.8  L38756031563.31 L39935534662.5  L40987796497.9  L40988025478.18 L40990188694.13 L41364395883.6  L41462195249.6  L43068201034.4  L43068429000.8  L43068477917.9  L43068643146.17 L43070280026.12 L43083158376.2  L43144798903.1  L43875673135.3  L44922866283.6  L46030209441.0  L46130367529.5  L46603236713.1  L46696440342.259L49664744988.1  L51182968008.11 L51195676127.31 L51854572294.18 L51854605713.9  L51856473366.13 L52715614025.7  L52715629660.9  L52715793099.18 L52715906507.3  L52717956315.13 L5332920696.15  L54006843703.1  L54973495411.6  L56002663575.31 L56608396471.1  L56732428411.6  L57498838785.5  L57563749431.1  L58742968907.3  L58743151947.18 L58743199945.7  L58743249884.9  L58745051995.13 L58972630378.17 L58974923642.12 L59427867805.203L59539575659.6  L59620532273.6  L60290916219.6  L61120265865.3  L61303378937.31 L62438632883.208L62438632883.217L62438632883.253L63098046059.6  L63176922929.6  L63847289467.6  L64876884407.1  L65728346578.31 L66572612610.3  L68239705399.1  L7018928183.1   L797407480.31   L8322245898.4   L8325611891.6   L9744456571.6   L9788829782.31  00000K00f01:01R01i02D03J04D04X05005D05\06006H07D08D08X09009D09\0:00:H0;V0<R0=R0=i0>D0?H0@:0@Y0A80BE0CA0DA0DU0Dm0F?0FS0Fk0G?0GW0Gk0HC0HW0Ho0IJ0Ie0JS0K30Kg0L90L=0LD0LE0LZ0Lk0Lo0M00M40M<0M=0M>0M?0MY0N30N:0NN0NU0NY0N]0Nd0Nk0O@0OQ0PR0Q:0QM0Qg0R=0RQ0Rf0Rg0S]0TB0TM0TU0TV0TW0TX0U00UH0V10VF0VJ0Vb0W:0WR0Wj0Wk0X@0XU0XY0Xl0Y70Y;0Y?0YC0YJ0Yg0Zd0Zh0[H0[I0[J0[N0[R0[S0[T0[U0[V0[W0[a0[e0\00\40\50\90\=0\U0\Y0]?0]@0]A0]a0]b0^;0^<0^=0^>0^?0^K0^O0^d0^e0^i0_00_A0_E0_F0_G0_`0_a0_b0_n0`:0`;0`?0`C0`J0`U0`e0a=0aU0am0b10b50b<0b@0cA0cL0cP0cT0dU0di0e>0eE0eeS2ra2sp3PKA1C3PAR2bs3ibs2HBS2ra2sp3PKA1C3PAR2bs3ibs2HBS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bs3ibsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C02p43ln43ibs2HB5Ha_st5Hl_stS2ra2sp3PKA1C2lo3PAR2bs1p2EC3x382x33x393x403x414POST3x421HS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C02p43ln43ibs2HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BAC3ibsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bs3ibsS2ra2sp3PKA1C2lo3PAR2bs2EC2p13ln13x663ibs3x543x673x683x694POST3x701HS2ra2sp3PKA1C3PAR2bs3SPR2p43ln43ibs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bs3SPR3ibs2HBS2ra2sp3PKA1C3PAR2bs3SPR3ibs2HBS1L2HI2ra2sp2h03PKA1C3PAR2bs3NZP3NZR4HTOP2C02p43ln43ibs2h23HT32HB5Ha_st5Hl_stS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C01a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C03ibs1a1HS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL2C03BAC2p43ln43ibs2HB5Ha_st5Hl_stS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibs2HBS2ra2sp3PKA1C3PAR2bs3ibs2HBS2ra2sp3PKA1C3PAR2bs2p43ln43ibs2HB5Ha_st5Hl_stS3LEN1P3BUF2bs2BP1p2EC2PB2p13PB1S3LEN1P3BUF2bs2BP2PL1p2EC3ECB2PB2p13ln13PB13LN11a2HaS2bs2EC2p13ln13LN1S2spS2sp2loFS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2spFS2spS2sp3SPAFFFS3LEN1P3BUF2bs2PL1p2EC3ECBS3LEN1P3BUF2bs2PL1p2EC3ECBS2sp2loS1L2HI2sp2h02bs4HTOPS2r12r4S2spS2spS2sp2bsS2sp2bsS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC1p2EC3ECB2p13ln13LN1S3LEN1P3BUF2bs2BP1p2EC2PB2p13ln13PB13LNRS3LEN1P2bs1p2EC3ECBS3LEN1P1p2EC3ECB2PB2p13PB1S3LEN1P3BUF2bs2BP1p2PBS2ra2sp3PKA1C3PAR2bsS1L3HLS2sp2lo3SLO3ACLFS3LEN1P1p2EC3ECB2PB2p13ln12p43ln43PB13LNR3PB44LNR43LN4S3LEN1P3BUF2bs2PL1p2EC3ECB2p13ln13LN1S2r13RR12NZS2sp3SPAFFFS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS3LEN1P1p2EC3ECB2PB2p13ln13PB13LNR2p43PB4S1L3HLS2sp2lo3SLO3ACLS2spS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsFS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS2spS3LEN1P1p2EC3ECB2PBS2r43RR42HqS2spS2spS2loS2sp2loS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS1L3HLS2sp2lo3LEN1P3BUF2bs2BP4BUF03SLO3ACL3ACP1p2EC2PB2p13PB1S2spS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFFS2spS2spFFFFFS3BUF4BUF0S2spS2r23RR22NZS2spSS2spS2spS2ra2sp3PKA1C3PAR2bs3ibsS2spS3LEN1P1p2EC3ECB2PB2p13ln13PB13LN13LNRFFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFS1L3HLS2sp2lo3SLO3ACL3ACPFFFFS2bs3ln13LNRS2spS1L3HLS2sp2lo3SLO3ACLFS2spS2sp2loS1L3HLS2sp2lo3SLOS2spFFS1L3HLS2sp2lo3SLO3ACL3ACPFFS3BUF2bs3B63S3BUF2bs3B63FS2spS2spS2sp2loS2sp2a'3Ha'S1L2sp2lo2bs3SLOS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS2spS2spS2sp2loS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3B633SLO3ACL3BAC1p2EC3ECB2p13ln13LN1S2r13RR12HqS2spS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC1p2EC3ECB2p13ln13LN1S2r13RR11q2Hq2r43RR4S1L3HLS2sp2lo3SLO3ACLS2sp2loS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACP". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specB2_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.PdN,$23.PdP,$23.PdA,$23.PdB,$23.PdX,$23.PdY,$23.PdZ,$23.Pp,$4.Plnw,(=.&40.)Pvw,(=.&40.)Ppb,(=.&40.)Pnb,(=.&40.)Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Ppj,(20.(=.&8.))Prj,(20.(=.&8.))PpB,(=.&40.)PpX,(=.&40.)PpY,(=.&40.)PpZ,(=.&40.)PEC,$4.Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(24.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,VLEN,VP,R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)P,(3.$23.R2<.(25.(7.(7.(11.&40.Vsp,)-1?8.)+28.)R1>.))P,(3.$23.R2<.(25.(7.(7.(11.&40.Vsp,)-1?8.)+38.)R1>.))P,(3.$23.R2<.(25.(7.(7.(11.&40.Vsp,)-1?8.)+48.)R1>.))P,(3.$23.R2<.(25.(7.(7.(11.&40.Vsp,)-1?8.)+58.)R1>.))P,(0.(6.R2<.R1>.)(6.R1>.(7.VP,VLEN,)))(26.$10.R35.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.(2=.R1>.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R1=.R1<.R1;.(1;.&40.VPKA,)(1;.&40.(7.VP,VLEN,))R1:.R19.R18.R17.R16.R15.R14.R13.(1;.&40.(7.(11.&40.Vsp,)-1?0.))(1;.&40.R1?.)R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(1;.&40.+29898.)Vfc,(2>.(=.&40.))R36.(2?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI DBI DXI DYI DZI ECB.
    dpose SI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (ctx_bytes' m PX) as HBS.
    (* [comment removed for export] *)
    pose proof U_asn1_get_tag_spec as SGT. unfold asn1_get_tag_stmt, asn1_get_tag_post, U_ASN1_GET_TAG in SGT.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP FRL HBS MI p EC 4 ltac:(clear -PB ECB BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells usegs m1 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP1; rename q into p1 end.
    match goal with H : rw_cells usegs m1 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL1; rename l into ln1 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end.
    match goal with H : p <= p1 <= _ |- _ => rename H into PB1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into RZ1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI MU1 WM1 MI1
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP1 ltac:(clear -PB PB1 ECB; lia) FRR FRL1 FRM FR0 FRH FRT FR ST) as SI1.
    clear MU1 WM1. match goal with H : ?x = Z_to_bv 64 r1 |- _ => subst x end.
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) assert (NZ : r1 <> 0) by (intros ->; apply K1; reflexivity).
      eapply spec_erradd'; [exact SI1| clear -RR1 NZ; lia| exact MK]. }
    assert (Z1 : r1 = 0).
    { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ1 Z1) as [P2 LN1]. subst r1. clear K1 RZ1 RR1.
    dpose SI1 as (CX1 & PX1 & TOK1 & _). dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1).
    clear SI PX TOK HH HT MF SOK EXT IDS MK HBS HBR HAP. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 HAP1].
    pose proof (bv_unsigned_in_range 64 ln1) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m1 PX1) as HBS1.
    set (ibs := firstn (Z.to_nat (bv_unsigned ln1)) (skipn (Z.to_nat (p1 - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = bv_unsigned ln1) by (subst ibs; apply bytes_at_sub_length; clear -PB PB1 LN1 ECB BP PL LNR; lia).
    assert (HIB : bytes_at usegs m1 p1 ibs) by (subst ibs; eapply bytes_at_sub; [exact HBS1| | |]; clear -PB PB1 LN1 ECB BP PL LNR; lia).
    pose proof (tmp_ok_in usegs _ _ _ _ _ dB TOK1 ltac:(inlist)) as MDB.
    pose proof (U_mpi_read_binary_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl) as SRB. unfold mpi_read_binary_stmt, mpi_read_binary_post, U_MPI_READ_BINARY in SRB.
    zstep. zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply SRB with (lo := lo) (h := h) (LB := LBi) (dX := dB) (B := p1) (ibs := ibs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia); rewrite ?LENI;
        first [ exact HH1 | exact MDB | exact HIB | exact TP | exact MI1 | exact SOK1 | exact CA | eassumption
              | subst dB; cbn; discriminate
              | rewrite HT1; eapply tmp_writable'; [exact HH1| exact TOK1| inlist| clear -SLO HLS; lia| clear; lia]
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [eapply lb_ext_sub; [exact EXT1| exact INB]| cbn; clear -Ha PB PB1 LN1 ECB BP PL; lia]
              | subst dB; cbn; intros O; discriminate O
              | rewrite ?EB; rewrite ?HT1; clear -PB PB1 LN1 ECB LNR BP PL B63 BUF0 BAC ACL ACP SLO HLS HTOP SPA SPR DHI; lia
              | reflexivity | rewrite EB; f_equal; clear; lia | symmetry; apply definitions.Z_to_bv_bv_unsigned
              | match goal with |- ?g => idtac "RBLEFT" g end ]. }
    clear SRB.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & HH2 & MD2 & OUT2 & PX2 & SOK2 & RR2 & RN2 & NEW2).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    match type of HH2 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB2 end.
    match type of MD2 with mpd_at _ _ _ ?dd => rename dd into dB' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r2 end.
    change (mpd_ivs dB) with ([] ++ mpd_ivs dB) in PX2.
    tmp_post m1 m2 dB EB CX1 PX1 TOK1 HH1 HH2 HT2 MF2 MI2 SOK2 MD2 OUT2 NEW2 PX2 CX2 PXn2 TOK2.
    pose proof (eq_trans EAD EB) as EB'.
    rewrite (proj1 (proj2 (proj2 (proj2 (tmp_upd7' dB' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ)))) EB') in CX2, TOK2.
    assert (SI2 : SPINV' h2 LB2 m2 mo2 dN dP dA dB' dX dY dZ p1 ln1 vw pb nb scj hj tj pj rj).
    { split; [exact CX2|]. split; [exact PXn2|]. split; [exact TOK2|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB'|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact FRP1|]. split; [clear -PB PB1 ECB; lia|]. split; [exact FRR|]. split; [exact FRL1|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST2]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear CX1 PX1 TOK1 HH1 HT1 MF1 SOK1 EXT1 IDS1 MK1 HBS1 HIB MDB PX2 HBR1 HAP1 CX2 PXn2 TOK2 MI1.
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2.
    { assert (NZ : r2 <> 0) by (intros ->; apply K2; reflexivity). unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in RR2. eapply spec_erradd'; [exact SI2| clear -RR2 NZ; lia| exact MK2]. }
    clear K2 RR2 RN2.
    (* [comment removed for export] *)
    clear HH2 HT2 MF2 SOK2 MD2 OUT2 NEW2 EAD ST.
    pose proof (munch_refl [(REF, REF + 8)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN; [pnull KN|].
    zstep. replace (bv_unsigned ln1 + p1) with (p1 + bv_unsigned ln1) in * by lia.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end. match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end.
    match goal with H : rw_cells usegs m3 REF [C8 _] |- _ => rename H into FRP3 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI2 MU WM3 MI3
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB' EX EY EZ)
                  FRP3 ltac:(clear -PB PB1 LN1 ECB LNR; lia) FRR FRL1 FRM FR0 FRH FRT FR ltac:(assumption)) as SI3.
    dpose SI3 as (CX3 & PX3 & TOK3 & _). dpose CX3 as (HH3 & HT3 & MF3 & _ & SOK3 & EXT3 & IDS3).
    clear MU WM3 SI2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3. clear MK2.
    pose proof (ctx_bytes' m3 PX3) as HBS3.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP3 FRL1 HBS3 MI3 (p1 + bv_unsigned ln1) EC 3 ltac:(clear -PB PB1 LN1 LNR ECB BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells usegs m4 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP4; rename q into p4 end.
    match goal with H : rw_cells usegs m4 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL4; rename l into ln4 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR4; rename r into r4 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR4; rename r into r4 end.
    match goal with H : _ <= p4 <= _ |- _ => rename H into PB4 end.
    match goal with H : r4 = 0 -> _ |- _ => rename H into RZ4 end.
    match goal with M : mem_inv usegs m4 |- _ => rename M into MI4 end.
    match goal with W : wmono usegs m3 m4 |- _ => rename W into WM4 end. rename MU into MU4.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI3 MU4 WM4 MI4
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB' EX EY EZ)
                  FRP4 ltac:(clear -PB PB1 PB4 LN1 LNR ECB; lia) FRR FRL4 FRM FR0 FRH FRT FR ltac:(assumption)) as SI4.
    clear MU4 WM4. match goal with H : ?x = Z_to_bv 64 r4 |- _ => subst x end.
    pose proof SI4 as (CX4 & _). pose proof CX4 as (HH4 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    pose proof (bv_unsigned_in_range 64 ln4) as LNR4. change (bv_modulus 64) with (2^64) in LNR4.
    (* [comment removed for export] *)
    zstep.
    zstep. if_cases K4; zify_cond K4.
    2:{ (* [comment removed for export] *) zstep. zstep. eapply specB3_walk; [exact SI4| exact DXI| exact DYI| exact DZI| clear -PB PB1 ECB LN1 LNR; lia]. }
    assert (Z4 : r4 = 0).
    { clear -K4 RR4. apply Z.mod_divide in K4; [| lia]. destruct K4 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ4 Z4) as [P5 LN4]. subst r4. clear K4 RZ4 RR4.
    (* [comment removed for export] *)
    pose proof (munch_refl [(REF, REF + 8)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    zstep. zstep. zstep. if_cases KW5; zify_cond KW5; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN5; zify_cond KN5; [pnull KN5|].
    zstep. replace (bv_unsigned ln4 + p4) with (p4 + bv_unsigned ln4) in * by lia.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with M : mem_inv usegs m5 |- _ => rename M into MI5 end. match goal with W : wmono usegs m4 m5 |- _ => rename W into WM5 end.
    match goal with H : rw_cells usegs m5 REF [C8 _] |- _ => rename H into FRP5 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI4 MU WM5 MI5
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB' EX EY EZ)
                  FRP5 ltac:(clear -PB PB1 PB4 LN1 LN4 ECB LNR LNR4; lia) FRR FRL4 FRM FR0 FRH FRT FR ltac:(assumption)) as SI5.
    eapply specB3_walk; [exact SI5| exact DXI| exact DYI| exact DZI| clear -PB PB1 ECB LN1 LNR; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02V0@D11805467289.247D13897687993.213D13897687993.233D18360801976.213D18360801976.233D22518009273.213D22518009273.233D24006757689.213D24006757689.233D24323521813.235D27373842873.213D27373842873.233D29298517109.215D34020630390.213D34020630390.233D36953774137.213D36953774137.233D3986801849.213 D3986801849.233 D4371694009.213 D4371694009.233 D46200682742.213D46200682742.233D47763733816.213D47763733816.233D49705053714.247D52101704109.216D52101704109.236D53269563319.213D53269563319.233D58526514487.213D58526514487.233D59953809465.213D59953809465.233D68578355769.213D68578355769.233D9383801913.213 D9383801913.233 D9919893866.247 L10472341635.246L11328196705.15 L11423978205.18 L12258919114.2  L12421309367.1  L12632560433.6  L13302926971.6  L1386329760.225 L1392622547.3   L14351168243.6  L14368737793.5  L14411982930.15 L1559264055.1   L15930225205.34 L16038473375.18 L16093294955.6  L16269778262.3  L16270054593.9  L16270152278.16 L16271922246.11 L16859315579.6  L17668647767.34 L18933043916.4  L19649668203.6  L19730642225.6  L20032160929.16 L20034454193.11 L20361976947.6  L20380073089.5  L21276178103.34 L21354991308.18 L22302152298.14 L23270378039.1  L24763131158.235L24850858691.6  L25583011654.10 L26387515891.6  L27300246154.15 L28379935446.3  L28380020182.16 L28380183361.9  L28382051270.11 L28456411139.238L28897400179.6  L29015421609.5  L29558833075.201L29558833075.230L29558833075.238L2981613086.34  L30392002547.6  L30944687130.6  L31471788297.3  L33734336981.10 L34347336241.6  L36784650892.34 L37808070763.6  L37905822001.6  L38237953557.5  L38574091387.6  L38732773782.8  L39935534662.5  L40515328308.34 L40987796497.9  L40988025478.16 L40990188694.11 L41364395883.6  L41462195249.6  L43068201034.4  L43068429000.8  L43068477917.9  L43068643146.15 L43070280026.10 L43083158376.2  L43875673135.3  L44256491740.18 L44922866283.6  L45374645815.1  L45739397526.215L46130367529.5  L46350850038.11 L48569119449.14 L49014974569.1  L49664744988.1  L49939655457.0  L51854572294.16 L51854605713.9  L51856473366.11 L52089062525.34 L52104085303.1  L52715614025.7  L52715629660.9  L52715793099.16 L52715906507.3  L52717956315.11 L54214706158.34 L54973495411.6  L56732428411.6  L57498838785.5  L58742968907.3  L58743151947.16 L58743199945.7  L58743249884.9  L58745051995.11 L58972630378.15 L58974923642.10 L59408831671.1  L59427867805.204L59539575659.6  L59620532273.6  L60290916219.6  L61120265865.3  L61288701401.34 L62438632883.201L62438632883.230L62438632883.238L63080246294.34 L63098046059.6  L63176922929.6  L63216279672.10 L63847289467.6  L66572612610.3  L66867980551.1  L67677319607.1  L8322245898.4   L8325611891.6   L9744456571.6   L9790930550.34  00000K00_01301J01a02502I02]03103n04B04V05S06O07K07_08308G08[08o09C0:?0;;0;R0;i0<H0=D0>@0>T0>h0?<0?P0?d0@80@L0@`0A40AH0Ac0Ad0BA0C=0CE0CI0CM0CT0CU0C`0D50DF0DU0DY0DZ0Dg0Dk0E30E40E50E60E=0EQ0EX0E\0E`0Eg0En0FC0FT0FU0G<0Gk0Go0HC0HV0Hl0IA0I]0Ie0If0Ig0Ih0J@0JU0JY0Jm0KE0K]0Lb0M70ML0MW0Mf0Mj0Nm0O10O50O90O@0O]0Oa0Ob0PB0PC0PD0PH0PL0PM0PN0PO0PP0PQ0P[0Pf0QN0QR0QV0Qj0Qn0RP0Rm0S10S50S60S70SW0SX0SY0S]0T60T70T80T90T:0U=0UR0UY0Uj0Uk0Ul0VE0VF0VG0VS0V_0Vc0Vd0Vh0Vl0W30W>0WN0Wb0X:0XR0YU0YY0Y]0Yn0Z50Z@0ZD0ZH0Z\0[10[80[XS2ra2sp3PKA1C3PAR2bs3ibs2HBS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C2lo3PAR2bs3x532p13ln13x413x543x553x564POST3x571HS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C2lo3PAR3LEN1P2bs1p3x392x33x403x413x424POST3x431HS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL3ACP2C03BACS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C2lo3PAR2bsS2ra2sp3PKA1C3PAR2bs3SPR3ibs2HBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C01a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI3ACP2C01a1HS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibs2HBFS3LEN1P3BUF2bs2BP1p2PB2p13PB1S3LEN1P3BUF2bs2BP2PL1p2PB2p13ln13PB13LN12p23ln23PB23LN21a2HaS2r13RR1S2spS2spS2sp2loFS2r33RR32NZS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2bs2p13ln13LNRS2spFS2bs3ln24LNR2S2spS2sp3SPAFFFS2sp2loS1L2HI2sp2h02bs4HTOPS2r12r2S2spS2spS2sp2bsS2sp2bsS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOFS3LEN1P3BUF2bs2PL2p13ln13LN12p23ln23LN2S3LEN1P1p2PB2p23ln22p13ln13PB13LN13PB23LN24LNR2S2spS2ra2sp3PKA1C3PAR2bsS3LEN1P1p2PB2p13PB1S3LEN1P3BUF2bs2BP1p2PBS1L3HLS2sp2lo3SLO3ACLS3LEN1P3BUF2bs2PL2p13ln13LN1S2sp3SPAFFFS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2sp2lo3SLO3ACLS2spS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2sp2lo3LEN1P3BUF2bs2BP4BUF03SLO3ACL3ACP1p2PB2p13ln13PB12p23PB2S1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLO3ACLS2r23RR22HqS3LEN1P2bs1p2PBS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3B633SLO3ACL3BAC2p13ln13LN12p23ln23LN2S2spS2spS2loS2sp2loS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS2spFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFFS2spS2spFFFFFS3BUF4BUF0S2r23RR22NZS3LEN1P3BUF2bs2BP1p2PB2p13ln13PB12p23PB2S2spS2spS2ra2sp3PKA1C3PAR2bsS2spS3LEN1P1p2PB2p13ln13PB13LN12p23PB2S3LEN1P2p23ln22p13ln13LN13LN2S2spS2spSFS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFFS2spS1L3HLS2sp2lo3SLO3ACL3ACPFFFFS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC2p13ln13LN12p23ln23LN2S1L3HLS2sp2lo3SLO3ACLS2sp2loS1L3HLS2sp2lo3SLOFFS1L3HLS2sp2lo3SLO3ACL3ACPFFS3BUF2bs3B63S3BUF2bs3B63S2spFS2spS2spS2sp2loS2sp2a'3Ha'S1L2sp2lo2bs3SLOS2ra2sp3PKA1C3PAR2bsS2ra2sp3PKA1C3PAR2bs3ibsS2ra2sp3PKA1C3PAR2bs3ibsS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC2p13ln13LN12p23ln23LN2S2spS2spS3LEN1P3BUF2bs2PLS2sp2loS2r13RR12HqS2spS2spS2r13RR11q2Hq2r23RR2S1L3HLS2sp2lo3SLO3ACLS2sp2loS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACP". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specB_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_J ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.PdN,$23.PdP,$23.PdA,$23.PdB,$23.PdX,$23.PdY,$23.PdZ,$23.Pp,$4.Plnw,(=.&40.)Pvw,(=.&40.)Ppb,(=.&40.)Pnb,(=.&40.)Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Ppj,(20.(=.&8.))Prj,(20.(=.&8.))PpA,(=.&40.)PpB,(=.&40.)PpX,(=.&40.)PpY,(=.&40.)PpZ,(=.&40.)Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(24.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,VLEN,VP,R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)P,(3.$23.R2>.(25.(7.(7.(11.&40.Vsp,)-1?8.)+18.)R1?.))P,(3.$23.R2>.(25.(7.(7.(11.&40.Vsp,)-1?8.)+28.)R1?.))P,(3.$23.R2>.(25.(7.(7.(11.&40.Vsp,)-1?8.)+38.)R1?.))P,(3.$23.R2>.(25.(7.(7.(11.&40.Vsp,)-1?8.)+48.)R1?.))P,(3.$23.R2>.(25.(7.(7.(11.&40.Vsp,)-1?8.)+58.)R1?.))(26.$10.R36.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.(2=.R1?.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R1>.R1=.R1<.(1;.&40.VPKA,)(1;.&40.(7.VP,VLEN,))R1;.R1:.R19.R18.R17.R16.R15.R14.(1;.&40.(7.(11.&40.Vsp,)-1?0.))R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)VF,(1;.&40.+29810.)Vfc,(2>.(=.&40.))R37.(2?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI DAI DBI DXI DYI DZI.
    dpose SI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (ctx_bytes' m PX) as HBS.
    (* [comment removed for export] *)
    pose proof U_asn1_get_tag_spec as SGT. unfold asn1_get_tag_stmt, asn1_get_tag_post, U_ASN1_GET_TAG in SGT.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP FRL HBS MI p (P + LEN) 0x30 ltac:(clear -PB BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells usegs m1 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP1; rename q into p1 end.
    match goal with H : rw_cells usegs m1 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL1; rename l into ln1 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end.
    match goal with H : p <= p1 <= _ |- _ => rename H into PB1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into RZ1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI MU1 WM1 MI1
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP1 ltac:(clear -PB PB1; lia) FRR FRL1 FRM FR0 FRH FRT FR ST) as SI1.
    clear MU1 WM1. match goal with H : ?x = Z_to_bv 64 r1 |- _ => subst x end.
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *) assert (NZ : r1 <> 0) by (intros ->; apply K1; reflexivity).
      zstep. zstep. eapply spec_err'; [exact SI1| clear -RR1; lia| exact NZ]. }
    assert (Z1 : r1 = 0).
    { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ1 Z1) as [P2 LN1]. subst r1. clear K1 RZ1 RR1.
    dpose SI1 as (CX1 & PX1 & TOK1 & _). dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1).
    clear SI PX TOK HH HT MF SOK EXT IDS MK HBS HBR HAP. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    pose proof (bv_unsigned_in_range 64 ln1) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN; zify_cond KN; [pnull KN|].
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m1 PX1) as HBS1.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep.
    gt_call SGT FRP1 FRL1 HBS1 MI1 p1 (p1 + bv_unsigned ln1) 4 ltac:(clear -PB PB1 LN1 LNR BP LEN0 PL B63; lia).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : rw_cells usegs m2 REF [C8 (Z_to_bv 64 ?q)] |- _ => rename H into FRP2; rename q into p2 end.
    match goal with H : rw_cells usegs m2 (bv_unsigned sp + -304) [C8 ?l] |- _ => rename H into FRL2; rename l into ln2 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR2; rename r into r2 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR2; rename r into r2 end.
    match goal with H : p1 <= p2 <= _ |- _ => rename H into PB2 end.
    match goal with H : r2 = 0 -> _ |- _ => rename H into RZ2 end.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end.
    match goal with W : wmono usegs m1 m2 |- _ => rename W into WM2 end. rename MU into MU2.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI1 MU2 WM2 MI2
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP2 ltac:(clear -PB PB1 PB2 LN1 LNR; lia) FRR FRL2 FRM FR0 FRH FRT FR ST) as SI2.
    clear MU2 WM2. match goal with H : ?x = Z_to_bv 64 r2 |- _ => subst x end.
    pose proof (heap_mok _ _ HI _ _ _ _ (proj1 (proj1 SI2))) as MK2.
    zstep. if_cases K2; zify_cond K2.
    { assert (NZ : r2 <> 0) by (intros ->; apply K2; reflexivity). eapply spec_erradd'; [exact SI2| clear -RR2 NZ; lia| exact MK2]. }
    assert (Z2 : r2 = 0).
    { clear -K2 RR2. apply Z.mod_divide in K2; [| lia]. destruct K2 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ2 Z2) as [P3 LN2]. subst r2. clear K2 RZ2 RR2.
    dpose SI2 as (CX2 & PX2 & TOK2 & _). dpose CX2 as (HH2 & HT2 & MF2 & _ & SOK2 & EXT2 & IDS2).
    clear SI1 CX1 PX1 TOK1 HH1 HT1 MF1 SOK1 EXT1 IDS1 MK1 HBS1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2].
    pose proof (bv_unsigned_in_range 64 ln2) as LNR2. change (bv_modulus 64) with (2^64) in LNR2.
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m2 PX2) as HBS2.
    set (ibs := firstn (Z.to_nat (bv_unsigned ln2)) (skipn (Z.to_nat (p2 - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = bv_unsigned ln2) by (subst ibs; apply bytes_at_sub_length; clear -PB PB1 PB2 LN1 LN2 BP PL LNR LNR2; lia).
    assert (HIB : bytes_at usegs m2 p2 ibs) by (subst ibs; eapply bytes_at_sub; [exact HBS2| | |]; clear -PB PB1 PB2 LN1 LN2 BP PL LNR LNR2; lia).
    pose proof (tmp_ok_in usegs _ _ _ _ _ dA TOK2 ltac:(inlist)) as MDA.
    pose proof (U_mpi_read_binary_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl) as SRB. unfold mpi_read_binary_stmt, mpi_read_binary_post, U_MPI_READ_BINARY in SRB.
    zstep. zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply SRB with (lo := lo) (h := h) (LB := LBi) (dX := dA) (B := p2) (ibs := ibs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia); rewrite ?LENI;
        first [ exact HH2 | exact MDA | exact HIB | exact TP | exact MI2 | exact SOK2 | exact CA | eassumption
              | subst dA; cbn; discriminate
              | rewrite HT2; eapply tmp_writable'; [exact HH2| exact TOK2| inlist| clear -SLO HLS; lia| clear; lia]
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [eapply lb_ext_sub; [exact EXT2| exact INB]| cbn; clear -Ha PB PB1 PB2 LN1 LN2 BP PL; lia]
              | subst dA; cbn; intros O; discriminate O
              | rewrite ?EA; rewrite ?HT2; clear -PB PB1 PB2 LN1 LN2 LNR LNR2 BP PL B63 BUF0 BAC ACL ACP SLO HLS HTOP SPA SPR DHI; lia
              | reflexivity | rewrite EA; f_equal; clear; lia | symmetry; apply definitions.Z_to_bv_bv_unsigned
              | match goal with |- ?g => idtac "RBLEFT" g end ]. }
    clear SRB.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI3 & ST3 & MF3 & HT3 & HH3 & MD3 & OUT3 & PX3 & SOK3 & RR3 & RN3 & NEW3).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m3; rename mox into mo3 end.
    match type of HT3 with heap_top _ _ _ ?hh = _ => rename hh into h3 end.
    match type of HH3 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB3 end.
    match type of MD3 with mpd_at _ _ _ ?dd => rename dd into dA' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r3 end.
    change (mpd_ivs dA) with ([] ++ mpd_ivs dA) in PX3.
    tmp_post m2 m3 dA EA CX2 PX2 TOK2 HH2 HH3 HT3 MF3 MI3 SOK3 MD3 OUT3 NEW3 PX3 CX0 PXn2 TOK0.
    pose proof (eq_trans EAD EA) as EA'.
    rewrite (proj1 (proj2 (proj2 (tmp_upd7' dA' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ))) EA') in CX0, TOK0.
    assert (SI3 : SPINV' h3 LB3 m3 mo3 dN dP dA' dB dX dY dZ p2 ln2 vw pb nb scj hj tj pj rj).
    { split; [exact CX0|]. split; [exact PXn2|]. split; [exact TOK0|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA'|]. split; [exact EB|]. split; [exact EX|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact FRP2|]. split; [clear -PB PB1 PB2 LN1 LNR; lia|]. split; [exact FRR|]. split; [exact FRL2|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST3]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    clear CX2 PX2 TOK2 HH2 HT2 MF2 SOK2 EXT2 IDS2 MK2 HBS2 HIB MDA PX3 HBR2 HAP2 CX0 PXn2 TOK0 MI2 SI2.
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    { assert (NZ : r3 <> 0) by (intros ->; apply K3; reflexivity). unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in RR3. eapply spec_erradd'; [exact SI3| clear -RR3 NZ; lia| exact MK3]. }
    clear K3 RR3 RN3 HH3 HT3 MF3 SOK3 MD3 OUT3 NEW3 EAD ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(REF, REF + 8)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. zstep. zstep. zstep. if_cases KW4; zify_cond KW4; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases KN4; zify_cond KN4; [pnull KN4|].
    zstep. replace (bv_unsigned ln2 + p2) with (p2 + bv_unsigned ln2) in * by lia.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with M : mem_inv usegs m4 |- _ => rename M into MI4 end. match goal with W : wmono usegs m3 m4 |- _ => rename W into WM4 end.
    match goal with H : rw_cells usegs m4 REF [C8 _] |- _ => rename H into FRP4 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI3 MU WM4 MI4
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA' EB EX EY EZ)
                  FRP4 ltac:(clear -PB PB1 PB2 LN1 LN2 LNR LNR2; lia) FRR FRL2 FRM FR0 FRH FRT FR ltac:(assumption)) as SI4.
    eapply specB2_walk; [exact SI4| exact DBI| exact DXI| exact DYI| exact DZI| clear -PB PB1 PB2 LN1 LN2 LNR LNR2; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
