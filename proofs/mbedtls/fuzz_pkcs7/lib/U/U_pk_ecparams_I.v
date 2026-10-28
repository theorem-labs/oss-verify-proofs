(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_ecp_keypair_init U_ecp_group_free U_ecp_group_load U_ecp_group_load_main U_ecp_defs U_ecp_mul_mod U_ecp_grp_id_list U_ecp_point_free U_asn1_get_sequence_of_A U_pk_wrap_eckey U_pk_free U_pk_type U_pk_ecc_set_group U_ecp_sinv U_string U_oid U_oidv U_oid_ec_grp U_oid_ec_grp_v U_ecp_group_init U_mpi_cmp U_mpi_bitlen U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_C U_pk_ecparams_D U_pk_ecparams_E U_pk_ecparams_F U_pk_ecparams_G U_asn1_get_tag U_asn1_get_int U_asn1_get_mpi U_mpi_read_binary U_mpi_read_binary_proof U_mpi_lset U_pk_ecparams_H.
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
Ltac2 gd_tbl_P_pk_ecparams_I () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_H.SPINV"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_pk_ecparams_A.pk_use_ecparams_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_keypair_init.kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].



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
  #[using="HI m0 mo0 h0 LB HH0 INC INB ACP"] Lemma ep_basics : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_I ()) "(0.(1.+1000.(2.VL,))(0.(1.=VC,)(0.(3.$4.(5.VC,+10.)=)(0.(6.(7.VC,+100.)(2.VL,))(0.(8.(6.(7.VC,+100.)(9.VL,))(6.(:.VL,)VC,))(0.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(2.VL,))(8.(6.(7.VBUF,(;.(<.(=.&8.)Vbs,)))(9.VL,))(6.(:.VL,)VBUF,))))))))")
(* [comment removed for export] *).
  Proof.
    destruct (heap_blocks _ _ HI _ _ _ _ HH0) as [HBR _].
    pose proof (proj1 (Forall_forall _ _) HBR _ INC) as (C0' & C16' & _ & CAC' & CIM'). cbn in C0', C16', CAC', CIM'.
    pose proof (proj1 (Forall_forall _ _) HBR _ INB) as (_ & _ & _ & BAC' & BIM'). cbn in BAC', BIM'. auto 10.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L2647750340.6  L2726914452.6  L52616404933.1000000D00X016S1L3PKA3PKD2I12I22I3S1L3PKA3PKD2I12I22I3S1L2HI2sp2h03PKA2lo3DSP1a2Ha1Q". (* [comment removed for export] *)
  #[using="HI h0 lo HPKA0 DSP CWP PKD IDL"] Lemma ctx_pka : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_I ()) "Pm,P,(=.&40.)(>.(=.&8.))P,(?.$10.VL,VLB,(11.&40.Vsp,)(12.(13.$4.$4.)(14.$4.$4.$15.(7.$15.+1.))(12.(13.$4.$4.)(14.$4.$4.$16.(7.$16.+38.))(17.(13.$4.$4.))))Vm0,R1.)(18.$10.R2.VPKA,(12.$19.(1:.(1;.&40.Vinfo,))(12.$19.(1:.(1;.&40.VC,))(17.$19.))))")
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
  #[using="IDL"] Lemma IL4 : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_I ()) "Pa,$4.P,(8.(0.(6.$15.R1.)(1.R1.(7.$15.+1.)))(0.(6.$16.R1.)(1.R1.(7.$16.+38.))))(0.(1<.VL,R2.)(1=.(1>.VL,R2.)))")
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
  Ltac tmp_post m1 m2 d Ed CX1 PX1 TOK1 HH1 HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2 :=
    let EAD := fresh "EAD" in let HBR1 := fresh "HBR1" in let MDd := fresh "MDd" in let NSd := fresh "NSd" in
    pose proof (proj1 OUT) as EAD;
    destruct (spinv_update' _ _ m1 _ _ _ m2 _ _ d _ _ CX1 PX1 TOK1 ltac:(inlist) HH2 HT2 MF2 MI2 SOK2 MD2 OUT NEW PX2
                ltac:(repeat constructor; cbn; clear -SLO HLS ACL; lia) ltac:(repeat constructor; cbn; clear -SLO HLS; lia)) as (CX2 & PXn2 & TOK2);
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

    (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03T0@D13897687993.210D18006987857.232D18360801976.210D18391880017.232D18412151797.253D22518009273.210D24006757689.210D25051751723.253D27373842873.210D28500980433.232D28885876689.232D29287336821.253D29298517109.212D34020630390.210D36953774137.210D37425516612.232D39083495786.253D39729596241.232D3986801849.210 D40144179957.253D4184545269.253 D4371694009.210 D44484923210.232D44487020398.253D46200682742.210D47034285009.232D47763733816.210D50588036817.232D52101704109.213D52101704109.234D52101704109.255D52422005.253   D53269563319.210D55620435040.253D58526514487.210D59953809465.210D60018419983.232D62231236341.253D62405389173.233D68578355769.210D68695437845.254D7562631285.253 D9383801913.210 L1017739819.4   L10892767639.2  L10895389109.14 L11423978205.15 L1155694775.1   L11628653111.1  L12017219383.1  L12632560433.6  L13302926971.6  L14351168243.6  L14368737793.5  L14494349489.276L15268985961.1  L1556779782.2   L15928130589.30 L16075571817.215L16075573500.215L16093294955.6  L16269778262.3  L16270054593.9  L16271922246.11 L16596701601.0  L16859315579.6  L17679081717.13 L17679132031.30 L18033084087.1  L18400595127.1  L18457785511.0  L18933043916.4  L19628480007.234L19649668203.6  L19730642225.6  L20034454193.11 L20361976947.6  L20380073089.5  L20540342678.212L21959505626.0  L22871007159.1  L24850858691.6  L251316151.1    L25583011654.10 L26233299767.1  L26387515891.6  L27487314458.30 L27588840607.30 L27668012539.3  L27837460028.5  L28379935446.3  L28380183361.9  L28382051270.11 L28509839415.1  L28882152759.1  L28897400179.6  L29015421609.5  L29253727031.1  L29558833075.205L29558833075.219L29558833075.240L29558833075.258L29722050409.1  L29742945110.256L30350278707.6  L30392002547.6  L30718654727.1  L30944687130.6  L3210077857.0   L32150172265.1  L32477877451.216L33732527671.1  L33734336981.10 L34347336241.6  L35862758523.11 L35864591583.5  L36757149239.1  L37421193428.224L37808070763.6  L37905822001.6  L38237953557.5  L38572570118.2  L38574091387.6  L38732773782.8  L39752062391.1  L39846539064.30 L39935534662.5  L40115772343.1  L40442210004.14 L40987796497.9  L40990188694.11 L41364395883.6  L41462195249.6  L42151037797.11 L42157884193.0  L42605012206.14 L42605012206.2  L43068201034.4  L43068429000.8  L43068477917.9  L43070280026.10 L43083158376.2  L44074763222.229L44074763222.268L44360025120.257L44360025126.216L44374806436.218L44480858074.224L44480858074.244L44487020398.244L44922866283.6  L46130367529.5  L46987149575.1  L47056808247.1  L47207771303.4  L47209306414.14 L475978495.11   L47901161914.30 L48409000767.11 L4932803255.1   L49661608318.11 L49664744988.1  L49846535446.228L50600009991.1  L50614238263.1  L50751898717.5  L50985812535.1  L51358125879.1  L51390623401.0  L51854605713.9  L51856473366.11 L52494493908.299L52715614025.7  L52715629660.9  L52715906507.3  L52717956315.11 L53134281077.10 L54348679437.30 L54496546231.1  L54973495411.6  L55620435040.244L55630787796.244L56547749183.13 L56732428411.6  L57498838785.5  L58742968907.3  L58743199945.7  L58743249884.9  L58745051995.11 L58767924669.14 L58974923642.10 L59427867805.201L59539575659.6  L59620532273.6  L60290916219.6  L61120265865.3  L61303378929.30 L61900301956.0  L62135540095.30 L62438632883.205L62438632883.225L62438632883.240L62820123290.14 L63098046059.6  L63176922929.6  L63216279672.10 L63267834119.1  L63735521057.30 L63847289467.6  L64010299185.11 L66572612610.3  L6700149497.5   L6700191867.13  L6701943322.3   L67019580928.219L6976152114.249 L8322245898.4   L8325611891.6   L9744456571.6   L9787043636.1   L9788617045.5   L9788620630.3   L9788829782.11  L9788829790.30  L9788854102.3   L9788913108.13  R38730382473.213R38730382473.23400000H00`01;01S01k02C02[03303K03c04;04S05T06P06h06i07e08=08U08m09E09]09^09_0:[0;30;N0;f0<b0=^0>Z0?20?J0?K0?c0@;0@S0@k0Aa0B90C;0CS0Ck0Cl0Cm0Cn0D[0D_0Dc0Dg0Dk0E20EG0EX0EY0E]0Ee0Ef0Eg0Eh0El0F40F50F60F70F>0FO0Fc0Fg0Fk0Fl0G00G10G50G90G@0GU0Gf0H>0H?0HC0HV0HZ0I00I40II0JA0JB0JM0J^0Jf0Jg0Jh0Jl0K00KE0KI0KM0Ke0L=0LY0M50M90M:0M;0MP0MT0Mi0Mj0Mn0O10O50OD0OH0OX0Oh0Ol0Om0P10P50P90P@0PG0Pd0Ph0Qb0Qf0Qj0R:0RZ0R[0R_0Rc0S<0S=0S>0S?0S@0SA0SB0SC0SM0Sl0TO0UN0VI0WD0WE0WF0WG0WK0WO0WS0WW0WX0WY0Wa0XY0Y20Y60Y:0Y>0YV0YZ0Y^0Z00Z40Z80Z90ZY0ZZ0Z[0[40[50[60[70[E0[F0[J0[_0[`0[a0[b0[i0\:0\;0\T0\U0\V0]20]>0]?0]C0]G0]N0]Y0]i0]j0]k0^C0^[0_70_T0_X0_\0_m0`10`i0a00aS0a^0a_0al0am0bE0b]0bj0c?0cF0cG0cH0cP0cm0dM0dN0dk0eg0fcS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C2lo3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C2lo3PAR3LEN1P2bs1p3x393GTB2x33x403x413x424POST3x431HS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL2C03BAC3GTBS2ra2sp3PKA1C3PAR2bs3GTBFS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL2C03BAC3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBFFS1L3HLS2ra2sp3PKA1C2lo3PAR3BUF2bs3NZP3NZR3SLO3ACL2C03BAC3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C2lo3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C03GTB1a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C03GTB1a1HS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3DHI2C03GTB1a1HS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBFS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C03GTB3x531HS2ra2sp3PKA1C3PAR2bs3GTBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO2C03GTB3ln13LNR3LNZ3x671HS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBFFFS3LEN1P3BUF2bs2BP2PL1p2PB2p13ln13PB13LN11a2HaS2spS2spS2spS2spS2sp2loS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOFS2spS2b03B0RFFFS2spS2sp3SPAFFSS2sp2loS1L2HI2sp2h04HTOPS1L2HI2sp2h02bs4HTOPS2spS2spSS2r1FS2spS2spS2sp2bsS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3SLOS2ra2sp3PKA1C3PAR2bs3GTBFS2spS3LEN1P1p2PB2p13PB1S2spS3LEN1P3BUF2bs2BP1p2PBS2spS1L3HLS2sp2lo3SLO3ACLS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC2p13ln13LN1FS2r13RR12NZS1L3HLS2sp2lo3SLOS2sp3SPAFFS2spS2spS1L3HLS2sp2lo3SLO3ACLS2spS2spS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTB3ibsS2ra2sp3PKA1C3PAR2bs3GTB3ibsS2spFFS1L3HLS2sp2lo3SLO3ACLS2spS1L3HLS2sp2lo3SLO3ACLSS2spS2ra2sp3PKA1C3PAR3LEN1P3BUF2bs3NZP3NZR2PL2C03GTB2p13ln13LN13LNR3LNZS2spS3LEN1P2bs1p2PBS2spS1L2lo2dP2P43ACLS1L2lo3ACL2dP2P4S2spFS2spS2spS2loS2sp2loS2sp2loS1L3HLS2sp2lo3SLO3ACL3SPR3ACPS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2BP4BUF03SLO3ACL3ACP1p2PB2p13PB1S2spS2spS2bs3ln13LNR3LNZS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFS2spS2spS1L3HLS2sp2lo3SLO3ACL3ACPSFFFFFFS3BUF4BUF0S2ra2sp3PKA1C3PAR3BUF2bs3GTB2p1S2ra2sp3PKA1C3PAR3BUF2bs3GTB2p13ibsS2ra2sp3PKA1C3PAR3LEN1P3BUF2bs3NZP3NZR2BP2C01p2PB3GTB2p12P23ibsS2ra2sp3PKA1C3PAR3LEN1P3BUF2bs3NZP3NZR2BP2C01p2PB3GTB2p12P2S2ra2sp3PKA1C3PAR3LEN1P3BUF2bs3NZP3NZR2BP2C01p2PB3GTB2p12P2FFFS2spS2spS2spS2spFFS2sp3SPRS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3SLO3ACL3ACP3BAC2p13ln13LN1S1L3HLS2sp2lo3SLO3ACL3ACPS2spS2spS2spS2ra2sp3PKA1C3PAR2bs3GTBS2spS2spS3LEN1P2p13ln13LN1S2spS2spSS1L3HLS2sp2lo3BUF2bs3SLO3ACL3BACFFS1L3HLS2sp2lo3SLO3ACL3ACPFFFS1L2lo3ACL3ACPFS2spS1L3HLS2sp2lo3SLO3ACLFFFS2sp2loS1L3HLS2sp2lo3SLOFS1L3HLS2sp2lo3SLO3ACL3ACPFFS3LEN1P3BUF2bs2PL2p13ln13LN1S3BUF2bs3B63FS2spS2spS2sp2loS2sp2a'3Ha'S1L2sp2lo2bs3SLOSFS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTB3ibsS3LEN1P3BUF2bs2BP1p2PB2p13PB1S2spS2spS3LEN1P3BUF2bs2PLS2spS1L3HLS2sp2lo3LEN1P3BUF2bs2PL3B633SLO3ACL3BAC2p13ln13LN1S2sp2loS3LEN1P3BUF2bs2BP2PL1p2PB2p13PB12P2S2r13RR12HqFS1L2sp2lo3SLOFS2ra2sp3PKA1C3PAR2bs3GTBS2ra2sp3PKA1C3PAR2bs3GTBS2r13RR11q2HqS1L3HLS2sp2lo3SLO3ACLS2sp2loFFS2sp3SPAS1L3HLS2sp2lo3SLO3ACL3SPA3ACPS1L3HLS2sp2lo2bs3SLO3ACL3SPA3ACPFS1L3HLS2sp2lo3SLO3ACL3SPA3ACPS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3SPR3ACP2C03GTBS1L3HLS2ra2sp3PKA1C2lo3PAR2bs3NZP3NZR3SLO3ACL3SPR3ACP2C03GTB". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND CA_RSA0 PAR BUF bs HH0 HPKA0 ALP NZP EI DSP CWP DPC PKD KP0 INC CD NZR DSR RC HBS0 INB BP PL B63 BUF0 CA CA_EC0 SLO ACL HTOP SPA DHI TP MI0 SPR IDL ACP CAC C0 CIM BAC BIM"] Lemma specC_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_ecparams_I ()) "Ph,(1?.$10.VL,VHI,)PLBi,(20.$21.)Pm,P,(=.&40.)(>.(=.&8.))Pmo,$22.PdN,$23.PdP,$23.PdA,$23.PdB,$23.PdX,$23.PdY,$23.PdZ,$23.Pp,$4.Plnw,(=.&40.)Pvw,(=.&40.)Ppb,(=.&40.)Pnb,(=.&40.)Pscj,(20.(=.&8.))Phj,(20.(=.&8.))Ptj,(20.(=.&8.))Ppj,(20.(=.&8.))Prj,(20.(=.&8.))PpX,(=.&40.)PpY,(=.&40.)PpZ,(=.&40.)Px1,(=.&40.)Px5,(=.&40.)Px6,(=.&40.)Px7,(=.&40.)Px10,(=.&40.)Px11,(=.&40.)Px12,(=.&40.)Px13,(=.&40.)Px14,(=.&40.)Px15,(=.&40.)Px16,(=.&40.)Px17,(=.&40.)Px19,(=.&40.)Px20,(=.&40.)Px21,(=.&40.)Px22,(=.&40.)Px23,(=.&40.)Px24,(=.&40.)Px25,(=.&40.)Px26,(=.&40.)Px27,(=.&40.)Px28,(=.&40.)Px29,(=.&40.)Px30,(=.&40.)Px31,(=.&40.)P,(24.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm0,Vmo0,Vh0,VLB,Vlo,VLEN,VP,R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)P,(3.$23.R2:.(25.(7.(7.(11.&40.Vsp,)-1?8.)+38.)R1=.))P,(3.$23.R2:.(25.(7.(7.(11.&40.Vsp,)-1?8.)+48.)R1=.))P,(3.$23.R2:.(25.(7.(7.(11.&40.Vsp,)-1?8.)+58.)R1=.))(26.$10.R32.(27.$10.VL,VHI,$28.$29.$2:.$15.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPKA,Vinfo,VC,(2;.VC,Vidpad,VpP,VpA,VpB,VpX,VpY,VpZ,VpN,Vhpad,Vqd,VqX,VqY,VqZ,)Vlo,Vm0,Vmo0,)(2<.(2=.R1=.(1;.&40.(7.(11.&40.Vsp,)-200.))Vgp,Vtp,R1<.R1;.R1:.(1;.&40.VPKA,)(1;.&40.(7.VP,VLEN,))R19.R18.R17.R16.R15.R14.R13.R12.(1;.&40.(7.(11.&40.Vsp,)-1?0.))R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)VF,(1;.&40.+29930.)Vfc,(2>.(=.&40.))R33.(2?.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros SI DXI DYI DZI.
    dpose SI as (CX & PX & TOK & EN & EP & EA & EB & EX & EY & EZ & FRP & PB & FRR & FRL & FRM & FR0 & FRH & FRT & FR & ST).
    ddestruct CX as (HH & HT & MF & MI & SOK & EXT & IDS). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    pose proof (ctx_bytes' m PX) as HBS.
    pose proof (rw_cells_bound _ _ _ _ FRT) as GTB. cbn [cells_size csize Nat.add] in GTB.
    (* [comment removed for export] *)
    pose proof U_asn1_get_tag_spec as SGT. unfold asn1_get_tag_stmt, asn1_get_tag_post, U_ASN1_GET_TAG in SGT.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512); (REF, REF + 8); (bv_unsigned sp + -304, bv_unsigned sp + -296)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep. zstep.
    acallx (eapply SGT with (PP := REF) (LENP := bv_unsigned sp + -304) (P := p) (END := PEND) (BUF := BUF) (bs := bs) (tag := 4);
            first [ exact FRP | exact FRL | exact HBS | exact MI | reflexivity
                  | clear -PB BP LEN0 PL B63; lia
                  | clear -BAC ACL SLO HLS; lia
                  | clear -SPA SPR; lia | clear -ACL ACP SLO HLS; lia | clear -BUF0; lia
                  | clear; lia
                  | match goal with |- ?g => idtac "GTLEFT" g end ]).
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
      eapply spec_erradd'; [exact SI1| clear -RR1 NZ; lia| exact MK]. }
    assert (Z1 : r1 = 0).
    { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ1 Z1) as [P2 LN1]. subst r1. clear K1 RZ1 RR1.
    dpose SI1 as (CX1 & PX1 & TOK1 & _). dpose CX1 as (HH1 & HT1 & MF1 & _ & SOK1 & EXT1 & IDS1).
    clear SI PX TOK HH HT MF SOK EXT IDS MK HBS HBR HAP. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 HAP1].
    pose proof (bv_unsigned_in_range 64 ln1) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    (* [comment removed for export] *)
    pose proof (tmp_ok_in usegs _ _ _ _ _ dP TOK1 ltac:(inlist)) as MDP.
    pose proof (tmp_ok_in usegs _ _ _ _ _ dX TOK1 ltac:(inlist)) as MDX.
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK1)) dP ltac:(inlist))) as NSP.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    zstep. zstep. zstep. zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -512) (eapply U_prb_none with (dP := dP) (dX := dX) (G := G) (lo := lo) (LBx := LBi);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact MDP | exact EP | exact NSP | exact MDX | exact EX | exact MI1 | eassumption
              | subst dX; reflexivity
              | intros O; destruct (mpdr_blk_facts usegs L _ _ _ (proj1 MDP) O HBR1) as (_ & _ & P0 & P4 & _); split; [exact P0| clear -P4 ACL; lia]
              | clear -SLO HLS ACL ACP SPR SPA LNR; lia
              | reflexivity | f_equal; clear; lia
              | match goal with |- ?g => idtac "PRLEFT" g end ]).
    try clear PC.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with M : mem_inv usegs m2 |- _ => rename M into MI2 end. match goal with W : wmono usegs m1 m2 |- _ => rename W into WM2 end.
    match goal with U : munch _ m1 m2 |- _ => rename U into MU2 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI1 MU2 WM2 MI2
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP1 ltac:(clear -PB PB1; lia) FRR FRL1 FRM FR0 FRH FRT FR ltac:(assumption)) as SI2.
    dpose SI2 as (CX2 & PX2 & TOK2 & _). dpose CX2 as (HH2 & HT2 & MF2 & _ & SOK2 & EXT2 & IDS2).
    clear MU2 WM2 SI1 CX1 PX1 TOK1 HH1 HT1 MF1 SOK1 EXT1 IDS1 MK1 MDP MDX NSP HBR1 HAP1. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    destruct (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2].
    (* [comment removed for export] *)
    zstep. if_cases KQ; zify_cond KQ.
    { exfalso. clear -KQ. unfold prb_none_ret in KQ. destruct (bv_unsigned ln1 =? 0); cbv in KQ; discriminate. }
    clear KQ.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KF; zify_cond KF.
    { zstep. zstep. zstep. zstep. zstep. eapply spec_err'; [exact SI2| clear; lia| clear; lia]. }
    assert (LNZ : bv_unsigned ln1 <> 0).
    { intros E0. unfold prb_none_ret in KF. rewrite E0 in KF. cbv in KF. discriminate KF. }
    clear KF.
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m2 PX2) as HBS2.
    get_byte bs (p1 - BUF) b0 NB0.
    zstep. zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?unsigned_lit in KP by lia; lia|].
    read_at HBS2 NB0 (p1 - BUF) RD0. zstep. clear RD0.
    zstep. zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB.
    { (* [comment removed for export] *) zstep. zstep. eapply spec_err'; [exact SI2| clear; lia| clear; lia]. }
    (* [comment removed for export] *)
    pose proof (tmp_ok_in usegs _ _ _ _ _ dP TOK2 ltac:(inlist)) as MDP.
    pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 (proj2 TOK2)) dP ltac:(inlist))) as NSP.
    assert (LIMB : md_p dP + 4 * md_n dP <= lo \/ bv_unsigned sp + -512 <= md_p dP).
    { pose proof MDP as [MDPr _]. assert (P4 : md_own dP = LHeap -> md_p dP + 4 * md_n dP <= alloc_ceiling)
        by (intros O; destruct (mpdr_blk_facts usegs L _ _ _ MDPr O HBR2) as (_ & _ & _ & P4 & _); exact P4).
      ddestruct MDPr as (_ & _ & _ & _ & _ & OWN). generalize OWN P4 NSP ACL ACP. clear. intros OWN P4 NSP ACL ACP.
      destruct (md_own dP); [destruct OWN as [-> ->]; left; lia| left; specialize (P4 eq_refl); lia| exfalso; exact (NSP eq_refl)]. }
    pose proof U_mpi_size_spec as SZ. unfold mpi_size_stmt, mpi_size_post, U_MPI_SIZE in SZ.
    pose proof (munch_refl [(lo, bv_unsigned sp + -512)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -512) (eapply SZ with (dX := dP) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
       first [ exact MDP | exact MI2 | exact LIMB | eassumption | rewrite EP; f_equal; clear; lia | rewrite EP; right; clear; lia
             | intros O; destruct (mpdr_blk_facts usegs L _ _ _ (proj1 MDP) O HBR2) as (_ & _ & P0 & _); exact P0
             | clear -SLO HLS; lia | clear -SPA SPR; lia
             | match goal with |- ?g => idtac "SZLEFT" g end ]).
    try clear PC.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with M : mem_inv usegs m3 |- _ => rename M into MI3 end. match goal with W : wmono usegs m2 m3 |- _ => rename W into WM3 end.
    match goal with U : munch _ m2 m3 |- _ => rename U into MU3 end.
    pose proof (spinv_munch' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SI2 MU3 WM3 MI3
                  ltac:(repeat constructor; cbn; clear -SLO HLS; lia) ltac:(dj7 EN EP EA EB EX EY EZ)
                  FRP1 ltac:(clear -PB PB1; lia) FRR FRL1 FRM FR0 FRH FRT FR ltac:(assumption)) as SI3.
    dpose SI3 as (CX3 & PX3 & TOK3 & _). dpose CX3 as (HH3 & HT3 & MF3 & _ & SOK3 & EXT3 & IDS3).
    clear MU3 WM3 SI2 CX2 PX2 TOK2 HH2 HT2 MF2 SOK2 EXT2 IDS2 MK2 MDP NSP LIMB HBR2 HAP2 HBS2 SZ. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    destruct (heap_blocks _ _ HI _ _ _ _ HH3) as [HBR3 HAP3].
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KS; zify_cond KS.
    { zstep. zstep. eapply spec_err'; [exact SI3| clear; lia| clear; lia]. }
    clear KS.
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m3 PX3) as HBS3.
    set (ibs := firstn (Z.to_nat (bv_unsigned ln1 - 1)) (skipn (Z.to_nat (p1 + 1 - BUF)) bs)).
    assert (LENI : Z.of_nat (length ibs) = bv_unsigned ln1 - 1) by (subst ibs; apply bytes_at_sub_length; clear -PB PB1 LN1 LNZ BP PL LNR; lia).
    assert (HIB : bytes_at usegs m3 (p1 + 1) ibs) by (subst ibs; eapply bytes_at_sub; [exact HBS3| | |]; clear -PB PB1 LN1 LNZ BP PL LNR; lia).
    pose proof (tmp_ok_in usegs _ _ _ _ _ dX TOK3 ltac:(inlist)) as MDX.
    pose proof (U_mpi_read_binary_spec L HI HFREE HCALLOC HLS SW DIMG HND _ eq_refl) as SRB. unfold mpi_read_binary_stmt, mpi_read_binary_post, U_MPI_READ_BINARY in SRB.
    zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|].
    zstep. zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply SRB with (lo := lo) (h := h) (LB := LBi) (dX := dX) (B := p1 + 1) (ibs := ibs);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia); rewrite ?LENI;
        first [ exact HH3 | exact MDX | exact HIB | exact TP | exact MI3 | exact SOK3 | exact CA | eassumption
              | subst dX; cbn; discriminate
              | rewrite HT3; eapply tmp_writable'; [exact HH3| exact TOK3| inlist| clear -SLO HLS; lia| clear; lia]
              | (* [comment removed for export] *) intros a Ha; right; right; exists (BUF, Z.of_nat (length bs)); split; [eapply lb_ext_sub; [exact EXT3| exact INB]| cbn; clear -Ha PB PB1 LN1 LNZ BP PL; lia]
              | subst dX; cbn; intros O; discriminate O
              | rewrite ?EX; rewrite ?HT3; clear -PB PB1 LN1 LNZ LNR BP PL B63 BUF0 BAC ACL ACP SLO HLS HTOP SPA SPR DHI; lia
              | reflexivity | rewrite EX; f_equal; clear; lia | f_equal; clear -LNZ LNR; lia
              | match goal with |- ?g => idtac "RBLEFT" g end ]. }
    clear SRB.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & MD4 & OUT4 & PX4 & SOK4 & RR4 & RN4 & NEW4).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m4; rename mox into mo4 end.
    match type of HT4 with heap_top _ _ _ ?hh = _ => rename hh into h4 end.
    match type of HH4 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB4 end.
    match type of MD4 with mpd_at _ _ _ ?dd => rename dd into dX' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r4 end.
    change (mpd_ivs dX) with ([] ++ mpd_ivs dX) in PX4.
    tmp_post m3 m4 dX EX CX3 PX3 TOK3 HH3 HH4 HT4 MF4 MI4 SOK4 MD4 OUT4 NEW4 PX4.
    pose proof (eq_trans EAD EX) as EX'. clear EAD.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (tmp_upd7' dX' dN dP dA dB dX dY dZ EN EP EA EB EX EY EZ))))) EX') in CX2, TOK2.
    assert (SI4 : SPINV' h4 LB4 m4 mo4 dN dP dA dB dX' dY dZ p1 ln1 vw pb nb scj hj tj pj rj).
    { split; [exact CX2|]. split; [exact PXn2|]. split; [exact TOK2|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX'|]. split; [exact EY|]. split; [exact EZ|].
      split; [exact FRP1|]. split; [clear -PB PB1; lia|]. split; [exact FRR|]. split; [exact FRL1|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST4]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear CX3 PX3 TOK3 HH3 HT3 MF3 SOK3 EXT3 IDS3 MK3 HBS3 HIB MDX PX4 HBR3 HAP3 CX2 PXn2 TOK2 MI3.
    (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4.
    { (* [comment removed for export] *) zstep. zstep. zstep. zstep. zstep. eapply spec_err'; [exact SI4| clear; lia| clear; lia]. }
    clear K4 RR4 RN4.
    destruct (heap_blocks _ _ HI _ _ _ _ HH4) as [HBR4 HAP4].
    (* [comment removed for export] *)
    pose proof (ctx_bytes' m4 (proj1 (proj2 SI4))) as HBS4.
    zstep. zstep. if_cases KP2; zify_cond KP2; [exfalso; rewrite ?unsigned_lit in KP2 by lia; lia|].
    read_at HBS4 NB0 (p1 - BUF) RD1. zstep. clear RD1.
    zstep. zstep. zstep.
    pose proof (tmp_ok_in usegs _ _ _ _ _ dY (proj1 (proj2 (proj2 SI4))) ltac:(inlist)) as MDY.
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SLS. unfold mpi_lset_stmt, mpi_binop_post, U_MPI_LSET in SLS.
    dpose SI4 as (CX4 & PX4 & TOK4 & _). dpose CX4 as (HH4' & HT4' & MF4' & _ & SOK4' & EXT4 & IDS4).
    pose proof (bv_unsigned_in_range 8 b0) as B0R. change (bv_modulus 8) with 256 in B0R.
    eapply aevtM_cut.
    { eapply SLS with (lo := lo) (h := h4) (LB := LB4) (dX := dY) (z := bv_unsigned b0 - 2);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH4 | exact MDY | exact TP | exact MI4 | exact SOK4 | exact CA | eassumption
              | subst dY; cbn; discriminate
              | rewrite HT4'; eapply tmp_writable'; [exact HH4| exact TOK4| inlist| clear -SLO HLS; lia| clear; lia]
              | clear -B0R; lia
              | rewrite ?HT4'; clear -SLO HLS ACL ACP HTOP SPA SPR DHI; lia
              | reflexivity | rewrite EY; f_equal; clear; lia | f_equal; clear -B0R; lia
              | match goal with |- ?g => idtac "LSLEFT" g end ]. }
    clear SLS.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI5 & ST5 & MF5 & HT5 & HH5 & MD5 & OUT5 & PX5 & SOK5 & LR5 & EAD5 & NEW5).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m5; rename mox into mo5 end.
    match type of HT5 with heap_top _ _ _ ?hh = _ => rename hh into h5 end.
    match type of HH5 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB5 end.
    match type of MD5 with mpd_at _ _ _ ?dd => rename dd into dY' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r5 end.
    change (mpd_ivs dY) with ([] ++ mpd_ivs dY) in PX5.
    tmp_post m4 m5 dY EY CX4 PX4 TOK4 HH4 HH5 HT5 MF5 MI5 SOK5 MD5 OUT5 NEW5 PX5.
    pose proof (eq_trans EAD5 EY) as EY'. try clear EAD.
    rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (tmp_upd7' dY' dN dP dA dB dX' dY dZ EN EP EA EB EX' EY EZ)))))) EY') in CX2, TOK2.
    assert (SI5 : SPINV' h5 LB5 m5 mo5 dN dP dA dB dX' dY' dZ p1 ln1 vw pb nb scj hj tj pj rj).
    { split; [exact CX2|]. split; [exact PXn2|]. split; [exact TOK2|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX'|]. split; [exact EY'|]. split; [exact EZ|].
      split; [exact FRP1|]. split; [clear -PB PB1; lia|]. split; [exact FRR|]. split; [exact FRL1|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST5]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH5) as MK5.
    clear CX4 PX4 TOK4 HH4 HH4' HT4 HT4' MF4 MF4' SOK4 SOK4' EXT4 IDS4 MK4 HBS4 MDY PX5 HBR4 HAP4 CX2 PXn2 TOK2 MI4 SI4 LR5 NEW5 OUT5 MD4 OUT4 NEW4 EAD5.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K5; zify_cond K5.
    { zstep. eapply spec_err'; [exact SI5| clear; lia| clear; lia]. }
    clear K5.
    destruct (heap_blocks _ _ HI _ _ _ _ HH5) as [HBR5 HAP5].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (tmp_ok_in usegs _ _ _ _ _ dZ (proj1 (proj2 (proj2 SI5))) ltac:(inlist)) as MDZ.
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SLS. unfold mpi_lset_stmt, mpi_binop_post, U_MPI_LSET in SLS.
    dpose SI5 as (CX5 & PX5 & TOK5 & _). dpose CX5 as (HH5' & HT5' & MF5' & _ & SOK5' & EXT5 & IDS5).
    eapply aevtM_cut.
    { eapply SLS with (lo := lo) (h := h5) (LB := LB5) (dX := dZ) (z := 1);
        rewrite ?(unsigned_lit (bv_unsigned sp + -512)) by (clear -SLO HLS ACL ACP SPR; lia);
        first [ exact HH5 | exact MDZ | exact TP | exact MI5 | exact SOK5 | exact CA | eassumption
              | subst dZ; cbn; discriminate
              | rewrite HT5'; eapply tmp_writable'; [exact HH5| exact TOK5| inlist| clear -SLO HLS; lia| clear; lia]
              | clear; lia
              | rewrite ?HT5'; clear -SLO HLS ACL ACP HTOP SPA SPR DHI; lia
              | reflexivity | rewrite EZ; f_equal; clear; lia
              | match goal with |- ?g => idtac "LSLEFT2" g end ]. }
    clear SLS.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -512)) in PO by (clear -SLO HLS ACL ACP SPR; lia).
    ddestruct PO as (MI6 & ST6 & MF6 & HT6 & HH6 & MD6 & OUT6 & PX6 & SOK6 & LR6 & EAD6 & NEW6).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
    match type of HT6 with heap_top _ _ _ ?hh = _ => rename hh into h6 end.
    match type of HH6 with HEAP _ _ _ _ ?lb _ _ => rename lb into LB6 end.
    match type of MD6 with mpd_at _ _ _ ?dd => rename dd into dZ' end.
    lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r6 end.
    change (mpd_ivs dZ) with ([] ++ mpd_ivs dZ) in PX6.
    tmp_post m5 m6 dZ EZ CX5 PX5 TOK5 HH5 HH6 HT6 MF6 MI6 SOK6 MD6 OUT6 NEW6 PX6.
    pose proof (eq_trans EAD6 EZ) as EZ'. try clear EAD.
    rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (tmp_upd7' dZ' dN dP dA dB dX' dY' dZ EN EP EA EB EX' EY' EZ)))))) EZ') in CX2, TOK2.
    assert (SI6 : SPINV' h6 LB6 m6 mo6 dN dP dA dB dX' dY' dZ' p1 ln1 vw pb nb scj hj tj pj rj).
    { split; [exact CX2|]. split; [exact PXn2|]. split; [exact TOK2|].
      split; [exact EN|]. split; [exact EP|]. split; [exact EA|]. split; [exact EB|]. split; [exact EX'|]. split; [exact EY'|]. split; [exact EZ'|].
      split; [exact FRP1|]. split; [clear -PB PB1; lia|]. split; [exact FRR|]. split; [exact FRL1|]. split; [exact FRM|].
      split; [exact FR0|]. split; [exact FRH|]. split; [exact FRT|]. split; [exact FR| exact ST6]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH6) as MK6.
    clear CX5 PX5 TOK5 HH5 HH5' HT5 HT5' MF5 MF5' SOK5 SOK5' EXT5 IDS5 MK5 MDZ PX6 HBR5 HAP5 CX2 PXn2 TOK2 MI5 SI5 LR6 NEW6 OUT6 EAD6.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K6; zify_cond K6.
    { zstep. zstep. eapply spec_err'; [exact SI6| clear; lia| clear; lia]. }
    (* [comment removed for export] *)
    eapply specC2_walk'; [exact SI6| clear -LN1; lia| clear -P2 PB PB1 BP PL; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End EP.
