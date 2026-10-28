(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB MpiCoreAux PresxStatics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_asn1_get_alg_A U_asn1_get_bitstring_null U_pk_parse_A U_pk_parse_B U_pk_parse_C.
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
Ltac2 gd_tbl_P_pk_parse_D () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.U.U_pk_parse_A.pctx"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.PKC_inst"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.U_pk_sinv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L16039907334.3L16040024469.3L42465045280.1L7688327973.3 00000500:00;00>S1w1BS1w1BSS1w". (* [comment removed for export] *)
Lemma sx32_low32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite swrap32_mod64. unfold sxz. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)) as B.
  destruct (Z.ltb_spec (bv_unsigned w mod 2^32) (2^31)) as [LT|GE].
  - apply Z.mod_small. lia.
  - replace (bv_unsigned w mod 2^32 + (2^64 - 2^32)) with (bv_unsigned w mod 2^32 + (2^32 - 1) * 2^32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_unsigned : forall w : word, bv_unsigned (sx32 w) = sxz (bv_unsigned w mod 2^32).
Proof. intros w. unfold sx32. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). apply swrap32_mod64. Qed.

Notation MT := U_MT (only parsing).

Section PA.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis HL : ecp_ids_lok L U_ECP_IDS_DONE U_ECP_IDS.
  Hypothesis HMC : mc_lok L U_MUL_COUNT.
  (* [comment removed for export] *)
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_D ()) "Ph,(0.$1.VL,VHI,)PLB,(2.$3.)PLB',(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$6.P,(7.$1.VL,VHI,R5.R4.R2.R1.)P,(8.$3.R5.R4.)(9.(0.$1.VL,VHI,)Lh',(0.$1.VL,VHI,)(:.(7.$1.VL,VHI,R1.R6.R5.R4.)(;.$<.(=.$1.VL,VHI,R1.)(=.$1.VL,VHI,R8.))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis CA_MSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.
  Hypothesis CA_RSA72 : const_at L (U_RSA_INFO + 72) 8.
  Hypothesis CA_RSA80 : const_at L (U_RSA_INFO + 80) 8.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.
  Hypothesis CA_EC72 : forall e, In e U_EC_INFOS -> const_at L (e + 72) 8.
  Hypothesis CA_EC80 : forall e, In e U_EC_INFOS -> const_at L (e + 80) 8.
  Hypothesis CAT_ECGRP : const_at L U_OID_EC_GRP_TBL 440.
  Hypothesis CAT_PKALG : const_at L U_OID_PK_ALG_TBL 120.
  Hypothesis CAT_ECALGID : const_at L U_OID_EC_GRP_ALGID_TBL 80.
  Hypothesis CA_PKTBL : const_at L U_PK_INFO_TBL 32.
  Hypothesis CA_BP : const_at L U_BAD_POINTS 32.
  (* [comment removed for export] *)
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_D ()) "(>.$1.VL,VHI,$?.$10.$11.+5<?:8.$12.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_D ()) "(13.$1.VL,VHI,$?.$14.$11.+5<?:8.$15.$16.)")
(* [comment removed for export] *).

  Notation SI := (U_pk_sinv L HL HMC).
  Notation PK := (PKC_inst usegs U_RSA_INFO U_EC_INFOS MT).
  Notation XS := [(U_ECP_IDS_DONE, U_ECP_IDS_DONE + 1); (U_MUL_COUNT, U_MUL_COUNT + 8); (U_ECP_IDS, U_ECP_IDS + 56)].

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (mo0 : Model) (h0 : HST usegs L HI) (LB : list blk) (PP P END BUF PKA lo : Z) (bs : list byte).
  Hypothesis HH0 : HEAP usegs L HI h0 LB m0 mo0.
  Hypothesis HPP0 : rw_cells usegs m0 PP [C8 (Z_to_bv 64 P)].
  Hypothesis ALPP : PP mod 8 = 0.
  Hypothesis HBS0 : bytes_at usegs m0 BUF bs.
  Hypothesis INB : In (BUF, Z.of_nat (length bs)) LB.
  Hypothesis BP : BUF <= P.
  Hypothesis PE : P <= END.
  Hypothesis EB : END <= BUF + Z.of_nat (length bs).
  Hypothesis B63 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis BUF0 : 0 < BUF.
  Hypothesis HPKA0 : rw_cells usegs m0 PKA [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Hypothesis ALP : PKA mod 8 = 0.
  Hypothesis SPP : bv_unsigned sp <= PP.
  Hypothesis PPT : PP + 8 <= heap_top usegs L HI h0.
  Hypothesis SPK : bv_unsigned sp <= PKA.
  Hypothesis PKT : PKA + 16 <= heap_top usegs L HI h0.
  Hypothesis DPK : PP + 8 <= PKA \/ PKA + 16 <= PP.
  Hypothesis ST0 : stk usegs m0 lo (bv_unsigned sp).
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - PK_PARSE_STACK - hl_stack L.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis MI0 : mem_inv usegs m0.
  Hypothesis SOK0 : statics_ok usegs L m0.
  Hypothesis SIP0 : pk_sinv_P m0.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis DKB : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis DPB : PKA + 16 <= BUF \/ BUF + Z.of_nat (length bs) <= PKA.
  Hypothesis NZPP : 0 < PP.
  Hypothesis NZP : 0 < PKA.
  Hypothesis DSPP : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DSP : PKA + 16 <= lo \/ bv_unsigned sp <= PKA.
  Hypothesis DSB : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h0) PP 8.
  Hypothesis CWP : client_wrange L LB lo (heap_top usegs L HI h0) PKA 16.
  Hypothesis CRB : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis SPR : bv_unsigned sp < 2^64.

  Notation POST := (pk_parse_subpubkey_post usegs L HI PK SI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0).
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FP := ([(PP, PP + 8); (PKA, PKA + 16)] ++ XS).

Notation pa_basics' := (pa_basics L HI HLS sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI).
  Notation pctx' := (pctx L HI sp m0 mo0 h0 LB PP PKA).
  Notation pctx_munch' := (pctx_munch L HI HLS HL HMC sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO HTOP DHI CWPP CWP).
  Notation ret_walk' := (ret_walk L HI HLS HL HMC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB).
  Notation early_walk' := (early_walk L HI HLS HL HMC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 SPP SPK DPK ACL SLO DHI DKB DPB NZPP NZP DSPP DSP DSB).
  Notation fail_free_walk' := (fail_free_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR).
  Notation pctx_bytes' := (pctx_bytes L HI HLS DIMG HL HMC sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 HBS0 INB SPP SPK ACL SLO DHI DKB DPB CRB).
  Notation keep_frame' := (keep_frame L sp).
  Notation keep_pp' := (keep_pp L HI sp h0 LB PP lo DSPP CWPP).
  Notation keep_pka' := (keep_pka L HI sp h0 LB PKA lo DSP CWP).
  Notation fresh_not_client' := (fresh_not_client L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI).
  Notation fresh_apart_pp' := (fresh_apart_pp L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI CWPP).
  Notation fresh_apart_pka' := (fresh_apart_pka L HI HLS DIMG sp m0 mo0 h0 LB PP BUF PKA lo bs HH0 INB SPP SPK ACL SLO DHI CWP).
  Notation heap_presx_weak'' := (heap_presx_weak' L ra sp LB PP P END BUF PKA bs BP PE EB DPK DKB DPB NZPP NZP).
  #[using="DIMG"] Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  #[using="DIMG"] Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  #[using="HL"] Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  #[using="L HL"] Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  #[using="HL"] Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  #[using="HMC"] Lemma ML1 : hl_data_lo L <= U_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  #[using="HMC"] Lemma ML2 : U_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.
  Notation rsa_walk' := (rsa_walk L HI HFREE HCALLOC HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).
  Notation ec_walk' := (ec_walk L HI HFREE HCALLOC HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 CAT_ECGRP CA_BP HPRB HCPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).
  Notation low_frame_merge' := (low_frame_merge ra sp PP PKA bs).
  Notation init_fail_walk' := (init_fail_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR).
  Notation ec_fin_walk' := (ec_fin_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 CA_BP HPRB HCPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L24906321761.106L28232829604.2  L47071308384.107L55445551334.105L66152802915.10800000G00N00e01<01SS2ra2sp2PP3PKA2bs2j02W0S2j02W0S2ra2sp2PP3PKA2bs2j02W0S2ra2sp2PP3PKA2bs2j02W0S2ra2sp2PP3PKA2bs2j02W0". (* [comment removed for export] *)
  #[using="ra PP PKA bs"] Lemma low48_merge : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse_D ()) "Pmm,P,(4.&40.)(5.(4.&8.))Pj0,(2.(4.&8.))Pidw,(4.&40.)Pagw,(4.&40.)Pptag,(4.&40.)Pppad,(4.&40.)Pplen,(4.&40.)Pppw,(4.&40.)Plnw,(4.&40.)P,(17.$1.R9.(18.(19.&40.Vsp,)-70.)(1:.$1;.(1<.#8.R8.)(1=.$1;.)))P,(17.$1.R:.(18.(19.&40.Vsp,)-68.)(1:.$1;.(1>.R8.)(1=.$1;.)))P,(17.$1.R;.(18.(19.&40.Vsp,)-64.)(1:.$1;.(1>.R8.)(1=.$1;.)))P,(17.$1.R<.(18.(19.&40.Vsp,)-60.)(1:.$1;.(1>.R8.)(1:.$1;.(1>.R7.)(1:.$1;.(1?.R6.)(1:.$1;.(1?.R5.)(1=.$1;.))))))P,(17.$1.R=.(18.(19.&40.Vsp,)-48.)(1:.$1;.(1?.R5.)(1=.$1;.)))(17.$1.R>.(18.(19.&40.Vsp,)-70.)(1:.$1;.(1<.#30.(20.(4.&8.)R=.(20.(4.&8.)(21.R<.)(20.(4.&8.)(21.R;.)(20.(4.&8.)(21.R:.)(20.(4.&8.)(21.R9.)(20.(4.&8.)(22.R8.)(20.(4.&8.)(22.R7.)(22.R6.)))))))))(1=.$1;.)))")
(* [comment removed for export] *).
  Proof.
    intros until lnw. intros F0 F1 F2 F3 F4.
    dpose F0 as [[[W0 _] _] _]. cbn in W0.
    chunk_join F0 F1 J1. chunk_join J1 F2 J2. chunk_join J2 F3 J3. chunk_join J3 F4 J4.
    eapply rw_cells_reshape; [exact J4| | cbn; rewrite ?app_nil_r, <- ?app_assoc; reflexivity].
    cbn. rewrite ?app_length, ?length_le8, ?length_le4. cbn. rewrite ?app_length, ?length_le8, ?length_le4. cbn. split; [clear -W0; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02M0@D12218223161.183D12261817888.183D12344077014.183D12428150072.183D1360339641.183 D1562460822.183 D16075577430.183D17565844854.183D19631951702.183D20669440068.183D20994638648.183D22528888377.183D23207214801.183D29234783309.184D30511339222.183D30993319891.183D33988790033.183D34335414293.183D37512423481.183D37642974545.183D38087543013.185D41166577273.183D41199876177.183D41371876950.183D44484923210.183D47881269829.184D5061948113.183 D50671478649.183D51914630841.183D52101704109.185D54312234830.183D59236064057.183D60123493068.183D62903610193.183L10125340708.6  L1077460508.1   L11518786483.166L11886305925.6  L12415176104.174L1301613930.6   L13174485201.7  L13181059450.12 L13181091578.5  L14399547411.3  L14921071815.7  L14927049452.6  L14927056236.13 L15623165340.1  L16720171459.166L1725003874.1   L18933043916.4  L19561826530.1  L19727857373.170L20656466132.174L21649695260.1  L22516434601.174L22695014857.10 L23091425887.10 L23091425887.7  L23097717476.4  L23097934836.11 L23097965684.4  L23268210308.0  L23271682978.1  L23305025156.0  L24108985636.8  L24132835969.4  L25584779078.10 L25638637199.4  L25638662415.11 L27665848786.2  L27687752827.5  L29934044989.9  L29944219926.5  L29944247958.11 L34331086981.174L34806988770.1  L3582028444.1   L36012194261.170L36571201320.0  L36694146884.0  L37317392303.8  L37339008021.166L3814477520.7   L3814477520.9   L3820585211.6   L3820617595.12  L40147641242.5  L41202929119.166L42682693488.7  L42682693488.9  L42697197275.11 L42697226587.5  L42697373643.3  L43068201034.4  L43068500314.10 L43068511962.4  L43082881265.8  L43082881265.9  L44480858074.174L45017891119.12 L45017923247.6  L45023965316.7  L46566427376.5  L4728363746.1   L49250620438.180L4966764130.1   L49728944076.10 L50432132596.6  L51158950247.3  L52991974620.1  L5428330263.4   L57637916299.12 L58807149418.10 L58933668659.168L58933668659.211L58972476282.10 L59308579027.1  L59308632694.1  L59314873579.1  L59427797044.168L59427867805.167L5958257762.1   L60008475664.2  L60264566684.1  L60408146425.5  L60598307806.6  L61288258626.7  L61302938854.5  L61845192195.11 L61845193091.4  L61851766696.10 L61851766696.7  L61999720429.7  L61999720429.9  L62001817430.3  L62002107974.11 L62002129350.5  L6238538067.5   L63203639558.12 L63203671686.6  L63214366893.9  L63383247523.10 L65258828961.0  L65351099977.3  L65351099990.3  L65351391046.11 L65351411910.5  L65361585901.7  L65361585901.9  L66291751964.1  L66572612610.3  L67962257179.5  L7036479304.1   L8322245898.4   L8370967830.185 R37321652361.16200000A00V00k00l01=01R01g02_03403503I03J03[04R04g05c06406506F06W07S07d08508J08K09Z09k0:C0:T0;L0<D0<U0<j0=;0=O0=S0=d0=e0>X0>Y0>d0>e0>f0>n0?<0?=0?>0?B0@m0A10A50A90A:0Am0B10BE0B[0B\0B]0B^0B_0B`0Ba0Be0Bf0C@0CN0Cc0D20D30D;0DK0Dl0Dm0Dn0E]0Ea0Ee0Ef0Eg0Eh0FF0H50H60HC0HD0HE0HS0Hd0I>0I?0I@0IA0IB0IC0ID0IE0IF0IG0J:0J;0J<0JN0J[0J_0K40K80KI0K]0Ki0Km0L90LC0LQ0Lb0M>0M?0MC0MG0MJ0MK0ML0MP0MQ0MU0Mf0N80NF0NG0NH0NI0NJ0NK0NL0NM0NU0NV0NW0N^0N_0N`0O80OI0OJ0OK0OS0OT0OU0O]0O^0Ob0Om0P?0PC0PP0Pa0QfS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bs3SPKS2ra2sp2PP3PKA2bs3SPPFS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bs3SPPS2ra2sp2PP3PKA2bs3SPPS1L3HLS2ra2sp2PP3BUF3PKA2lo2bs3ACL4NZPP3NZP3ACP3BAC4SLO'S2ra2sp2PP3PKA2bs3SPPFS2ra2sp2PP3PKA2lo2bsFS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2lo2bs1p2E23x272x33x323x333x344POST3x351HS2ra2sp2PP3PKA2bs3SPPS1L3HLS2ra2sp2PP3BUF3PKA2lo2bs3SPP3ACL4NZPP3NZP3ACP3BAC4SLO'S2ra2sp2PP3PKA2bsFS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bsS1L3HLS2ra2sp2PP3PKA2lo2bs3SPP3ACL3DHI4NZPP3NZP3ACP4SLO'1a1HS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bs3SPPFS2ra2sp2PP3PKA2lo2bs1p2E23x272x33x323x333x344POST3x351H1L3HLS3SPP4NZPP3NZP4SLO'S2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2lo2bs3SPPS2ra2sp2PP3PKA2bsS1L3HLS2ra2sp2PP3PKA2lo2bs3ACL3DHI4NZPP3NZP3ACP4SLO'1a1HS1L3HLS2ra2sp2PP3BUF3PKA2lo2bs3ACL4NZPP3NZP3ACP3BAC4SLO'S2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bs3SPKS2ra2sp2PP3PKA2bsS1L3PKA3PKD2I12I22I3S2spS2ra2sp2PP3PKA2bsFS1L3HLS2ra2sp2PP3PKA2lo2bs3SPK4NZPP3NZP4SLO'2HD3SPPFS2sp2PP3SPPFFS2r13RR1S2sp2PP2lo3SPPFFS2spS1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1p2E22PB3E2B3ACP3BAC4SLO'2p13ln13LNR2P33LN1S2spS2r1S2spFS1L3HLS2ra2sp2PP3PKA2lo2bs3SPK4NZPP3NZP4SLO'2HD3SPPS2spS2ra2sp2PP3PKA2bs2HDS3END3BUF2bs2EB2E23E2BFFFFFSS2spSS1P3END1p2E22PB3E2B2p13PB1S3agw1t3T142T1S1P3BUF2bs2BP1p2E22PBS2PP3BUF2bs3DKBFS2r13RR1S1L3PKA3PKD1a2HaS1L3HLS2sp3BUF2lo2bs3ACL3BAC4SLO'FFS1L3HLS2ra2sp2PP3PKA2lo2bs3SPP4NZPP3NZP4SLO'2HDS2spS2spFSSS1L3HLS2sp2lo3ACL3SPR3ACP4SLO'S1L3HLS2ra2sp2PP1P3END3BUF3PKA2lo2bs2BP2EB3B634BUF03ACL4NZPP3NZP1p2E22PB3E2B3ACP3BAC4SLO'2p13PB12P33ln13LNR3LN1FS1L2lo2bs3ACLFFS1L2M12M21a2HaS2ra2sp2PP3PKA2bsS1L3HLS2sp2lo3ACL3ACP4SLO'FFFFFFFFFS1L3HLS2ra2sp2PP3PKA2lo2bs3SPK4NZPP3NZP4SLO'2HD3SPPFFS1L3HLS2sp2lo4SLO'S3agw1t2KD2TRS2spS2ra2sp2PP3PKA2bs3agwS2spS1L2HI2sp2h04HTOPS1L3PKA3PKD2I12I22I3S2sp3PKA3SPKS2spS3agw1t1H2H0S2sp2lo2bsS1P2bs1p2E22PBS2ra2sp2PP3PKA2bsS2ra2sp2PP3PKA2bs3agw1t4infoFS2H0S2KSS1HFFS2spSS2spS1L3PKA3PKD2M12M2S1P1p2E22PB2p13PB1S1L2sp2lo4SLO'FFFFFFFS2sp3SPAFFS2sp2loFFS1L2sp3BUF2lo2bs3ACL3BACS1L2HI2h03PKA3PKTSFS2sp3SPAFFS2sp3SPAFS2spS2r13RR12HqS1L3HLS2sp2lo4SLO'S2spS2r13RR11q2HqS2ra2sp2PP3PKA2bsS1L3HLS2ra2sp2PP3BUF3PKA2lo2bs4BUF03SPP3SPK3ACL4NZPP3NZP3SPR3ACP4SLO'". (* [comment removed for export] *)
  #[using="HFREE HCALLOC HLS SW DIMG HND HPERM CA_MSF CA_RSA0 CA_RSA72 CA_RSA80 CA_EC0 CA_EC72 CA_EC80 CAT_ECGRP CA_PKTBL CA_BP HPRB HCPK bs HH0 ALPP HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR"] Lemma head2_walk : forall (m : (@stdpp.bitvector.definitions.bv 64%N -> @Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), forall (mo :
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (p : @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (pp : @Corelib.Numbers.BinNums.Z), forall (j0 : @Corelib.Init.Datatypes.list
    (@stdpp.bitvector.definitions.bv 8%N)), forall (idw : @stdpp.bitvector.definitions.bv 64%N), forall (agw : @stdpp.bitvector.definitions.bv 64%N), forall (oj :
    @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (alen : @stdpp.bitvector.definitions.bv 64%N), forall (ptag : @stdpp.bitvector.definitions.bv 64%N),
    forall (ppad : @stdpp.bitvector.definitions.bv 64%N), forall (plen : @stdpp.bitvector.definitions.bv 64%N), forall (lnw : @stdpp.bitvector.definitions.bv 64%N), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x10 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (p0 :
    @Corelib.Numbers.BinNums.Z), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv
    64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h LB m mo ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z); @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)] -> @Corelib.Init.Logic.or
    (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) pp 0%Z) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z)
    (@stdpp.bitvector.definitions.bv_unsigned 64%N plen) 0%Z) (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) ptag (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z))))
    (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF pp) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add pp (@stdpp.bitvector.definitions.bv_unsigned 64%N plen)) E2))
    -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-112)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-104)%Z)
    [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-100)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] ->
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-96)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N pp)] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z)
    [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-64)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) x10 x11 x12 x13 x14 x15 x16 x17
    (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv
    64%N 0x29364%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom
    (@OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros until x31. intros CX HPP PB E2B HPKA PARD F0 FID FALG FPAR FLEN FSC FR ST P00.
    dpose pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    dpose CX as (HH & HT & MF & MI & SOK & SIP & SUB & PX). pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (pctx_bytes' _ _ _ _ CX) as HBS.
    (* [comment removed for export] *)
    pose proof U_asn1_get_bitstring_null_spec as SBS. unfold asn1_get_bitstring_null_stmt, asn1_get_bitstring_null_post, U_ASN1_GET_BITSTRING_NULL in SBS.
    pose proof (munch_refl [(PP, PP + 8); (bv_unsigned sp + -72, bv_unsigned sp + -64); (lo, bv_unsigned sp + -112)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. zstep. zstep. zstep.
    acallx_sp (bv_unsigned sp + -112)
      (eapply SBS with (PP := PP) (LENP := bv_unsigned sp + -72) (P := p) (END := E2) (BUF := BUF) (bs := bs) (lo := lo);
       rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia);
       first [ exact HPP | exact FLEN | exact HBS | exact MI | exact ST | reflexivity
             | clear -PB E2B BP EB; lia | exact B63
             | clear -DKB; lia
             | clear -SPP SLO' HLS; lia | clear -BAC ACL SLO' HLS; lia
             | exact ALPP | clear -SPA SPR; lia | exact NZPP | clear -SLO' HLS ACL ACP; lia | exact BUF0
             | clear -SLO' HLS; lia
             | right; exact SPP' || (right; clear -SPP; lia)
             | right; clear; lia
             | match goal with |- ?g => idtac "BSLEFT" g end ]).
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : rw_cells usegs m1 PP [C8 (Z_to_bv 64 ?q)] |- _ => rename H into HPP1; rename q into p1 end.
    match goal with H : rw_cells usegs m1 (bv_unsigned sp + -72) [C8 ?l] |- _ => rename H into FLEN1; rename l into ln1 end.
    match goal with H : - (127) < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end || match goal with H : _ < ?r <= 0 |- _ => rename H into RR1; rename r into r1 end.
    match goal with H : p <= p1 <= _ |- _ => rename H into PB1 end.
    match goal with H : r1 = 0 -> _ |- _ => rename H into RZ1 end.
    match goal with M : mem_inv usegs m1 |- _ => rename M into MI1 end.
    match goal with W : wmono usegs m m1 |- _ => rename W into WM1 end. rename MU into MU1.
    match goal with S : stk usegs m1 lo _ |- _ => rename S into ST1 end.
    pose proof (pctx_munch' _ _ _ _ _ _ CX MU1 WM1 MI1 ltac:(constructor; [cbn; right; left; reflexivity| constructor; [cbn; left; clear -SLO' HLS; lia| constructor; [cbn; left; clear -SLO' HLS; lia| constructor]]])) as CX1.
    clear MU1 WM1 CX HBS. match goal with H : ?x = Z_to_bv 64 r1 |- _ => subst x end.
    dpose CX1 as (HH1 & _ & _ & _ & SOK1 & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. clear MK HH HT MF SOK SIP SUB PX.
    pose proof (bv_unsigned_in_range 64 ln1) as LNR. change (bv_modulus 64) with (2^64) in LNR.
    zstep. if_cases K1; zify_cond K1.
    2:{ (* [comment removed for export] *)
        assert (NZ : r1 <> 0) by (intros ->; apply K1; reflexivity).
        zstep. zstep. zstep. zstep. zstep. rewrite swrap32_errsum by (clear -RR1; lia).
        zstep. if_cases KO; zify_cond KO.
        2:{ exfalso. clear -KO RR1 NZ. rewrite !signed_lit64 in KO by lia. lia. }
        match goal with H : rw_cells usegs m1 PKA _ |- _ => rename H into HPKA1 end.
        eapply early_walk'; [exact CX1| clear -RR1 NZ; lia| exact HPP1| clear -PB PB1 E2B; lia| exact HPKA1
          | exact (low_frame_merge' _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN1 FSC)
          | exact FR| exact ST1]. }
    assert (Z1 : r1 = 0).
    { clear -K1 RR1. apply Z.mod_divide in K1; [| lia]. destruct K1 as [q Hq]. assert (q = 0 \/ q = -1) as [->| ->] by lia; lia. }
    destruct (RZ1 Z1) as [P3 LN1]. subst r1. clear K1 RZ1 RR1.
    match goal with H : rw_cells usegs m1 PKA _ |- _ => rename H into HPKA1 end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KW; zify_cond KW.
    1-2: try (exfalso; clear -KW PB PB1 LN1 LNR E2B BP EB PE B63 BUF0; rewrite ?unsigned_lit in KW by lia; lia).
    zstep. zstep. zstep. zstep. pk_ckb KN ltac:(clear -PB PB1 LN1 LNR E2B BP EB PE B63 BUF0; lia).
    zstep. zstep. if_cases KE; zify_cond KE.
    2:{ zstep. zstep.
        eapply early_walk'; [exact CX1| clear; lia| exact HPP1| clear -PB PB1 E2B; lia| exact HPKA1
          | exact (low_frame_merge' _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN1 FSC) | exact FR| exact ST1]. }
    rewrite ?unsigned_lit in KE by (clear -PB PB1 LN1 LNR E2B BP EB PE B63 BUF0; lia).
    (* [comment removed for export] *)
    pose proof (U_pk_info_from_type_spec L CA_PKTBL) as SIF. unfold pk_info_from_type_stmt, pk_info_from_type_post, U_PK_INFO_FROM_TYPE in SIF.
    zstep. zstep.
    acallp (eapply SIF; first [exact MI1 | exact SOK1 | exact CA_PKTBL | reflexivity]).
    clear SIF.
    match goal with H : ?x = Z_to_bv 64 (pk_info_of _ _) |- _ => subst x end.
    rewrite sx32_low32.
    set (t := bv_unsigned agw mod 2^32). set (info := pk_info_of U_PK_INFOS t).
    pose proof (pk_info_of_in U_PK_INFOS t) as INFO. fold info in INFO.
    zstep. if_cases KI; zify_cond KI.
    { (* [comment removed for export] *) zstep. zstep.
      eapply early_walk'; [exact CX1| clear; lia| exact HPP1| clear -PB PB1 E2B; lia| exact HPKA1
        | exact (low_frame_merge' _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN1 FSC) | exact FR| exact ST1]. }
    assert (NI : info <> 0) by (intros E0; apply KI; rewrite E0; reflexivity). clear KI.
    assert (HINF : info = U_RSA_INFO \/ In info U_EC_INFOS).
    { destruct INFO as [E0|IN]; [exfalso; exact (NI E0)|]. cbn in IN. unfold U_EC_INFOS. cbn.
      destruct IN as [E|[E|[E|[E|[]]]]]; [left; symmetry; exact E| right; left; exact E| right; right; left; exact E| right; right; right; left; exact E]. }
    (* [comment removed for export] *)
    dpose CX1 as (_ & HT1 & MF1 & _ & _ & SIP1 & _ & PX1).
    pose proof (U_pk_setup_spec L HI U_MT HCALLOC HLS DIMG CA_RSA72 CA_EC72) as SSU. unfold pk_setup_stmt, pk_setup_post, U_PK_SETUP in SSU.
    zstep. zstep. zstep.
    eapply aevtM_cut.
    { eapply SSU with (lo := lo) (h := h) (LB := LB) (PKA := PKA) (info := info);
        rewrite ?(unsigned_lit (bv_unsigned sp + -112)) by (clear -SLO' HLS ACL ACP SPR; lia);
        first [ exact HH1 | exact HPKA1 | exact ALP | exact HINF | exact ST1 | exact ACL | exact DHI | exact MI1 | exact SOK1 | exact TP | reflexivity
              | clear -SPK; lia
              | rewrite HT1; clear -PKT HTOP SLO' HLS; lia
              | clear -SLO' HLS SPA SPR; lia
              | match goal with |- ?g => idtac "SULEFT" g end ]. }
    clear SSU.
    intros ms' mo' PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2'. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in PO by (clear -SLO' HLS ACL ACP SPR; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HT2 & A0 & PX2 & SU).
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    match type of HT2 with heap_top _ _ _ ?hh = _ => rename hh into h2 end.
    match type of A0 with ?x = Z_to_bv 64 ?rr => subst x; rename rr into r2 end.
    (* [comment removed for export] *)
    assert (XF : Forall (fun iv => snd iv <= bv_unsigned sp + -112 \/ bv_unsigned sp <= fst iv) [(PKA, PKA + 16)]) by (constructor; [cbn; right; exact SPK| constructor]).
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in F0; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FID; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FALG; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FPAR; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FLEN1; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FSC; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_frame' _ _ _ m1 m2 _ _ PX2 ltac:(clear; lia)) in FR; [| clear; lia| cbn; clear; lia| exact XF].
    apply (keep_pp' LB _ _ m1 m2 _ PX2 ltac:(intros b Hb; exact Hb) ltac:(clear; lia)) in HPP1; [| reflexivity| cbn; split; [exact DPK| exact I]].
    assert (SOK2 : statics_ok usegs L m2).
    { eapply statics_ok_heap_presx; [exact SOK1| exact PX2| exact SW|]. intros a Ha NW. cbn. split; [clear -Ha PKD; lia| exact I]. }
    assert (SIP2 : pk_sinv_P m2).
    { destruct SIP1 as [IDS1 [cnt CNT1]]. pose proof IL1 as I1; pose proof IL2 as I2; pose proof IL3 as I3; pose proof ML1 as M1; pose proof ML2 as M2. split.
      - apply (ecp_ids_state_presx usegs L _ _ _ _ _ m1 m2 IDS1 PX2 HL); cbn; clear -PKD I1 I2 I3; (split; [lia| exact I]).
      - exists cnt. eapply heap_presx_rw_cells; [exact PX2| exact CNT1| |]; cbn [cells_size csize Nat.add disjoint_from].
        + intros a Ha. right; left. split; [clear -Ha M1 M2; lia| exact (proj2 (proj2 (proj2 HMC) a Ha))].
        + split; [clear -PKD M1 M2; lia| exact I]. }
    assert (PXF : heap_presx usegs L LB (bv_unsigned sp) FP m0 m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply heap_presx_weak; [exact PX2| intros b Hb; exact Hb| clear; lia| intros a Ha; cbn in Ha |- *; split; [exact (proj1 (proj2 Ha))| exact I]]. }
    destruct SU as [(-> & HH2 & HPKA2)|(-> & BRC & APC & HH2 & HPKA2 & RSAC & ECC)].
    2: match type of BRC with block_range _ ?c ?sz => rename c into C; rename sz into SZ end.
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep. if_cases KS; zify_cond KS. 2:{ exfalso. clear -KS. cbv in KS. lia. }
      eapply early_walk'; [| clear; lia| exact HPP1| clear -PB PB1 E2B; lia| exact HPKA2
        | exact (low_frame_merge' _ _ _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN1 FSC) | exact FR| exact ST2].
      split; [exact HH2|]. split; [rewrite HT2; exact HT1|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|]. split; [exact SIP2|].
      split; [intros b Hb; exact Hb| exact PXF].
    - (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      zstep. if_cases KS; zify_cond KS. { exfalso. apply KS. reflexivity. }
      clear KS.
      assert (CX2 : pctx' h2 ((C, SZ) :: LB) m2 mo2).
      { split; [exact HH2|]. split; [rewrite HT2; exact HT1|]. split; [eapply mo_frame_trans; [exact MF1| exact MF2]|]. split; [exact MI2|]. split; [exact SOK2|]. split; [exact SIP2|].
        split; [intros b Hb; right; exact Hb| exact PXF]. }
      zstep. zstep. zstep. if_cases KD; zify_cond KD.
      + (* [comment removed for export] *)
        rewrite sx32_unsigned in KD. fold t in KD.
        assert (T234 : t = 2 \/ t = 3 \/ t = 4).
        { pose proof (Z.mod_pos_bound (bv_unsigned agw) (2^32) ltac:(clear; lia)) as TR. fold t in TR.
          assert (T14 : 1 <= t <= 4).
          { subst info. unfold pk_info_of in NI. destruct (Z.leb_spec 1 t); destruct (Z.leb_spec t 4); cbn [andb] in NI; try (exfalso; apply NI; reflexivity). clear -H H0; lia. }
          assert (T1 : t <> 1) by (intros E1'; apply KD; rewrite E1'; reflexivity).
          clear -T14 T1. lia. }
        assert (EI : In info U_EC_INFOS).
        { subst info. unfold pk_info_of, U_EC_INFOS, U_PK_INFOS. destruct T234 as [->|[->| ->]]; cbn; [left| right; left| right; right; left]; reflexivity. }
        assert (NR : info <> U_RSA_INFO).
        { intros ER. rewrite ER in EI. unfold U_EC_INFOS, U_RSA_INFO, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn in EI. clear -EI. intuition lia. }
        ddestruct (ECC NR) as (-> & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & KP).
        eapply ec_walk'; [exact CX2| exact KP| exact BRC| exact APC| exact EI| exact PARD| exact HPP1| clear -PB PB1; lia| exact E2B| exact HPKA2
          | exact F0| exact FID| exact FALG| exact FPAR| exact FLEN1| exact FSC| exact FR| exact ST2| exact P00].
      + (* [comment removed for export] *)
        rewrite sx32_unsigned in KD. fold t in KD.
        assert (T1 : t = 1).
        { pose proof (Z.mod_pos_bound (bv_unsigned agw) (2^32) ltac:(clear; lia)) as TR. fold t in TR. clear -KD TR. unfold sxz in KD.
          destruct (Z.ltb_spec t (2^31)); lia. }
        assert (EINF : info = U_RSA_INFO) by (subst info; rewrite T1; reflexivity).
        rewrite EINF in HPKA2. destruct (RSAC EINF) as [-> RSA0].
        eapply rsa_walk'; [exact CX2| exact RSA0| exact BRC| exact APC| exact HPP1| clear -PB PB1; lia| exact E2B| exact HPKA2
          | exact (low48_merge _ _ _ _ _ _ _ _ _ F0 FID FALG FPAR FLEN1)| exact FSC| exact FR| exact ST2| exact P00].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
