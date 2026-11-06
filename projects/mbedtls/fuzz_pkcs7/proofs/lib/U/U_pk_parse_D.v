(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB MpiCoreAux PresxStatics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_asn1_get_alg_A U_asn1_get_bitstring_null U_pk_parse_A U_pk_parse_B U_pk_parse_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_pk_parse_D () : Init.string Init.list := ["OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.U.U_ecp_defs.U_MT"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.U.U_platform_zeroize.U_MEMSET_FUNC"; "OSSVerify.KrLib.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.U_BAD_POINTS"; "OSSVerify.KrLib.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.Mem.le4"; "OSSVerify.KrLib.Lib.Mem.le8"; "OSSVerify.KrLib.U.U_pk_parse_A.pctx"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "OSSVerify.KrLib.USpec.RepPk.PKC_inst"; "OSSVerify.KrLib.U.U_pk_free.U_RSA_INFO"; "OSSVerify.KrLib.U.U_pk_free.U_EC_INFOS"; "OSSVerify.KrLib.U.U_pk_sinv.U_pk_sinv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


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
  Notation FRS mv := (rw_cells usegs mv (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
    @LinuxProcessSemantics.LinuxProcessSem.State.Model), forall (h : @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.HeapIface.HST (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI),
    forall (p : @Corelib.Numbers.BinNums.Z), forall (E2 : @Corelib.Numbers.BinNums.Z), forall (pp : @Corelib.Numbers.BinNums.Z), forall (j0 : @Corelib.Init.Datatypes.list
    (@stdpp.bitvector.definitions.bv 8%N)), forall (idw : @stdpp.bitvector.definitions.bv 64%N), forall (agw : @stdpp.bitvector.definitions.bv 64%N), forall (oj :
    @Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), forall (alen : @stdpp.bitvector.definitions.bv 64%N), forall (ptag : @stdpp.bitvector.definitions.bv 64%N),
    forall (ppad : @stdpp.bitvector.definitions.bv 64%N), forall (plen : @stdpp.bitvector.definitions.bv 64%N), forall (lnw : @stdpp.bitvector.definitions.bv 64%N), forall (x1 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x5 : @stdpp.bitvector.definitions.bv 64%N), forall (x6 : @stdpp.bitvector.definitions.bv 64%N), forall (x7 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x10 : @stdpp.bitvector.definitions.bv 64%N), forall (x11 : @stdpp.bitvector.definitions.bv 64%N), forall (x12 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x13 : @stdpp.bitvector.definitions.bv 64%N), forall (x14 : @stdpp.bitvector.definitions.bv 64%N), forall (x15 :
    @stdpp.bitvector.definitions.bv 64%N), forall (x16 : @stdpp.bitvector.definitions.bv 64%N), forall (x17 : @stdpp.bitvector.definitions.bv 64%N), forall (p0 :
    @Corelib.Numbers.BinNums.Z), forall (x28 : @stdpp.bitvector.definitions.bv 64%N), forall (x29 : @stdpp.bitvector.definitions.bv 64%N), forall (x30 : @stdpp.bitvector.definitions.bv
    64%N), forall (x31 : @stdpp.bitvector.definitions.bv 64%N), @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_parse_A.pctx L HI sp m0 mo0 h0 LB PP PKA h LB m mo ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PP [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N p)] -> @Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le P p) (@Stdlib.ZArith.BinInt.Z.le p E2) -> @Stdlib.ZArith.BinInt.Z.le E2 END ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m PKA [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8
    (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z); @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z)] -> @Corelib.Init.Logic.or
    (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) pp 0%Z) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z)
    (@stdpp.bitvector.definitions.bv_unsigned 64%N plen) 0%Z) (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv 64%N) ptag (@stdpp.bitvector.definitions.Z_to_bv 64%N 0%Z))))
    (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le BUF pp) (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add pp (@stdpp.bitvector.definitions.bv_unsigned 64%N plen)) E2))
    -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned
    64%N sp) (-112)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat j0] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-104)%Z)
    [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 idw] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-100)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 agw] ->
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N
    sp) (-96)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ptag; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C4 ppad; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 plen;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 (@stdpp.bitvector.definitions.Z_to_bv 64%N pp)] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-72)%Z)
    [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 lnw] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-64)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.CB 8%nat oj;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 alen] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Step.rw_cells (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m
    (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-48)%Z) [@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s4;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s3; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s2; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s1;
    @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 s0; @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Cells.C8 ra] -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.stk
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) m lo (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp) (-112)%Z) -> @Corelib.Init.Logic.and
    (@Stdlib.ZArith.BinInt.Z.le BUF p0) (@Stdlib.ZArith.BinInt.Z.le p0 END) -> @OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.AEvt.aevtM (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) mo
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.CrtParseStmts.pk_parse_subpubkey_post (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) L HI
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.USpec.RepPk.PKC_inst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_RSA_INFO)
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_free.U_EC_INFOS) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_ecp_defs.U_MT)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_pk_sinv.U_pk_sinv L HL
    HMC) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h0 LB PP P END PKA lo m0 mo0) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MS
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Frame.mkR x1 (@stdpp.bitvector.definitions.Z_to_bv 64%N (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N sp)
    (-112)%Z)) gp tp x5 x6 x7 (@stdpp.bitvector.definitions.Z_to_bv 64%N PKA) (@stdpp.bitvector.definitions.Z_to_bv 64%N PP) x10 x11 x12 x13 x14 x15 x16 x17
    (@stdpp.bitvector.definitions.Z_to_bv 64%N E2) (@stdpp.bitvector.definitions.Z_to_bv 64%N p0) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (@stdpp.bitvector.definitions.Z_to_bv
    64%N 0x29364%Z) fc (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N)) m (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom
    (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.UImg.usegs)))
(* [comment removed for export] *).
  Proof.
    intros m mo h p E2 pp j0 idw agw oj alen ptag ppad plen lnw x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 p0 x28 x29 x30 x31
      hCtx hPcell hPrange hEnd hPka hParams hJ0 hIdw hAgw hPar hLnw hOj hSaved hStk hP0.
    pose proof pa_basics' as (hCeil & hBufCeil & hBufImg & hPPdata & hPKAdata & hRoom).
    unfold PK_PARSE_STACK in SLO.
    pose proof hCtx as (hHeap0 & _ & _ & hMi0 & _).
    pose proof (heap_mok usegs L HI h LB m mo hHeap0) as hMok.
    pose proof (pctx_bytes' h LB m mo hCtx) as hBytes.
    assert (hSpLit : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
    do 4 zstep.
    pose proof (@U_asn1_get_bitstring_null_spec L) as hBsn.
    unfold asn1_get_bitstring_null_stmt, U_ASN1_GET_BITSTRING_NULL in hBsn.
    eapply aevtM_cut_evt; [exact hMok | eapply hBsn with (PP := PP) (LENP := bv_unsigned sp + -72) (P := p) (END := E2) (BUF := BUF) (lo := lo) (bs := bs) (lenv := lnw) | ].
    all: rewrite ?hSpLit; try (first [assumption | lia | reflexivity]).
    clear hBsn. intros ms1 hPost1.
    destruct hPost1 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m1 & r1 & p1 & lw1
      & hMs1 & hMunch1 & hWm1 & hMi1 & hA01 & hR1 & hPcell1 & hLnw1 & hStk1 & hP1 & hOk1).
    subst ms1 a0. rewrite hSpLit in hMunch1, hStk1.
    rewrite (ret_pc_even 168820) by lia.
    assert (hCtx1 : pctx' h LB m1 mo).
    { refine (pctx_munch' h LB m m1 mo _ hCtx hMunch1 hWm1 hMi1 _).
      apply Forall_cons; [right; left; reflexivity |].
      apply Forall_cons; [left; cbn [fst snd]; lia |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    transport_after_call usegs m m1 hMunch1 hWm1.
    clear hCtx hMunch1 hWm1 hHeap0 hMi0.
    pose proof hCtx1 as (hHeap1 & hTop1 & hMof1 & _ & hSok1 & hSinv1 & _ & hKeep1).
    zstep. if_cases hR0; cbv_concl_iota; zify_cond hR0.
    2: {
      do 6 zstep.
      assert (hWr : bv_swrap 32 (r1 mod 18446744073709551616 + 18446744073709536512) = r1 - 15104).
      { rewrite swrap32_as_mod. lia. }
      rewrite hWr.
      assert (hLt : bv_lts (Z_to_bv 64 (r1 - 15104)) (Z_to_bv 64 r1) = true).
      { unfold bv_lts. rewrite !Z_to_bv_signed, !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). apply Z.ltb_lt. lia. }
      rewrite hLt. cbv_concl_iota.
      pose proof (low_frame_merge' m1 j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lw1 alen oj hJ0 hIdw hAgw hPar hLnw1 hOj) as hLow1.
      eapply early_walk' with (r := r1 - 15104) (p' := p1);
        [exact hCtx1 | lia | exact hPcell1 | lia | exact hPka | exact hLow1 | exact hSaved | exact hStk1]. }
    assert (hR1z : r1 = 0) by lia. subst r1. clear hR0.
    destruct (hOk1 eq_refl) as (hP1lo & hLw1). clear hOk1.
    pose proof (bv_unsigned_in_range _ lw1) as hLwR.
    assert (hP1lit : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
    assert (hSumLit : bv_unsigned (Z_to_bv 64 (bv_unsigned lw1 + p1)) = bv_unsigned lw1 + p1) by (apply unsigned_lit; lia).
    do 4 zstep.
    replace (bv_ltu (Z_to_bv 64 (bv_unsigned lw1 + p1)) (Z_to_bv 64 p1)) with false
      by (unfold bv_ltu; rewrite hSumLit, hP1lit; symmetry; apply Z.ltb_ge; lia).
    cbv_concl_iota.
    zstep. zstep. zstep. zstep.
    rewrite (proj2 (Z.ltb_lt 0 p1)) by lia.
    rewrite (proj2 (Z.ltb_ge (bv_unsigned lw1 + p1) 1)) by lia.
    if_false.
    zstep. zstep. if_cases hLenEq; cbv_concl_iota; zify_cond hLenEq.
    2: {
      zstep. zstep.
      pose proof (low_frame_merge' m1 j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lw1 alen oj hJ0 hIdw hAgw hPar hLnw1 hOj) as hLow1.
      eapply early_walk' with (r := -15206) (p' := p1);
        [exact hCtx1 | lia | exact hPcell1 | lia | exact hPka | exact hLow1 | exact hSaved | exact hStk1]. }
    zstep. zstep.
    pose proof (U_pk_info_from_type_spec L CA_PKTBL) as hInfoSpec.
    unfold pk_info_from_type_stmt, U_PK_INFO_FROM_TYPE in hInfoSpec.
    eapply aevtM_cut_evt; [exact hMok | eapply hInfoSpec; [exact hMi1 | exact hSok1 | exact CA_PKTBL | reflexivity] | ].
    clear hInfoSpec. intros ms2 (a0i & a1i & hMs2 & hA0i). subst ms2 a0i.
    rewrite (ret_pc_even 168892) by lia.
    rewrite sx32_low32.
    remember (bv_unsigned agw mod 2 ^ 32) as t eqn:hTdef.
    pose proof (pk_info_of_in U_PK_INFOS t) as hInfoCase.
    remember (pk_info_of U_PK_INFOS t) as info eqn:hInfoDef.
    zstep.
    destruct hInfoCase as [hNone | hSome].
    { rewrite hNone. if_true. zstep. zstep.
      pose proof (low_frame_merge' m1 j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lw1 alen oj hJ0 hIdw hAgw hPar hLnw1 hOj) as hLow1.
      eapply early_walk' with (r := -15488) (p' := p1);
        [exact hCtx1 | lia | exact hPcell1 | lia | exact hPka | exact hLow1 | exact hSaved | exact hStk1]. }
    assert (hInfoV : info = U_RSA_INFO \/ In info U_EC_INFOS).
    { unfold U_PK_INFOS in hSome. destruct hSome as [hR | hE]; [left; symmetry; exact hR | right; exact hE]. }
    assert (hInfoR : 0 < info < 2 ^ 64).
    { destruct hInfoV as [hR | hE]; [rewrite hR; unfold U_RSA_INFO; lia |].
      unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in hE. cbn in hE.
      destruct hE as [hE | [hE | [hE | []]]]; rewrite <- hE; lia. }
    replace (bv_eqb (Z_to_bv 64 info) (Z_to_bv 64 0)) with false
      by (unfold bv_eqb; rewrite !unsigned_lit by lia; symmetry; apply Z.eqb_neq; lia).
    cbv_concl_iota.
    zstep. zstep. zstep.
    pose proof (U_pk_setup_spec L HI U_MT HCALLOC HLS DIMG CA_RSA72 CA_EC72) as hSetup.
    unfold pk_setup_stmt, U_PK_SETUP in hSetup.
    eapply aevtM_cut; [eapply hSetup with (h := h) (LB := LB) (PKA := PKA) (info := info) (lo := lo) | ].
    all: rewrite ?hSpLit, ?hTop1; try (first [assumption | lia | reflexivity]).
    clear hSetup. intros ms3 mo3 hPost3.
    destruct hPost3 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & mo3' & h3 & r3 & C & SZ
      & hCfg3 & hMi3 & hStk3 & hMof3 & hTop3 & hB03 & hPres3 & hRes3).
    injection hCfg3 as hMs3 hMo3. subst ms3 mo3 b0.
    rewrite (ret_pc_even 168908) by lia.
    rewrite hSpLit in hStk3, hPres3.
    assert (hFr : forall A cs, rw_cells usegs m1 A cs -> bv_unsigned sp + -112 <= A ->
                  A + Z.of_nat (cells_size cs) <= bv_unsigned sp -> rw_cells usegs m3 A cs).
    { intros A cs hA hLo hHi.
      refine (keep_frame' LB (bv_unsigned sp + -112) [(PKA, PKA + 16)] m1 m3 A cs hPres3 _ hA hLo hHi _); [lia |].
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    apply hFr in hJ0; [| lia | cbn; lia].
    apply hFr in hIdw; [| lia | cbn; lia].
    apply hFr in hAgw; [| lia | cbn; lia].
    apply hFr in hPar; [| lia | cbn; lia].
    apply hFr in hLnw1; [| lia | cbn; lia].
    apply hFr in hOj; [| lia | cbn; lia].
    apply hFr in hSaved; [| lia | cbn; lia].
    pose proof (keep_pp' LB _ _ m1 m3 _ hPres3 (fun b hb => hb) ltac:(lia) hPcell1 eq_refl ltac:(cbn [disjoint_from]; slia)) as hPcell3.
    clear hFr hPcell1 hPka.
    assert (hMk : forall LBc, HEAP usegs L HI h3 LBc m3 mo3' -> (forall b, In b LB -> In b LBc) -> pctx' h3 LBc m3 mo3').
    { intros LBc hHp hSub. unfold pctx.
      split; [exact hHp |]. split; [rewrite hTop3; exact hTop1 |].
      split; [exact (mo_frame_trans _ _ _ hMof1 hMof3) |]. split; [exact hMi3 |].
      split.
      { apply (statics_ok_heap_presx usegs L LB _ _ m1 m3 hSok1 hPres3 SW).
        intros a hDat _. cbn [outside]. split; [lia | exact I]. }
      split.
      { change (si_P (U_pk_sinv L HL HMC) m3). apply (si_frame (U_pk_sinv L HL HMC) m1 m3 hSinv1).
        intros a hRa hFp. destruct (si_data (U_pk_sinv L HL HMC) a hFp) as (hDat & _ & hNs).
        apply (hPres3 a hRa); [right; left; split; [exact hDat | exact hNs] | cbn [outside]; split; [lia | exact I]]. }
      split; [exact hSub |].
      apply (heap_presx_trans usegs L LB (bv_unsigned sp) FP m0 m1 m3 hKeep1).
      apply (heap_presx_weak'' LB (bv_unsigned sp + -112) [(PKA, PKA + 16)] FP m1 m3 hPres3 (fun b hb => hb)); [lia |].
      intros a _ hOut. cbn [outside app] in hOut |- *. destruct hOut as (_ & hOk & _). split; [exact hOk | exact I]. }
    destruct hRes3 as [(hR3 & hHeap3 & hPka3) | (hR3 & hBlk & hApart & hHeap3 & hPka3 & hRsaImp & hEcImp)].
    { subst r3. pose proof (heap_mok usegs L HI h3 LB m3 mo3' hHeap3) as hMok3.
      zstep. if_true.
      pose proof (low_frame_merge' m3 j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lw1 alen oj hJ0 hIdw hAgw hPar hLnw1 hOj) as hLow3.
      eapply early_walk' with (r := -16256) (p' := p1) (h := h3);
        [exact (hMk LB hHeap3 (fun b hb => hb)) | lia | exact hPcell3 | lia | exact hPka3 | exact hLow3 | exact hSaved | exact hStk3]. }
    subst r3. pose proof (heap_mok usegs L HI h3 ((C, SZ) :: LB) m3 mo3' hHeap3) as hMok3.
    zstep. if_false.
    zstep. zstep. zstep. if_cases hIsRsa; cbv_concl_iota; zify_cond hIsRsa.
    2: {
      rewrite sx32_unsigned, <- hTdef in hIsRsa. unfold sxz in hIsRsa.
      assert (hT1 : t = 1) by (revert hIsRsa; destruct (Z.ltb_spec t (2 ^ 31)); intros hIsRsa; lia).
      assert (hIsR : info = U_RSA_INFO) by (rewrite hInfoDef, hT1; reflexivity).
      destruct (hRsaImp hIsR) as (hSZ & hRsaAt). subst SZ. rewrite hIsR in hPka3.
      pose proof (low48_merge m3 j0 idw agw ptag ppad plen (Z_to_bv 64 pp) lw1 hJ0 hIdw hAgw hPar hLnw1) as hLow48.
      eapply rsa_walk' with (C := C) (p := p1) (E2 := E2);
        [exact (hMk _ hHeap3 (fun b hb => or_intror hb)) | exact hRsaAt | exact hBlk | exact hApart | exact hPcell3 | lia
        | exact hEnd | exact hPka3 | exact hLow48 | exact hOj | exact hSaved | exact hStk3 | exact hP0]. }
    rewrite sx32_unsigned, <- hTdef in hIsRsa. unfold sxz in hIsRsa.
    assert (hTn1 : t <> 1) by (revert hIsRsa; destruct (Z.ltb_spec t (2 ^ 31)); intros hIsRsa; lia).
    assert (hInEc : In info U_EC_INFOS).
    { destruct hInfoV as [hR | hE]; [exfalso | exact hE].
      rewrite hInfoDef in hR. unfold pk_info_of in hR.
      destruct ((1 <=? t) && (t <=? 4)) eqn:hRng; [| unfold U_RSA_INFO in hR; lia].
      apply andb_true_iff in hRng as [hRl hRh]. apply Z.leb_le in hRl. apply Z.leb_le in hRh.
      assert (hT : t = 2 \/ t = 3 \/ t = 4) by lia.
      destruct hT as [hT | [hT | hT]]; rewrite hT in hR; vm_compute in hR; discriminate hR. }
    assert (hNotR : info <> U_RSA_INFO).
    { intros hR. rewrite hR in hInEc.
      unfold U_EC_INFOS, U_RSA_INFO, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in hInEc. cbn in hInEc. lia. }
    destruct (hEcImp hNotR) as (hSZ & idpad & pP & pA & pB & pX & pY & pZ & pN & hpad & pd & qX & qY & qZ & hKp). subst SZ.
    eapply ec_walk' with (C := C) (p := p1) (E2 := E2) (info := info) (pp := pp);
      [exact (hMk _ hHeap3 (fun b hb => or_intror hb)) | exact hKp | exact hBlk | exact hApart | exact hInEc | exact hParams
      | exact hPcell3 | lia | exact hEnd | exact hPka3 | exact hJ0 | exact hIdw | exact hAgw | exact hPar | exact hLnw1
      | exact hOj | exact hSaved | exact hStk3 | exact hP0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.
