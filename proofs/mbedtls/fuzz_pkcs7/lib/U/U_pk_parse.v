(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB MpiCoreAux PresxStatics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad RepRsa RepCrt CrtStmts CrtParseStmts SInv PkTmp. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_addsub U_asn1_sequence_free U_asn1_get_sequence_of_A U_ecp_defs U_ecp_group_load U_ecp_grp_id_list U_ecp_sinv U_pk_sinv U_ecp_keypair_init U_pk_wrap_rsa U_pk_wrap_eckey U_pk_free U_pk_type U_pk_setup U_pk_ecc_set_group U_pk_ecc_set_pubkey U_pk_ecparams_A U_pk_ecparams_B U_pk_ecparams_D U_rsa_parse_pubkey U_oid U_oid_pk_alg U_oid_ec_grp U_oid_ec_grp_algid U_pk_info U_ecp_point_read_binary U_ecp_check_pubkey U_ecp_bad_points U_asn1_get_mpi U_asn1_get_tag U_asn1_get_alg_A U_asn1_get_alg U_platform_zeroize_proof U_asn1_get_bitstring_null U_x509_get_hash_alg U_pk_parse_A U_pk_parse_B U_pk_parse_C U_pk_parse_D.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1 LxU_SumsHeapO LxU_SumsCrt LxU_SumsCrt2 LxU_SumsPk LxU_checks.
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
Ltac2 gd_tbl_P_pk_parse () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_post"; "RocqVerifyHarness.AgentSubmission.USpec.RepPk.PKC_inst"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_RSA_INFO"; "RocqVerifyHarness.AgentSubmission.U.U_pk_free.U_EC_INFOS"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.U_pk_sinv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.U_pk_parse_A.U_PK_PARSE_SUBPUBKEY"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_sinv.ecp_ids_lok"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS_DONE"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_grp_id_list.U_ECP_IDS"; "RocqVerifyHarness.AgentSubmission.U.U_pk_sinv.mc_lok"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_sequence_free.U_FREE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_get_sequence_of_A.U_CALLOC"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.U_oid_ec_grp.U_OID_EC_GRP_TBL"; "RocqVerifyHarness.AgentSubmission.U.U_oid_pk_alg.U_OID_PK_ALG_TBL"; "RocqVerifyHarness.AgentSubmission.U.U_oid_ec_grp_algid.U_OID_EC_GRP_ALGID_TBL"; "RocqVerifyHarness.AgentSubmission.U.U_pk_info.U_PK_INFO_TBL"; "RocqVerifyHarness.AgentSubmission.Spec.CrtParseStmts.pk_parse_subpubkey_stmt"].


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L11607912823.3L16046331926.4L198874384.4  L54713065586.400000100800?00DSS1x1d1HS1x1d1DS1x1d". (* [comment removed for export] *)
Lemma swrap32_mod64_add : forall x d, -2^31 <= x + d < 2^31 -> bv_swrap 32 (x mod 2^64 + d) = x + d.
Proof.
  intros x d H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  pose proof (Z.div_mod x (2^64) ltac:(lia)) as D.
  replace (x mod 2^64 + d + 2^31) with ((x + d + 2^31) + (-(x / 2^64) * 2^32) * 2^32) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Hypothesis HPERM : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse ()) "Ph,(0.$1.VL,VHI,)PLB,(2.$3.)PLB',(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$6.P,(7.$1.VL,VHI,R5.R4.R2.R1.)P,(8.$3.R5.R4.)(9.(0.$1.VL,VHI,)Lh',(0.$1.VL,VHI,)(:.(7.$1.VL,VHI,R1.R6.R5.R4.)(;.$<.(=.$1.VL,VHI,R1.)(=.$1.VL,VHI,R8.))))")
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
  Hypothesis HPRB : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse ()) "(>.$1.VL,VHI,$?.$10.$11.+5<?:8.$12.)")
(* [comment removed for export] *).
  Hypothesis HCPK : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse ()) "(13.$1.VL,VHI,$?.$14.$11.+5<?:8.$15.$16.)")
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
  Notation FRS mm := (rw_cells usegs mm (bv_unsigned sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
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
  Lemma DI1 : hl_img_lo L <= hl_data_lo L. Proof. exact (proj1 DIMG). Qed.
  Lemma DI2 : hl_data_hi L <= hl_img_hi L. Proof. exact (proj2 DIMG). Qed.
  Lemma IL1 : hl_data_lo L <= U_ECP_IDS_DONE. Proof. exact (proj1 HL). Qed.
  Lemma IL2 : U_ECP_IDS_DONE + 1 <= U_ECP_IDS. Proof. exact (proj1 (proj2 HL)). Qed.
  Lemma IL3 : U_ECP_IDS + 56 <= hl_data_hi L. Proof. exact (proj1 (proj2 (proj2 HL))). Qed.
  Lemma ML1 : hl_data_lo L <= U_MUL_COUNT. Proof. exact (proj1 HMC). Qed.
  Lemma ML2 : U_MUL_COUNT + 8 <= hl_data_hi L. Proof. exact (proj1 (proj2 HMC)). Qed.
  Notation rsa_walk' := (rsa_walk L HI HFREE HCALLOC HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).
  Notation ec_walk' := (ec_walk L HI HFREE HCALLOC HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA0 CA_RSA80 CA_EC0 CA_EC80 CAT_ECGRP CA_BP HPRB HCPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).
  Notation low_frame_merge' := (low_frame_merge ra sp PP PKA bs).
  Notation init_fail_walk' := (init_fail_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 INB BP PE EB BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP SPR).
  Notation ec_fin_walk' := (ec_fin_walk L HI HFREE HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA80 CA_EC80 CA_BP HPRB HCPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 HBS0 INB BP PE EB B63 BUF0 ALP SPP SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).
  Notation head2_walk' := (head2_walk L HI HFREE HCALLOC HLS SW DIMG HND HL HMC HPERM CA_MSF CA_RSA0 CA_RSA72 CA_RSA80 CA_EC0 CA_EC72 CA_EC80 CAT_ECGRP CA_PKTBL CA_BP HPRB HCPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 mo0 h0 LB PP P END BUF PKA lo bs HH0 ALPP HBS0 INB BP PE EB B63 BUF0 ALP SPP PPT SPK PKT DPK ACL SLO SPA HTOP DHI TP DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB SPR).


  (* [comment removed for export] *)
  Ltac lxjoin H1 H2 :=
    lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
      let v := eval vm_compute in (Z.of_nat (cells_size cs1)) in
      let Hj := fresh "J" in
      pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2)) as Hj;
      let He := fresh "E" in
      assert (He : Z.of_nat (cells_size cs1) = v) by reflexivity; rewrite He in Hj; clear He;
      replace A2 with (A1 + v) in H2 by lia;
      specialize (Hj (conj H1 H2)); clear H1 H2; rename Hj into H1; cbn [app] in H1
    end end.
  Ltac join_frame mx := repeat (
    lazymatch goal with Hf0 : rw_cells usegs mx (bv_unsigned sp + -112) ?cs0 |- _ =>
      let v := eval vm_compute in (-112 + Z.of_nat (cells_size cs0)) in
      match goal with Hf1 : rw_cells usegs mx (bv_unsigned sp + v) _ |- _ => lxjoin Hf0 Hf1 end end).
  Ltac flia := first [clear_disj; lia | lia].
  (* [comment removed for export] *)
  Ltac wforall := first [apply Forall_nil | apply Forall_cons; [cbn [fst snd]; first [right; left; reflexivity | right; right; reflexivity | left; clear_disj; lia] | wforall]].
  (* [comment removed for export] *)
  Ltac keep_disj_about x := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [x] => fail | _ => clear H end end.
  Ltac dlia := lazymatch goal with |- ?x = 0 => keep_disj_about x; lia | |- ?x + _ <= _ => keep_disj_about x; lia | |- _ <= ?x => keep_disj_about x; lia end.
  (* [comment removed for export] *)
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
    end.
  Ltac pk_carve2 mx :=
    lazymatch goal with STx : stk usegs mx lo _ |- _ => carve_frame 64%nat STx end;
    lazymatch goal with FRx : rw_cells usegs mx ?A [CB 64 ?j] |- _ =>
      let JK := fresh "JK" in set (JK := j) in FRx; clearbody JK;
      change (rw_cells usegs mx A ([] ++ CB 64 JK :: [])) in FRx;
      apply (rw_cells_split_CB usegs mx A [] 64 JK [] [8; 4; 4; 8; 8; 8; 8; 8; 8]%nat) in FRx; [| reflexivity]; cbn [mk_CB_cells app] in FRx;
      lazymatch type of FRx with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 FRx [c0] end;
      lazymatch type of FRx with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb4_to_c4 FRx [c0; c1] end;
      lazymatch type of FRx with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb8_to_c8 FRx [c0; c1; c2] end;
      lazymatch type of FRx with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) => cb8_to_c8 FRx [c0; c1; c2; c3] end;
      lazymatch type of FRx with rw_cells _ _ _ [?d0; C4 ?v1; C4 ?v2; C8 ?v3; C8 ?v4; ?d5; ?d6; ?d7; ?d8] =>
        set (ow0 := v1) in FRx; set (ow1 := v2) in FRx; set (ow2 := v3) in FRx; set (ow3 := v4) in FRx;
        clearbody ow0 ow1 ow2 ow3 end
    end.
  Ltac pk_cut_at H target :=
    lazymatch type of H with rw_cells _ _ _ ?cs =>
      let n := eval compute in (length cs) in
      let rec go k :=
        let b := eval compute in (Nat.ltb k n) in
        lazymatch b with
        | true => let s := eval vm_compute in (Z.of_nat (cells_size (firstn k cs))) in
                  tryif constr_eq s target then (let H2 := fresh "CUT" in splitat H k H2) else go constr:(Datatypes.S k)
        | false => fail 1 "pk_cut_at: no cell edge"
        end in
      go 1%nat
    end.
  Ltac pk_release2 mx :=
    lazymatch goal with
    | STx : stk usegs mx lo (bv_unsigned sp + -176) |- _ =>
        try (match goal with Hc : rw_cells usegs mx (bv_unsigned sp + ?a) ?cs |- _ =>
               let lt := eval vm_compute in (andb (Z.ltb a (-112)) (Z.ltb (-112) (a + Z.of_nat (cells_size cs)))) in
               constr_eq lt true;
               let t := eval vm_compute in (-112 - a) in pk_cut_at Hc t end);
        repeat (lazymatch goal with Hf0 : rw_cells usegs mx (bv_unsigned sp + -176) ?cs0 |- _ =>
          let v := eval vm_compute in (-176 + Z.of_nat (cells_size cs0)) in
          tryif constr_eq v (-112) then fail else
          match goal with Hf1 : rw_cells usegs mx (bv_unsigned sp + v) _ |- _ => lxjoin Hf0 Hf1 end end);
        lazymatch goal with Hf0 : rw_cells usegs mx (bv_unsigned sp + -176) ?cs0 |- _ =>
          let v := eval vm_compute in (-176 + Z.of_nat (cells_size cs0)) in constr_eq v (-112);
          release_frame Hf0 STx (bv_unsigned sp + -112) end
    | |- _ => idtac
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02K0@L13339157337.208L13339157337.262L13339157337.287L13339157337.292L13339157337.293L13339157337.295L13339157337.310L13412099717.286L13412099846.263L13412099846.264L13412099846.267L13412099846.270L13412099846.272L13412099975.237L13412099975.287L161865222.263  L161865222.264  L161865222.267  L161865222.270  L161865222.272  L161865351.237  L161865351.287  L161865605.286  L19037187871.191L24769935717.286L24769935717.292L24769935717.294L24769935717.309L24912622425.264L24912622425.289L24912622425.294L24912622425.295L24912622425.297L24912622425.312L26339349477.268L26339349477.275L26339349477.277L26339349477.292L2731828513.266 L2731828513.288 L30828242209.269L30828242209.272L30828242209.274L34329078259.284L34329078259.290L34329078259.292L34329078259.307L34874598452.274L34874598452.281L34874598452.283L34874598452.298L35228988409.287L35228988409.293L35228988409.295L35228988409.310L35438476194.268L35438476194.275L35438476194.277L35438476194.292L37003246433.289L37003246433.295L37003246433.297L37003246433.312L37661809514.268L37661809514.275L37661809514.277L37661809514.292L3979369333.191 L40606388057.261L40606388057.286L40606388057.291L40606388057.292L40606388057.294L40606388057.309L4242593633.206 L4242593633.259 L4242593633.284 L4242593633.289 L4242593633.290 L4242593633.292 L4242593633.307 L42626265204.268L42626265204.275L42626265204.277L42626265204.292L43055365136.146L43218743027.288L43218743027.294L43218743027.296L43218743027.311L43639447992.189L44225163777.189L47073400537.290L47073400537.295L47073400537.296L47073400537.298L47073400537.313L50064117212.272L50064117212.279L50064117212.281L50064117212.296L51726650171.268L51726650171.275L51726650171.277L51726650171.292L52310203883.239L52310203883.266L52310203883.269L52310203883.272L52310203883.274L52310203883.288L52404896980.268L52404896980.275L52404896980.277L52404896980.292L55443441497.209L55443441497.263L55443441497.288L55443441497.293L55443441497.294L55443441497.296L55443441497.311L563601847.274  L563601847.281  L563601847.283  L563601847.298  L60330452198.148L60656340540.286L60656340798.237L60656340798.287L60656340927.263L60656340927.264L60656340927.267L60656340927.270L60656340927.272L61709497589.239L62529245694.285L62529245694.291L62529245694.293L62529245694.308L66159171417.312L66159171417.314L67949513733.286L67949513991.237L67949513991.287L67949514118.263L67949514118.264L67949514118.267L67949514118.270L67949514118.272L67949514241.189L8772778634.270 L8772778634.277 L8772778634.279 L8772778634.294 00000F00\01201H01^02402J03F04B04i05e06a07]08Y09U0:Q0;80<40=00=l0>h0?d0@`0AI0A_0B50BK0Ba0C70CM0Cc0D90DO0De0EI0Em0FQ0G50GK0Ga0H70HM0Hc0I90IO0Ie0J;0Kn0Ma0OT0QG0Q]0R30RI0R_0T?0U_0W?0X_0Y50YK0Ya0Z70Z_0[G0[o0\W0]80]N0]d0^:0^P0^f0_<0_R0_h0`>0`T0`j0a@0aV0b:0b^0cB0cf0e^0f40fJ0f`0g60h20hn0iD0iZ0j00jF0j\0kT0l80l\0mT0nn10H11b13<14^15N17018R1:41;V1<:1<^1=B1=f1><1>R1>h1?>1?T1?j1@@1A71An1Be1C\1D21Dn1Ej1Ff1Gb1HI1IE1JA1K=1Ka1L71LM1Lc1M91MO1Me1Na1O]1PY1QU1R<1S81T41U01Ul1Vd1W\1XT1YLS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H62S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H55S2sp2PP3PKA2lo2bs3PPB3PKB5lxv403H113H15S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H58S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H59S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H47S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H55S2sp2PP3PKA2lo2bs3PPB3PKB5lxv403H113H15S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H58S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H59S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H47S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H62S2sp2PP1P3END3PKA2bs3PPB3PKB4lxv03H133H14S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3BUF3PKA2bs3PPB3PKB5lxv213H25S2sp2PP3BUF3PKA2bs3PPB3PKB5lxv213H29S2sp2PP3BUF3PKA2bs3PPB3PKB5lxv213H30S2sp2PP3BUF3PKA2bs3PPB3PKB5lxv213H30S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3PKA2lo2bs4NZPP3NZP3ACP4SLO'3PPB3PKB4SPA'4ACL'4HLS'4lxv04lxv15lxv165lxv175lxv245lxv253H183H223H273H424NEppS1L2sp2PP3PKA2lo2bs4NZPP3NZP3ACP4SLO'3PPB3PKB4SPA'4ACL'4HLS'4lxv04lxv15lxv165lxv175lxv245lxv253H223H263H313H464NEppS1L2sp2PP3PKA2lo2bs4NZPP3NZP3ACP4SLO'3PPB3PKB4SPA'4ACL'4HLS'4lxv04lxv15lxv165lxv175lxv245lxv253H233H273H323H474NEppS1L2sp2PP3PKA2lo2bs4NZPP3NZP3ACP4SLO'3PPB3PKB4SPA'4ACL'4HLS'4lxv04lxv15lxv165lxv175lxv245lxv253H233H273H323H474NEppS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv175lxv205lxv213H243H423H55S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv175lxv205lxv213H283H463H59S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv175lxv205lxv213H293H473H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv175lxv205lxv213H293H473H60S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3END3PKA2bs3PPB3PKB4lxv04lxv13H49S2sp2PP3END3PKA2bs3PPB3PKB4lxv04lxv13H53S2sp2PP3END3PKA2bs3PPB3PKB4lxv04lxv13H54S2sp2PP3END3PKA2bs3PPB3PKB4lxv04lxv13H54S2sp2PP3PKA2bs3PPB3PKB3lxv2H83H16S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKB5lxv243H283H29S2sp2PP3PKA2bs3PPB3PKB5lxv243H113H33S2sp2PP3PKA2bs3PPB3PKB5lxv243H113H34S2sp2PP3PKA2bs3PPB3PKB5lxv243H333H34S1L2sp2PP1P3END3BUF3PKA2lo2bs3DPK3DKB4NZPP3NZP3DSB3ACP3BAC4SLO'3PPB3PKB4ACL'4HLS'3BP'3PE'3EB'5BUF0'5NZPP'4NZP'4SPP'4SPK'S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H17S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H17S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKB5lxv165lxv245lxv253H183H203H293EppS2sp2PP3PKA2bs3PPB3PKB5lxv243H113H33S2sp2PP3PKA2bs3PPB3PKB5lxv243H113H34S2sp2PP3PKA2bs3PPB3PKB5lxv165lxv245lxv253H233H253H343EppS1L2sp2PP1P3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H423H433H503H55S1L2sp2PP1P3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H463H473H543H59S1L2sp2PP1P3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H473H483H553H60S1L2sp2PP1P3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H473H483H553H60S1L2sp2PP1P3END3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H343H353H413H423H47S2sp2PP1P3END3PKA2bs3PPB3PKB5lxv175lxv403H113H15S1L2sp2PP1P3END3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H453H463H523H533H58S1L2sp2PP1P3END3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H463H473H533H543H59S1L2sp2PP1P3END3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H473H483H543H553H60S1L2sp2PP1P3END3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'4lxv04lxv15lxv173H493H503H563H573H62S2sp2PP3PKA2bs3PPB3PKB5lxv203H363H37S2sp2PP3PKA2bs3PPB3PKB5lxv203H403H41S2sp2PP3PKA2bs3PPB3PKB5lxv203H413H42S2sp2PP3PKA2bs3PPB3PKB5lxv203H413H42S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3BUF3PKA2bs3PPB3PKB5lxv165lxv253H183H233H274NEppS2sp2PP3BUF3PKA2bs3PPB3PKB5lxv165lxv253H223H273H314NEppS2sp2PP3BUF3PKA2bs3PPB3PKB5lxv165lxv253H233H283H324NEppS2sp2PP3BUF3PKA2bs3PPB3PKB5lxv165lxv253H233H283H324NEppS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H62S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H47S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H55S2sp2PP3PKA2lo2bs3PPB3PKB5lxv403H113H15S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H58S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H59S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S2sp2PP3PKA2bs3PPB3PKB5lxv163H103H37S2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS2sp2PP3PKA2bs3PPB3PKBS1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H62S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H47S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H55S2sp2PP3PKA2lo2bs3PPB3PKB5lxv403H113H15S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H58S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H59S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H60S1L2sp2PP3BUF3PKA2lo2bs4NZPP3NZP4SLO'3PPB3PKB4HLS'5BUF0'3H17S2sp2PP3PKA2bs3PPB3PKB5lxv165lxv225lxv253H183H193H333EppS2sp2PP3PKA2bs3PPB3PKB5lxv165lxv225lxv253H223H233H373EppS2sp2PP3PKA2bs3PPB3PKB5lxv165lxv225lxv253H233H243H383EppS2sp2PP3PKA2bs3PPB3PKB5lxv165lxv225lxv253H233H243H383Epp". (* [comment removed for export] *)
  Lemma head1_walk : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse ()) "Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)(17.$1.Vmo0,(18.$1.VL,VHI,(19.$1.$1:.$1;.$?.)(1<.VL,VHL,VHMC,)Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh0,VLB,VPP,VP,VEND,VPKA,Vlo,Vm0,Vmo0,)(1=.(1>.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(1?.&40.VPP,)(1?.&40.VEND,)(1?.&40.VPKA,)R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(1?.&40.$20.)Vfc,(21.(4.&40.))Vm0,(22.$1.)))")
(* [comment removed for export] *).
  Proof.
    intros. unfold U_PK_PARSE_SUBPUBKEY. clear RA.
    pose proof pa_basics' as (ACP & BAC & BIM & PPD & PKD & SLO').
    pose proof (heap_mok _ _ HI _ _ _ _ HH0) as MK0.
    pose proof (rw_cells_bound _ _ _ _ HPP0) as PPB. cbn [cells_size csize Nat.add] in PPB.
    pose proof (rw_cells_bound _ _ _ _ HPKA0) as PKB. cbn [cells_size csize Nat.add] in PKB.
    assert (CX0 : pctx' h0 LB m0 mo0).
    { split; [exact HH0|]. split; [reflexivity|]. split; [apply mo_frame_refl|]. split; [exact MI0|]. split; [exact SOK0|]. split; [exact SIP0|].
      split; [intros b Hb; exact Hb| apply heap_presx_refl]. }
    (* [comment removed for export] *)
    pose proof HPP0 as HPP. pose proof HPKA0 as HPKA. pose proof HBS0 as HBS. pose proof ST0 as ST. pose proof MI0 as MI. pose proof SOK0 as SOK.
    lazymatch type of HPP0 with ?T => change (lx_hidden T) in HPP0 end. lazymatch type of HPKA0 with ?T => change (lx_hidden T) in HPKA0 end.
    lazymatch type of HBS0 with ?T => change (lx_hidden T) in HBS0 end. lazymatch type of ST0 with ?T => change (lx_hidden T) in ST0 end.
    lazymatch type of MI0 with ?T => change (lx_hidden T) in MI0 end. lazymatch type of SOK0 with ?T => change (lx_hidden T) in SOK0 end.
    pose proof (bytes_at_bound _ _ _ _ HBS) as BB. pose proof SPA as SPA'. pose proof SPR as SPR'. pose proof ACL as ACL'. pose proof DHI as DHI'. pose proof HLS as HLS'.
    pose proof BP as BP'. pose proof PE as PE'. pose proof EB as EB'. pose proof B63 as B63'. pose proof BUF0 as BUF0'. pose proof ALPP as ALPP'. pose proof ALP as ALP'.
    pose proof NZPP as NZPP'. pose proof NZP as NZP'. pose proof DKB as DKB'. pose proof DPB as DPB'. pose proof DPK as DPK'. pose proof DSPP as DSPP'. pose proof DSP as DSP'. pose proof DSB as DSB'.
    pose proof SPP as SPP'. pose proof SPK as SPK'. pose proof HTOP as HTOP'. pose proof DI1 as DI1'. pose proof DI2 as DI2'.
    (* [comment removed for export] *)
    carve_frame 112%nat ST.
    lazymatch type of FR with rw_cells usegs ?mx ?A [CB 112 ?j] =>
      set (JJ := j) in FR; clearbody JJ;
      change (rw_cells usegs mx A ([] ++ CB 112 JJ :: [])) in FR;
      apply (rw_cells_split_CB usegs mx A [] 112 JJ [] [8; 4; 4; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: _) => cb4_to_c4 FR [c0] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb4_to_c4 FR [c0; c1] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: _) => cb4_to_c4 FR [c0; c1; c2] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: _) => cb4_to_c4 FR [c0; c1; c2; c3] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: _) => cb8_to_c8 FR [c0; c1; c2; c3; c4] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: _) => cb8_to_c8 FR [c0; c1; c2; c3; c4; c5] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: _) => cb8_to_c8 FR [c0; c1; c2; c3; c4; c5; c6] end.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: _) => cb8_to_c8 FR [c0; c1; c2; c3; c4; c5; c6; c7; c8] end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells ?sg ?mx ?A [?c0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C8 ?w5; C8 ?w6; C8 ?w7; ?c8; C8 ?w9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15] =>
      set (iw0 := w1) in FR; set (aw0 := w2) in FR; set (pw0 := w3) in FR; set (pw1 := w4) in FR; set (pw2 := w5) in FR; set (pw3 := w6) in FR;
      set (lw0 := w7) in FR; set (sw0 := w9) in FR;
      clearbody iw0 aw0 pw0 pw1 pw2 pw3 lw0 sw0 end.
    (* [comment removed for export] *)
    pose proof (heapkit_introX L HI h0 LB m0 mo0 [(lo, heap_top usegs L HI h0)] HH0
       ltac:(constructor; [apply ok_stack; exact ACL | constructor])) as HK.
    pose proof (so_box L m0 SOK) as Q0.
    rewrite TP.
    lazymatch goal with |- aevtM _ _ ?Q _ =>
    assert (SU : Forall (summary_okMR usegs lx_no_layout (GS9 L lo (heap_top usegs L HI h0)) [statics_ok usegs L] [] (PROPS3 L LB lo (heap_top usegs L HI h0)) LB
                          (hpP L HI (heap_top usegs L HI h0) mo0) (cwP L (heap_top usegs L HI h0)) (LH2 L) (HRS1 L) (tgt_aevtM usegs Q) (fun _ => True))
                   [SUM_gettagP; SUM_agetalgP; SUM_oid1P U_OID_GET_PK_ALG 32; SUM_oid1P U_OID_GET_EC_GRP_ALGID 32])
      by (constructor; [apply sum_plain_MR; [reflexivity| apply sum_gettagP_valid]
         | constructor; [apply (sum_agetalgP_MR L U_MEMSET_FUNC (U_asn1_get_alg_spec L (U_platform_zeroize_spec L)) CA_MSF [statics_ok usegs L] eq_refl)
         | constructor; [apply (sum_oid1P_MR L U_OID_GET_PK_ALG U_OID_PK_ALG_TBL 120 32 (U_oid_get_pk_alg_spec L) CAT_PKALG [statics_ok usegs L] eq_refl)
         | constructor; [apply (sum_oid1P_MR L U_OID_GET_EC_GRP_ALGID U_OID_EC_GRP_ALGID_TBL 80 32 (U_oid_get_ec_grp_algid_spec L) CAT_ECALGID [statics_ok usegs L] eq_refl)
         | constructor]]]])
    end.
    lx_run_tac (PLANS [0x2952c; 0x29344; 0x29528] [] 200%N [SUM_gettagP; SUM_agetalgP; SUM_oid1P U_OID_GET_PK_ALG 32; SUM_oid1P U_OID_GET_EC_GRP_ALGID 32]); lx_tree.
    all: lxu_chk_leaves 0x29528.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x2952c) _ _ ?mx _) =>
           rename LXHK into HK1; pk_carve2 mx;
           lx_run_tac (PLANS [0x29344; 0x29364; 0x29578] [] 200%N [SUM_gettagP; SUM_agetalgP; SUM_oid1P U_OID_GET_PK_ALG 32; SUM_oid1P U_OID_GET_EC_GRP_ALGID 32]); lx_tree
         | |- _ => idtac end.
    all: lxu_chk_leaves 0x29578.
    all: destruct LXHK as [[(hc3 & HH3 & HT3 & MF3) _] _]; rewrite <- TP; clear HK SU Q0; try clear HK1.
    all: lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => pk_release2 mx end.

    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         join_frame mx;
         lazymatch goal with Hm1 : munch ?W1 m0 mx, Hw1 : wmono _ m0 mx, MIx : mem_inv _ mx |- _ =>
           pose proof (pctx_munch' _ _ _ _ _ _ CX0 Hm1 Hw1 MIx ltac:(wforall)) as CXl; clear Hm1 Hw1
         end end.
    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x29344) _ _ ?mx _) =>
         lazymatch goal with HF : rw_cells _ mx (bv_unsigned sp + -112) ?cs, HP : rw_cells _ mx PP _, HA : rw_cells _ mx PKA _, STx : stk _ mx lo _ |- _ =>
           let n := eval compute in (length cs - 6)%nat in
           let HS := fresh "SV" in splitat HF n HS;
           let lj := fresh "lj" in let HL := fresh "FRL" in
           destruct (rw_cells_forget _ _ _ _ HF) as [lj HL]; cbn [cells_size csize Nat.add length] in HL;
           eapply early_walk'; [exact CXl| clear_disj; lia| exact HP| clear_disj; lia| exact HA| exact HL| exact HS| exact STx]
         end
       | |- _ => idtac end.
    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x29364) _ _ ?mx _) =>
         lazymatch goal with HF : rw_cells _ mx (bv_unsigned sp + -112) _, HP : rw_cells _ mx PP _, HA : rw_cells _ mx PKA _, STx : stk _ mx lo _ |- _ =>
           let H1 := fresh "FID" in let H2 := fresh "FALG" in let H3 := fresh "FPAR" in let H4 := fresh "FLEN" in let H5 := fresh "FSCR" in let H6 := fresh "SV" in
           splitat HF 1%nat H1; splitat H1 1%nat H2; splitat H2 1%nat H3; splitat H3 4%nat H4; splitat H4 1%nat H5; splitat H5 2%nat H6;
           eapply head2_walk'; [exact CXl| exact HP| | | exact HA| | exact HF| exact H1| exact H2| exact H3| exact H4| exact H5| exact H6| exact STx| ];
             rewrite ?unsigned_lit by (clear_disj; lia);
             [clear_disj; lia| clear_disj; lia
             | lazymatch goal with |- (?pp = 0 /\ _) \/ _ =>
                 destruct (Z.eq_dec pp 0) as [Epp|NEpp]; [left; split; [exact Epp| split; [dlia| f_equal; dlia]] | right; split; dlia] end
             | clear_disj; lia]
         end
       | |- _ => idtac end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PA.

Theorem U_pk_parse_subpubkey_spec : ltac2:(CDefT.buildp (gd_tbl_P_pk_parse ()) "PL,$23.PHI,(24.$1.R1.)PHL,(25.R2.$26.$27.)PHMC,(28.R3.+5<?:8.)P,(;.$<.(29.R4.)$2:.)P,(;.$<.(2;.R5.)$2<.)P,Ph,(0.$1.R6.R5.)PLB,(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$6.P,(7.$1.R:.R9.R4.R3.R2.R1.)(2=.$<.(2>.(2?.$<.$<.)$<.(30.$<.$<.)R4.))P,Ph,(0.$1.R7.R6.)PLB,(2.$3.)PLB',(2.$3.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$6.P,(7.$1.R<.R;.R5.R4.R2.R1.)P,(8.$3.R5.R4.)(9.(0.$1.R>.R=.)Lh',(0.$1.R>.R=.)(:.(7.$1.R?.R>.R1.R6.R5.R4.)(;.$<.(=.$1.R?.R>.R1.)(=.$1.R?.R>.R8.))))P,(31.R8.$11.+8.)P,(31.R9.$1:.+4.)P,(31.R:.(32.$1:.+48.)+8.)P,(31.R;.(32.$1:.+50.)+8.)P,Pe,$<.P,(33.$<.R1.$1;.)(31.R>.R2.+4.)P,Pe,$<.P,(33.$<.R1.$1;.)(31.R?.(32.R2.+48.)+8.)P,Pe,$<.P,(33.$<.R1.$1;.)(31.R10.(32.R2.+50.)+8.)P,(31.R?.$34.+1;8.)P,(31.R10.$35.+78.)P,(31.R11.$36.+50.)P,(31.R12.$37.+20.)P,(31.R13.$15.+20.)P,(>.$1.R14.R13.$?.$10.$11.+5<?:8.$12.)P,(13.$1.R15.R14.$?.$14.$11.+5<?:8.$15.$16.)(38.$1.R16.R15.(19.$1.$1:.$1;.$?.)(1<.R16.R14.R13.)$20.)")
(* [comment removed for export] *).
Proof.
  intros L HI HL HMC HFREE HCALLOC HND HPERM CA_MSF CA_RSA0 CA_RSA72 CA_RSA80 CA_EC0 CA_EC72 CA_EC80 CAT_ECGRP CAT_PKALG CAT_ECALGID CA_PKTBL CA_BP HPRB HCPK.
  unfold pk_parse_subpubkey_stmt. intros until bs.
  intros HH0 HPP0 ALPP HBS0 INB BP PE EB B63 BUF0 HPKA0 ALP SPP PPT SPK PKT DPK ST0 ACL SLO SPA HTOP DHI MI0 SOK0 SIP0 TP DPK' DKB DPB NZPP NZP DSPP DSP DSB CWPP CWP CRB DI1' DI2' SW' HLS' -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  eapply head1_walk; first [ eassumption | exact (conj DI1' DI2') | exact (proj2 SPR) | match goal with |- ?g => idtac "THMLEFT" g end ].
Qed.
