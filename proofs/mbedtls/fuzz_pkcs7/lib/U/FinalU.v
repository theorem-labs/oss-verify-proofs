(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape HeapIface Walk AStep Statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv RepCrt CrtStmts CrtRelStmts CrtParseStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts RepPk.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout U_heap U_heap_laws U_ecp_defs U_ecp_grp_id_list U_pk_free U_pk_free_crt U_ecp_sinv U_pk_sinv U_fuzz_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_sub_abs U_ecp_mod_p192k1 U_ecp_mod_p224k1 U_ecp_mod_p256k1 U_ecp_check_pubkey U_ecp_point_read_binary U_ecp_closed
     U_oid_ec_grp U_oid_ec_grp_algid U_oid_pk_alg U_pk_info U_pk_parse.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib Require FinalP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require U_top.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import TopUbsan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Definition PKU : pk_class usegs := PKC_inst usegs U_RSA_INFO U_EC_INFOS U_MT.
(* [comment removed for export] *)
Definition SIU (sp0 : word) : sinv (U_layout sp0) := U_pk_sinv (U_layout sp0) (U_ecp_ids_lok sp0) (U_mc_lok sp0).

Lemma SIU_fp : forall sp0 (a : Z), ~ outside (si_fp (SIU sp0)) a -> 0x5cf90 <= a < 0x5cff8.
Proof.
  intros sp0 a NO. unfold SIU, U_pk_sinv in NO. cbn [si_fp] in NO. unfold U_ECP_IDS_DONE, U_ECP_IDS in NO. cbn in NO. lia.
Qed.

Lemma PKFREE_U sp0 : pk_free_stmt2 usegs (U_layout sp0) (U_HI sp0) PKU U_PK_FREE.
Proof.
  destruct (U_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  apply (U_pk_free_spec2 (U_layout sp0) (U_HI sp0) U_MT F1 F3 F5 F6 (U_heap_nodup sp0) F2).
  - unfold const_at, U_RSA_INFO. cbn [hl_data_lo hl_data_hi hl_written U_layout]. unfold U_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
  - intros e He. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in He.
    destruct He as [<-|[<-|[<-|[]]]]; unfold const_at; cbn [hl_data_lo hl_data_hi hl_written U_layout]; unfold U_written; (split; [lia|]; split; [lia|]; intros a Ha; lia).
Qed.

(* [comment removed for export] *)
Ltac p_const := unfold const_at; cbn [hl_data_lo hl_data_hi hl_written U_layout]; unfold U_written; (split; [lia|]); (split; [lia|]); intros a Ha; lia.

Lemma U_imgc sp0 : hl_img_hi (U_layout sp0) <= @alloc_ceiling (U_layout sp0).
Proof. pose proof (@alloc_ceiling_lo (U_layout sp0)) as ACLO. change (hl_img_hi (U_layout sp0)) with 0x7e000. lia. Qed.

Lemma PKPARSE_U sp0 : pk_parse_subpubkey_stmt usegs (U_layout sp0) (U_HI sp0) PKU (SIU sp0) 0x292a8.
Proof.
  destruct (U_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). destruct (U_layout_facts2 sp0) as [F8 F9].
  pose proof (fun a H1 H2 => U_layout_roimg sp0 a H2 H1) as ROIMG'.
  assert (CRP1 : const_at (U_layout sp0) U_ecp_mod_p192k1.RP 8) by (unfold U_ecp_mod_p192k1.RP; p_const).
  assert (CRP2 : const_at (U_layout sp0) U_ecp_mod_p224k1.RP 8) by (unfold U_ecp_mod_p224k1.RP; p_const).
  assert (CRP3 : const_at (U_layout sp0) U_ecp_mod_p256k1.RP 8) by (unfold U_ecp_mod_p256k1.RP; p_const).
  pose proof (U_ecp_point_read_binary_closed (U_layout sp0) (U_HI sp0) F1 F8 F3 F5 F6 (U_heap_nodup sp0) (U_layout_roimg sp0) (U_imgc sp0) CRP1 CRP2 CRP3) as HPRB.
  pose proof (U_ecp_check_pubkey_closed (U_layout sp0) (U_HI sp0) F1 F8 F3 F5 F6 (U_heap_nodup sp0) (U_layout_roimg sp0) (U_imgc sp0) CRP1 CRP2 CRP3) as HCPK.
  unfold PKU, SIU.
  apply (U_pk_parse_subpubkey_spec (U_layout sp0) (U_HI sp0) (U_ecp_ids_lok sp0) (U_mc_lok sp0) F1 F8 (U_heap_nodup sp0) (U_heap_perm sp0) F2).
  - unfold U_RSA_INFO. p_const.
  - unfold U_RSA_INFO. p_const.
  - unfold U_RSA_INFO. p_const.
  - intros e He. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - intros e He. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - intros e He. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - unfold U_OID_EC_GRP_TBL. p_const.
  - unfold U_OID_PK_ALG_TBL. p_const.
  - unfold U_OID_EC_GRP_ALGID_TBL. p_const.
  - unfold U_PK_INFO_TBL. p_const.
  - unfold U_BAD_POINTS. p_const.
  - exact HPRB.
  - exact HCPK.
Qed.


Lemma PF_U : forall sp0, fuzz_entry_stmt usegs (U_layout sp0) (U_HI sp0) (SIU sp0) 0x1d6ec.
Proof. intros sp0. exact (U_fuzz_top.fuzz_entry_top sp0 PKU (SIU sp0) (PKFREE_U sp0) (PKPARSE_U sp0)). Qed.

Theorem ubsan_assembled_shipped :
  strong_universal_error_free_T_budgets Equivalence.ShippedBudgets.lim_source Equivalence.ShippedBudgets.lim_target
    src_img ubsan_img.
Proof. exact (top_ubsan_shipped (@U_top.U_realizes_spec_lim SIU SIU_fp PF_U) FinalP.SIP FinalP.SIP_fp FinalP.PF_P). Qed.
