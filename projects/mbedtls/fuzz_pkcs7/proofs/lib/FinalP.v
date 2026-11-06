(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape HeapIface Walk AStep Statics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import TopContract SInv RepCrt CrtStmts CrtRelStmts CrtParseStmts CrtExtStmts RepPk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_heap P_heap_laws P_ecp_defs P_ecp_grp_id_list P_pk_free P_pk_free_crt P_ecp_sinv P_pk_sinv P_fuzz_top.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_sub_abs P_ecp_mod_p192k1 P_ecp_mod_p224k1 P_ecp_mod_p256k1 P_ecp_check_pubkey P_ecp_point_read_binary P_ecp_closed
     P_oid_ec_grp P_oid_ec_grp_algid P_oid_pk_alg P_pk_info P_pk_parse.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Definition PKP : pk_class psegs := PKC_inst psegs P_RSA_INFO P_EC_INFOS P_MT.
(* [comment removed for export] *)
Definition SIP (sp0 : word) : sinv (P_layout sp0) := P_pk_sinv (P_layout sp0) (P_ecp_ids_lok sp0) (P_mc_lok sp0).

Lemma SIP_fp : forall sp0 (a : Z), ~ outside (si_fp (SIP sp0)) a -> 0x59890 <= a < 0x598f8.
Proof.
  intros sp0 a NO. unfold SIP, P_pk_sinv in NO. cbn [si_fp] in NO. unfold P_ECP_IDS_DONE, P_ECP_IDS in NO. cbn in NO. lia.
Qed.

Lemma PKFREE_P sp0 : pk_free_stmt2 psegs (P_layout sp0) (P_HI sp0) PKP P_PK_FREE.
Proof.
  destruct (P_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  apply (P_pk_free_spec2 (P_layout sp0) (P_HI sp0) P_MT F1 F3 F5 F6 (P_heap_nodup sp0) F2).
  - unfold const_at, P_RSA_INFO. cbn [hl_data_lo hl_data_hi hl_written P_layout]. unfold P_written. split; [lia|]. split; [lia|]. intros a Ha. lia.
  - intros e He. unfold P_EC_INFOS, P_ECKEY_INFO, P_ECKEYDH_INFO, P_ECDSA_INFO in He.
    destruct He as [<-|[<-|[<-|[]]]]; unfold const_at; cbn [hl_data_lo hl_data_hi hl_written P_layout]; unfold P_written; (split; [lia|]; split; [lia|]; intros a Ha; lia).
Qed.

(* [comment removed for export] *)
Ltac p_const := unfold const_at; cbn [hl_data_lo hl_data_hi hl_written P_layout]; unfold P_written; (split; [lia|]); (split; [lia|]); intros a Ha; lia.

Lemma P_imgc sp0 : hl_img_hi (P_layout sp0) <= @alloc_ceiling (P_layout sp0).
Proof. pose proof (@alloc_ceiling_lo (P_layout sp0)) as ACLO. change (hl_img_hi (P_layout sp0)) with 0x7b000. lia. Qed.

Lemma PKPARSE_P sp0 : pk_parse_subpubkey_stmt psegs (P_layout sp0) (P_HI sp0) PKP (SIP sp0) 0x27230.
Proof.
  destruct (P_layout_facts sp0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). destruct (P_layout_facts2 sp0) as [F8 F9].
  pose proof (fun a H1 H2 => P_layout_roimg sp0 a H2 H1) as ROIMG'.
  assert (CRP1 : const_at (P_layout sp0) P_ecp_mod_p192k1.RP 8) by (unfold P_ecp_mod_p192k1.RP; p_const).
  assert (CRP2 : const_at (P_layout sp0) P_ecp_mod_p224k1.RP 8) by (unfold P_ecp_mod_p224k1.RP; p_const).
  assert (CRP3 : const_at (P_layout sp0) P_ecp_mod_p256k1.RP 8) by (unfold P_ecp_mod_p256k1.RP; p_const).
  pose proof (P_ecp_point_read_binary_closed (P_layout sp0) (P_HI sp0) F1 F8 F3 F5 F6 (P_heap_nodup sp0) (P_layout_roimg sp0) (P_imgc sp0) CRP1 CRP2 CRP3) as HPRB.
  pose proof (P_ecp_check_pubkey_closed (P_layout sp0) (P_HI sp0) F1 F8 F3 F5 F6 (P_heap_nodup sp0) (P_layout_roimg sp0) (P_imgc sp0) CRP1 CRP2 CRP3) as HCPK.
  unfold PKP, SIP.
  apply (P_pk_parse_subpubkey_spec (P_layout sp0) (P_HI sp0) (P_ecp_ids_lok sp0) (P_mc_lok sp0) F1 F8 (P_heap_nodup sp0) (P_heap_perm sp0) F2).
  - unfold P_RSA_INFO. p_const.
  - unfold P_RSA_INFO. p_const.
  - unfold P_RSA_INFO. p_const.
  - intros e He. unfold P_EC_INFOS, P_ECKEY_INFO, P_ECKEYDH_INFO, P_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - intros e He. unfold P_EC_INFOS, P_ECKEY_INFO, P_ECKEYDH_INFO, P_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - intros e He. unfold P_EC_INFOS, P_ECKEY_INFO, P_ECKEYDH_INFO, P_ECDSA_INFO in He. destruct He as [<-|[<-|[<-|[]]]]; p_const.
  - unfold P_OID_EC_GRP_TBL. p_const.
  - unfold P_OID_PK_ALG_TBL. p_const.
  - unfold P_OID_EC_GRP_ALGID_TBL. p_const.
  - unfold P_PK_INFO_TBL. p_const.
  - unfold P_BAD_POINTS. p_const.
  - exact HPRB.
  - exact HCPK.
Qed.


Lemma PF_P : forall sp0, fuzz_entry_stmt psegs (P_layout sp0) (P_HI sp0) (SIP sp0) 0x1d26c.
Proof. intros sp0. exact (P_fuzz_top.fuzz_entry_top sp0 PKP (SIP sp0) (PKFREE_P sp0) (PKPARSE_P sp0)). Qed.
