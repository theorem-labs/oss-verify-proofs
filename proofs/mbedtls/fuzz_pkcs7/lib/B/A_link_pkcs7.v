(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets A_link_adapt A_link_rates.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_misc A_link_asn1 A_link_oid A_link_mpi A_link_pk A_link_x509.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_ecp_defs A_pkcs7_cinfo A_pkcs7_free A_pkcs7_free24 A_pkcs7_getcerts24 A_pkcs7_getsig A_pkcs7_nextlen A_pkcs7_parse24 A_pkcs7_signer_I A_pkcs7_signers_M.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_pkcs7 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_cinfo.A_pkcs7_cinfo_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc0"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_getsig.A_pkcs7_getsig_spec"; "RocqVerifyHarness.AgentSubmission.B.A_pkcs7_nextlen.A_pkcs7_nextlen_spec"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"].


Definition A_pkcs7_cinfo_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pkcs7 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.))")
(* [comment removed for export] *).

Definition A_pkcs7_free_walk_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_free.A_pkcs7_free_walk R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_free R LO) (A_link_layout.alo_need_free R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_malloc R LO) (A_link_misc.A_platform_zeroize_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) (A_link_mpi.A_zeroize_and_free_spec_cl R HIA LO HO) _ _ _ _ _ _ _ _ (A_link_pk.A_pk_free_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_free_walk24_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_free24.A_pkcs7_free_walk24 R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_free R LO) (A_link_layout.alo_need_free R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_malloc R LO) (A_link_misc.A_platform_zeroize_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) (A_link_mpi.A_zeroize_and_free_spec_cl R HIA LO HO) _ _ _ _ _ _ _ _ (A_link_pk.A_pk_free_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_getcerts_spec24_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_getcerts24.A_pkcs7_getcerts_spec24 R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc1 R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) _ _ _ _ _ _ _ (A_link_x509.A_x509_crt_parse_spec_cl R HIA LO HO) _ _ _ (A_link_layout.alo_dimg R LO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_getsig_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pkcs7 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(9.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.))")
(* [comment removed for export] *).

Definition A_pkcs7_nextlen_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pkcs7 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.(;.R4.)(<.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_pkcs7_signer_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_signer_I.A_pkcs7_signer_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_free R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) _ _ _ _ _ _ _ (A_pkcs7_getsig_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_alg_null_spec_cl R HIA LO HO) (A_link_layout.alo_memcmp_i R LO) (A_link_x509.A_x509_get_name_spec_cl R HIA LO HO) (A_link_x509.A_x509_get_serial_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_int_spec_cl R HIA LO HO) (A_link_layout.alo_need_amem R LO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_getsigners_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_signers_M.A_pkcs7_getsigners_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_free R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) _ _ _ _ (A_pkcs7_signer_spec_cl R HIA LO HO) _ _ _ _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_parse_der_spec24_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pkcs7_parse24.A_pkcs7_parse_der_spec24 R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) _ _ (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) _ _ _ _ _ _ (A_pkcs7_getcerts_spec24_cl R HIA LO HO) _ _ _ _ (A_pkcs7_getsigners_spec_cl R HIA LO HO) A_link_rates.PJ_PHI A_link_rates.PJ_FFR A_link_rates.PJ_CNT _ _ _ (A_pkcs7_free_walk24_cl R HIA LO HO) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_link_layout.alo_amemset R LO) (A_link_layout.alo_memcmp_i R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_calloc R LO) (A_pkcs7_cinfo_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_alg_null_spec_cl R HIA LO HO) (A_link_oid.A_oid_get_md_alg_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_int_spec_cl R HIA LO HO) (A_pkcs7_nextlen_spec_cl R HIA LO HO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_bcmp R LO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).
