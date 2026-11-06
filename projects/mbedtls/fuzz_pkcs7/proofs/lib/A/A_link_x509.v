(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_link_layout A_link_base A_link_budgets A_link_adapt A_link_rates.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_link_misc A_link_asn1 A_link_mpi A_link_pk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_ecp_defs A_link_adapt A_pk_parse_G0 A_x509_akid A_x509_basic A_x509_crl_free A_x509_crt_ext A_x509_crt_free A_x509_crt_free2 A_x509_crt_init A_x509_crt_parse A_x509_get_alg A_x509_get_dates A_x509_get_ext A_x509_get_name_I A_x509_get_san A_x509_get_serial A_x509_get_sig A_x509_get_sig_alg A_x509_get_time A_x509_get_uid A_x509_hash_alg A_x509_key_usage A_x509_ns_cert_type A_x509_parse_san_C A_x509_policies A_x509_rates A_x509_rsassa_pss A_x509_san_ext_M A_x509_skid.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_x509 () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.A_link_layout.a_layout_ok"; "OSSVerify.KrLib.A.A_link_layout.a_hia_ok"; "OSSVerify.KrLib.A.A_x509_get_name_I.A_x509_get_name_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_img"; "OSSVerify.KrLib.A.A_link_layout.alo_uar_got"; "OSSVerify.KrLib.A.A_link_layout.alo_smalloc1"; "OSSVerify.KrLib.A.A_link_layout.alo_calloc"; "OSSVerify.KrLib.A.A_link_asn1.A_asn1_get_tag_spec_cl"; "OSSVerify.KrLib.A.A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl"; "OSSVerify.KrLib.A.A_x509_basic.A_x509_basic_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_smalloc0"; "OSSVerify.KrLib.A.A_x509_crl_free.A_x509_crl_free_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_free"; "OSSVerify.KrLib.A.A_link_layout.alo_need_free"; "OSSVerify.KrLib.A.A_link_layout.alo_need_amem"; "OSSVerify.KrLib.A.A_link_misc.A_platform_zeroize_spec_cl"; "OSSVerify.KrLib.A.A_x509_get_ext.A_x509_get_ext_spec"; "OSSVerify.KrLib.A.A_x509_key_usage.A_x509_key_usage_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_amemset"; "OSSVerify.KrLib.A.A_x509_skid.A_x509_skid_spec"; "OSSVerify.KrLib.A.A_x509_ns_cert_type.A_x509_ns_cert_type_spec"; "OSSVerify.KrLib.A.A_x509_policies.A_x509_policies_specE"; "OSSVerify.KrLib.A.A_link_layout.alo_need_smalloc"; "OSSVerify.KrLib.A.A_link_layout.alo_need_bcmp"; "OSSVerify.KrLib.A.A_link_layout.alo_need_malloc"; "OSSVerify.KrLib.A.A_link_base.alo_oid_rt"; "OSSVerify.KrLib.A.A_x509_crt_init.A_pkcs7_init_spec"; "OSSVerify.KrLib.A.A_x509_crt_init.A_x509_crt_init_spec"; "OSSVerify.KrLib.A.A_x509_get_serial.A_x509_get_serial_spec"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.A.A_x509_get_alg.A_x509_get_alg_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_memset_i"; "OSSVerify.KrLib.A.A_link_layout.alo_rtc"; "OSSVerify.KrLib.A.A_x509_get_sig_alg.A_x509_get_sig_alg_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_smalloc2"; "OSSVerify.KrLib.A.A_x509_get_dates.A_x509_get_dates_spec"; "OSSVerify.KrLib.A.A_x509_get_uid.A_x509_get_uid_spec"; "OSSVerify.KrLib.A.A_x509_get_sig.A_x509_get_sig_spec"; "OSSVerify.KrLib.A.A_x509_get_name_I.A_x509_get_name_specE"; "OSSVerify.KrLib.A.A_x509_get_time.A_x509_get_time_spec"; "OSSVerify.KrLib.A.A_x509_hash_alg.A_x509_hash_alg_spec"; "OSSVerify.KrLib.A.A_x509_policies.A_x509_policies_spec"; "OSSVerify.KrLib.A.A_x509_rsassa_pss.A_x509_rsassa_pss_spec"].


Definition A_x509_get_name_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(9.R4.R2.)(:.R4.R3.R2.R1.)(;.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_x509_parse_san_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_parse_san_C.A_x509_parse_san_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_bcmp R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_memcmp_i R LO) (A_link_layout.alo_gsb R LO) _ _ _ _ _ (A_x509_get_name_spec_cl R HIA LO HO) _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_san_ext_specE_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_san_ext_M.A_x509_san_ext_specE R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_calloc R LO) (A_link_layout.aho_nodup R HIA HO) _ _ _ _ _ (A_x509_parse_san_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) _ _ _ _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_akid_specE_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_akid.A_x509_akid_specE R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_layout.alo_dimg R LO) A_x509_rates.PHIsan A_x509_rates.FFRsan A_x509_rates.CNTsan _ _ (A_x509_san_ext_specE_cl R HIA LO HO) _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_basic_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(<.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_crl_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(>.R4.R3.(6.R4.R2.)(?.R4.R2.)(10.R4.R2.)(11.R4.R2.)(12.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_x509_get_ext_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(13.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_key_usage_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(14.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_skid_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(16.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_ns_cert_type_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(17.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_san_specE_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_get_san.A_x509_get_san_specE R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) A_x509_rates.PHIsan A_x509_rates.FFRsan A_x509_rates.CNTsan _ _ (A_x509_san_ext_specE_cl R HIA LO HO) _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_policies_specE_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(18.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.)(19.R4.R2.)(1:.R4.R2.)(1;.R4.R2.)(9.R4.R2.)(:.R4.R3.R2.R1.)(1<.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_x509_crt_ext_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_crt_ext.A_x509_crt_ext_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_adapt.STKext R) _ (A_link_layout.alo_amemset R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_bool_spec_cl R HIA LO HO) (A_link_base.alo_oid_rt R HIA LO) (A_x509_get_ext_spec_cl R HIA LO HO) (A_x509_basic_spec_cl R HIA LO HO) (A_x509_key_usage_spec_cl R HIA LO HO) (A_x509_skid_spec_cl R HIA LO HO) (A_x509_ns_cert_type_spec_cl R HIA LO HO) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_link_asn1.A_asn1_get_seq_of_specE_cl R HIA LO HO) (A_x509_get_san_specE_cl R HIA LO HO) (A_x509_policies_specE_cl R HIA LO HO) (A_x509_akid_specE_cl R HIA LO HO) _ _ _ _ _ _ _ A_x509_rates.XJ_PHI A_x509_rates.XJ_FFR A_x509_rates.XJ_CNT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_crt_free_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_crt_free.A_x509_crt_free_spec R HIA _ _ _ _ (A_link_layout.alo_img R LO) (A_link_layout.alo_free R LO) (A_link_layout.alo_need_free R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_malloc R LO) (A_link_misc.A_platform_zeroize_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) (A_link_mpi.A_zeroize_and_free_spec_cl R HIA LO HO) _ _ _ _ _ (A_link_pk.A_pk_free_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_layout.alo_dimg R LO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_crt_free_walk2_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_crt_free2.A_x509_crt_free_walk2 R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_free R LO) (A_link_layout.alo_need_free R LO) (A_link_layout.alo_need_malloc R LO) (A_link_misc.A_platform_zeroize_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) (A_link_mpi.A_zeroize_and_free_spec_cl R HIA LO HO) _ _ _ _ _ _ _ (A_link_pk.A_pk_free_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_layout.alo_dimg R LO)); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_pkcs7_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1=.R4.R3.(6.R4.R2.)(15.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_crt_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1>.R4.R3.(6.R4.R2.)(15.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_serial_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1?.(20.R4.)(21.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(22.R4.R3.(6.R4.R2.)(23.R4.R2.)(24.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_sig_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(25.R4.R3.(1<.R4.R3.R2.)(9.R4.R2.)(?.R4.R2.)(7.R4.R2.)(26.R4.R2.)(8.R4.R2.)(15.R4.R2.)(23.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_dates_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(27.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_uid_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(28.(20.R4.)(21.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_sig_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(29.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_get_name_specE_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2:.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(9.R4.R2.)(:.R4.R3.R2.R1.)(;.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_x509_crt_parse_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_crt_parse.A_x509_crt_parse_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc3 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_adapt.STKcrt R) _ (A_link_layout.alo_setf5 R LO) _ (A_link_layout.alo_amemset R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_memcmp_i R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_bcmp R LO) (A_link_layout.alo_need_malloc R LO) (A_link_layout.alo_need_free R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) _ _ (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_int_spec_cl R HIA LO HO) (A_x509_get_serial_spec_cl R HIA LO HO) (A_x509_get_alg_spec_cl R HIA LO HO) (A_x509_get_sig_alg_spec_cl R HIA LO HO) (A_x509_get_dates_spec_cl R HIA LO HO) (A_x509_get_uid_spec_cl R HIA LO HO) (A_x509_get_sig_spec_cl R HIA LO HO) _ _ _ _ (A_x509_get_name_specE_cl R HIA LO HO) _ _ _ _ _ (A_link_pk.A_pk_parse_subpubkey_spec_cl R HIA LO HO) _ _ _ _ (A_x509_crt_ext_spec_cl R HIA LO HO) _ _ _ (A_x509_crt_free_walk2_cl R HIA LO HO) _ _ _ _ _ _ _ _ _ A_x509_rates.CJ_PHI A_x509_rates.CJ_FFR A_x509_rates.CJ_CNT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_pk_parse_G0.PKP_C24 + 1)%Z _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_x509_get_time_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2;.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_hash_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2<.R4.R3.(1<.R4.R3.R2.)(7.R4.R2.)(26.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_policies_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2=.R4.R3.(6.R4.R2.)(7.R4.R2.)(=.R4.R2.)(19.R4.R2.)(1:.R4.R2.)(1;.R4.R2.)(9.R4.R2.)(:.R4.R3.R2.R1.)(1<.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_x509_rsassa_pss_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_x509 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2>.R4.R3.(1<.R4.R3.R2.)(7.R4.R2.)(26.R4.R2.)(8.R4.R2.)(15.R4.R2.)(23.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_x509_san_ext_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_x509_san_ext_M.A_x509_san_ext_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_calloc R LO) (A_link_layout.aho_nodup R HIA HO) _ _ _ _ _ (A_x509_parse_san_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_free_named_data_list_shallow_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_sequence_free_spec_cl R HIA LO HO) _ _ _ _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).
