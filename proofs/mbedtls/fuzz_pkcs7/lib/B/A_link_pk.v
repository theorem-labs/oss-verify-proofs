(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_misc A_link_asn1 A_link_oid A_link_mpi A_link_rsa A_link_ecp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_ecp_defs A_pk_ecc_set_group A_pk_ecc_set_pubkey A_pk_ecparams_E A_pk_ecparams_aux A_pk_free A_pk_parse_H A_pk_setup A_pk_wrap_alloc A_pk_wrap_free BX_pk_use_ecparams_rfc8410 BX_pk_get_pk_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_pk () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_group.A_pk_ecc_set_group_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_CA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_ONE"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc1"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_base.alo_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_rtc"; "RocqVerifyHarness.AgentSubmission.B.A_link_ecp.A_ecp_group_load_spec_closed_cl"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecc_set_pubkey.A_pk_ecc_set_pubkey_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.aho_nodup"; "RocqVerifyHarness.AgentSubmission.B.A_link_ecp.A_ecp_point_read_binary_spec_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_ecp.A_ecp_check_pubkey_spec_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_pk_ecparams_aux.A_ecp_point_read_unset"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_pk_wrap_free.A_rsa_free_wrap_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_free"; "RocqVerifyHarness.AgentSubmission.B.A_link_rsa.A_rsa_free_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_free"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_dimg"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.A_pk_wrap_free.A_eckey_free_wrap_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_ecp.A_ecp_keypair_free_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_pk_free.A_pk_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_misc.A_platform_zeroize_spec_cl"; "A_rsa_free_wrap_spec_cl"; "A_eckey_free_wrap_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_pk_setup.A_pk_setup_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_malloc"; "RocqVerifyHarness.AgentSubmission.B.A_pk_wrap_alloc.A_eckey_alloc_wrap_spec"; "RocqVerifyHarness.AgentSubmission.B.A_pk_wrap_alloc.A_rsa_alloc_wrap_spec"].


Definition A_pk_ecc_set_group_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.$6.$7.$8.(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_pk_ecc_set_pubkey_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(10.R4.R3.$6.(9.R4.R2.)(=.R4.R2.)(<.R4.R2.)(>.R4.R2.)(11.R4.R3.R1.)(12.R4.R3.R2.R1.)(13.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition pk_use_ecparams_spec_cl :=
  fun (R : LibB.ARt.art_layout) (HIA : LibB.ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pk_ecparams_E.pk_use_ecparams_spec R HIA _ _ (A_link_layout.alo_img R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc4 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_setf5 R LO) (A_link_layout.alo_nsh R LO) (A_link_layout.alo_memcmp_i R LO) _ (A_pk_ecc_set_group_spec_cl R HIA LO HO) (A_link_mpi.A_mpi_free_spec_closed_cl R HIA LO HO) (A_link_ecp.A_ecp_point_free_spec_cl R HIA LO HO) (A_link_ecp.A_ecp_group_free_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_ecp.A_ecp_group_load_spec_closed_cl R HIA LO HO) (A_link_ecp.A_ecp_group_init_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_ecp.A_ecp_grp_id_list_spec_cl R HIA LO HO) (A_link_mpi.A_mpi_read_binary_spec_closed_c_cl R HIA LO HO) (A_link_asn1.A_asn1_get_mpi_spec_c_cl R HIA LO HO) (A_link_mpi.A_mpi_lset_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_oid.A_oid_get_ec_grp_v_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_int_spec_cl R HIA LO HO)); try solve [A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_ecp_point_read_unset_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(14.(15.R4.)(9.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_free_wrap_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(16.R4.R3.(9.R4.R2.)(17.R4.R2.)(18.R4.R3.R2.R1.)(=.R4.R2.)(19.R4.R2.)(1:.R4.R2.)(11.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_eckey_free_wrap_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(1;.$1<.)(1=.R5.R4.R1.(9.R5.R3.)(17.R5.R3.)(1>.R5.R4.R3.R2.R1.)(=.R5.R3.)(19.R5.R3.)(1:.R5.R3.)(11.R5.R4.R2.))")
(* [comment removed for export] *).

Definition A_pk_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(1;.$1<.)(1?.R5.R4.R1.(9.R5.R3.)(>.R5.R3.)(20.R5.R4.R3.R2.)(21.R5.R4.R3.R2.)(22.R5.R4.R3.R2.R1.)(=.R5.R3.)(23.R5.R3.)(1:.R5.R3.)(11.R5.R4.R2.))")
(* [comment removed for export] *).

Definition A_pk_setup_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(1;.$1<.)(24.R5.R4.R1.(9.R5.R3.)(>.R5.R3.)(25.R5.R3.)(26.R5.R3.)(27.R5.R3.)(23.R5.R3.))")
(* [comment removed for export] *).

Definition A_pk_use_ecparams_rfc8410_spec_cl :=
  fun (R : LibB.ARt.art_layout) (HIA : LibB.ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  BX_pk_use_ecparams_rfc8410.A_pk_use_ecparams_rfc8410_spec R HIA A_ecp_defs.A_MT A_ecp_defs.A_CA A_ecp_defs.A_ONE
    (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc1 R LO)
    (A_link_layout.alo_need_smalloc R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.alo_rtc R LO)
    (A_link_ecp.A_ecp_group_load_spec_closed_cl R HIA LO HO).

Definition A_pk_get_pk_alg_spec_cl :=
  fun (R : LibB.ARt.art_layout) (HIA : LibB.ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  BX_pk_get_pk_alg.A_pk_get_pk_alg_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc1 R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_memset_i R LO)
    (A_link_layout.alo_rtc R LO) (A_link_layout.alo_need_amem R LO) (A_link_base.alo_oid_rt R HIA LO).

Definition A_pk_parse_subpubkey_spec_cl :=
  fun (R : LibB.ARt.art_layout) (HIA : LibB.ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_pk_parse_H.A_pk_parse_subpubkey_spec R HIA A_ecp_defs.A_MT (A_link_layout.alo_ids_lok R LO) (A_link_layout.alo_mc_lok R LO) (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_need_amem R LO) (A_link_layout.alo_need_bcmp R LO) (A_link_layout.alo_need_malloc R LO) _ (A_link_layout.alo_dimg R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.aho_hmperm R HIA HO) (A_link_asn1.A_asn1_get_tag_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_alg_spec_cl R HIA LO HO) (A_link_oid.A_oid_get_pk_alg_spec_cl R HIA LO HO) (A_link_oid.A_oid_get_ec_grp_algid_spec_cl R HIA LO HO) (A_link_asn1.A_asn1_get_bitstring_null_spec_cl R HIA LO HO) (A_pk_setup_spec_cl R HIA LO HO A_ecp_defs.A_MT) (A_link_rsa.A_rsa_parse_pubkey_spec_c_cl R HIA LO HO) (pk_use_ecparams_spec_cl R HIA LO HO) (A_pk_use_ecparams_rfc8410_spec_cl R HIA LO HO) (A_pk_get_pk_alg_spec_cl R HIA LO HO) (A_pk_ecc_set_pubkey_spec_cl R HIA LO HO) (A_pk_free_spec_cl R HIA LO HO A_ecp_defs.A_MT)); try solve [A_link_base.alink_side LO HO]; A_link_base.alink_open).

Definition A_eckey_alloc_wrap_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(1;.$1<.)(28.R5.R4.R1.(9.R5.R3.)(25.R5.R3.)(26.R5.R3.)(27.R5.R3.)(23.R5.R3.))")
(* [comment removed for export] *).

Definition A_rsa_alloc_wrap_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_pk ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(29.R4.R3.(9.R4.R2.)(25.R4.R2.)(26.R4.R2.)(27.R4.R2.)(23.R4.R2.))")
(* [comment removed for export] *).
