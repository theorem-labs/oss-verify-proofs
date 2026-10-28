(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_oid_ec_grp A_oid_ec_grp_algid A_oid_md_alg A_oid_pk_alg A_oid_sig_alg A_oid_x509_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_oid () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_oid_ec_grp.A_oid_get_ec_grp_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_base.alo_oid_rt"; "RocqVerifyHarness.AgentSubmission.B.A_oid_ec_grp.A_oid_get_ec_grp_v_spec"; "RocqVerifyHarness.AgentSubmission.B.A_oid_ec_grp_algid.A_oid_get_ec_grp_algid_spec"; "RocqVerifyHarness.AgentSubmission.B.A_oid_md_alg.A_oid_get_md_alg_spec"; "RocqVerifyHarness.AgentSubmission.B.A_oid_pk_alg.A_oid_get_pk_alg_spec"; "RocqVerifyHarness.AgentSubmission.B.A_oid_sig_alg.A_oid_get_sig_alg_spec"; "RocqVerifyHarness.AgentSubmission.B.A_oid_x509_ext.A_oid_get_x509_ext_type_spec"].


Definition A_oid_get_ec_grp_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_ec_grp_v_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(7.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_ec_grp_algid_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(8.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_md_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(9.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_pk_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_sig_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(;.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).

Definition A_oid_get_x509_ext_type_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_oid ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(<.R4.R3.(6.R4.R3.R2.))")
(* [comment removed for export] *).
