(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_asn1 A_link_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_rsa_check_context A_rsa_check_pubkey A_rsa_complete A_rsa_free A_rsa_init A_rsa_parse_pubkey_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_rsa () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_check_context.A_rsa_check_context_spec"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_check_pubkey.A_rsa_check_pubkey_spec"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_complete.A_rsa_complete_spec"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_free.A_rsa_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_free_spec_closed_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_base.alo_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_dimg"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.aho_nodup"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_init.A_rsa_init_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_rsa_parse_pubkey_c24.A_rsa_parse_pubkey_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc1"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_asn1.A_asn1_get_tag_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_size_spec_cl"; "A_rsa_complete_spec_cl"; "A_rsa_check_pubkey_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_read_binary_spec_r_c_cl"].


Definition A_rsa_check_context_spec_cl := fun R HIA (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_rsa_check_context.A_rsa_check_context_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO)
(* [comment removed for export] *).

Definition A_rsa_check_pubkey_spec_cl := fun R HIA (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_rsa_check_pubkey.A_rsa_check_pubkey_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO)
(* [comment removed for export] *).

Definition A_rsa_complete_spec_cl := fun R HIA (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_rsa_complete.A_rsa_complete_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO)
(* [comment removed for export] *).

Definition A_rsa_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.R4.R3.(7.R4.R2.)(;.R4.R3.R2.R1.)(<.R4.R2.)(=.R4.R2.)(>.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_rsa_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(?.R4.R3.(7.R4.R2.)(10.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_parse_pubkey_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(12.R4.R3.(7.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R2.)(<.R4.R2.)(16.R4.R3.R2.R1.)(17.R4.R3.R2.R1.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(1:.R4.R3.R2.R1.))")
(* [comment removed for export] *).
