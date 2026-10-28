(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_platform_zeroize.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_misc () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_platform_zeroize_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_rtc"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"].


Definition A_platform_zeroize_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_misc ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(9.R4.R2.))")
(* [comment removed for export] *).
