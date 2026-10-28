(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets A_link_adapt A_link_rates.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_pkcs7.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_fuzz_entry24 A_link_adapt A_x509_crt_parse_A.

Definition fuzz_entryA24_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  ltac:(refine (@A_fuzz_entry24.fuzz_entryA24 R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc5 R LO) (A_link_layout.alo_sfree5 R LO) (A_link_layout.alo_set00 R LO) (A_link_layout.alo_setf8 R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_layout.alo_need_setsh R LO) (A_link_layout.alo_need_amem R LO) _ _ _ _ _ _ _ _ _ _ _ (A_link_pkcs7.A_pkcs7_parse_der_spec24_cl R HIA LO HO) (A_link_pkcs7.A_pkcs7_free_walk24_cl R HIA LO HO) _ _ _ _ (A_link_budgets.FSTKc R (A_x509_crt_parse_A.STKx R (A_link_adapt.STKcrt R))) _ _ _ _ _); try solve [A_link_adapt.alink_fstk | A_link_rates.alink_rates | A_link_base.alink_side LO HO]; A_link_base.alink_open).
