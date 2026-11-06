(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_link_layout A_link_base A_link_budgets.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_oid_ec_grp A_oid_ec_grp_algid A_oid_md_alg A_oid_pk_alg A_oid_sig_alg A_oid_x509_ext.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_oid () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.A_link_layout.a_layout_ok"; "OSSVerify.KrLib.A.A_link_layout.a_hia_ok"; "OSSVerify.KrLib.A.A_oid_ec_grp.A_oid_get_ec_grp_spec"; "OSSVerify.KrLib.A.A_link_base.alo_oid_rt"; "OSSVerify.KrLib.A.A_oid_ec_grp.A_oid_get_ec_grp_v_spec"; "OSSVerify.KrLib.A.A_oid_ec_grp_algid.A_oid_get_ec_grp_algid_spec"; "OSSVerify.KrLib.A.A_oid_md_alg.A_oid_get_md_alg_spec"; "OSSVerify.KrLib.A.A_oid_pk_alg.A_oid_get_pk_alg_spec"; "OSSVerify.KrLib.A.A_oid_sig_alg.A_oid_get_sig_alg_spec"; "OSSVerify.KrLib.A.A_oid_x509_ext.A_oid_get_x509_ext_type_spec"].


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
