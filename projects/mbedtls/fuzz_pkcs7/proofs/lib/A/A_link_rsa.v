(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_link_layout A_link_base A_link_budgets.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_link_asn1 A_link_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_rsa_check_context A_rsa_check_pubkey A_rsa_complete A_rsa_free A_rsa_init A_rsa_parse_pubkey_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_rsa () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.A.A_link_layout.a_layout_ok"; "OSSVerify.KrLib.A.A_link_layout.a_hia_ok"; "OSSVerify.KrLib.A.A_rsa_check_context.A_rsa_check_context_spec"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.A.A_link_layout.alo_img"; "OSSVerify.KrLib.A.A_rsa_check_pubkey.A_rsa_check_pubkey_spec"; "OSSVerify.KrLib.A.A_rsa_complete.A_rsa_complete_spec"; "OSSVerify.KrLib.A.A_rsa_free.A_rsa_free_spec"; "OSSVerify.KrLib.A.A_link_mpi.A_mpi_free_spec_closed_cl"; "OSSVerify.KrLib.A.A_link_base.alo_need_rt"; "OSSVerify.KrLib.A.A_link_layout.alo_dimg"; "OSSVerify.KrLib.A.A_link_layout.aho_nodup"; "OSSVerify.KrLib.A.A_rsa_init.A_rsa_init_spec"; "OSSVerify.KrLib.A.A_link_layout.alo_amemset"; "OSSVerify.KrLib.A.A_link_layout.alo_need_amem"; "OSSVerify.KrLib.A.A_rsa_parse_pubkey_c24.A_rsa_parse_pubkey_spec_c"; "OSSVerify.KrLib.A.A_link_layout.alo_uar_got"; "OSSVerify.KrLib.A.A_link_layout.alo_smalloc1"; "OSSVerify.KrLib.A.A_link_layout.alo_need_smalloc"; "OSSVerify.KrLib.A.A_link_asn1.A_asn1_get_tag_spec_cl"; "OSSVerify.KrLib.A.A_link_mpi.A_mpi_size_spec_cl"; "A_rsa_complete_spec_cl"; "A_rsa_check_pubkey_spec_cl"; "OSSVerify.KrLib.A.A_link_mpi.A_mpi_read_binary_spec_r_c_cl"].


Definition A_rsa_check_context_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_check_pubkey_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(8.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_complete_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(9.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.R4.R3.(7.R4.R2.)(;.R4.R3.R2.R1.)(<.R4.R2.)(=.R4.R2.)(>.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_rsa_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(?.R4.R3.(7.R4.R2.)(10.R4.R2.)(11.R4.R2.))")
(* [comment removed for export] *).

Definition A_rsa_parse_pubkey_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_rsa ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(12.R4.R3.(7.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R2.)(<.R4.R2.)(16.R4.R3.R2.R1.)(17.R4.R3.R2.R1.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(1:.R4.R3.R2.R1.))")
(* [comment removed for export] *).
