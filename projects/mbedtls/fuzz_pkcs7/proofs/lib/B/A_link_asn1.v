(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_asn1_empty A_asn1_free_named_data_list_shallow A_asn1_get_alg A_asn1_get_alg_null A_asn1_get_bitstring A_asn1_get_bitstring_null A_asn1_get_bool A_asn1_get_int A_asn1_get_len A_asn1_get_mpi_c24 A_asn1_get_seq_of A_asn1_get_tag A_asn1_seq_cb A_asn1_sequence_free A_asn1_trav.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_asn1 () : Init.string Init.list := ["OSSVerify.KrLib.LibB.ARt.art_layout"; "OSSVerify.KrLib.LibB.ARt.artA"; "OSSVerify.KrLib.B.AImg.asegs"; "OSSVerify.KrLib.B.A_link_layout.a_layout_ok"; "OSSVerify.KrLib.B.A_link_layout.a_hia_ok"; "OSSVerify.KrLib.B.A_asn1_empty.A_asn1_get_int_empty"; "OSSVerify.KrLib.LibB.ARt.arl_AL"; "OSSVerify.KrLib.B.A_link_layout.alo_img"; "OSSVerify.KrLib.B.A_asn1_empty.A_asn1_get_tag_empty"; "OSSVerify.KrLib.B.A_asn1_free_named_data_list_shallow.A_asn1_free_named_data_list_shallow_spec"; "OSSVerify.KrLib.B.A_link_layout.alo_free"; "OSSVerify.KrLib.B.A_link_layout.alo_need_free"; "OSSVerify.KrLib.B.A_asn1_get_alg.A_asn1_get_alg_spec"; "OSSVerify.KrLib.B.A_link_layout.alo_memset_i"; "OSSVerify.KrLib.B.A_link_layout.alo_rtc"; "OSSVerify.KrLib.B.A_link_layout.alo_need_amem"; "OSSVerify.KrLib.B.A_asn1_get_alg_null.A_asn1_get_alg_null_spec"; "OSSVerify.KrLib.B.A_link_layout.alo_uar_got"; "OSSVerify.KrLib.B.A_link_layout.alo_smalloc1"; "OSSVerify.KrLib.B.A_link_layout.alo_amemset"; "OSSVerify.KrLib.B.A_asn1_get_bitstring.A_asn1_get_bitstring_spec"; "OSSVerify.KrLib.LibB.ARt.arl_L"; "OSSVerify.KrLib.B.A_asn1_get_bitstring_null.A_asn1_get_bitstring_null_spec"; "OSSVerify.KrLib.B.A_asn1_get_bool.A_asn1_get_bool_spec"; "OSSVerify.KrLib.B.A_asn1_get_int.A_asn1_get_int_spec"; "OSSVerify.KrLib.B.A_asn1_get_len.A_asn1_get_len_spec"; "OSSVerify.KrLib.B.A_asn1_get_mpi_c24.A_asn1_get_mpi_spec_c"; "OSSVerify.KrLib.B.A_link_base.alo_need_rt"; "OSSVerify.KrLib.B.A_asn1_seq_cb.A_asn1_seq_cb_spec"; "OSSVerify.KrLib.B.A_link_layout.alo_calloc"; "OSSVerify.KrLib.B.A_link_layout.alo_need_malloc"; "OSSVerify.KrLib.B.A_link_layout.alo_ceil"; "OSSVerify.KrLib.B.A_asn1_trav.A_asn1_trav_spec"; "A_asn1_seq_cb_spec_cl"; "OSSVerify.KrLib.B.A_asn1_get_seq_of.A_asn1_get_seq_of_spec"; "OSSVerify.KrLib.B.A_link_layout.alo_smalloc0"; "OSSVerify.KrLib.B.A_link_layout.alo_need_smalloc"; "A_asn1_trav_spec_cl"; "OSSVerify.KrLib.B.A_asn1_get_seq_of.A_asn1_get_seq_of_specE"; "OSSVerify.KrLib.B.A_asn1_get_tag.A_asn1_get_tag_spec"; "OSSVerify.KrLib.B.A_asn1_sequence_free.A_asn1_sequence_free_spec"].


Definition A_asn1_get_int_empty_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_tag_empty_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(8.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_free_named_data_list_shallow_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(9.R4.R3.(7.R4.R2.)(:.R4.R2.)(;.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_alg_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(<.R4.R3.(7.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_alg_null_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(10.R4.R3.(7.R4.R2.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_bitstring_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(14.(15.R4.)(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_bitstring_null_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(16.(15.R4.)(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_bool_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(17.(15.R4.)(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_int_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(18.(15.R4.)(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_len_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(19.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_get_mpi_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1:.R4.R3.(7.R4.R2.)(1;.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_seq_cb_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1<.R4.R3.(7.R4.R2.)(1=.R4.R2.)(1>.R4.R2.)(1?.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_trav_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(20.R4.R3.(7.R4.R2.)(1>.R4.R2.)(21.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_asn1_get_seq_of_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(22.R4.R3.(7.R4.R2.)(11.R4.R2.)(23.R4.R2.)(13.R4.R2.)(24.R4.R2.)(?.R4.R2.)(1>.R4.R2.)(25.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_asn1_get_seq_of_specE_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(26.R4.R3.(7.R4.R2.)(11.R4.R2.)(23.R4.R2.)(13.R4.R2.)(24.R4.R2.)(?.R4.R2.)(1>.R4.R2.)(25.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_asn1_get_tag_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(27.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_asn1_sequence_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_asn1 ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(28.R4.R3.(7.R4.R2.)(:.R4.R2.)(;.R4.R2.))")
(* [comment removed for export] *).
