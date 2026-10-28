(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_misc A_link_mpicore A_link_mpi.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_ecp_check_pubkey_c24 A_ecp_defs A_ecp_group_free A_ecp_group_init A_ecp_group_load_mx A_ecp_grp_id_list A_ecp_keypair_free A_ecp_keypair_init A_ecp_mod_p192 A_ecp_mod_p192k1 A_ecp_mod_p224 A_ecp_mod_p224k1 A_ecp_mod_p255 A_ecp_mod_p256 A_ecp_mod_p256k1 A_ecp_mod_p384 A_ecp_mod_p448 A_ecp_mod_p521 A_ecp_modp_table A_ecp_mul_mod A_ecp_point_free A_ecp_point_read_binary_c24 A_ecp_sw_derive_y A_ecp_sw_rhs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_ecp () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_modp_table.A_modp_table_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc1"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc2"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_base.alo_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_grow_sz_spec_closed_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpicore.A_mpi_core_mul_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.aho_amemmove"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_rtc"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_primg"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_dimg"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_roimg"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.aho_nodup"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mul_mod.A_ecp_mul_mod_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_defs.A_MT"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.mpi_mul_mpi_stmtA_sz_of_A_MPI_MUL_MPI_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_mod_mpi_sz_spec_cl"; "A_modp_table_ok_cl"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_sw_rhs.A_ecp_sw_rhs_spec"; "A_ecp_mul_mod_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_add_mpi_sz_spec_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_add_mpi_ng_sz_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_sub_abs_ng_sz_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_sub_int_sz_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_check_pubkey_c24.A_ecp_check_pubkey_spec_c"; "A_ecp_sw_rhs_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_copy_spec_closed_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_sub_mpi_ng_sz_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_add_int_sz_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_free_spec_closed_cl"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_free.A_ecp_group_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_misc.A_platform_zeroize_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_init.A_ecp_group_init_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load_mx.A_ecp_group_load_spec_closed"; "A_ecp_group_free_spec_cl"; "A_ecp_group_init_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_lset_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load_mx.mx_case13"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_group_load_mx.mx_case9"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_grp_id_list.A_ecp_grp_id_list_spec"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_keypair_free.A_ecp_keypair_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_keypair_init.A_ecp_keypair_init_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p192.A_ecp_mod_p192_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p192k1.A_ecp_mod_p192k1_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p224.A_ecp_mod_p224_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p224k1.A_ecp_mod_p224k1_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p255.A_ecp_mod_p255_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p256.A_ecp_mod_p256_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p256k1.A_ecp_mod_p256k1_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p384.A_ecp_mod_p384_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p448.A_ecp_mod_p448_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_mod_p521.A_ecp_mod_p521_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_point_free.A_ecp_point_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_sw_derive_y.A_ecp_sw_derive_y_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc0"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_shift_r_spec_closed_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_exp_mod_spec_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_sub_mpi_sz_spec_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_point_read_binary_c24.A_ecp_point_read_binary_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_read_binary_spec_r_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpi.A_mpi_read_binary_le_spec_r_c_cl"; "A_ecp_sw_derive_y_spec_cl"].


Definition A_modp_table_ok_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(>.R4.R2.)(?.R4.R3.R2.R1.)(10.R4.R3.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mul_mod_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(16.R4.R3.$17.(6.R4.R2.)(7.R4.R2.)(43.R4.R2.)(:.R4.R2.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(1:.R4.R3.R2.R1.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_sw_rhs_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1;.R4.R3.$17.(6.R4.R2.)(1<.R4.R3.R2.R1.)(1=.R4.R3.R2.R1.)(1>.R4.R3.R2.R1.)(1?.R4.R3.R2.R1.)(20.R4.R3.R2.R1.)(7.R4.R2.)(43.R4.R2.)(:.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_check_pubkey_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(21.R4.R3.$17.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(:.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.)(11.R4.R2.)(1<.R4.R3.R2.R1.)(22.R4.R3.R2.R1.)(23.R4.R3.R2.R1.)(24.R4.R3.R2.R1.)(25.R4.R3.R2.R1.)(26.R4.R3.R2.R1.)(43.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_group_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(27.$28.)(29.R5.R4.R1.(6.R5.R3.)(26.R5.R4.R3.R2.)(2:.R5.R4.R3.R2.)(;.R5.R3.)(2;.R5.R3.)(13.R5.R3.)(15.R5.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_group_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(27.$28.)(2<.R5.R4.R1.(6.R5.R3.)(=.R5.R3.)(2;.R5.R3.))")
(* [comment removed for export] *).

Definition A_ecp_group_load_spec_closed_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2=.R4.R3.(6.R4.R2.)(;.R4.R2.)(2;.R4.R2.)(13.R4.R2.)(15.R4.R3.R1.)(2>.R4.R3.R2.R1.$17.)(2?.R4.R3.R2.R1.$17.)(30.R4.R3.R2.R1.)(26.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition mx_case13_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(31.R4.R3.(6.R4.R2.)(;.R4.R2.)(13.R4.R2.)(15.R4.R3.R1.)(2>.R4.R3.R2.R1.$17.)(30.R4.R3.R2.R1.)(26.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition mx_case9_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(32.R4.R3.(6.R4.R2.)(;.R4.R2.)(13.R4.R2.)(15.R4.R3.R1.)(2>.R4.R3.R2.R1.$17.)(30.R4.R3.R2.R1.)(26.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_ecp_grp_id_list_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(33.(34.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_keypair_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(27.$28.)(35.R5.R4.R1.(6.R5.R3.)(26.R5.R4.R3.R2.)(2>.R5.R4.R3.R2.R1.)(;.R5.R3.)(13.R5.R3.)(15.R5.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_keypair_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)LMT,(27.$28.)(36.R5.R4.R1.(6.R5.R3.)(=.R5.R3.)(2;.R5.R3.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p192_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(37.R4.R3.(6.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p192k1_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(38.R4.R3.(6.R4.R2.)(7.R4.R2.)(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(>.R4.R2.)(?.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p224_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(39.R4.R3.(6.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p224k1_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3:.R4.R3.(6.R4.R2.)(7.R4.R2.)(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(>.R4.R2.)(?.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p255_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3;.R4.R3.(6.R4.R2.)(7.R4.R2.)(8.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(13.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p256_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3<.R4.R3.(6.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p256k1_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3=.R4.R3.(6.R4.R2.)(7.R4.R2.)(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(>.R4.R2.)(?.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p384_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3>.R4.R3.(6.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p448_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3?.R4.R3.(6.R4.R2.)(7.R4.R2.)(9.R4.R2.)(:.R4.R2.)(;.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(>.R4.R2.)(10.R4.R3.R1.)(13.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_mod_p521_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(40.R4.R3.(6.R4.R2.)(<.R4.R3.R2.R1.)(=.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).

Definition A_ecp_point_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(41.R4.R3.(6.R4.R2.)(26.R4.R3.R2.R1.)(;.R4.R2.)(13.R4.R2.)(15.R4.R3.R1.))")
(* [comment removed for export] *).

Definition A_ecp_sw_derive_y_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(42.R4.R3.$17.(6.R4.R2.)(7.R4.R2.)(43.R4.R2.)(:.R4.R2.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.)(22.R4.R3.R2.R1.)(25.R4.R3.R2.R1.)(44.R4.R3.R2.R1.)(45.R4.R3.R2.R1.)(46.R4.R3.R2.R1.)(26.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_ecp_point_read_binary_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_ecp ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(47.R4.R3.$17.(6.R4.R2.)(30.R4.R3.R2.R1.)(48.R4.R3.R2.R1.)(49.R4.R3.R2.R1.)(26.R4.R3.R2.R1.)(4:.R4.R3.R2.R1.)(;.R4.R2.)(15.R4.R3.R1.)(13.R4.R2.)(14.R4.R2.))")
(* [comment removed for export] *).
