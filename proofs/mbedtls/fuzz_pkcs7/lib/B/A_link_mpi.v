(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_misc A_link_mpicore.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require BX_mpi_cmp_abs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_asn1_get_mpi A_ct_memcpy_if A_mpi_add_abs_c24 A_mpi_add_abs_sz_c24 A_mpi_add_int_sz_c24 A_mpi_add_sub_ng A_mpi_add_sub_ng_sz A_mpi_add_sub_o_c24 A_mpi_add_sub_sz_c24 A_mpi_addsub_sz_glue A_mpi_addsub_sz_glue_c24 A_mpi_bitlen A_mpi_cmp_int A_mpi_cmp_int_z0 A_mpi_cmp_mpi A_mpi_cmp_mpi_raw A_mpi_copy_c24 A_mpi_div_mpi_c24 A_mpi_exp_mod_c24 A_mpi_free A_mpi_get_mont_r2_c24 A_mpi_grow_c24 A_mpi_grow_sz_c24 A_mpi_init A_mpi_lset A_mpi_lset_ng A_mpi_mod_mpi_sz A_mpi_mul_int_c24 A_mpi_mul_int_ng A_mpi_mul_int_ng_c24 A_mpi_mul_int_v_c24 A_mpi_mul_mpi_c24 A_mpi_mul_mpi_sz A_mpi_read_binary_c24 A_mpi_read_binary_le_c24 A_mpi_resize_clear_c24 A_mpi_set_bit A_mpi_shift_l_c24 A_mpi_shift_r A_mpi_shrink_c24 A_mpi_stmtA A_mpi_sub_abs_c24 A_mpi_sub_abs_ng A_mpi_sub_abs_ng_sz A_mpi_sub_abs_sz_c24 A_mpi_sub_int_sz_c24 A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_mpi () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_asn1_get_mpi.A_asn1_get_mpi_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_link_base.alo_need_rt"; "RocqVerifyHarness.AgentSubmission.B.A_ct_memcpy_if.A_ct_memcpy_if_spec"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.A_zeroize_and_free_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_free"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_rtc"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_free"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.A_mpi_copy_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.aho_nodup"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_dimg"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img_w"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_c24.A_mpi_add_abs_spec_c"; "A_zeroize_and_free_spec_cl"; "A_mpi_copy_spec_closed_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_roimg"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_c24.A_mpi_add_abs_spec_o_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_sz_c24.A_mpi_add_abs_spec_oz_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_abs_sz_c24.A_mpi_add_abs_spec_z_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_sz_c24.A_mpi_sub_abs_spec_oz_c"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_sz_c24.A_add_sub_mpi_spec_oz_c"; "A_mpi_add_abs_spec_oz_c_cl"; "A_mpi_sub_abs_spec_oz_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_ng.A_mpi_sub_abs_ng_spec_o"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_ng.A_add_sub_mpi_ng_spec_o"; "A_mpi_sub_abs_ng_spec_o_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_ng_sz.A_mpi_sub_abs_ng_spec_oz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_ng_sz.A_add_sub_mpi_ng_spec_oz"; "A_mpi_sub_abs_ng_spec_oz_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_addsub_sz_glue.A_mpi_add_int_sz_spec"; "A_mpi_add_int_spec_sz_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_addsub_sz_glue.A_mpi_sub_int_sz_spec"; "A_mpi_sub_int_spec_sz_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.A_mpi_bitlen_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.A_mpi_get_bit_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_bitlen.A_mpi_size_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.A_mpi_cmp_int_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int_z0.A_mpi_cmp_int_z0_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.A_mpi_cmp_mpi_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi_raw.A_mpi_cmp_mpi_raw_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.A_mpi_copy_spec_x_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow_c24.A_mpi_grow_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_l_c24.A_mpi_shift_l_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset_ng.A_mpi_lset_ng_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int_ng.A_mpi_mul_int_ng_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int_v_c24.A_mpi_mul_int_vspec_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.A_mpi_lset_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shrink_c24.A_mpi_shrink_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2_c24.A_mpi_get_mont_r2_spec_c"; "A_mpi_lset_spec_cl"; "A_mpi_shift_l_spec_closed_c_cl"; "A_mpi_mod_mpi_spec_cl"; "A_mpi_shrink_spec_closed_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.A_mpi_free_spec_closed"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow_sz_c24.A_mpi_grow_sz_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_init.A_mpi_init_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int_c24.A_mpi_mul_int_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_int_ng_c24.A_mpi_mul_int_ng_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_mpi_c24.A_mpi_mul_mpi_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc1"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpicore.A_mpi_core_mul_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_c24.A_mpi_read_binary_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear_c24.A_mpi_resize_clear_core_r_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_c24.A_mpi_read_binary_spec_r_c"; "A_mpi_resize_clear_core_r_c_cl"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpicore.A_mpi_core_read_be_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_le_c24.A_mpi_read_binary_le_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_le_c24.A_mpi_read_binary_le_spec_r_c"; "RocqVerifyHarness.AgentSubmission.B.A_link_mpicore.A_mpi_core_read_le_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear_c24.A_mpi_resize_clear_core_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_resize_clear_c24.A_mpi_resize_clear_spec_closed_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_set_bit.A_mpi_set_bit0_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_r.A_mpi_shift_r_spec_closed"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_c24.A_mpi_sub_abs_spec_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_c24.A_mpi_sub_abs_spec_o_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_ng.A_mpi_sub_abs_ng_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_ng_sz.A_mpi_sub_abs_ng_sz_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_sub_abs_sz_c24.A_mpi_sub_abs_spec_z_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_mul_mpi_sz.mpi_mul_mpi_stmtA_sz_of"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_MUL_MPI"; "A_mpi_mul_mpi_spec_c_cl"].


Definition A_asn1_get_mpi_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.R4.R3.(6.R4.R2.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_ct_memcpy_if_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(8.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_zeroize_and_free_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_copy_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(10.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(16.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_add_abs_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(17.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_add_abs_spec_o_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1;.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_add_abs_spec_oz_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1<.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_add_abs_spec_z_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1=.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(19.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_spec_oz_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1>.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_add_sub_mpi_spec_oz_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) (flip : Z) (H1 : flip = 1%Z \/ flip = (-1)%Z) =>
  A_mpi_add_sub_sz_c24.A_add_sub_mpi_spec_oz_c flip H1 R HIA (A_link_layout.alo_img R LO) (A_mpi_add_abs_spec_oz_c_cl R HIA LO HO) (A_mpi_sub_abs_spec_oz_c_cl R HIA LO HO) (BX_mpi_cmp_abs.BX_mpi_cmp_abs_raw_spec (ARt.arl_AL R) (A_link_layout.alo_img R LO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_add_int_spec_sz_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_add_int_sz_c24.A_mpi_add_int_spec_sz_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc1 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_base.alo_need_rt R LO) (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)) (A_link_layout.alo_roimg R LO).

Definition A_mpi_sub_abs_ng_spec_o_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(25.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_add_sub_mpi_ng_spec_o_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) (flip : Z) (H1 : flip = 1%Z \/ flip = (-1)%Z) =>
  A_mpi_add_sub_ng.A_add_sub_mpi_ng_spec_o flip H1 R HIA (A_link_layout.alo_img R LO) (A_mpi_sub_abs_ng_spec_o_cl R HIA LO HO) (BX_mpi_cmp_abs.BX_mpi_cmp_abs_raw_spec (ARt.arl_AL R) (A_link_layout.alo_img R LO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_add_mpi_ng_spec_o_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_add_sub_ng.A_mpi_add_mpi_ng_spec_o R HIA (A_add_sub_mpi_ng_spec_o_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_sub_mpi_ng_spec_o_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_add_sub_ng.A_mpi_sub_mpi_ng_spec_o R HIA (A_add_sub_mpi_ng_spec_o_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_sub_abs_ng_spec_oz_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(28.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_add_sub_mpi_ng_spec_oz_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) (flip : Z) (H1 : flip = 1%Z \/ flip = (-1)%Z) =>
  A_mpi_add_sub_ng_sz.A_add_sub_mpi_ng_spec_oz flip H1 R HIA (A_link_layout.alo_img R LO) (A_mpi_sub_abs_ng_spec_oz_cl R HIA LO HO) (BX_mpi_cmp_abs.BX_mpi_cmp_abs_raw_spec (ARt.arl_AL R) (A_link_layout.alo_img R LO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_add_mpi_ng_sz_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_add_sub_ng_sz.A_mpi_add_mpi_ng_sz_spec R HIA (A_link_base.alo_need_rt R LO) (A_add_sub_mpi_ng_spec_oz_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_sub_mpi_ng_sz_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_add_sub_ng_sz.A_mpi_sub_mpi_ng_sz_spec R HIA (A_link_base.alo_need_rt R LO) (A_add_sub_mpi_ng_spec_oz_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)).

Definition A_add_sub_mpi_spec_o_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) (flip : Z) (H1 : flip = 1%Z \/ flip = (-1)%Z) =>
  @A_mpi_add_sub_o_c24.A_add_sub_mpi_spec_o_c flip H1 R HIA (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO flip ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_add_int_sz_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2;.R4.R3.(2<.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_mpi_sub_int_spec_sz_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_sub_int_sz_c24.A_mpi_sub_int_spec_sz_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc1 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_base.alo_need_rt R LO) (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)) (A_link_layout.alo_roimg R LO).

Definition A_mpi_sub_int_sz_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2=.R4.R3.(2>.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_add_sub_mpi_spec_osz_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) (flip : Z) (H1 : flip = 1%Z \/ flip = (-1)%Z) =>
  @A_mpi_addsub_sz_glue_c24.A_add_sub_mpi_spec_osz_c flip H1 R HIA (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO flip ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_add_mpi_sz_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_addsub_sz_glue_c24.A_mpi_add_mpi_sz_spec_c R HIA (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_sub_mpi_sz_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_addsub_sz_glue_c24.A_mpi_sub_mpi_sz_spec_c R HIA (A_add_sub_mpi_spec_oz_c_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_bitlen_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(2?.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_get_bit_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(30.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_size_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(31.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_cmp_int_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_cmp_int.A_mpi_cmp_int_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO)
(* [comment removed for export] *).

Definition A_mpi_cmp_int_z0_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_cmp_int_z0.A_mpi_cmp_int_z0_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO)
    (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO)
(* [comment removed for export] *).

Definition A_mpi_cmp_mpi_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(34.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_cmp_mpi_raw_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(35.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_copy_spec_x_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(36.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(16.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_grow_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(37.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(12.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_shift_l_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(38.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_lset_ng_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(39.R4.R3.(6.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_mul_int_ng_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_mul_int_ng.A_mpi_mul_int_ng_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_amemset R LO) (A_mpi_lset_ng.A_mpi_lset_ng_spec_v R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_mul_int_vspec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_mul_int_v_c24.A_mpi_mul_int_vspec_c R HIA (A_link_layout.alo_img R LO) (A_zeroize_and_free_spec_cl R HIA LO HO) (A_mpi_copy_spec_closed_c_cl R HIA LO HO) (A_mpi_lset.A_mpi_lset_spec_v R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO)) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_div_mpi_spec_s_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_div_mpi_c24.A_mpi_div_mpi_spec_s_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc2 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_misc.A_platform_zeroize_spec_cl R HIA LO HO) (A_zeroize_and_free_spec_cl R HIA LO HO) (A_mpi_copy_spec_x_c_cl R HIA LO HO) (A_mpi_grow_spec_closed_c_cl R HIA LO HO) (A_link_mpicore.A_mpi_core_bitlen_spec_cl R HIA LO HO) (A_mpi_shift_l_spec_closed_c_cl R HIA LO HO) (A_mpi_cmp_mpi_spec_cl R HIA LO HO) (A_mpi_cmp_mpi_raw_spec_cl R HIA LO HO) (BX_mpi_cmp_abs.BX_mpi_cmp_abs_spec (ARt.arl_AL R) (A_link_layout.alo_img R LO)) (A_mpi_shift_r.A_mpi_shift_r_spec_closed R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_amemset R LO) (A_link_layout.alo_need_amem R LO)) (A_mpi_lset_ng_spec_cl R HIA LO HO) (A_mpi_mul_int_ng_spec_cl R HIA LO HO) (A_mpi_mul_int_vspec_c_cl R HIA LO HO) (A_add_sub_mpi_ng_spec_o_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)) (A_add_sub_mpi_spec_o_c_cl R HIA LO HO (-1) ltac:(A_link_base.alink_side LO HO)) (A_add_sub_mpi_spec_o_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)) (A_link_layout.alo_calloc R LO).

Definition A_mpi_lset_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3<.R4.R3.(6.R4.R2.)(11.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_mod_mpi_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_mod_mpi_sz.A_mpi_mod_mpi_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_mpi_div_mpi_spec_s_c_cl R HIA LO HO) (fun (flip : Z) (Hq : flip = 1%Z \/ flip = (-1)%Z) => A_add_sub_mpi_ng_spec_oz_cl R HIA LO HO flip Hq) (A_add_sub_mpi_spec_osz_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO).

Definition A_mpi_shrink_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3=.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(12.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_get_mont_r2_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(3>.R4.R3.(6.R4.R2.)(3?.R4.R3.R2.R1.)(40.R4.R3.R2.R1.)(41.R4.R3.R2.R1.)(42.R4.R3.R2.R1.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_mod_mpi_sz_spec_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_mod_mpi_sz.A_mpi_mod_mpi_sz_spec R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc0 R LO) (A_link_layout.alo_need_smalloc R LO) (A_mpi_div_mpi_spec_s_c_cl R HIA LO HO) (fun (flip : Z) (Hq : flip = 1%Z \/ flip = (-1)%Z) => A_add_sub_mpi_ng_spec_oz_cl R HIA LO HO flip Hq) (A_add_sub_mpi_spec_osz_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO).

Definition A_mpi_exp_mod_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  @A_mpi_exp_mod_c24.A_mpi_exp_mod_spec_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.aho_ssmap R HIA HO) (A_link_layout.alo_calloc R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO) (A_mpi_lset_spec_cl R HIA LO HO) (A_mpi_get_mont_r2_spec_c_cl R HIA LO HO) (A_zeroize_and_free_spec_cl R HIA LO HO) (A_mpi_copy_spec_x_c_cl R HIA LO HO) (A_mpi_mod_mpi_sz_spec_cl R HIA LO HO) (A_mpi_grow_spec_closed_c_cl R HIA LO HO) (A_link_mpicore.A_mpi_core_to_mont_rep_spec_cl R HIA LO HO) (A_link_mpicore.A_mpi_core_exp_mod_spec_cl R HIA LO HO) (A_link_mpicore.A_mpi_core_from_mont_rep_spec_cl R HIA LO HO) (A_add_sub_mpi_spec_osz_c_cl R HIA LO HO 1 ltac:(A_link_base.alink_side LO HO)).

Definition A_mpi_free_spec_closed_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(43.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_grow_sz_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(44.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(12.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(45.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_mul_int_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_mul_int_c24.A_mpi_mul_int_spec_c R HIA (A_link_layout.alo_img R LO) (A_zeroize_and_free_spec_cl R HIA LO HO) (A_mpi_copy_spec_closed_c_cl R HIA LO HO) (A_mpi_lset.A_mpi_lset_spec_v R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO)) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_mul_int_ng_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_mul_int_ng_c24.A_mpi_mul_int_ng_spec_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_amemset R LO) (A_mpi_lset_ng.A_mpi_lset_ng_spec_v R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_amemset R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO)) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO)
(* [comment removed for export] *).

Definition A_mpi_mul_mpi_spec_c_cl :=
  fun (R : ARt.art_layout) (HIA : ARt.artA AImg.asegs R) (LO : A_link_layout.a_layout_ok R) (HO : A_link_layout.a_hia_ok R HIA) =>
  A_mpi_mul_mpi_c24.A_mpi_mul_mpi_spec_c R HIA (A_link_layout.alo_img R LO) (A_link_layout.alo_uar_got R LO) (A_link_layout.alo_smalloc1 R LO) (A_link_layout.alo_need_smalloc R LO) (A_link_base.alo_need_rt R LO) (A_link_layout.aho_nodup R HIA HO) (A_link_layout.alo_dimg R LO) (A_link_layout.alo_roimg R LO) (A_zeroize_and_free_spec_cl R HIA LO HO) (A_mpi_copy_spec_closed_c_cl R HIA LO HO) (A_link_mpicore.A_mpi_core_mul_spec_cl R HIA LO HO) (A_link_layout.alo_calloc R LO) (A_link_layout.alo_amemcpy R LO) (A_link_layout.alo_amemset R LO) (A_mpi_lset_spec_cl R HIA LO HO)
(* [comment removed for export] *).

Definition A_mpi_read_binary_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(4=.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(13.R4.R2.)(12.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_resize_clear_core_r_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(4>.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_read_binary_spec_r_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(4?.R4.R3.(6.R4.R2.)(50.R4.R3.R2.R1.)(51.R4.R3.R2.R1.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_read_binary_le_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(52.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(13.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_read_binary_le_spec_r_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(53.R4.R3.(6.R4.R2.)(50.R4.R3.R2.R1.)(54.R4.R3.R2.R1.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_resize_clear_core_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(55.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_resize_clear_spec_closed_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(56.R4.R3.(6.R4.R2.)(;.R4.R2.)(<.R4.R2.)(11.R4.R2.)(13.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_set_bit0_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(57.(9.R4.)(6.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_shift_r_spec_closed_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(58.R4.R3.(6.R4.R2.)(13.R4.R2.)(>.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_spec_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(59.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_spec_o_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5:.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_ng_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5;.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_ng_sz_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5<.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_sub_abs_spec_z_c_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5=.R4.R3.(6.R4.R2.)(18.R4.R3.R2.R1.)(11.R4.R2.)(12.R4.R2.)(13.R4.R2.)(7.R4.R2.)(14.R4.R3.R1.)(15.R4.R2.)(1:.R4.R2.))")
(* [comment removed for export] *).

Definition mpi_mul_mpi_stmtA_sz_of_A_MPI_MUL_MPI_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpi ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5>.R4.R3.$5?.(60.R4.R3.R2.R1.))")
(* [comment removed for export] *).
