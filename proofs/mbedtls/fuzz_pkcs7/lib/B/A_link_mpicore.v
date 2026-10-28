(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_link_layout A_link_base A_link_budgets.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require A_mpi_core_add A_mpi_core_add_if A_mpi_core_bitlen A_mpi_core_check_zero_ct A_mpi_core_exp_mod A_mpi_core_exp_mod_working_limbs A_mpi_core_from_mont_rep A_mpi_core_mla A_mpi_core_mla_v A_mpi_core_montmul A_mpi_core_montmul_init A_mpi_core_mul A_mpi_core_read_be A_mpi_core_read_le A_mpi_core_shift_l A_mpi_core_shift_r A_mpi_core_sub A_mpi_core_sub_int A_mpi_core_to_mont_rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_link_mpicore () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_layout_ok"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.a_hia_ok"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_add.A_mpi_core_add_spec"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_img"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_add_if.A_mpi_core_add_if_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_bitlen.A_mpi_core_bitlen_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_bitlen.A_mpi_core_bitlen_z_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_check_zero_ct.A_mpi_core_check_zero_ct_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod.A_mpi_core_exp_mod_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_amemcpy"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_amem"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_working_limbs.A_mpi_core_exp_mod_working_limbs_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul.A_mpi_core_montmul_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_from_mont_rep.A_mpi_core_from_mont_rep_spec"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_uar_got"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_smalloc0"; "RocqVerifyHarness.AgentSubmission.B.A_link_layout.alo_need_smalloc"; "A_mpi_core_montmul_spec_cl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.A_mpi_core_mla_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla_v.A_mpi_core_mla_vspec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_montmul_init.A_mpi_core_montmul_init_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mul.A_mpi_core_mul_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_read_be.A_mpi_core_read_be_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_read_le.A_mpi_core_read_le_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_l.A_mpi_core_shift_l_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_shift_r.A_mpi_core_shift_r_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_sub.A_mpi_core_sub_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_sub_int.A_mpi_core_sub_int_spec"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_to_mont_rep.A_mpi_core_to_mont_rep_spec"].


Definition A_mpi_core_add_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(5.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_add_if_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(8.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_bitlen_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(9.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_bitlen_z_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(:.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_check_zero_ct_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(;.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_exp_mod_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(<.R4.R3.(7.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_exp_mod_working_limbs_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(10.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_montmul_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(11.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_from_mont_rep_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(12.R4.R3.(7.R4.R2.)(13.R4.R2.)(14.R4.R2.)(15.R4.R2.)(?.R4.R2.)(16.R4.R3.R2.R1.))")
(* [comment removed for export] *).

Definition A_mpi_core_mla_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(17.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_mla_vspec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(18.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_montmul_init_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(19.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_mul_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1:.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_read_be_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1;.R4.R3.(7.R4.R2.)(=.R4.R2.)(>.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_read_le_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1<.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_shift_l_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1=.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_shift_r_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1>.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_sub_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(1?.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_sub_int_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(20.(6.R4.)(7.R4.R2.))")
(* [comment removed for export] *).

Definition A_mpi_core_to_mont_rep_spec_cl := ltac2:(CDefT.buildp (gd_tbl_A_link_mpicore ()) "LR,$0.LHIA,(1.$2.R1.)LLO,(3.R2.)LHO,(4.R3.R2.)(21.R4.R3.(7.R4.R2.)(=.R4.R2.)(?.R4.R2.))")
(* [comment removed for export] *).
