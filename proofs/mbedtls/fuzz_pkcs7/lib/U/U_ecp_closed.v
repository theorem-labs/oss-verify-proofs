(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_mpi_free U_mpi_grow U_mpi_copy U_mpi_lset U_mpi_shrink U_mpi_shift_l U_mpi_shift_r U_mpi_init U_mpi_set_bit U_mpi_bitlen U_mpi_cmp U_mpi_cmp_int U_mpi_addsub U_mpi_add_sub U_mpi_add_int U_mpi_sub_abs U_mpi_read_binary U_mpi_read_binary_proof U_mpi_read_binary_le U_mpi_mul_stmt U_mpi_mul_mpi U_mpi_divmod_stmt U_mpi_div_mpi U_mpi_mod_mpi U_mpi_divmod U_mpi_core_bitlen U_mpi_core_bitlen_z U_mpi_core_exp_mod_working_limbs U_mpi_core_montmul_init U_mpi_core_to_mont_rep U_mpi_core_exp_mod U_mpi_core_from_mont_rep U_mpi_core_check_zero_ct U_mpi_get_mont_r2 U_mpi_exp_mod_stmt U_mpi_exp_mod U_ecp_defs U_ecp_red U_ecp_mul_mod U_ecp_mul_mod_proof U_ecp_modp_table U_ecp_mod_p192k1 U_ecp_mod_p224k1 U_ecp_mod_p256k1 U_ecp_sw_rhs U_ecp_derive_y U_ecp_check_pubkey U_ecp_point_read_binary.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_closed () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ecp_check_pubkey_stmt"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_ECP_CHECK_PUBKEY"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.U_BAD_POINTS"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ecp_point_read_binary_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.U_ECP_POINT_READ_BINARY"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_point_read_binary.ECP_POINT_READ_STACK"].


Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis CRP_P192K1 : const_at L U_ecp_mod_p192k1.RP 8.
  Hypothesis CRP_P224K1 : const_at L U_ecp_mod_p224k1.RP 8.
  Hypothesis CRP_P256K1 : const_at L U_ecp_mod_p256k1.RP 8.

  Let ROIMG' : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L :=
    fun a H1 H2 => ROIMG a H2 H1.

  Ltac layout := first [ exact HFREE | exact HCALLOC | exact HLS | exact SW | exact DIMG | exact HND | exact ROIMG | exact ROIMG' | exact IMGC
                       | exact CRP_P192K1 | exact CRP_P224K1 | exact CRP_P256K1 | reflexivity ].

  (* [comment removed for export] *)
  Ltac leaf :=
    lazymatch goal with
    | |- mpi_lset_stmt _ _ _ _ _ => eapply U_mpi_lset_spec; layout
    | |- mpi_shift_l_stmt _ _ _ _ _ => eapply U_mpi_shift_l_spec; layout
    | |- mpi_mod_mpi_stmt _ _ _ _ _ => eapply U_mpi_mod_mpi_spec; layout
    | |- mpi_shrink_stmt _ _ _ _ _ => eapply U_mpi_shrink_spec; layout
    | |- mpi_core_bitlen_stmt _ _ => exact U_mpi_core_bitlen_spec
    | |- mpi_core_bitlen_z_stmt _ _ => exact U_mpi_core_bitlen_z_spec
    | |- mpi_core_exp_mod_working_limbs_stmt _ _ => exact U_mpi_core_exp_mod_working_limbs_spec
    | |- zeroize_and_free_stmt _ _ _ _ _ => eapply U_zeroize_and_free_spec; layout
    | |- mpi_copy_stmt _ _ _ _ _ => eapply U_mpi_copy_spec; layout
    | |- mpi_cmp_mpi_stmt _ _ => exact U_mpi_cmp_mpi_spec
    | |- mpi_cmp_mpi_stmt_o _ _ => exact U_mpi_cmp_mpi_spec_o
    | |- mpi_cmp_int_stmt _ _ => exact U_mpi_cmp_int_spec
    | |- mpi_grow_stmt _ _ _ _ _ => eapply U_mpi_grow_spec; layout
    | |- mpi_core_montmul_init_stmt _ _ => exact U_mpi_core_montmul_init_spec
    | |- mpi_core_to_mont_rep_stmt _ _ => exact U_mpi_core_to_mont_rep_spec
    | |- mpi_core_exp_mod_stmt _ _ => exact U_mpi_core_exp_mod_spec
    | |- mpi_core_from_mont_rep_stmt _ _ => exact U_mpi_core_from_mont_rep_spec
    | |- mpi_core_check_zero_ct_stmt _ _ => exact U_mpi_core_check_zero_ct_spec
    | |- add_sub_mpi_stmt_e _ _ _ _ _ => exact (U_add_sub_mpi_spec_closed L HI HFREE HCALLOC HLS SW DIMG HND ROIMG')
    | |- mpi_mul_mpi_stmt _ _ _ _ _ => eapply U_mpi_mul_mpi_spec; layout
    | |- mpi_add_mpi_stmt _ _ _ _ _ => eapply U_mpi_add_mpi_spec; layout
    | |- mpi_sub_mpi_stmt _ _ _ _ _ => eapply U_mpi_sub_mpi_spec; layout
    | |- mpi_add_int_stmt _ _ _ _ _ => eapply U_mpi_add_int_spec; layout
    | |- mpi_sub_int_stmt _ _ _ _ _ => eapply U_mpi_sub_int_spec; layout
    | |- mpi_sub_abs_stmt _ _ _ _ _ => eapply U_mpi_sub_abs_spec; layout
    | |- mpi_get_bit_stmt _ _ => exact U_mpi_get_bit_spec
    | |- mpi_init_stmt _ _ => exact U_mpi_init_spec
    | |- mpi_free_stmt _ _ _ _ _ => eapply U_mpi_free_spec; layout
    | |- mpi_shift_r_stmt _ _ => exact U_mpi_shift_r_spec
    | |- mpi_size_stmt _ _ => exact U_mpi_size_spec
    | |- mpi_read_binary_stmt _ _ _ _ _ => eapply U_mpi_read_binary_spec; layout
    | |- mpi_read_binary_le_stmt _ _ _ _ _ => eapply U_mpi_read_binary_le_spec; layout
    | |- mpi_set_bit0_stmt _ _ => exact U_mpi_set_bit0_spec
    | |- modp_table_ok _ _ _ _ _ => eapply U_modp_table_ok; layout
    | |- _ => layout
    end.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem U_mpi_get_mont_r2_closed : mpi_get_mont_r2_stmt usegs L HI U_MPI_GET_MONT_R2 U_MEMSET_FUNC.
  Proof. eapply U_mpi_get_mont_r2_spec; leaf. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem U_mpi_exp_mod_closed : mpi_exp_mod_stmt_n usegs L HI U_MPI_EXP_MOD U_MEMSET_FUNC.
  Proof. eapply U_mpi_exp_mod_spec; first [ exact U_mpi_get_mont_r2_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem U_ecp_mul_mod_closed : ecp_mul_mod_stmt usegs L HI U_MT U_ECP_MUL_MOD U_MEMSET_FUNC 380840 ECP_MUL_MOD_STACK.
  Proof. eapply U_ecp_mul_mod_proof.U_ecp_mul_mod_spec; leaf. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem U_ecp_sw_rhs_closed : ecp_sw_rhs_stmt usegs L HI U_MT U_ECP_SW_RHS U_MEMSET_FUNC 380840 ECP_SW_RHS_STACK.
  Proof. eapply U_ecp_sw_rhs_spec; first [ exact U_ecp_mul_mod_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem U_ecp_derive_y_closed : ecp_derive_y_stmt usegs L HI U_MT U_ECP_DERIVE_Y U_MEMSET_FUNC 380840 ECP_DERIVE_Y_STACK.
  Proof. eapply U_ecp_derive_y_spec; first [ exact U_ecp_sw_rhs_closed | exact U_mpi_exp_mod_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem U_ecp_check_pubkey_closed : ltac2:(CDefT.buildp (gd_tbl_P_ecp_closed ()) "(0.$1.VL,VHI,$2.$3.$4.+5<?:8.$5.$6.)")
(* [comment removed for export] *).
  Proof. eapply U_ecp_check_pubkey_spec; first [ exact U_ecp_mul_mod_closed | exact U_ecp_sw_rhs_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem U_ecp_point_read_binary_closed : ltac2:(CDefT.buildp (gd_tbl_P_ecp_closed ()) "(7.$1.VL,VHI,$2.$8.$4.+5<?:8.$9.)")
(* [comment removed for export] *).
  Proof. eapply U_ecp_point_read_binary_spec; first [ exact U_ecp_derive_y_closed | leaf ]. Qed.
End C.
