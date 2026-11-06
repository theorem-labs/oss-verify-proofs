(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_grow P_mpi_copy P_mpi_lset P_mpi_shrink
     P_mpi_shift_l P_mpi_shift_r P_mpi_init P_mpi_set_bit P_mpi_bitlen P_mpi_cmp P_mpi_cmp_int P_mpi_addsub P_mpi_add_sub P_mpi_add_int
     P_mpi_sub_abs P_mpi_read_binary P_mpi_read_binary_proof P_mpi_read_binary_le P_mpi_mul_stmt P_mpi_mul_mpi P_mpi_divmod_stmt
     P_mpi_div_mpi P_mpi_mod_mpi P_mpi_divmod P_mpi_core_bitlen P_mpi_core_bitlen_z P_mpi_core_exp_mod_working_limbs
     P_mpi_core_montmul_init P_mpi_core_to_mont_rep P_mpi_core_exp_mod P_mpi_core_from_mont_rep P_mpi_core_check_zero_ct
     P_mpi_get_mont_r2 P_mpi_exp_mod_stmt P_mpi_exp_mod
     P_ecp_defs P_ecp_red P_ecp_mul_mod P_ecp_mul_mod_proof P_ecp_modp_table P_ecp_mod_p192k1 P_ecp_mod_p224k1 P_ecp_mod_p256k1
     P_ecp_sw_rhs P_ecp_derive_y P_ecp_check_pubkey P_ecp_point_read_binary.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_ecp_closed () : Init.string Init.list := ["OSSVerify.KrLib.P.P_ecp_check_pubkey.ecp_check_pubkey_stmt"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.P.P_ecp_defs.P_MT"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_ECP_CHECK_PUBKEY"; "OSSVerify.KrLib.P.P_platform_zeroize.P_MEMSET_FUNC"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.P_BAD_POINTS"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.ECP_CHECK_PUBKEY_STACK"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ecp_point_read_binary_stmt"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.P_ECP_POINT_READ_BINARY"; "OSSVerify.KrLib.P.P_ecp_point_read_binary.ECP_POINT_READ_STACK"].


Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis CRP_P192K1 : const_at L P_ecp_mod_p192k1.RP 8.
  Hypothesis CRP_P224K1 : const_at L P_ecp_mod_p224k1.RP 8.
  Hypothesis CRP_P256K1 : const_at L P_ecp_mod_p256k1.RP 8.

  Let ROIMG' : forall a, 0 <= a < 2^64 -> ro_addr psegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L :=
    fun a H1 H2 => ROIMG a H2 H1.

  Ltac layout := first [ exact HFREE | exact HCALLOC | exact HLS | exact SW | exact DIMG | exact HND | exact ROIMG | exact ROIMG' | exact IMGC
                       | exact CRP_P192K1 | exact CRP_P224K1 | exact CRP_P256K1 | reflexivity ].

  (* [comment removed for export] *)
  Ltac leaf :=
    lazymatch goal with
    | |- mpi_lset_stmt _ _ _ _ _ => eapply P_mpi_lset_spec; layout
    | |- mpi_shift_l_stmt _ _ _ _ _ => eapply P_mpi_shift_l_spec; layout
    | |- mpi_mod_mpi_stmt _ _ _ _ _ => eapply P_mpi_mod_mpi_spec; layout
    | |- mpi_shrink_stmt _ _ _ _ _ => eapply P_mpi_shrink_spec; layout
    | |- mpi_core_bitlen_stmt _ _ => exact P_mpi_core_bitlen_spec
    | |- mpi_core_bitlen_z_stmt _ _ => exact P_mpi_core_bitlen_z_spec
    | |- mpi_core_exp_mod_working_limbs_stmt _ _ => exact P_mpi_core_exp_mod_working_limbs_spec
    | |- zeroize_and_free_stmt _ _ _ _ _ => eapply P_zeroize_and_free_spec; layout
    | |- mpi_copy_stmt _ _ _ _ _ => eapply P_mpi_copy_spec; layout
    | |- mpi_cmp_mpi_stmt _ _ => exact P_mpi_cmp_mpi_spec
    | |- mpi_cmp_int_stmt _ _ => exact P_mpi_cmp_int_spec
    | |- mpi_grow_stmt _ _ _ _ _ => eapply P_mpi_grow_spec; layout
    | |- mpi_core_montmul_init_stmt _ _ => exact P_mpi_core_montmul_init_spec
    | |- mpi_core_to_mont_rep_stmt _ _ => exact P_mpi_core_to_mont_rep_spec
    | |- mpi_core_exp_mod_stmt _ _ => exact P_mpi_core_exp_mod_spec
    | |- mpi_core_from_mont_rep_stmt _ _ => exact P_mpi_core_from_mont_rep_spec
    | |- mpi_core_check_zero_ct_stmt _ _ => exact P_mpi_core_check_zero_ct_spec
    | |- add_sub_mpi_stmt_e _ _ _ _ _ => exact (P_add_sub_mpi_spec_closed L HI HFREE HCALLOC HLS SW DIMG HND ROIMG')
    | |- mpi_mul_mpi_stmt _ _ _ _ _ => eapply P_mpi_mul_mpi_spec; layout
    | |- mpi_add_mpi_stmt _ _ _ _ _ => eapply P_mpi_add_mpi_spec; layout
    | |- mpi_sub_mpi_stmt _ _ _ _ _ => eapply P_mpi_sub_mpi_spec; layout
    | |- mpi_add_int_stmt _ _ _ _ _ => eapply P_mpi_add_int_spec; layout
    | |- mpi_sub_int_stmt _ _ _ _ _ => eapply P_mpi_sub_int_spec; layout
    | |- mpi_sub_abs_stmt _ _ _ _ _ => eapply P_mpi_sub_abs_spec; layout
    | |- mpi_get_bit_stmt _ _ => exact P_mpi_get_bit_spec
    | |- mpi_init_stmt _ _ => exact P_mpi_init_spec
    | |- mpi_free_stmt _ _ _ _ _ => eapply P_mpi_free_spec; layout
    | |- mpi_shift_r_stmt _ _ => exact P_mpi_shift_r_spec
    | |- mpi_size_stmt _ _ => exact P_mpi_size_spec
    | |- mpi_read_binary_stmt _ _ _ _ _ => eapply P_mpi_read_binary_spec; layout
    | |- mpi_read_binary_le_stmt _ _ _ _ _ => eapply P_mpi_read_binary_le_spec; layout
    | |- mpi_set_bit0_stmt _ _ => exact P_mpi_set_bit0_spec
    | |- modp_table_ok _ _ _ _ _ => eapply P_modp_table_ok; layout
    | |- _ => layout
    end.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem P_mpi_get_mont_r2_closed : mpi_get_mont_r2_stmt psegs L HI P_MPI_GET_MONT_R2 P_MEMSET_FUNC.
  Proof. eapply P_mpi_get_mont_r2_spec; leaf. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem P_mpi_exp_mod_closed : mpi_exp_mod_stmt_n psegs L HI P_MPI_EXP_MOD P_MEMSET_FUNC.
  Proof. eapply P_mpi_exp_mod_spec; first [ exact P_mpi_get_mont_r2_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem P_ecp_mul_mod_closed : ecp_mul_mod_stmt psegs L HI P_MT P_ECP_MUL_MOD P_MEMSET_FUNC 366760 ECP_MUL_MOD_STACK.
  Proof. eapply P_ecp_mul_mod_proof.P_ecp_mul_mod_spec; leaf. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem P_ecp_sw_rhs_closed : ecp_sw_rhs_stmt psegs L HI P_MT P_ECP_SW_RHS P_MEMSET_FUNC 366760 ECP_SW_RHS_STACK.
  Proof. eapply P_ecp_sw_rhs_spec; first [ exact P_ecp_mul_mod_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem P_ecp_derive_y_closed : ecp_derive_y_stmt psegs L HI P_MT P_ECP_DERIVE_Y P_MEMSET_FUNC 366760 ECP_DERIVE_Y_STACK.
  Proof. eapply P_ecp_derive_y_spec; first [ exact P_ecp_sw_rhs_closed | exact P_mpi_exp_mod_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem P_ecp_check_pubkey_closed : ltac2:(CDefT.buildp (gd_tbl_P_ecp_closed ()) "(0.$1.VL,VHI,$2.$3.$4.+598:8.$5.$6.)")
(* [comment removed for export] *).
  Proof. eapply P_ecp_check_pubkey_spec; first [ exact P_ecp_mul_mod_closed | exact P_ecp_sw_rhs_closed | leaf ]. Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC CRP_P192K1 CRP_P224K1 CRP_P256K1 ROIMG'"] Theorem P_ecp_point_read_binary_closed : ltac2:(CDefT.buildp (gd_tbl_P_ecp_closed ()) "(7.$1.VL,VHI,$2.$8.$4.+598:8.$9.)")
(* [comment removed for export] *).
  Proof. eapply P_ecp_point_read_binary_spec; first [ exact P_ecp_derive_y_closed | leaf ]. Qed.
End C.
