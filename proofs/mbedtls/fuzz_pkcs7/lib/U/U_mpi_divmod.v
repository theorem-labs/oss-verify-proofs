(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiClient MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_mpi_addsub U_mpi_grow U_mpi_copy U_mpi_shift_l U_mpi_cmp U_mpi_cmp_int U_mpi_add_abs U_mpi_sub_abs U_mpi_add_sub U_mpi_lset U_mpi_mul_int_W U_mpi_mul_int U_mpi_core_mla_v U_mpi_core_bitlen U_mpi_core_shift_r U_mpi_shift_r U_mpi_cmp_abs U_mpi_divmod_stmt U_mpi_div_mpi U_mpi_mod_mpi.
Import ListNotations.
Open Scope Z_scope.

Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr usegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Lemma U_add_sub_mpi_spec_closed : add_sub_mpi_stmt usegs L HI U_ADD_SUB_MPI U_MEMSET_FUNC.
  Proof.
    unfold add_sub_mpi_stmt. intros flip Hf. intros.
    eapply (U_add_sub_mpi_spec_o L HI HFREE HCALLOC HLS SW DIMG HND (fun a H1 H2 => ROIMG a H2 H1) _ eq_refl flip Hf); try eassumption.
    apply opnd_at_mpd. assumption.
  Qed.

  Let ROIMG' : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L :=
    fun a H1 H2 => ROIMG a H2 H1.

  Ltac callees :=
    lazymatch goal with
    | |- mpi_copy_stmt_x _ _ _ _ _ => exact (U_mpi_copy_spec_x L HI HFREE HCALLOC HLS SW DIMG HND ROIMG)
    | |- mpi_grow_stmt _ _ _ _ _ => exact (U_mpi_grow_spec L HI HFREE HCALLOC HLS SW DIMG HND)
    | |- mpi_shift_l_stmt _ _ _ _ _ => exact (U_mpi_shift_l_spec L HI HFREE HCALLOC HLS SW DIMG HND ROIMG' _ eq_refl)
    | |- mpi_cmp_mpi_stmt _ _ => exact U_mpi_cmp_mpi_spec
    | |- mpi_cmp_mpi_stmt_o _ _ => exact U_mpi_cmp_mpi_spec_o
    | |- mpi_cmp_abs_stmt _ _ => exact U_mpi_cmp_abs_spec
    | |- mpi_shift_r_stmt _ _ => exact U_mpi_shift_r_spec
    | |- mpi_cmp_int_stmt _ _ => exact U_mpi_cmp_int_spec
    | |- add_sub_mpi_stmt _ _ _ _ _ => exact U_add_sub_mpi_spec_closed
    | |- mpi_lset_stmt _ _ _ _ _ => exact (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND)
    | |- mpi_mul_int_stmt_g _ _ _ _ _ => exact (U_mpi_mul_int_spec_closed L HI HFREE HCALLOC HLS SW DIMG HND ROIMG' IMGC _ eq_refl)
    | |- mpi_core_bitlen_stmt _ _ => exact U_mpi_core_bitlen_spec
    | |- mpi_core_shift_r_stmt _ _ => exact U_mpi_core_shift_r_spec
    | |- zeroize_and_free_stmt _ _ _ _ _ => exact (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG)
    | |- platform_zeroize_stmt _ _ _ _ => apply U_platform_zeroize_spec
    | |- _ => idtac
    end.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem U_mpi_div_mpi_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_div_mpi_stmt usegs L HI U_MPI_DIV_MPI MSF.
  Proof.
    intros MSF ->. eapply (U_mpi_div_mpi_ok L HI HCALLOC HLS SW DIMG HND ROIMG IMGC U_MEMSET_FUNC); callees.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem U_mpi_mod_mpi_spec : forall MSF, MSF = U_MEMSET_FUNC -> mpi_mod_mpi_stmt usegs L HI U_MPI_MOD_MPI' MSF.
  Proof.
    intros MSF ->. eapply (U_mpi_mod_mpi_ok L HI); try eassumption; callees. apply U_mpi_div_mpi_spec. reflexivity.
  Qed.
End C.
