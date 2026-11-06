(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts EcpFacts MpiClient MpiOpnd.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_platform_zeroize_proof P_mpi_free P_mpi_addsub P_mpi_grow
     P_mpi_copy P_mpi_shift_l P_mpi_cmp P_mpi_cmp_int P_mpi_add_abs P_mpi_sub_abs P_mpi_add_sub P_mpi_lset P_mpi_mul_int_W P_mpi_mul_int P_mpi_core_mla_v
     P_mpi_core_bitlen P_mpi_core_shift_r P_mpi_divmod_stmt P_mpi_div_mpi P_mpi_mod_mpi.
Import ListNotations.
Open Scope Z_scope.

Section C.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, 0 <= a < 2^64 -> ro_addr psegs (wa a) = true -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis IMGC : hl_img_hi L <= alloc_ceiling.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Lemma P_add_sub_mpi_spec_closed : add_sub_mpi_stmt psegs L HI P_ADD_SUB_MPI P_MEMSET_FUNC.
  Proof.
    unfold add_sub_mpi_stmt. intros flip Hf. intros.
    eapply (P_add_sub_mpi_spec_o L HI HFREE HCALLOC HLS SW DIMG HND (fun a H1 H2 => ROIMG a H2 H1) _ eq_refl flip Hf); try eassumption.
    apply opnd_at_mpd. assumption.
  Qed.

  Let ROIMG' : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L :=
    fun a H1 H2 => ROIMG a H2 H1.

  Ltac callees :=
    lazymatch goal with
    | |- mpi_copy_stmt_x _ _ _ _ _ => exact (P_mpi_copy_spec_x L HI HFREE HCALLOC HLS SW DIMG HND ROIMG)
    | |- mpi_grow_stmt _ _ _ _ _ => exact (P_mpi_grow_spec L HI HFREE HCALLOC HLS SW DIMG HND)
    | |- mpi_shift_l_stmt _ _ _ _ _ => exact (P_mpi_shift_l_spec L HI HFREE HCALLOC HLS SW DIMG HND ROIMG' _ eq_refl)
    | |- mpi_cmp_mpi_stmt _ _ => exact P_mpi_cmp_mpi_spec
    | |- mpi_cmp_int_stmt _ _ => exact P_mpi_cmp_int_spec
    | |- add_sub_mpi_stmt _ _ _ _ _ => exact P_add_sub_mpi_spec_closed
    | |- mpi_lset_stmt _ _ _ _ _ => exact (P_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND)
    | |- mpi_mul_int_stmt_g _ _ _ _ _ => exact (P_mpi_mul_int_spec_closed L HI HFREE HCALLOC HLS SW DIMG HND ROIMG' IMGC _ eq_refl)
    | |- mpi_core_bitlen_stmt _ _ => exact P_mpi_core_bitlen_spec
    | |- mpi_core_shift_r_stmt _ _ => exact P_mpi_core_shift_r_spec
    | |- zeroize_and_free_stmt _ _ _ _ _ => exact (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG)
    | |- platform_zeroize_stmt _ _ _ _ => apply P_platform_zeroize_spec
    | |- _ => idtac
    end.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem P_mpi_div_mpi_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_div_mpi_stmt psegs L HI P_MPI_DIV_MPI MSF.
  Proof.
    intros MSF ->. eapply (P_mpi_div_mpi_ok L HI HCALLOC HLS SW DIMG HND ROIMG IMGC P_MEMSET_FUNC); callees.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG IMGC ROIMG'"] Theorem P_mpi_mod_mpi_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_mod_mpi_stmt psegs L HI P_MPI_MOD_MPI' MSF.
  Proof.
    intros MSF ->. eapply (P_mpi_mod_mpi_ok L HI); try eassumption; callees. apply P_mpi_div_mpi_spec. reflexivity.
  Qed.
End C.
