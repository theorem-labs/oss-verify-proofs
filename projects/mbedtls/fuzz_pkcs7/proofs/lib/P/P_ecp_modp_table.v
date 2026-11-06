(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal RepEcp EcpCurves.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_platform_zeroize P_mpi_free P_mpi_grow P_ecp_red P_ecp_mul_mod P_ecp_defs P_ecp_mod_p192 P_ecp_mod_p224 P_ecp_mod_p256 P_ecp_mod_p384 P_ecp_mod_p521 P_ecp_mod_p255 P_ecp_mod_p192k1 P_ecp_mod_p224k1 P_ecp_mod_p256k1 P_ecp_mod_p448.
Import ListNotations.
Open Scope Z_scope.

Section TBL.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Hypothesis CRP_P192K1 : const_at L P_ecp_mod_p192k1.RP 8.
  Hypothesis CRP_P224K1 : const_at L P_ecp_mod_p224k1.RP 8.
  Hypothesis CRP_P256K1 : const_at L P_ecp_mod_p256k1.RP 8.

  #[using="HFREE HCALLOC HLS SW DIMG HND CRP_P192K1 CRP_P224K1 CRP_P256K1"] Lemma P_modp_table_ok : modp_table_ok psegs L HI P_MT P_MEMSET_FUNC.
  Proof.
  unfold modp_table_ok, P_MT. intros e lp ws IN.
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p192_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p224_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p256_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p384_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p521_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p255_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p192k1_spec L HI HFREE HCALLOC HLS SW DIMG HND CRP_P192K1)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p224k1_spec L HI HFREE HCALLOC HLS SW DIMG HND CRP_P224K1)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p256k1_spec L HI HFREE HCALLOC HLS SW DIMG HND CRP_P256K1)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN as [E|IN].
  { injection E as <- <- <-. split; [reflexivity|]. eexists _, _. split; [| split; [| exact (P_ecp_mod_p448_spec L HI HFREE HCALLOC HLS SW DIMG HND)]]; [cbn; lia| unfold ECP_RED_STACK; lia]. }
  destruct IN.
  Qed.
End TBL.
