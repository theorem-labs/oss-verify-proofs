(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Definition U_MEMSET : Z := 0x46e44.

Lemma U_platform_zeroize_spec : forall L, platform_zeroize_stmt usegs L U_PLATFORM_ZEROIZE U_MEMSET_FUNC.
Proof.
  intros L. unfold platform_zeroize_stmt, U_PLATFORM_ZEROIZE.
  intros until junk. intros HB Hn HA ST LO ACL SPA SX SOK CA DHI DA MI -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(A, A + n); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  destruct HB as [[WF HBb] HW]. dpose HW as (HW1 & HW2 & _). cbn [cells_size csize Nat.add] in HW2.
  assert (HB : rw_cells usegs m A [CB (Z.to_nat n) junk]) by (split; [split|]; assumption).
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  - (* [comment removed for export] *)
    zstep. finish. subst n. cbn [Z.to_nat repeat] in *. cbn in WF. destruct junk; [exact HB | cbn in WF; lia].
  - pose proof (statics_ok_cells usegs L _ U_MEMSET_FUNC (le8 (Z_to_bv 64 U_MEMSET)) SOK CA ltac:(vm_compute; reflexivity)) as [_ MSFB].
    assert (MSFC : ro_cells usegs m U_MEMSET_FUNC [C8 (Z_to_bv 64 U_MEMSET)]) by (split; [cbn; auto| exact MSFB]). clear MSFB.
    unfold U_MEMSET_FUNC, U_MEMSET in MSFC. dpose CA as (CA1 & CA2 & _). unfold U_MEMSET_FUNC in CA1, CA2.
    carve_frame 16%nat ST.
    do 9 zstep. clear MSFC.
    pose proof U_memset_spec as SP. unfold memset_stmt in SP.
    eapply evt_cut; [ eapply SP; rewrite ?unsigned_lit by lia; [exact HB | eassumption] | ].
    clear SP. unfold memset_post. rewrite !unsigned_lit by lia.
    match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    change (0 mod 256) with 0 in *.
    zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    finish.
Qed.
