(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_mpi_read_binary_stmt A_oid A_link_layout.
Import ListNotations.
Open Scope Z_scope.

Lemma alo_need_rt : forall R, a_layout_ok R -> 0 <= arl_need_rt R.
Proof. intros R LO. unfold arl_need_rt. pose proof (alo_need_malloc R LO). lia. Qed.

Lemma alo_oid_rt : forall R (HIA : artA asegs R), a_layout_ok R -> oid_rt_hyps R HIA.
Proof.
  intros R HIA LO. unfold oid_rt_hyps.
  split; [exact (alo_img R LO)|]. split; [exact (alo_gsb R LO)|]. split; [exact (alo_memcmp_i R LO)|].
  split; [exact (alo_rtc R LO)|]. split; [exact (alo_need_bcmp R LO)|].
  intros h LB LF m H. exact (hm_img_shadow asegs R HIA h LB LF m H).
Qed.

(* [comment removed for export] *)
Create HintDb alink_unf.
Create HintDb alink_unf0.   (* [comment removed for export] *)
Create HintDb alink_bud discriminated.   (* [comment removed for export] *)
#[global] Hint Constants Opaque : alink_bud.   (* [comment removed for export] *)
#[global] Hint Variables Opaque : alink_bud.
Ltac alink_needs LO :=
  pose proof (alo_need_malloc _ LO); pose proof (alo_need_free _ LO); pose proof (alo_need_smalloc _ LO);
  pose proof (alo_need_amem _ LO); pose proof (alo_need_bcmp _ LO); pose proof (alo_need_setsh _ LO);
  pose proof (alo_need_rip _ LO).
Ltac alink_side LO HO :=
  first [ eassumption
        | alink_lo LO
        | exact (aho_nodup _ _ HO) | exact (aho_amemmove _ _ HO) | exact (aho_ssmap _ _ HO) | exact (aho_hmperm _ _ HO)   (* [comment removed for export] *)
        | solve [ intros; lia ]
        | solve [ left; reflexivity ] | solve [ right; reflexivity ]
        | solve [ lazymatch goal with |- _ = true => vm_compute; reflexivity end ]   (* [comment removed for export] *)
        | solve [ intros; autounfold with alink_unf0; lia ]
        | solve [ intros; alink_needs LO; autounfold with alink_unf; unfold arl_need_rt; timeout 60 lia ]   (* timeout-ok: expiry takes the eauto and nia arms after it, which prove the same side condition *)
        | solve [ eauto 12 with alink_bud nocore ]
        | solve [ intros; alink_needs LO; autounfold with alink_unf; unfold arl_need_rt; nia ] ].
Ltac alink_open := match goal with |- ?g => idtac "ALINK-OPEN:" g end.
