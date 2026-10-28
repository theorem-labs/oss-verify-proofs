(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame AKinvM AW_FreeK.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Section ARUN_1. Context {hAR : arun}.

Section FR.
  Variable AL : asan_layout.
  Variable F0 : ffam AL.
  Variable mo0 : Model.

  Definition Kfr (h : ahst) (mo : Model) : Prop := ff_K AL F0 h mo /\ mo_frame mo0 mo.

  Local Ltac fr L := eapply mo_frame_trans; [eassumption| apply L].

  Definition ffam_fr : ffam AL.
  Proof.
    unshelve refine (FF AL (ff_CS AL F0) Kfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); unfold Kfr.
    - exact (ff_csok AL F0).
    - intros h. apply kinv_KF. exact (ff_kinv AL F0 h).
    - intros h h' mo V [K M]. split; [exact (ff_view_K AL F0 h h' mo V K)| exact M].
    - exact (ff_view_CS AL F0).
    - exact (ff_noshadow AL F0).
    - intros h mo [K _]. exact (ff_halted AL F0 h mo K).
    - intros h mo W [K _]. exact (ff_geom AL F0 h mo W K).
    - intros h mo a n [K _]. exact (ff_apart AL F0 h mo a n K).
    - exact (ff_cs_T AL F0). - exact (ff_cs_ctx AL F0). - exact (ff_cs_ri AL F0). - exact (ff_cs_fs AL F0). - exact (ff_cs_stack AL F0).
    - exact (ff_cs_user AL F0). - exact (ff_cs_fa AL F0).
    - intros h mo b [K _]. exact (ff_cs_node AL F0 h mo b K).
    - intros h mo b [K _]. exact (ff_cs_store AL F0 h mo b K).
    - intros h mo sh [K _]. exact (ff_cs_sec AL F0 h mo sh K).
    - exact (ff_cs_pa AL F0). - exact (ff_cs_img AL F0).
    - intros h c mo W C R [K _]. exact (ff_fa_ledger AL F0 h c mo W C R K).
    - intros h c mo W C R [K M] MC. split; [exact (ff_fa_commit AL F0 h c mo W C R K MC)| fr mo_frame_fixrw_commit].
    - intros h c mo W C R [K M] RF. split; [exact (ff_fa_fresh AL F0 h c mo W C R K RF)| fr mo_frame_fixrw_fresh].
    - intros h c mo W C R [K _]. exact (ff_fa_room AL F0 h c mo W C R K).
    - intros h c W C R. exact (scar_site_KF AL _ _ mo0 _ _ (ff_fa_scar AL F0 h c W C R)).   (* [comment removed for export] *)
    - intros h c mo W C R [K _]. exact (ff_u_ledger AL F0 h c mo W C R K).
    - intros h c mo W C R [K M] MC. split; [exact (ff_u_commit AL F0 h c mo W C R K MC)| fr mo_frame_fixrw_commit].
    - intros h c mo W C R [K M] RF. split; [exact (ff_u_fresh AL F0 h c mo W C R K RF)| fr mo_frame_fixrw_fresh].
    - intros h c mo W C R [K _]. exact (ff_u_room AL F0 h c mo W C R K).
    - intros h c W C R. exact (scar_site_KF AL _ _ mo0 _ _ (ff_u_scar AL F0 h c W C R)).
    - intros h k i mo W N B [K _]. exact (ff_madv_ok AL F0 h k i mo W N B K).
    - intros h k i mo W N B [K M]. cbn zeta. split; [exact (ff_madv AL F0 h k i mo W N B K)| fr mo_frame_madvise_model].
    - intros h k i mo W N [K _]. exact (ff_unmap_has AL F0 h k i mo W N K).
    - intros h k i mo W N [K M]. split; [exact (ff_unmap AL F0 h k i mo W N K)| fr mo_frame_munmap_model].
    - intros h nb bl mo a W E [K M] A0 A1 A2 RF. destruct (ff_node AL F0 h nb bl mo a W E K A0 A1 A2 RF) as [K' C']. split; [split; [exact K'| fr mo_frame_anon_grant]| exact C'].
    - intros h nb bl mo a W E [K M] A0 A1 A2 RF. destruct (ff_store AL F0 h nb bl mo a W E K A0 A1 A2 RF) as [K' C']. split; [split; [exact K'| fr mo_frame_anon_grant]| exact C'].
    - intros h nb bl mo W E [K _]. exact (ff_room_n AL F0 h nb bl mo W E K).
    - intros h nb bl mo W E [K _]. exact (ff_room_s AL F0 h nb bl mo W E K).
    - exact (ff_cs_mono_fa AL F0). - exact (ff_cs_mono_u AL F0). - exact (ff_cs_rec_sec AL F0). - exact (ff_cs_mono_dep AL F0).
  Defined.

    End FR.

End ARUN_1.
