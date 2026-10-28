(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_state RT_rep RT_facts0 RT_sep RT_facts RT_release TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rta_frames_hi : forall Σ m f k, ART_A Σ m -> In (f, k) (frames Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f.
Proof.
  intros Σ m f k HA Hin. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & _).
  pose proof (fsb_grant Σ m HA) as (_ & _ & _ & G4 & _). unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. lia.
Qed.

(* [comment removed for export] *)
Lemma rta_lib_shadow : forall Σ m, ART_A Σ m -> Forall (fun r => bytes_at asegs m (fst r) (map (Z_to_bv 8) (snd r))) LIB_SHADOW.
Proof. intros Σ m HA. destruct (ART_shadow Σ m HA) as (_ & _ & _ & _ & LS & _). exact LS. Qed.

(* [comment removed for export] *)
Lemma rta_lib_ro : forall Σ m, ART_A Σ m -> Forall (fun p => ro_cells asegs m (fst p) (snd p)) LIB_RO.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat (apply proj2 in IC).
  assert (E : io_ro = firstn 11 io_ro ++ LIB_RO) by reflexivity.
  rewrite E in IC. apply Forall_app in IC as [_ IC]. exact IC.
Qed.

Theorem rta_art_facts : art_facts RTA.
Proof.
  apply mkAF.
  - exact rta_client_consts.
  - exact ART_client_frame.
  - exact rta_with_fds.
  - exact rta_mat_stable.
  - intros Σ m p n HA Hin. exact (rta_acc_live Σ m HA p n Hin).
  - intros Σ m p n HA Hin. exact (rta_live_slack Σ m HA p n Hin).
  - intros Σ m a n HA H1 H2. exact (rta_acc_stack Σ m HA a n H1 H2).
  - exact rta_acc_static.
  - intros Σ m p n HA Hin. exact (rta_live_range Σ m p n HA Hin).
  - intros Σ m p1 n1 p2 n2 l1 l2 HA E Hin. exact (rta_live_disj Σ m HA p1 n1 p2 n2 l1 l2 E Hin).
  - intros Σ m f k HA Hin. exact (rta_frames_range Σ m HA f k Hin).
  - exact rta_sp0_range.
  - exact rta_sp0_win.
  - intros Σ m f k fr HA E. exact (rta_frame_release Σ m f k fr HA E).
  - intros Σ m f k HA Hin. exact (rta_frames_align Σ m HA f k Hin).
  - intros Σ m f1 k1 f2 k2 l1 l2 HA E Hin. exact (rta_frames_disj Σ m HA f1 k1 f2 k2 l1 l2 E Hin).
  - intros Σ m f k HA Hin. exact (rta_fshadow_apart Σ m HA f k Hin).
  - intros Σ m HA. exact (rta_got_lib Σ m HA).
  - exact rta_lib_shadow.
  - exact rta_lib_ro.
  - intros Σ m f k HA Hin. exact (rta_frames_hi Σ m f k HA Hin).
Qed.
