(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts0 RT_sep RT_facts RT_release.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Lemma rta_frames_hi : forall Σ m f k, ART_A Σ m -> In (f, k) (frames Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f.
Proof.
  intros Σ m f k HA Hin. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & _).
  pose proof (fsb_grant Σ m HA) as (_ & _ & _ & G4 & _). unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. lia.
Qed.

Theorem rta_art_facts : art_facts RTA.
Proof.
  apply mkAF.
  - exact rta_client_consts.
  - exact ART_client_frame_vis.
  - exact rta_with_fds.
  - exact rta_mat_stable.
  - intros Σ m p n HA Hin. exact (rta_acc_live Σ m HA p n Hin).
  - intros Σ m p n HA Hin. exact (rta_live_slack Σ m HA p n Hin).
  - intros Σ m a n HA H1 H2. exact (rta_acc_stack Σ m HA a n H1 H2).
  - exact rta_acc_static.
  - intros Σ m p n HA Hin. exact (rta_live_range_vis Σ m HA p n Hin).
  - intros Σ m p1 n1 p2 n2 l1 l2 HA E Hin. exact (rta_live_disj Σ m HA p1 n1 p2 n2 l1 l2 E Hin).
  - intros Σ m f k HA Hin. exact (rta_frames_range_vis Σ m HA f k Hin).
  - exact rta_sp0_range.
  - exact rta_sp0_win.
  - intros Σ m f k fr HA E. exact (rta_frame_release_vis Σ m f k fr HA E).
  - intros Σ m f k HA Hin. exact (rta_frames_align Σ m HA f k Hin).
  - intros Σ m f1 k1 f2 k2 l1 l2 HA E Hin. exact (rta_frames_disj Σ m HA f1 k1 f2 k2 l1 l2 E Hin).
  - intros Σ m f k HA Hin. exact (rta_fshadow_apart_vis Σ m HA f k Hin).
  - intros Σ m HA. exact (rta_got_lib Σ m HA).
  - exact rta_acc_lits.
  - intros Σ m f k HA Hin. exact (rta_frames_hi Σ m f k HA Hin).
Qed.

End GWIN.
