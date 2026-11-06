(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fy X0fg X0d8 X0fq X0d7 X0ff.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X16j X161 X13t X16b X13s X160.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X160.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_frames_hi : forall Σ m f k, ART_A Σ m -> In (f, k) (frames Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f.
Proof.
intros Σ m f k HA Hin. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & _).
pose proof (fsb_grant Σ m HA) as (_ & _ & _ & G4 & _). unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. lia.
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
- intros Σ m a n HA H1 H2 H3. exact (rta_acc_stack Σ m HA a n H1 H2 H3).
- exact rta_acc_static.
- intros Σ m p n HA Hin. exact (rta_live_range Σ m p n HA Hin).
- intros Σ m p1 n1 p2 n2 l1 l2 HA E Hin. exact (rta_live_disj Σ m HA p1 n1 p2 n2 l1 l2 E Hin).
- intros Σ m f k HA Hin. exact (rta_frames_range Σ m HA f k Hin).
- exact rta_sp0_range.
- exact rta_sp0_win.
- intros Σ m f k fr HA E HPN. exact (rta_frame_release Σ m f k fr HA E HPN).
- intros Σ m f k HA Hin. exact (rta_frames_align Σ m HA f k Hin).
- intros Σ m f1 k1 f2 k2 l1 l2 HA E Hin. exact (rta_frames_disj Σ m HA f1 k1 f2 k2 l1 l2 E Hin).
- intros Σ m f k HA Hin. exact (rta_fshadow_apart Σ m HA f k Hin).
- intros Σ m HA. exact (rta_got_lib Σ m HA).
- exact rta_acc_lits.
- intros Σ m f k HA Hin. exact (rta_frames_hi Σ m f k HA Hin).
- intros Σ m p n HA Hin. exact (rta_live_offshadow Σ m p n HA Hin).
- intros Σ m HA. exact (rta_credit_nonneg Σ m HA).
- intros Σ m a n HA Hin. exact (rta_acc_pois Σ m HA a n Hin).
- intros Σ m _ HF. cbn [rt_pois rt_frames RTA] in *. unfold rtA_pois, rtA_frames in *. rewrite HF. reflexivity.
- intros Σ m a n HA Hin. exact (rta_pois_range Σ m HA a n Hin).
- intros Σ m p n HA Hin Hsz. exact (rta_live_small Σ m p n HA Hin Hsz).
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma rta_frames_hi : forall Σ m f k, ART_A Σ m -> In (f, k) (frames Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f.
Proof.
intros Σ m f k HA Hin. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & _).
pose proof (fsb_grant Σ m HA) as (_ & _ & _ & G4 & _). unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. lia.
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
- intros Σ m a n HA H1 H2 H3. exact (rta_acc_stack Σ m HA a n H1 H2 H3).
- exact rta_acc_static.
- intros Σ m p n HA Hin. exact (rta_live_range Σ m p n HA Hin).
- intros Σ m p1 n1 p2 n2 l1 l2 HA E Hin. exact (rta_live_disj Σ m HA p1 n1 p2 n2 l1 l2 E Hin).
- intros Σ m f k HA Hin. exact (rta_frames_range Σ m HA f k Hin).
- exact rta_sp0_range.
- exact rta_sp0_win.
- intros Σ m f k fr HA E HPN. exact (rta_frame_release Σ m f k fr HA E HPN).
- intros Σ m f k HA Hin. exact (rta_frames_align Σ m HA f k Hin).
- intros Σ m f1 k1 f2 k2 l1 l2 HA E Hin. exact (rta_frames_disj Σ m HA f1 k1 f2 k2 l1 l2 E Hin).
- intros Σ m f k HA Hin. exact (rta_fshadow_apart Σ m HA f k Hin).
- intros Σ m HA. exact (rta_got_lib Σ m HA).
- exact rta_acc_lits.
- intros Σ m f k HA Hin. exact (rta_frames_hi Σ m f k HA Hin).
- intros Σ m p n HA Hin. exact (rta_live_offshadow Σ m p n HA Hin).
- intros Σ m HA. exact (rta_credit_nonneg Σ m HA).
- intros Σ m a n HA Hin. exact (rta_acc_pois Σ m HA a n Hin).
- intros Σ m _ HF. cbn [rt_pois rt_frames RTA] in *. unfold rtA_pois, rtA_frames in *. rewrite HF. reflexivity.
- intros Σ m a n HA Hin. exact (rta_pois_range Σ m HA a n Hin).
- intros Σ m p n HA Hin Hsz. exact (rta_live_small Σ m p n HA Hin Hsz).
Qed.
