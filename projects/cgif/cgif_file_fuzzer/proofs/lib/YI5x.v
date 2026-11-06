(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04 YI09 YI08 YI0m YI5w YI5z YI67 YI5v YI5s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma frame_vals_set_fr_gen : forall f v, frame_vals (set_fr_gen f v) = list_set (frame_vals f) 3 v.
Proof. intros. reflexivity. Qed.
Lemma fr_ptr_set_fr_gen : forall f v, fr_ptr (set_fr_gen f v) = fr_ptr f. Proof. reflexivity. Qed.
Lemma cg_raw_flush_upd : forall s i gen rcur, cg_raw (flush_upd s i gen rcur) = cg_raw s. Proof. reflexivity. Qed.
Lemma cg_frames_flush_upd : forall s i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) ->
cg_frames (flush_upd s i gen rcur) = list_set (cg_frames s) i (Some (set_fr_gen f gen)).
Proof.
intros s i gen rcur f H. rewrite flush_upd_wf_frames. rewrite (nth_error_nth _ _ None H). reflexivity.
Qed.
Lemma In_frames_flush_upd : forall s i gen rcur f x,
nth_error (cg_frames s) i = Some (Some f) ->
In (Some x) (cg_frames (flush_upd s i gen rcur)) -> x = set_fr_gen f gen \/ (In (Some x) (cg_frames s) /\ exists j, nth_error (cg_frames s) j = Some (Some x) /\ j <> i).
Proof.
intros s i gen rcur f x Hf Hin. rewrite (cg_frames_flush_upd s i gen rcur f Hf) in Hin.
apply In_list_set in Hin as [H | (j & Hj & Hne)]; [left; congruence | right]. split; [eapply nth_error_In; exact Hj | exists j; auto].
Qed.
Lemma cgif_wf_flush_upd : forall s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_wf s N -> cgif_wf (flush_upd s i gen rcur) N.
Proof.
intros s N i gen rcur f Hf (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold cgif_wf. rewrite (cg_frames_flush_upd s i gen rcur f Hf). cbn -[list_set Z.mul Z.land].
rewrite length_list_set. repeat (split; [assumption|]). split.
- destruct Hih as [H1 | [H2 Hn1]]; [left; exact H1 | right]. split; [exact H2|].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by exact Hne. exact Hn1.
- intros x Hx. apply In_list_set in Hx as [Hx1 | (j & Hj & _)].
+ injection Hx1 as ->. apply (frame_wf_fields (cg_attr s) f); [apply Hfwf; eapply nth_error_In; exact Hf | reflexivity | reflexivity].
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma cgif_blocks_flush_upd : forall g s N i gen rcur f,
nth_error (cg_frames s) i = Some (Some f) -> cgif_blocks g (flush_upd s i gen rcur) N = cgif_blocks g s N.
Proof.
intros g s N i gen rcur f Hf. apply flush_upd_blocks. apply (proj1 (nth_error_Some _ _)). rewrite Hf. discriminate.
Qed.
Lemma perm_img_front : forall {X} (g r x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (r :: g :: i :: (pal ++ F1 ++ x :: pf ++ F2) ++ rest).
Proof.
intros.
assert (E1 : g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest = (g :: r :: pal ++ F1 ++ [x]) ++ i :: ((pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
assert (E2 : r :: g :: i :: (pal ++ F1 ++ x :: pf ++ F2) ++ rest = r :: g :: i :: (pal ++ F1 ++ [x]) ++ ((pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
change (i :: (g :: r :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest) with ((i :: g :: r :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest).
change (r :: g :: i :: (pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest) with ((r :: g :: i :: pal ++ F1 ++ [x]) ++ (pf ++ F2) ++ rest).
apply Permutation_app_tail.
eapply Permutation_trans; [apply perm_swap|]. eapply Permutation_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap.
Qed.
Lemma flush_blocks_img0 : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) ->
exists rest0, Permutation (cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f, N) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
exists ((pal_blocks s ++ frames_blocks N l1 ++ (fr_ptr f, FRAME_SIZE) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) ++ frames_blocks N l2) ++ rest).
split.
- unfold cgif_blocks. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
cbn [app]. apply perm_img_front.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right. apply in_app_iff. right. right.
apply in_app_iff. left. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
Lemma flush_blocks_img1 : forall g s N rest f p Nt, In (Some f) (cg_frames s) ->
exists rest0, Permutation ((p, Nt) :: cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (p, Nt) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest f p Nt Hf.
exists ((pal_blocks s ++ frames_blocks N (cg_frames s)) ++ rest). split.
- unfold cgif_blocks. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply perm_swap|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
- intros Ha. apply in_app_iff. left. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf|].
unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
Qed.
End c.