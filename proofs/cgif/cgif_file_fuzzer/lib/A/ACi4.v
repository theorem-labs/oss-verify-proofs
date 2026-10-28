(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5s YI5v YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC7x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma aftok_mono : forall FP FP' bl b, aftok FP bl b -> (forall a, inFP FP a -> inFP FP' a) -> aftok FP' bl b.
Proof. intros FP FP' bl b H Hm Hin i Hi. apply Hm. exact (H Hin i Hi). Qed.
Lemma flag_raw_attr_of : forall a, YO07.flag (raw_attr_of a) 1 = YO07.flag a 2.
Proof. intros a. unfold raw_attr_of, YO07.flag. destruct (Z.land a 2 =? 0), (Z.land a 16 =? 0); reflexivity. Qed.
Lemma raw_sgct_model : forall s GPAL, raw_sgct s = (if YO07.flag (YO07.g_attr (gcfg_of s GPAL)) 4 then 0 else YO07.g_ngp (gcfg_of s GPAL)).
Proof. intros s GPAL. unfold raw_sgct, YO07.flag. cbn. destruct (Z.land (cg_attr s) 4 =? 0); reflexivity. Qed.
Lemma perm_pull4 : forall {A} (a b c p : A) (l r1 r2 : list A),
Permutation l (a :: b :: c :: r1 ++ p :: r2) -> Permutation l (a :: b :: c :: p :: r1 ++ r2).
Proof.
intros A a b c p l r1 r2 H. eapply Permutation_trans; [exact H|]. do 3 apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma flush_blocks_imgX0 : forall g s N rest i f pf, nth_error (cg_frames s) i = Some (Some f) -> In (pf, FILE_BLOCK) rest ->
exists rest0, Permutation (cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (fr_img f, N) :: (pf, FILE_BLOCK) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest i f pf Hf Hpf.
destruct (in_split _ _ Hpf) as (r1 & r2 & ->).
destruct (flush_blocks_img0 g s N (r1 ++ r2) i f Hf) as (rest0 & HP & Hl).
exists rest0. split; [|exact Hl].
eapply Permutation_trans; [| do 3 apply perm_skip; apply Permutation_refl].
eapply Permutation_trans.
{ apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle. }
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
eapply Permutation_trans; [apply perm_skip; exact HP|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
Qed.
Lemma flush_blocks_imgX1 : forall g s N rest f p Nt pf, In (Some f) (cg_frames s) -> In (pf, FILE_BLOCK) rest ->
exists rest0, Permutation ((p, Nt) :: cgif_blocks g s N ++ rest) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (p, Nt) :: (pf, FILE_BLOCK) :: rest0) /\
(Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) rest0).
Proof.
intros g s N rest f p Nt pf Hf Hpf.
destruct (in_split _ _ Hpf) as (r1 & r2 & ->).
destruct (flush_blocks_img1 g s N (r1 ++ r2) f p Nt Hf) as (rest0 & HP & Hl).
exists rest0. split; [|exact Hl].
eapply Permutation_trans; [| do 3 apply perm_skip; apply Permutation_refl].
eapply Permutation_trans.
{ apply perm_skip. apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle. }
eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|].
eapply Permutation_trans; [apply perm_swap|].
eapply Permutation_trans; [apply perm_skip; exact HP|].
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
Qed.
Lemma perm_two_front : forall {A} (l : list A) l1 a b l2, Permutation l (l1 ++ a :: b :: l2) -> Permutation l (a :: b :: l1 ++ l2).
Proof.
intros A l l1 a b l2 H. eapply Permutation_trans; [exact H|].
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma frame_blocks_front : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) ->
exists r, Permutation (cgif_blocks g s N ++ rest) ((fr_ptr f, FRAME_SIZE) :: (fr_img f, N) :: r).
Proof.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
eexists. apply perm_two_front with (l1 := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1).
unfold cgif_blocks. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
cbn [app]. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
Qed.
Lemma perm_three_front : forall {A} (l : list A) l1 a b c l2, Permutation l (l1 ++ a :: b :: c :: l2) -> Permutation l (a :: c :: b :: l1 ++ l2).
Proof.
intros A l l1 a b c l2 H. eapply Permutation_trans; [exact H|].
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip.
eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
eapply Permutation_trans; [apply perm_skip; apply Permutation_sym; apply Permutation_middle|]. apply perm_swap.
Qed.
Lemma frame_blocks_front3 : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) -> Z.land (fr_attr f) 1 <> 0 ->
exists r, Permutation (cgif_blocks g s N ++ rest) ((fr_ptr f, FRAME_SIZE) :: (fr_lpal f, 3 * fr_nlp f) :: (fr_img f, N) :: r).
Proof.
intros g s N rest i f Hf Hz.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
eexists. apply perm_three_front with (l1 := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1).
unfold cgif_blocks. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|].
cbn [app]. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl.
Qed.
Lemma fl_fp0_out_frame : forall (f : frame_st) (p : Z) i,
(p + 40 <= fr_ptr f + 20 \/ fr_ptr f + 24 <= p) -> 0 <= i < 40 -> ~ inFP [(fr_ptr f + 20, fr_ptr f + 24)] (p + i).
Proof. intros f p i H1 Hi (r & Hr & Ha). cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd] in Ha; lia. Qed.
