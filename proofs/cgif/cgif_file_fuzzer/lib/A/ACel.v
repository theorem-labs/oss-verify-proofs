(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l ACej ACeh ACei.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Let HBgot := tl_got_shadow B TL.
Let HBcell := tl_shadow_cell B TL.
Lemma obj_at_kept : forall (m m' : word -> option byte) p lay vals sz,
obj_at tfibsegs m p lay vals -> lay_inside lay sz = true ->
(forall i, 0 <= i < sz -> mbyte tfibsegs m' (p + i) = mbyte tfibsegs m (p + i)) -> obj_at tfibsegs m' p lay vals.
Proof. intros m m' p lay vals sz H Hl Hk. exact (obj_at_transport_range tfibsegs m m' p lay vals sz H Hl Hk). Qed.
Lemma lay_inside_CGIF : lay_inside LAY_CGIF 96 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Frame : lay_inside LAY_Frame 40 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lay_inside_Raw : lay_inside LAY_Raw 48 = true. Proof. vm_compute. reflexivity. Qed.
Definition blk_kept (H H' : word -> bool) (m m' : word -> option byte) (b n : Z) : Prop :=
forall i, 0 <= i < n -> aview tfibsegs H' m' (b + i) = aview tfibsegs H m (b + i).
Lemma obj_at_blk_kept : forall H H' m m' p lay vals sz,
obj_at tfibsegs (mrestrict H m) p lay vals -> lay_inside lay sz = true -> blk_kept H H' m m' p sz ->
obj_at tfibsegs (mrestrict H' m') p lay vals.
Proof.
intros H H' m m' p lay vals sz Ho Hl Hk. apply (obj_at_kept _ _ p lay vals sz Ho Hl).
intros i Hi. apply (mbyte_of_aview tfibsegs). apply Hk. exact Hi.
Qed.
Lemma tcgif_at_kept : forall H H' m m' g s1,
tcgif_at (mrestrict H m) g s1 -> blk_kept H H' m m' g 96 -> blk_kept H H' m m' (cg_raw s1) 48 ->
(forall f, In (Some f) (cg_frames s1) -> blk_kept H H' m m' (fr_ptr f) 40) ->
tcgif_at (mrestrict H' m') g s1.
Proof.
intros H H' m m' g s1 (Hg & Hr & Hf) Kg Kr Kf. split; [|split].
- exact (obj_at_blk_kept H H' m m' g LAY_CGIF _ 96 Hg lay_inside_CGIF Kg).
- exact (obj_at_blk_kept H H' m m' (cg_raw s1) LAY_Raw _ 48 Hr lay_inside_Raw Kr).
- intros f Hin. exact (obj_at_blk_kept H H' m m' (fr_ptr f) LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame (Kf f Hin)).
Qed.
Lemma frames_blocks_in : forall N (fs : list (option frame_st)) i j f b,
(i <= j)%nat -> nth_error fs j = Some (Some f) -> In b (frame_blocks N f) -> In b (frames_blocks N (skipn i fs)).
Proof.
intros N fs. induction fs as [|o fs IH]; intros i j f b Hij Hj Hb; [destruct j; discriminate|].
destruct i as [|i].
- cbn [skipn]. destruct j as [|j]; cbn in Hj.
+ injection Hj as ->. cbn [frames_blocks flat_map]. apply in_or_app. left. exact Hb.
+ cbn [frames_blocks flat_map]. apply in_or_app. right. change (In b (frames_blocks N (skipn 0 fs))). eapply IH; [| exact Hj | exact Hb]. lia.
- destruct j as [|j]; [lia|]. cbn [skipn]. cbn in Hj. eapply IH; [| exact Hj | exact Hb]. lia.
Qed.
End c.
End a.
