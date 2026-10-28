(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zlit := lazymatch goal with |- 0 <= ?x < _ => let v := eval vm_compute in x in change x with v end; lia.
Lemma tfib_val0_range : forall a, 0 <= tfib_val0 a < 2 ^ 64.
Proof.
intros a. unfold tfib_val0. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold tfib_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
- unfold tfib_hi. generalize (a - A_HI 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma tfib_val1_range : forall a, 0 <= tfib_val1 a < 2 ^ 64.
Proof.
intros a. unfold tfib_val1. destruct (Nat.eqb a A_TEXT); [zlit|].
destruct (Nat.ltb a (A_HI 0)).
- unfold tfib_obj. generalize (a - A_OBJ 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
- unfold tfib_hi. generalize (a - A_HI 0)%nat as m. intros m. do 40 (destruct m as [|m]; [zlit|]). zlit.
Qed.
Lemma tfib_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma tfib_segs_low0 : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma tfib_img_range0 : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg)) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tfib_img_cover0 : forall ly S md, ALedger tfibsegs ly S md -> fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros ly S md LG. split.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_000 ltac:(left; reflexivity)) as [H _]. cbn in H. lia.
- destruct (al_img _ _ _ _ LG Asan.Asan_segment_003 ltac:(do 3 right; left; reflexivity)) as [_ H]. cbn in H. lia.
Qed.
Lemma tfib_relro_img : forall a, 0x9da38 <= a < 0x9eca8 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma tfib_xcalls : forall s k, In (s, k) asan3_xcalls -> tfib_sigma s = tfib_val1 A_TEXT + k.
Proof. intros s k H. cbn in H. destruct H as [H|[H|[H|[]]]]; injection H as <- <-; vm_compute; reflexivity. Qed.
#[global] Instance PB2_tfib : PAImg2 lib_asan3_0_listing lib_asan3_1_listing asan3_xcalls := {|
pa2_segs := tfibsegs;
pa2_tbl := tfibtbl_lib;
pa2_tbl_ok := tfibtbl_lib_ok;
pa2_val0 := tfib_val0;
pa2_val1 := tfib_val1;
pa2_sigma := tfib_sigma;
pa2_cert0 := tfib_lib_check0;
pa2_cert1 := tfib_lib_check1;
pa2_B0_ok := ltac:(unfold tfib_val0, tfib_B0; cbn; lia);
pa2_B1_ok := ltac:(unfold tfib_val1, tfib_B1; cbn; lia);
pa2_val0_range := tfib_val0_range;
pa2_val01 := ltac:(intros a Ha; unfold tfib_val1, tfib_val0; destruct (Nat.eqb_spec a A_TEXT); [contradiction | reflexivity]);
pa2_wx := tfib_wx;
pa2_segs_low := tfib_segs_low0;
pa2_img_range := tfib_img_range0;
pa2_img_cover := tfib_img_cover0;
pa2_obj_img := ltac:(intros i Hi; do 13 (destruct i as [|i]; [unfold tfib_val0, tfib_obj, A_OBJ, A_TEXT, A_HI; cbn; lia|]); exfalso; lia);
pa2_relro_lo := 0x9da38;
pa2_relro_hi := 0x9eca8;
pa2_relro_img := tfib_relro_img;
pa2_xcalls := tfib_xcalls |}.
#[global] Instance PB_tfib : PAImg lib_asan3_0_listing := PI0_of (X2 := PB2_tfib).
#[global] Instance PB_tfib1 : PAImg lib_asan3_1_listing := PI1_of (X2 := PB2_tfib).
End c.
