(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP09 YI04 YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5s YI5v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YC4a YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma cur_obj_tail : forall g s N rest i f, nth_error (cg_frames s) i = Some (Some f) ->
exists tail, Permutation (cgif_blocks g s N ++ rest) ((fr_ptr f, FRAME_SIZE) :: tail) /\
(Z.land (cg_attr s) 4 = 0 -> In (cg_pal s, 3 * cg_ngp s) tail) /\
In (fr_img f, N) tail /\ (Z.land (fr_attr f) 1 <> 0 -> In (fr_lpal f, 3 * fr_nlp f) tail) /\
(forall j fb, j <> i -> nth_error (cg_frames s) j = Some (Some fb) -> forall y, In y (frame_blocks N fb) -> In y tail).
Proof.
intros g s N rest i f Hf.
destruct (nth_error_split _ _ Hf) as (l1 & l2 & Hfr & Hl1).
set (lp := if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]).
set (A := (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1).
set (Bq := ((fr_img f, N) :: lp) ++ frames_blocks N l2 ++ rest).
exists (A ++ Bq).
split; [|split; [|split; [|split]]].
- replace (cgif_blocks g s N ++ rest) with (A ++ (fr_ptr f, FRAME_SIZE) :: Bq); [apply Permutation_sym; apply Permutation_middle|].
unfold cgif_blocks, A, Bq, lp. rewrite Hfr, frames_blocks_app, frames_blocks_cons_some. unfold frame_blocks at 1.
repeat (first [rewrite <- app_assoc | progress cbn [app]]). reflexivity.
- intros Ha. apply in_app_iff. left. unfold A. right. right. apply in_app_iff. left. unfold pal_blocks.
rewrite (proj2 (Z.eqb_eq _ _) Ha). left. reflexivity.
- apply in_app_iff. right. unfold Bq. left. reflexivity.
- intros Hz. apply in_app_iff. right. unfold Bq, lp. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [lia|]. left. reflexivity.
- intros j fb Hj Hfb y Hy.
assert (Hin : In (Some fb) l1 \/ In (Some fb) l2).
{ rewrite Hfr in Hfb. destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
- left. rewrite nth_error_app1 in Hfb by exact Hlt. eapply nth_error_In. exact Hfb.
- right. rewrite nth_error_app2 in Hfb by exact Hge.
destruct (j - length l1)%nat as [|k] eqn:Hk; [lia|]. cbn in Hfb. eapply nth_error_In. exact Hfb. }
apply in_app_iff. destruct Hin as [Hin | Hin].
+ left. unfold A. right. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some fb). split; [exact Hin | exact Hy].
+ right. unfold Bq. apply in_app_iff. right. apply in_app_iff. left. unfold frames_blocks. apply in_flat_map. exists (Some fb). split; [exact Hin | exact Hy].
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma sep_head_tail : forall ly S W mem md x tail y,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: tail) -> In y tail -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md x tail y HAR HP Hy. apply in_split in Hy as (t1 & t2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y (t1 ++ t2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma fp0_off_tail : forall ly S W mem md (f : frame_st) tail b n,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((fr_ptr f, FRAME_SIZE) :: tail) -> In (b, n) tail ->
forall a, b <= a < b + req_size n -> ~ inFP [(fr_ptr f + 20, fr_ptr f + 24)] a.
Proof.
intros ly S W mem md f tail b n HAR HP Hy a Ha (r & Hr0 & Hr).
pose proof (sep_head_tail ly S W mem md _ tail _ HAR HP Hy) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size FRAME_SIZE) with 40 in Hd.
cbn [In] in Hr0. destruct Hr0 as [<- | []]. cbn [fst snd] in Hr. lia.
Qed.
End e.
End d.
End c.
Lemma fl_img_trans : forall (G : YO07.gcfg) (cur b : YO07.frame) w h top left,
YO07.flag (fl_gen3 G cur (Some b)) 1 = true -> fl_dims G cur (Some b) = (w, h, top, left) ->
fl_img G cur (Some b) =
map (fun pq => if YO07.cmp_pixel G cur b (fst pq) (snd pq) then fst pq else fl_tOpt G cur)
(combine (fl_tmp G cur (Some b)) (YO07.window (YO07.g_w G) (YO07.f_img b) w h top left)).
Proof.
intros G cur b w h top left HF HD. unfold fl_img, fl_tidx, fl_w, fl_h, fl_top, fl_left. rewrite HF, HD. reflexivity.
Qed.
Lemma fl_tidx_trans : forall (G : YO07.gcfg) (cur b : YO07.frame),
YO07.flag (fl_gen3 G cur (Some b)) 1 = true -> fl_tidx G cur (Some b) = fl_tOpt G cur.
Proof. intros G cur b HF. unfold fl_tidx. rewrite HF. reflexivity. Qed.
Lemma length_mark : forall (F : Z * Z -> Z) (TMP WIN : list Z) n, Z.of_nat (length TMP) = n -> length WIN = Z.to_nat n ->
Z.of_nat (length (map F (combine TMP WIN))) = n.
Proof. intros F TMP WIN n H1 H2. rewrite length_map, length_combine, H2. lia. Qed.
