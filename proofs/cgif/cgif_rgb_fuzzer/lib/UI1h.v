(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK15 YN06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ04 YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI03
UI1e UI39 UI1i UI20 UI56 YI0x.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition set_cur (s : cgif_st) (c : Z) : cgif_st :=
mkCgif (cg_frames s) (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) c (cg_ihead s)
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s).
Lemma set_cur_blocks : forall g s c N, cgif_blocks g (set_cur s c) N = cgif_blocks g s N.
Proof. intros. reflexivity. Qed.
Lemma set_cur_wf : forall s c N, cgif_wf s N -> cgif_wf (set_cur s c) N.
Proof. intros s c N H. exact H. Qed.
Lemma flush_upd_wf_frames : forall s i gen' rwcur', cg_frames (flush_upd s i gen' rwcur') =
list_set (cg_frames s) i (option_map (fun f => set_fr_gen f gen') (nth i (cg_frames s) None)).
Proof. intros. reflexivity. Qed.
Definition LAY15 : layout_t := firstn 15 LAY_CGIF.
Definition LAY2 : layout_t := [(88, 4%N); (92, 4%N)].
Lemma LAY_CGIF_split : LAY_CGIF = LAY15 ++ LAY2.
Proof. reflexivity. Qed.
Lemma LAY15_ok : lay_inside LAY15 88 = true /\ lay_widths_ok LAY15 = true.
Proof. split; reflexivity. Qed.
Definition vals15 (s : cgif_st) : list Z := firstn 15 (cgif_vals s).
Lemma cgif_vals_split : forall s, cgif_vals s = vals15 s ++ [cg_cur s; cg_ihead s].
Proof. intros s. reflexivity. Qed.
Lemma cgif_vals_set_cur : forall s c, cgif_vals (set_cur s c) = vals15 s ++ [c; cg_ihead s].
Proof. intros s c. reflexivity. Qed.

Lemma obj_cgif_join : forall m g v15 c ih,
obj_at ubs2segs m g LAY15 v15 ->
val_mem ubs2segs m (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
val_mem ubs2segs m (g + 92) 4 ih -> 0 <= ih < 2 ^ 32 ->
obj_at ubs2segs m g LAY_CGIF (v15 ++ [c; ih]).
Proof.
intros m g v15 c ih H15 Hc Rc Hi Ri.
rewrite LAY_CGIF_split. apply (proj2 (obj_at_app ubs2segs m g LAY15 LAY2 v15 [c; ih] ltac:(rewrite (obj_at_length _ _ _ _ _ H15); reflexivity))).
split; [exact H15|]. cbn. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
change (2 ^ (8 * 4)) with (2 ^ 32). repeat split; try assumption; lia.
Qed.
Lemma obj_cgif_parts : forall m g s,
obj_at ubs2segs m g LAY_CGIF (cgif_vals s) ->
obj_at ubs2segs m g LAY15 (vals15 s) /\ val_mem ubs2segs m (g + 88) 4 (cg_cur s) /\ 0 <= cg_cur s < 2 ^ 32 /\
val_mem ubs2segs m (g + 92) 4 (cg_ihead s) /\ 0 <= cg_ihead s < 2 ^ 32.
Proof.
intros m g s H. rewrite LAY_CGIF_split, cgif_vals_split in H.
apply (proj1 (obj_at_app ubs2segs m g LAY15 LAY2 (vals15 s) [cg_cur s; cg_ihead s] eq_refl)) in H as [H15 H2].
split; [exact H15|]. cbn in H2. unfold field_ok in H2. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in H2.
change (2 ^ (8 * 4)) with (2 ^ 32) in H2. tauto.
Qed.
Lemma obj_cgif_set_cur : forall m m' g s c,
obj_at ubs2segs m g LAY_CGIF (cgif_vals s) ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte ubs2segs m' (g + i) = mbyte ubs2segs m (g + i)) ->
val_mem ubs2segs m' (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
obj_at ubs2segs m' g LAY_CGIF (cgif_vals (set_cur s c)).
Proof.
intros m m' g s c H Hk Hc Rc. rewrite cgif_vals_set_cur.
destruct (obj_cgif_parts m g s H) as (H15 & _ & _ & Hi & Ri).
apply obj_cgif_join; [| exact Hc | exact Rc | | exact Ri].
- eapply obj_at_transport_range; [exact H15 | exact (proj1 LAY15_ok) |]. intros i Hi'. apply Hk; lia.
- intros k Hk'. rewrite <- (Hi k Hk'). replace (g + 92 + Z.of_nat k) with (g + (92 + Z.of_nat k)) by lia. apply Hk; lia.
Qed.
Lemma cgif_at_set_cur : forall m m' g s c,
cgif_at m g s ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte ubs2segs m' (g + i) = mbyte ubs2segs m (g + i)) ->
(forall i, 0 <= i < RAW_SIZE -> mbyte ubs2segs m' (cg_raw s + i) = mbyte ubs2segs m (cg_raw s + i)) ->
(forall f i, In (Some f) (cg_frames s) -> 0 <= i < FRAME_SIZE -> mbyte ubs2segs m' (fr_ptr f + i) = mbyte ubs2segs m (fr_ptr f + i)) ->
val_mem ubs2segs m' (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
cgif_at m' g (set_cur s c).
Proof.
intros m m' g s c (Hg & Hr & Hf) Hkg Hkr Hkf Hc Rc. split; [|split].
- apply (obj_cgif_set_cur m m' g s c Hg Hkg Hc Rc).
- cbn [cg_raw set_cur]. eapply obj_at_transport_range; [exact Hr | exact (proj1 LAY_Raw_ok) | exact Hkr].
- cbn [cg_frames set_cur]. intros f Hin. eapply obj_at_transport_range; [exact (Hf f Hin) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. apply Hkf; [exact Hin | exact Hi].
Qed.
Definition frames_at (m : word -> option byte) (fs : list (option frame_st)) : Prop :=
forall f, In (Some f) fs -> obj_at ubs2segs m (fr_ptr f) LAY_Frame (frame_vals f).
Lemma frames_at_kept : forall m m' fs,
frames_at m fs ->
(forall f i, In (Some f) fs -> 0 <= i < FRAME_SIZE -> mbyte ubs2segs m' (fr_ptr f + i) = mbyte ubs2segs m (fr_ptr f + i)) ->
frames_at m' fs.
Proof.
intros m m' fs H Hk f Hin. eapply obj_at_transport_range; [exact (H f Hin) | exact (proj1 LAY_Frame_ok) |].
intros i Hi. apply Hk; [exact Hin | exact Hi].
Qed.
Lemma frames_at_tl : forall m o fs, frames_at m (o :: fs) -> frames_at m fs.
Proof. intros m o fs H f Hin. apply H. right. exact Hin. Qed.
Lemma inFP_blocks_fp : forall bl a, inFP (blocks_fp bl) a <-> exists b n, In (b, n) bl /\ b <= a < b + n.
Proof.
intros bl a. unfold inFP, blocks_fp. split.
- intros (r & Hr & Ha). apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha. exists b, n. auto.
- intros (b & n & Hin & Ha). exists (b, b + n). split; [| cbn; lia]. apply in_map_iff. exists (b, n). auto.
Qed.
Lemma frame_blocks_in_cgif : forall g s N f b n,
In (Some f) (cg_frames s) -> In (b, n) (frame_blocks N f) -> In (b, n) (cgif_blocks g s N).
Proof.
intros g s N f b n Hf Hb. unfold cgif_blocks. right. right. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). auto.
Qed.
Lemma frames_blocks_cons_some : forall N f fs, frames_blocks N (Some f :: fs) = frame_blocks N f ++ frames_blocks N fs.
Proof. intros. reflexivity. Qed.
Lemma frames_blocks_cons_none : forall N fs, frames_blocks N (None :: fs) = frames_blocks N fs.
Proof. intros. reflexivity. Qed.
Lemma perm_front_mid : forall {X} (x : X) (p a b r : list X),
Permutation (x :: p ++ (a ++ b) ++ r) (a ++ (x :: p ++ b ++ r)).
Proof.
intros X x p a b r. rewrite <- app_assoc. change (x :: p ++ a ++ b ++ r) with ((x :: p) ++ a ++ (b ++ r)).
change (x :: p ++ b ++ r) with ((x :: p) ++ (b ++ r)). apply Permutation_app_swap_app.
Qed.
Lemma flush_upd_frames_shape : forall s i gen' rwcur' k,
frame_ptr (nth k (cg_frames (flush_upd s i gen' rwcur')) None) = frame_ptr (nth k (cg_frames s) None).
Proof.
intros s i gen' rwcur' k. rewrite flush_upd_wf_frames.
revert i k. generalize (cg_frames s) as l. induction l as [|o l IH]; intros [|i] [|k]; cbn; try reflexivity.
- destruct o; reflexivity.
- apply IH.
Qed.
Lemma nth_error_list_set_same : forall {X} (l : list X) i x, (i < length l)%nat -> nth_error (list_set l i x) i = Some x.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_error_list_set_other : forall {X} (l : list X) i j x, i <> j -> nth_error (list_set l i x) j = nth_error l j.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [exfalso; lia|]. apply IH. lia.
Qed.
Lemma nth_list_set_other : forall {X} (l : list X) i j x d, i <> j -> nth j (list_set l i x) d = nth j l d.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x d Hij; cbn; try reflexivity; [exfalso; lia|]. apply IH. lia.
Qed.
Lemma length_list_set : forall {X} (l : list X) i x, length (list_set l i x) = length l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

End e.
