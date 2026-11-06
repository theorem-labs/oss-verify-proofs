(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5s.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YI09 YI08 YI0m YI5w YI5z YI67 YI5v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition set_frames (s : cgif_st) (fr : list (option frame_st)) : cgif_st :=
mkCgif fr (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) (cg_ihead s)
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s).
Definition set_ihead (s : cgif_st) (ih : Z) : cgif_st :=
mkCgif (cg_frames s) (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) (cg_cur s) ih
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s).
Definition set_fr_delay (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) (fr_gen f) v (fr_nlp f) (fr_ctidx f) (fr_disp f) (fr_tidx f).
Definition set_fr_tidx (f : frame_st) (v : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) (fr_gen f) (fr_delay f) (fr_nlp f) (fr_ctidx f) (fr_disp f) v.
Definition set_fr_gen_disp (f : frame_st) (gen disp : Z) : frame_st :=
mkFrame (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) gen (fr_delay f) (fr_nlp f) (fr_ctidx f) disp (fr_tidx f).
Lemma cgif_blocks_set_frames : forall g s fr N,
cgif_blocks g (set_frames s fr) N = (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N fr.
Proof. intros. reflexivity. Qed.
Lemma frame_blocks_set_fr_delay : forall N f v, frame_blocks N (set_fr_delay f v) = frame_blocks N f.
Proof. intros. reflexivity. Qed.
Lemma frames_blocks_app : forall N l1 l2, frames_blocks N (l1 ++ l2) = frames_blocks N l1 ++ frames_blocks N l2.
Proof. intros N l1 l2. unfold frames_blocks. rewrite flat_map_app. reflexivity. Qed.
Lemma frames_blocks_3 : forall N o0 o1 o2,
frames_blocks N [o0; o1; o2] = frames_blocks N [o0] ++ frames_blocks N [o1] ++ frames_blocks N [o2].
Proof. intros. unfold frames_blocks. cbn. rewrite !app_nil_r. reflexivity. Qed.
Lemma frames_blocks_some : forall N f, frames_blocks N [Some f] = frame_blocks N f.
Proof. intros. unfold frames_blocks. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma frames_blocks_none : forall N, frames_blocks N [None] = [].
Proof. intros. reflexivity. Qed.
Lemma cgif_wf_intro : forall s fr cur ih N,
cgif_wf s N -> length fr = 3%nat ->
(ih = 1 \/ (ih = 2 /\ nth 1 fr None <> None)) ->
(forall f, In (Some f) fr -> frame_wf (cg_attr s) f) ->
cgif_wf (mkCgif fr (cg_pal s) (cg_attr s) (cg_gen s) (cg_W s) (cg_H s) (cg_ngp s) (cg_loops s) (cg_raw s) cur ih
(rw_gct s) (rw_attr s) (rw_loops s) (rw_cur s)) N.
Proof.
intros s fr cur ih N (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf) Hl Hi Hf.
unfold cgif_wf. cbn. repeat (split; [assumption|]). exact Hf.
Qed.
Section u.
Variable segs : list Segment.
Lemma obj_at_of_fields : forall mem a lay vals,
length vals = length lay ->
(forall j f v, nth_error lay j = Some f -> nth_error vals j = Some v -> field_ok segs mem a f v) ->
obj_at segs mem a lay vals.
Proof.
intros mem a lay. induction lay as [|f lay IH]; intros [|v vals] Hlen HF; cbn in Hlen |- *; try discriminate; [exact I|].
split; [exact (HF 0%nat f v eq_refl eq_refl)|].
apply IH; [lia|]. intros j f' v' Hf Hv. exact (HF (S j) f' v' Hf Hv).
Qed.
End u.
Lemma af_frames_blocks_ptr_in : forall N fs f, In (Some f) fs -> In (fr_ptr f, FRAME_SIZE) (frames_blocks N fs).
Proof. intros N fs f H. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact H | left; reflexivity]. Qed.
Lemma perm_frame_front : forall {X} (g r x i : X) (pal F1 pf F2 rest : list X),
Permutation (g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest) (x :: g :: r :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest).
Proof.
intros.
assert (E1 : g :: r :: (pal ++ F1 ++ x :: i :: pf ++ F2) ++ rest = (g :: r :: pal ++ F1) ++ x :: ((i :: pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
assert (E2 : x :: g :: r :: (pal ++ F1 ++ i :: pf ++ F2) ++ rest = x :: (g :: r :: pal ++ F1) ++ ((i :: pf ++ F2) ++ rest)).
{ cbn. rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. reflexivity. }
rewrite E1, E2. apply Permutation_sym. apply Permutation_middle.
Qed.
Section b0.
Variable segs : list Segment.
Definition in_wins (wins : list (Z * Z)) (i : Z) : bool := existsb (fun w => (fst w <=? i) && (i <? snd w)) wins.
Fixpoint lay_upd_ok (lay : layout_t) (j0 : nat) (js : list nat) (wins : list (Z * Z)) : bool :=
match lay with
| [] => true
| f :: lay' =>
(existsb (Nat.eqb j0) js
|| forallb (fun i => negb (in_wins wins (fst f + Z.of_nat i))) (seq 0 (N.to_nat (snd f))))
&& lay_upd_ok lay' (S j0) js wins
end.
Lemma field_ok_kept : forall m m' a f v,
field_ok segs m a f v -> (forall i, 0 <= i < Z.of_N (snd f) -> mbyte segs m' (a + fst f + i) = mbyte segs m (a + fst f + i)) ->
field_ok segs m' a f v.
Proof.
intros m m' a [o w] v [Hv Hr] Hk. split; [|exact Hr]. cbn [fst snd] in *.
intros k Hk'. rewrite Hk by lia. apply Hv. exact Hk'.
Qed.
Lemma in_wins_cons_false : forall lo hi wins i, in_wins ((lo, hi) :: wins) i = false -> (i < lo \/ hi <= i) /\ in_wins wins i = false.
Proof.
intros lo hi wins i H. unfold in_wins in H. cbn [existsb fst snd] in H. apply orb_false_elim in H as [H1 H2].
split; [|exact H2]. destruct (Z.leb_spec lo i); destruct (Z.ltb_spec i hi); cbn in H1; try discriminate; lia.
Qed.
Lemma obj_at_upd_gen : forall m m' a lay j0 vals vals' js wins,
obj_at segs m a lay vals -> lay_upd_ok lay j0 js wins = true -> length vals' = length vals ->
(forall i, (exists f, In f lay /\ fst f <= i < fst f + Z.of_N (snd f)) -> in_wins wins i = false -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
(forall j f v', In (j0 + j)%nat js -> nth_error lay j = Some f -> nth_error vals' j = Some v' -> field_ok segs m' a f v') ->
(forall j, ~ In (j0 + j)%nat js -> nth_error vals' j = nth_error vals j) ->
obj_at segs m' a lay vals'.
Proof.
intros m m' a lay. induction lay as [|f lay IH]; intros j0 [|v vals] [|v' vals'] js wins Hobj Hok Hlen Hkeep Hupd Hsame;
cbn in Hobj, Hlen |- *; first [exact I | discriminate Hlen | destruct Hobj; fail | idtac].
cbn [lay_upd_ok] in Hok. apply andb_prop in Hok as [Hf Hok].
destruct Hobj as [Hfv Hobj]. split.
- destruct (existsb (Nat.eqb j0) js) eqn:Hin.
+ apply existsb_exists in Hin as (j' & Hj' & Heq). apply Nat.eqb_eq in Heq. subst j'.
apply (Hupd 0%nat f v'); [rewrite Nat.add_0_r; exact Hj' | reflexivity | reflexivity].
+ cbn [orb] in Hf.
assert (Hv' : Some v' = Some v).
{ change (nth_error (v' :: vals') 0 = nth_error (v :: vals) 0). apply Hsame. rewrite Nat.add_0_r.
intros Hj. assert (existsb (Nat.eqb j0) js = true) by (apply existsb_exists; exists j0; split; [exact Hj | apply Nat.eqb_refl]). congruence. }
injection Hv' as ->. apply (field_ok_kept m m' a f v Hfv).
intros i Hi. replace (a + fst f + i) with (a + (fst f + i)) by lia. apply Hkeep.
* exists f. split; [left; reflexivity | lia].
* pose proof (proj1 (forallb_forall _ _) Hf (Z.to_nat i) ltac:(apply in_seq; lia)) as Hb. cbn beta in Hb.
rewrite Z2Nat.id in Hb by lia. destruct (in_wins wins (fst f + i)); [discriminate | reflexivity].
- apply (IH (S j0) vals vals' js wins Hobj Hok ltac:(lia)).
+ intros i (f' & Hf' & Hi) Hw. apply Hkeep; [| exact Hw]. exists f'. split; [right; exact Hf' | exact Hi].
+ intros j f' v'' Hj Hf' Hv''. apply (Hupd (S j) f' v''); [rewrite Nat.add_succ_r; exact Hj | exact Hf' | exact Hv''].
+ intros j Hj. apply (Hsame (S j)). rewrite Nat.add_succ_r. exact Hj.
Qed.
Lemma obj_at_upd : forall m m' a lay sz vals vals' js wins,
obj_at segs m a lay vals -> lay_inside lay sz = true -> lay_upd_ok lay 0 js wins = true -> length vals' = length vals ->
(forall i, 0 <= i < sz -> in_wins wins i = false -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
(forall j f v', In j js -> nth_error lay j = Some f -> nth_error vals' j = Some v' -> field_ok segs m' a f v') ->
(forall j, ~ In j js -> nth_error vals' j = nth_error vals j) ->
obj_at segs m' a lay vals'.
Proof.
intros m m' a lay sz vals vals' js wins Hobj Hin Hok Hlen Hkeep Hupd Hsame.
apply (obj_at_upd_gen m m' a lay 0 vals vals' js wins Hobj Hok Hlen).
- intros i (f & Hf & Hi) Hw. apply Hkeep; [|exact Hw].
unfold lay_inside in Hin. pose proof (proj1 (forallb_forall _ _) Hin f Hf) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
- exact Hupd.
- exact Hsame.
Qed.
End b0.
Definition chunks_between (lo hi : Z) (cs : list YP09.chunk) : list YP09.chunk :=
List.filter (fun c => (lo <=? c_off c) && (c_off c <? hi)) cs.
Lemma region_ok_part : forall segs E mem b lo0 hi0 wlo0 whi0 cs lo hi wlo whi,
region_ok segs E mem (YP09.mkRegion b lo0 hi0 wlo0 whi0 cs) -> lo0 <= lo -> hi <= hi0 ->
(forall i, wlo <= i < whi -> writable_at segs mem (base_val E b + i)) ->
region_ok segs E mem (YP09.mkRegion b lo hi wlo whi (chunks_between lo hi cs)).
Proof.
intros segs E mem b lo0 hi0 wlo0 whi0 cs lo hi wlo whi (R1 & R2 & R3 & R4) Hlo Hhi Hw.
unfold region_ok in *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks] in *.
split; [lia|]. split; [lia|]. split; [exact Hw|].
unfold chunks_between. apply incl_Forall with (l1 := cs); [apply incl_filter | exact R4].
Qed.
Lemma lay_inside_FrameConfig : lay_inside LAY_FrameConfig 32 = true.
Proof. reflexivity. Qed.
Definition upd_frame (s : cgif_st) (i : nat) (f' : frame_st) : cgif_st := set_frames s (list_set (cg_frames s) i (Some f')).
Lemma nth_list_set_same : forall {X} (l : list X) i x d, (i < length l)%nat -> nth i (list_set l i x) d = x.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x d Hi; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.
Lemma In_list_set : forall {X} (l : list X) i x y, In y (list_set l i x) -> y = x \/ exists j, nth_error l j = Some y /\ j <> i.
Proof.
intros X l. induction l as [|z l IH]; intros [|i] x y H; cbn in H.
- destruct H.
- destruct H.
- destruct H as [<-|H]; [left; reflexivity|]. right. destruct (In_nth_error _ _ H) as [j Hj]. exists (S j). split; [exact Hj | lia].
- destruct H as [<-|H]; [right; exists 0%nat; split; [reflexivity | lia]|].
destruct (IH i x y H) as [->|(j & Hj & Hne)]; [left; reflexivity|]. right. exists (S j). split; [exact Hj | lia].
Qed.
Lemma frames_blocks_upd : forall N l i f f',
nth_error l i = Some (Some f) -> frame_blocks N f' = frame_blocks N f -> frames_blocks N (list_set l i (Some f')) = frames_blocks N l.
Proof.
intros N l. induction l as [|o l IH]; intros [|i] f f' Hi Hb; cbn in Hi; try discriminate.
- injection Hi as ->. cbn [list_set]. rewrite !frames_blocks_cons_some. rewrite Hb. reflexivity.
- cbn [list_set]. unfold frames_blocks in *. cbn [flat_map]. rewrite (IH i f f' Hi Hb). reflexivity.
Qed.
Lemma cgif_blocks_upd_frame : forall g s N i f f',
nth_error (cg_frames s) i = Some (Some f) -> frame_blocks N f' = frame_blocks N f -> cgif_blocks g (upd_frame s i f') N = cgif_blocks g s N.
Proof.
intros g s N i f f' Hi Hb. unfold upd_frame. rewrite cgif_blocks_set_frames. unfold cgif_blocks.
rewrite (frames_blocks_upd N _ i f f' Hi Hb). reflexivity.
Qed.
Lemma cgif_wf_upd_frame : forall s N i f f',
cgif_wf s N -> nth_error (cg_frames s) i = Some (Some f) -> frame_wf (cg_attr s) f' -> cgif_wf (upd_frame s i f') N.
Proof.
intros s N i f f' Hwf Hi Hf'. pose proof Hwf as (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold upd_frame, set_frames. apply cgif_wf_intro; [exact Hwf | rewrite length_list_set; exact Hlen | |].
- destruct Hih as [H1|[H2 Hn1]]; [left; exact H1 | right; split; [exact H2|]].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by lia. exact Hn1.
- intros x Hx. destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
+ injection Hx' as ->. exact Hf'.
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma frame_wf_fields : forall gattr f f',
frame_wf gattr f -> fr_attr f' = fr_attr f -> fr_disp f' = fr_disp f -> frame_wf gattr f'.
Proof. intros gattr f f' [H1 H2] Ha Hd. split; [rewrite Ha; exact H1 | rewrite Hd; exact H2]. Qed.
Lemma nth_error_upd_frame_same : forall s i (f : option frame_st) f', nth_error (cg_frames s) i = Some f ->
nth_error (cg_frames (upd_frame s i f')) i = Some (Some f').
Proof.
intros s i f f' H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_error_list_set_same.
apply (proj1 (nth_error_Some _ _)). rewrite H. discriminate.
Qed.
Lemma nth_error_upd_frame_other : forall s i j f', j <> i -> nth_error (cg_frames (upd_frame s i f')) j = nth_error (cg_frames s) j.
Proof. intros s i j f' H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_error_list_set_other. lia. Qed.
Lemma nth_upd_frame_other : forall s i j f' d, j <> i -> nth j (cg_frames (upd_frame s i f')) d = nth j (cg_frames s) d.
Proof. intros s i j f' d H. unfold upd_frame, set_frames. cbn [cg_frames]. apply nth_list_set_other. lia. Qed.
Lemma cg_attr_upd_frame : forall s i f', cg_attr (upd_frame s i f') = cg_attr s.
Proof. intros. reflexivity. Qed.
Lemma cg_raw_upd_frame : forall s i f', cg_raw (upd_frame s i f') = cg_raw s.
Proof. intros. reflexivity. Qed.
Lemma cgif_blocks_ins_frame : forall g s N i f',
nth_error (cg_frames s) i = Some None ->
Permutation (cgif_blocks g (upd_frame s i f') N) (frame_blocks N f' ++ cgif_blocks g s N).
Proof.
intros g s N i f' Hi. unfold upd_frame. rewrite cgif_blocks_set_frames. unfold cgif_blocks.
destruct (nth_error_split _ _ Hi) as (l1 & l2 & Hfr & Hl1). rewrite Hfr at 2.
assert (E : list_set (cg_frames s) i (Some f') = l1 ++ Some f' :: l2).
{ rewrite Hfr, <- Hl1. clear. induction l1 as [|y l1 IH]; cbn; [reflexivity | rewrite IH; reflexivity]. }
rewrite E, !frames_blocks_app. cbn [frames_blocks flat_map]. fold (frames_blocks N l2). cbn [app].
apply Permutation_sym.
change ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1 ++ frame_blocks N f' ++ frames_blocks N l2)
with (((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s) ++ (frames_blocks N l1 ++ frame_blocks N f' ++ frames_blocks N l2)).
change (frame_blocks N f' ++ (g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s ++ frames_blocks N l1 ++ frames_blocks N l2)
with (frame_blocks N f' ++ ((g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: pal_blocks s) ++ (frames_blocks N l1 ++ frames_blocks N l2)).
rewrite (app_assoc (frames_blocks N l1)).
eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_swap_app|].
rewrite <- app_assoc. rewrite (app_assoc (frame_blocks N f')).
eapply Permutation_trans; [apply Permutation_app_swap_app|].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.
Lemma cgif_wf_ins_frame : forall s N i f',
cgif_wf s N -> nth_error (cg_frames s) i = Some None -> frame_wf (cg_attr s) f' -> cgif_wf (upd_frame s i f') N.
Proof.
intros s N i f' Hwf Hi Hf'. pose proof Hwf as (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf).
unfold upd_frame, set_frames. apply cgif_wf_intro; [exact Hwf | rewrite length_list_set; exact Hlen | |].
- destruct Hih as [H1|[H2 Hn1]]; [left; exact H1 | right; split; [exact H2|]].
destruct (Nat.eq_dec i 1) as [->|Hne].
+ rewrite nth_list_set_same by (rewrite Hlen; lia). discriminate.
+ rewrite nth_list_set_other by lia. exact Hn1.
- intros x Hx. destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
+ injection Hx' as ->. exact Hf'.
+ apply Hfwf. eapply nth_error_In. exact Hj.
Qed.
Lemma cgif_wf_set_ihead : forall s N ih,
cgif_wf s N -> (ih = 1 \/ (ih = 2 /\ nth 1 (cg_frames s) None <> None)) -> cgif_wf (set_ihead s ih) N.
Proof.
intros s N ih (Hlen & HW & HH & HN & HNle & Hngp & Hih & Hfwf) H. unfold cgif_wf, set_ihead. cbn. repeat (split; [assumption|]). exact Hfwf.
Qed.
Lemma cgif_blocks_set_ihead : forall g s N ih, cgif_blocks g (set_ihead s ih) N = cgif_blocks g s N.
Proof. intros. reflexivity. Qed.
Lemma U_sext32_low : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) mod 2 ^ 32 = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt. rewrite (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). apply sext32_low. exact Hv.
Qed.
End h.