(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YI08 YN3v YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Lemma oframe_relbA_occ : forall wg m N o q, oframe_relbA segs wg m N o q -> (o = None <-> q = None).
Proof. intros wg m N [f|] [fr|] H; cbn in H; split; intros X; try discriminate X; try reflexivity; destruct H. Qed.
Lemma frame_relbA_weaken : forall wg m N f fr, frame_relbA segs wg m N f fr -> frame_relbA segs false m N f fr.
Proof. intros wg m N f fr (A1 & A2 & A3). split; [exact A1|]. split; [exact I | exact A3]. Qed.
Lemma oframe_relbA_weaken : forall wg m N o q, oframe_relbA segs wg m N o q -> oframe_relbA segs false m N o q.
Proof. intros wg m N [f|] [fr|] H; cbn in H |- *; try exact H. exact (frame_relbA_weaken wg m N f fr H). Qed.
Definition af_xlive (mem : word -> option byte) (s : cgif_st) (N : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
oframe_relbA segs false mem N (nth 0 (cg_frames s) None) (YO07.s_q0 gs) /\
oframe_relbA segs true mem N (nth 1 (cg_frames s) None) (YO07.s_q1 gs) /\
oframe_relbA segs true mem N (nth 2 (cg_frames s) None) (YO07.s_q2 gs).
Lemma af_xlive_set_cur : forall mem s N GPAL gs c, af_xlive mem (cl_set_cur s c) N GPAL gs <-> af_xlive mem s N GPAL gs.
Proof. intros. unfold af_xlive, cl_set_cur. cbn. tauto. Qed.
Lemma cgif_occ_set_cur : forall s c gs, cgif_occ (cl_set_cur s c) gs <-> cgif_occ s gs.
Proof. intros. unfold cgif_occ, cl_set_cur. cbn. tauto. Qed.
Lemma cgif_occ_ext : forall s s' gs gs', cg_frames s' = cg_frames s ->
YO07.s_q0 gs' = YO07.s_q0 gs -> YO07.s_q1 gs' = YO07.s_q1 gs -> YO07.s_q2 gs' = YO07.s_q2 gs ->
cgif_occ s gs -> cgif_occ s' gs'.
Proof. intros s s' gs gs' Hf H0 H1 H2 H. unfold cgif_occ in *. rewrite Hf, H0, H1, H2. exact H. Qed.
Definition af_xvblocks (s : cgif_st) (N : Z) : list (Z * Z) :=
pal_blocks s ++ flat_map (fun o => match o with Some f => (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) | None => [] end) (cg_frames s).
Lemma frame_relb_kept : forall wg mem mem' N f fr,
(forall k, 0 <= k < N -> mbyte segs mem' (fr_img f + k) = mbyte segs mem (fr_img f + k)) ->
(Z.land (fr_attr f) 1 <> 0 -> forall k, 0 <= k < 3 * fr_nlp f -> mbyte segs mem' (fr_lpal f + k) = mbyte segs mem (fr_lpal f + k)) ->
frame_relbA segs wg mem N f fr -> frame_relbA segs wg mem' N f fr.
Proof.
intros wg mem mem' N f fr Ki Kl (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [| split; [exact Hil|]].
- eapply garr8_frame; [exact Hi|]. intros a Ha. replace a with (fr_img f + (a - fr_img f)) by lia. apply Ki. lia.
- intros Hz. destruct (Hl Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (fr_lpal f + (a - fr_lpal f)) by lia. apply (Kl Hz). lia.
Qed.
Lemma af_xlive_kept : forall mem mem' s N GPAL gs,
cgif_wf s N ->
(forall a n k, In (a, n) (af_xvblocks s N) -> 0 <= k < n -> mbyte segs mem' (a + k) = mbyte segs mem (a + k)) ->
af_xlive mem s N GPAL gs -> af_xlive mem' s N GPAL gs.
Proof.
intros mem mem' s N GPAL gs Hwf K (R1 & R2 & R3 & R4 & F0 & F1 & F2).
pose proof Hwf as (Hlen & _).
assert (FR : forall wg j q, oframe_relbA segs wg mem N (nth j (cg_frames s) None) q -> oframe_relbA segs wg mem' N (nth j (cg_frames s) None) q).
{ intros wg j q H. destruct (nth j (cg_frames s) None) as [f|] eqn:Hn; destruct q as [fr|]; cbn [oframe_relbA] in H |- *; try exact H.
assert (Hin : In (Some f) (cg_frames s)).
{ rewrite <- Hn. apply nth_In. destruct (Nat.lt_ge_cases j (length (cg_frames s))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ _ Hl) in Hn. discriminate Hn. }
apply (frame_relb_kept wg mem mem' N f fr); [| | exact H].
- intros k Hk. apply (K (fr_img f) N k); [| exact Hk]. unfold af_xvblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
- intros Hz k Hk. apply (K (fr_lpal f) (3 * fr_nlp f) k); [| exact Hk]. unfold af_xvblocks. apply in_app_iff. right. apply in_flat_map. exists (Some f). split; [exact Hin|].
right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]. }
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [| split; [apply FR; exact F0 | split; [apply FR; exact F1 | apply FR; exact F2]]].
intros Hz. destruct (R4 Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K (cg_pal s) (3 * cg_ngp s)); [| lia]. unfold af_xvblocks. apply in_app_iff. left. unfold pal_blocks. rewrite Hz. left. reflexivity.
Qed.
Definition wgk (k : nat) : bool := match k with 0%nat => false | _ => true end.
Definition af_xhdr (mem : word -> option byte) (s : cgif_st) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s).
Definition af_xslots (mem : word -> option byte) (s : cgif_st) (N : Z) (gs : YO07.gif_st) (P : nat -> Prop) : Prop :=
forall k, (k < 3)%nat -> P k -> oframe_relbA segs (wgk k) mem N (nth k (cg_frames s) None) (qslot gs k).
Lemma af_xlive_iff : forall mem s N GPAL gs, af_xlive mem s N GPAL gs <-> af_xhdr mem s GPAL gs /\ af_xslots mem s N gs (fun _ => True).
Proof.
intros. unfold af_xlive, af_xhdr, af_xslots. split.
- intros (A & B & C & D & F0 & F1 & F2). split; [tauto|]. intros k Hk _. destruct k as [|[|[|k]]]; cbn [wgk qslot]; [exact F0 | exact F1 | exact F2 | lia].
- intros ((A & B & C & D) & F). pose proof (F 0%nat ltac:(lia) I) as F0. pose proof (F 1%nat ltac:(lia) I) as F1. pose proof (F 2%nat ltac:(lia) I) as F2.
cbn [wgk qslot] in F0, F1, F2. tauto.
Qed.
Lemma af_xslots_mono : forall mem s N gs (P Q : nat -> Prop), (forall k, Q k -> P k) -> af_xslots mem s N gs P -> af_xslots mem s N gs Q.
Proof. intros mem s N gs P Q HPQ H k Hk HQ. exact (H k Hk (HPQ k HQ)). Qed.
Lemma af_xhdr_kept : forall mem mem' s GPAL gs,
(Z.land (cg_attr s) 4 = 0 -> forall k, 0 <= k < 3 * cg_ngp s -> mbyte segs mem' (cg_pal s + k) = mbyte segs mem (cg_pal s + k)) ->
af_xhdr mem s GPAL gs -> af_xhdr mem' s GPAL gs.
Proof.
intros mem mem' s GPAL gs K (A & B & C & D). split; [exact A|]. split; [exact B|]. split; [exact C|].
intros Hz. destruct (D Hz) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (cg_pal s + (a - cg_pal s)) by lia. apply (K Hz). lia.
Qed.
Definition af_xfvb (N : Z) (o : option frame_st) : list (Z * Z) :=
match o with Some f => (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)]) | None => [] end.
Lemma af_xvblocks_eq : forall s N, af_xvblocks s N = pal_blocks s ++ flat_map (af_xfvb N) (cg_frames s).
Proof. intros. reflexivity. Qed.
Lemma af_xslots_kept : forall mem mem' s N gs (P : nat -> Prop),
(forall k f, (k < 3)%nat -> P k -> nth k (cg_frames s) None = Some f ->
forall a n j, In (a, n) (af_xfvb N (Some f)) -> 0 <= j < n -> mbyte segs mem' (a + j) = mbyte segs mem (a + j)) ->
af_xslots mem s N gs P -> af_xslots mem' s N gs P.
Proof.
intros mem mem' s N gs P K H k Hk HP. pose proof (H k Hk HP) as Ho.
destruct (nth k (cg_frames s) None) as [f|] eqn:Hn; destruct (qslot gs k) as [fr|]; cbn [oframe_relbA] in Ho |- *; try exact Ho.
apply (frame_relb_kept (wgk k) mem mem' N f fr); [| | exact Ho].
- intros j Hj. apply (K k f Hk HP Hn (fr_img f) N j); [left; reflexivity | exact Hj].
- intros Hz j Hj. apply (K k f Hk HP Hn (fr_lpal f) (3 * fr_nlp f) j); [| exact Hj].
cbn [af_xfvb]. right. destruct (Z.eqb_spec (Z.land (fr_attr f) 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity].
Qed.
Lemma af_xslots_occ : forall mem s N gs, af_xslots mem s N gs (fun _ => True) -> cgif_occ s gs.
Proof.
intros mem s N gs H. unfold cgif_occ.
pose proof (oframe_relbA_occ _ _ _ _ _ (H 0%nat ltac:(lia) I)) as H0. pose proof (oframe_relbA_occ _ _ _ _ _ (H 1%nat ltac:(lia) I)) as H1.
pose proof (oframe_relbA_occ _ _ _ _ _ (H 2%nat ltac:(lia) I)) as H2. cbn [qslot] in H0, H1, H2. tauto.
Qed.
Lemma cgif_occ_iff : forall s gs, cgif_occ s gs <-> forall k, (k < 3)%nat -> (nth k (cg_frames s) None = None <-> qslot gs k = None).
Proof.
intros s gs. unfold cgif_occ. split.
- intros (H0 & H1 & H2) [|[|[|k]]] Hk; cbn [qslot]; [exact H0 | exact H1 | exact H2 | lia].
- intros H. pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1. pose proof (H 2%nat ltac:(lia)) as H2. cbn [qslot] in H0, H1, H2. tauto.
Qed.
Lemma nth_upd_frame : forall s ih fh' k, length (cg_frames s) = 3%nat -> (ih < 3)%nat ->
nth k (cg_frames (upd_frame s ih fh')) None = if (k =? ih)%nat then Some fh' else nth k (cg_frames s) None.
Proof.
intros s ih fh' k Hlen Hih. unfold upd_frame, set_frames. cbn [cg_frames].
destruct (Nat.eqb_spec k ih) as [->|Hne]; [apply nth_list_set_same; rewrite Hlen; exact Hih | apply nth_list_set_other; lia].
Qed.
Lemma af_xslots_upd : forall mem s N gs ih fh' fr' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_xslots mem s N gs (fun k => k <> ih /\ P k) -> (P ih -> frame_relbA segs (wgk ih) mem N fh' fr') ->
af_xslots mem (upd_frame s ih fh') N (YO07.q_set gs (Z.of_nat ih) (Some fr')) P.
Proof.
intros mem s N gs ih fh' fr' P Hih Hlen H Hnew k Hk HP. rewrite (nth_upd_frame s ih fh' k Hlen Hih), (qslot_set gs ih _ k Hk Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [cbn [oframe_relbA]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_xslots_upd_same : forall mem s N gs ih fh' fr' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_xslots mem s N gs (fun k => k <> ih /\ P k) -> qslot gs ih = Some fr' -> (P ih -> frame_relbA segs (wgk ih) mem N fh' fr') ->
af_xslots mem (upd_frame s ih fh') N gs P.
Proof.
intros mem s N gs ih fh' fr' P Hih Hlen H Hq Hnew k Hk HP. rewrite (nth_upd_frame s ih fh' k Hlen Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [rewrite Hq; cbn [oframe_relbA]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_xslots_upd_skip : forall mem s N gs ih fh' (P : nat -> Prop),
(ih < 3)%nat -> length (cg_frames s) = 3%nat ->
af_xslots mem s N gs P -> (forall k, P k -> k <> ih) -> af_xslots mem (upd_frame s ih fh') N gs P.
Proof.
intros mem s N gs ih fh' P Hih Hlen H HP k Hk HPk. rewrite (nth_upd_frame s ih fh' k Hlen Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [exfalso; exact (HP ih HPk eq_refl) | exact (H k Hk HPk)].
Qed.
Lemma af_xhdr_ext2 : forall mem s s' GPAL gs gs',
rw_cur s' = rw_cur s -> rw_attr s' = rw_attr s -> cg_attr s' = cg_attr s -> cg_pal s' = cg_pal s -> cg_ngp s' = cg_ngp s ->
YO07.s_rcur gs' = YO07.s_rcur gs -> cg_ihead s' = YO07.s_ihead gs' ->
af_xhdr mem s GPAL gs -> af_xhdr mem s' GPAL gs'.
Proof.
intros mem s s' GPAL gs gs' E1 E2 E3 E5 E6 E7 E8 (A & B & C & D). unfold af_xhdr. rewrite E1, E2, E3, E5, E6, E7.
split; [exact A|]. split; [exact B|]. split; [exact E8 | exact D].
Qed.
Lemma af_xslots_fill : forall mem s N gs i fn fr (P : nat -> Prop),
af_xslots mem s N gs (fun k => k <> i /\ P k) -> nth i (cg_frames s) None = Some fn -> qslot gs i = Some fr -> (P i -> frame_relbA segs (wgk i) mem N fn fr) ->
af_xslots mem s N gs P.
Proof.
intros mem s N gs i fn fr P H Hn Hq Hnew k Hk HP.
destruct (Nat.eq_dec k i) as [->|Hne]; [rewrite Hn, Hq; cbn [oframe_relbA]; exact (Hnew HP) | exact (H k Hk (conj Hne HP))].
Qed.
Lemma af_xslots_qext : forall mem s N gs gs' (P : nat -> Prop),
(forall k, (k < 3)%nat -> P k -> qslot gs' k = qslot gs k) -> af_xslots mem s N gs P -> af_xslots mem s N gs' P.
Proof. intros mem s N gs gs' P E H k Hk HP. rewrite (E k Hk HP). exact (H k Hk HP). Qed.
Lemma af_xslots_fext : forall mem s s' N gs (P : nat -> Prop),
cg_frames s' = cg_frames s -> af_xslots mem s N gs P -> af_xslots mem s' N gs P.
Proof. intros mem s s' N gs P E H k Hk HP. rewrite E. exact (H k Hk HP). Qed.
Lemma af_xhdr_set_cur : forall mem s GPAL gs c, af_xhdr mem (cl_set_cur s c) GPAL gs <-> af_xhdr mem s GPAL gs.
Proof. intros. unfold af_xhdr, cl_set_cur. cbn. tauto. Qed.
Lemma af_xhdr_ext : forall mem s s' GPAL gs gs',
rw_cur s' = rw_cur s -> rw_attr s' = rw_attr s -> cg_attr s' = cg_attr s -> cg_ihead s' = cg_ihead s -> cg_pal s' = cg_pal s -> cg_ngp s' = cg_ngp s ->
YO07.s_rcur gs' = YO07.s_rcur gs -> YO07.s_ihead gs' = YO07.s_ihead gs ->
af_xhdr mem s GPAL gs -> af_xhdr mem s' GPAL gs'.
Proof. intros mem s s' GPAL gs gs' E1 E2 E3 E4 E5 E6 E7 E8 H. unfold af_xhdr in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8. exact H. Qed.
Lemma cgif_occ_upd : forall s gs ih fh' fr', (ih < 3)%nat -> length (cg_frames s) = 3%nat ->
cgif_occ s gs -> cgif_occ (upd_frame s ih fh') (YO07.q_set gs (Z.of_nat ih) (Some fr')).
Proof.
intros s gs ih fh' fr' Hih Hlen H. apply (proj2 (cgif_occ_iff _ _)). pose proof (proj1 (cgif_occ_iff _ _) H) as HK. intros k Hk.
rewrite (nth_upd_frame s ih fh' k Hlen Hih), (qslot_set gs ih _ k Hk Hih).
destruct (Nat.eqb_spec k ih) as [->|Hne]; [split; intros X; discriminate X | exact (HK k Hk)].
Qed.
Lemma af_xhdr_upd : forall mem s GPAL gs ih fh' o, af_xhdr mem s GPAL gs -> af_xhdr mem (upd_frame s ih fh') GPAL (YO07.q_set gs (Z.of_nat ih) o).
Proof.
intros mem s GPAL gs ih fh' o (A & B & C & D). pose proof (q_set_fields gs (Z.of_nat ih) o) as (_ & E1 & _ & E2).
unfold af_xhdr. cbn [upd_frame set_frames rw_cur rw_attr cg_attr cg_ihead cg_pal cg_ngp]. rewrite E1, E2. exact (conj A (conj B (conj C D))).
Qed.
Definition af_xnewf (mem : word -> option byte) (N : Z) (fn : frame_st) (fattr fgen delay nlp tidx : Z) (IMG LPAL : list Z) (disp tcur : Z) : Prop :=
fr_attr fn = fattr /\ fr_gen fn = fgen /\ fr_delay fn = delay /\ fr_nlp fn = nlp /\ (Z.land fattr 6 <> 0 -> fr_ctidx fn = tidx) /\
fr_disp fn = disp /\ fr_tidx fn = tcur /\
garr8 segs mem (fr_img fn) IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 segs mem (fr_lpal fn) LPAL /\ Z.of_nat (length LPAL) = 3 * nlp).
Lemma af_xnewf_rel : forall mem N fn fattr fgen delay nlp tidx IMG LPAL G wg,
let nf := YO07.new_frame G fattr fgen delay tidx nlp LPAL IMG in
af_xnewf mem N fn fattr fgen delay nlp tidx IMG LPAL (YO07.f_disp nf) (YO07.f_trans nf) -> frame_relbA segs wg mem N fn nf.
Proof.
intros mem N fn fattr fgen delay nlp tidx IMG LPAL G wg nf (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl). subst nf.
unfold frame_relbA, YO07.new_frame. cbn [YO07.f_attr YO07.f_gen YO07.f_delay YO07.f_nlp YO07.f_ctrans YO07.f_disp YO07.f_trans YO07.f_img YO07.f_lpal].
cbn [YO07.f_disp YO07.f_trans YO07.new_frame] in A6, A7.
split; [exact A1|]. split; [destruct wg; [exact A2 | exact I]|]. split; [exact A3|]. split; [exact A4|].
split; [intros H6; rewrite A1 in H6; rewrite (A5 H6); unfold YO07.flag; destruct (Z.eqb_spec (Z.land fattr 6) 0); [lia | reflexivity]|].
split; [exact A6|]. split; [exact A7|]. split; [exact Hi|]. split; [exact Hil|].
intros H1. rewrite A1 in H1. rewrite A4. exact (Hl H1).
Qed.
Lemma af_xnewf_kept : forall mem mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur,
(forall j, 0 <= j < N -> mbyte segs mem' (fr_img fn + j) = mbyte segs mem (fr_img fn + j)) ->
(Z.land fattr 1 <> 0 -> forall j, 0 <= j < 3 * nlp -> mbyte segs mem' (fr_lpal fn + j) = mbyte segs mem (fr_lpal fn + j)) ->
af_xnewf mem N fn fattr fgen delay nlp tidx IMG LPAL disp tcur -> af_xnewf mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur.
Proof.
intros mem mem' N fn fattr fgen delay nlp tidx IMG LPAL disp tcur Ki Kl (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl).
do 7 (split; [assumption|]). split; [| split; [exact Hil|]].
- eapply garr8_frame; [exact Hi|]. intros a Ha. replace a with (fr_img fn + (a - fr_img fn)) by lia. apply Ki. lia.
- intros H1. destruct (Hl H1) as [Hg Hgl]. split; [| exact Hgl]. eapply garr8_frame; [exact Hg|]. intros a Ha.
replace a with (fr_lpal fn + (a - fr_lpal fn)) by lia. apply (Kl H1). lia.
Qed.
Lemma af_xnewf_fields : forall mem N fn fn' fattr fgen delay nlp tidx IMG LPAL disp tcur disp' tcur',
af_xnewf mem N fn fattr fgen delay nlp tidx IMG LPAL disp tcur ->
fr_attr fn' = fr_attr fn -> fr_gen fn' = fr_gen fn -> fr_delay fn' = fr_delay fn -> fr_nlp fn' = fr_nlp fn -> fr_ctidx fn' = fr_ctidx fn ->
fr_img fn' = fr_img fn -> fr_lpal fn' = fr_lpal fn -> fr_disp fn' = disp' -> fr_tidx fn' = tcur' ->
af_xnewf mem N fn' fattr fgen delay nlp tidx IMG LPAL disp' tcur'.
Proof.
intros mem N fn fn' fattr fgen delay nlp tidx IMG LPAL disp tcur disp' tcur' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & Hi & Hil & Hl) E1 E2 E3 E4 E5 E6 E7 E8 E9.
unfold af_xnewf. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hi|]. split; [exact Hil|]. exact Hl.
Qed.
Lemma cgif_relA_split : forall K m md s f N GPAL gs,
cgif_relA segs K m md s f N GPAL gs <->
((rc_int (cg_cur s) = YO07.s_cur gs /\ cgif_occ s gs) /\ asink_at segs K m md f (concat (YO07.s_out gs)) /\ (cgif_live gs -> af_xlive m s N GPAL gs)).
Proof. intros. unfold cgif_relA, af_xlive. tauto. Qed.
Lemma cgif_relA_kept : forall K (m m' : word -> option byte) md md' s f N GPAL gs,
cgif_wf s N ->
(forall a n k, In (a, n) (af_xvblocks s N) -> 0 <= k < n -> mbyte segs m' (a + k) = mbyte segs m (a + k)) ->
(forall a, f <= a < f + FILE_BLOCK \/ aenv_addr K a -> mbyte segs m' a = mbyte segs m a) ->
m_fs md' = m_fs md -> m_fds md' = m_fds md ->
cgif_relA segs K m md s f N GPAL gs -> cgif_relA segs K m' md' s f N GPAL gs.
Proof.
intros K m m' md md' s f N GPAL gs Hwf KV KF Efs Efd H. apply (proj2 (cgif_relA_split _ _ _ _ _ _ _ _)).
apply (proj1 (cgif_relA_split _ _ _ _ _ _ _ _)) in H as (H1 & H2 & H3).
split; [exact H1|]. split; [apply (asink_at_model segs K m' md md' f _ Efs Efd); apply (asink_at_frame segs K m m' md f _ KF H2)|].
intros Hl. exact (af_xlive_kept m m' s N GPAL gs Hwf KV (H3 Hl)).
Qed.
Lemma asink_at_kept_mm : forall K (m m' : word -> option byte) md md' f S,
(forall a, f <= a < f + FILE_BLOCK \/ aenv_addr K a -> mbyte segs m' a = mbyte segs m a) ->
m_fs md' = m_fs md -> m_fds md' = m_fds md ->
asink_at segs K m md f S -> asink_at segs K m' md' f S.
Proof. intros K m m' md md' f S KF Efs Efd H. apply (asink_at_model segs K m' md md' f _ Efs Efd). exact (asink_at_frame segs K m m' md f _ KF H). Qed.
Lemma xcgif_vals_set_cur_nth : forall pth hw pfv s1 c j, j <> 15%nat -> nth_error (xcgif_vals pth hw pfv (cl_set_cur s1 c)) j = nth_error (xcgif_vals pth hw pfv s1) j.
Proof.
intros pth hw pfv s1 c j Hj. do 17 (destruct j as [|j]; [first [reflexivity | exfalso; lia] |]). reflexivity.
Qed.
Lemma obj_cgif_setcurX : forall pth hw pfv (m m' : word -> option byte) g s1 c,
obj_at segs m g LAY_CGIF (xcgif_vals pth hw pfv s1) ->
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte segs m' (g + i) = mbyte segs m (g + i)) ->
val_mem segs m' (g + 88) 4 c -> 0 <= c < 2 ^ 32 ->
obj_at segs m' g LAY_CGIF (xcgif_vals pth hw pfv (cl_set_cur s1 c)).
Proof.
intros pth hw pfv m m' g s1 c HO HK Vc Rc.
apply YI5s.obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct (Nat.eq_dec j 15) as [-> | Hne].
- cbn in Hf. injection Hf as <-. cbn in Hv. injection Hv as <-. split; [exact Vc | cbn; lia].
- rewrite (xcgif_vals_set_cur_nth pth hw pfv s1 c j Hne) in Hv.
pose proof (obj_at_nth segs _ _ _ _ j f v HO Hf Hv) as [V R]. split; [|exact R].
assert (HIN : In f LAY_CGIF) by (eapply nth_error_In; exact Hf).
assert (Hoff : 0 <= fst f /\ fst f + Z.of_N (snd f) <= 96 /\ (fst f + Z.of_N (snd f) <= 88 \/ 92 <= fst f)).
{ assert (Hj : (j < 17)%nat) by (apply (proj1 (nth_error_Some LAY_CGIF j)); rewrite Hf; discriminate).
do 17 (destruct j as [|j]; [cbn in Hf; injection Hf as <-; cbn; lia|]). lia. }
intros kk Hkk. rewrite <- (V kk Hkk). pose proof (N_nat_Z (snd f)).
replace (g + fst f + Z.of_nat kk) with (g + (fst f + Z.of_nat kk)) by lia. apply HK; lia.
Qed.
Lemma xcgif_vals_upd_frame : forall pth hw pfv s i f f',
nth_error (cg_frames s) i = Some (Some f) -> fr_ptr f' = fr_ptr f -> xcgif_vals pth hw pfv (upd_frame s i f') = xcgif_vals pth hw pfv s.
Proof.
intros pth hw pfv s i f f' Hi Hp. unfold upd_frame, set_frames, xcgif_vals. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead].
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some f')) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
rewrite (nth_error_nth _ _ _ Hi). cbn. exact Hp.
- rewrite YI5v.nth_list_set_other by lia. reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma xcgif_vals_ins_frame : forall pth hw pfv s i f', (i < 3)%nat -> length (cg_frames s) = 3%nat ->
xcgif_vals pth hw pfv (upd_frame s i f') = list_set (xcgif_vals pth hw pfv s) i (fr_ptr f').
Proof.
intros pth hw pfv s i f' Hi Hlen. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold upd_frame. rewrite Hfr. unfold xcgif_vals, set_frames. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead].
rewrite Hfr. destruct i as [|[|[|i]]]; try lia; reflexivity.
Qed.
Lemma xcgif_vals_set_ihead_ls : forall pth hw pfv s ih, xcgif_vals pth hw pfv (set_ihead s ih) = list_set (xcgif_vals pth hw pfv s) 16 ih.
Proof. intros. reflexivity. Qed.
Lemma xcgif_vals_set_cur_ls : forall pth hw pfv s c, xcgif_vals pth hw pfv (cl_set_cur s c) = list_set (xcgif_vals pth hw pfv s) 15 c.
Proof. intros. reflexivity. Qed.
End d.
End b.
