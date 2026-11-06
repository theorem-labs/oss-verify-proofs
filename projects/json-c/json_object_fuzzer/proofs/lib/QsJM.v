(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKBN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKBN.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.solve_load ::= Qqyb.mkr__solve_load_3. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition kFsClasses : Z := 11.
Definition fs_N (c : Z) : Z := 2 ^ (14 - c).
Definition fs_foff (c : Z) : Z := 2 ^ 15 - 2 ^ (15 - c).
Definition fs_flag (FS c pos : Z) : Z := FS + 0x1000 + fs_foff c + pos.
Definition fs_frame (FS c pos : Z) : Z := FS + 0x9000 + c * 2 ^ 20 + pos * ff_size c.
Definition fs_hint (FS c : Z) : Z := FS + 8 * c.
Definition fs_area_lo (FS : Z) : Z := FS + 0x9000.
Definition fs_area_hi (FS : Z) : Z := FS + A_FS_MAP_SIZE.

Lemma ff_size_eq : forall c, 0 <= c -> ff_size c = 2 ^ (c + 6).
Proof. intros c Hc. unfold ff_size. change 64 with (2 ^ 6). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma fs_N_pos : forall c, 0 <= c < kFsClasses -> 8 <= fs_N c <= 16384.
Proof.
intros c Hc. unfold fs_N, kFsClasses in *.
split; [change 8 with (2 ^ 3); apply Z.pow_le_mono_r; lia| change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia].
Qed.

Lemma fs_N_size : forall c, 0 <= c < kFsClasses -> fs_N c * ff_size c = 2 ^ 20.
Proof.
intros c Hc. unfold fs_N, kFsClasses in *. rewrite ff_size_eq by lia. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma fs_foff_range : forall c, 0 <= c < kFsClasses -> 0 <= fs_foff c /\ fs_foff c + fs_N c <= 2 ^ 15.
Proof.
intros c Hc. unfold fs_foff, fs_N, kFsClasses in *.
assert (2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; lia).
assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
assert (2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. change (2 ^ 15) with 32768. lia.
Qed.

Lemma fs_foff_mono : forall c c', 0 <= c -> c < c' -> c' < kFsClasses -> fs_foff c + fs_N c <= fs_foff c'.
Proof.
intros c c' H0 Hlt Hc'. unfold fs_foff, fs_N, kFsClasses in *.
assert (2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; lia).
assert (2 ^ (15 - c') <= 2 ^ (14 - c)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma fs_flag_range : forall FS c pos, 0 <= c < kFsClasses -> 0 <= pos < fs_N c ->
FS + 0x1000 <= fs_flag FS c pos < FS + 0x9000.
Proof. intros FS c pos Hc Hp. unfold fs_flag. pose proof (fs_foff_range c Hc). change (2 ^ 15) with 0x8000 in *. lia. Qed.

Lemma fs_frame_range : forall FS c pos, 0 <= c < kFsClasses -> 0 <= pos < fs_N c ->
FS + 0x9000 + c * 2 ^ 20 <= fs_frame FS c pos /\ fs_frame FS c pos + ff_size c <= FS + 0x9000 + (c + 1) * 2 ^ 20.
Proof.
intros FS c pos Hc Hp. unfold fs_frame. pose proof (fs_N_size c Hc) as S.
assert (0 < ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
split; [nia|]. assert ((pos + 1) * ff_size c <= fs_N c * ff_size c) by (apply Z.mul_le_mono_nonneg_r; lia). nia.
Qed.

Lemma fs_frame_in_area : forall FS c pos, 0 <= c < kFsClasses -> 0 <= pos < fs_N c ->
fs_area_lo FS <= fs_frame FS c pos /\ fs_frame FS c pos + ff_size c <= fs_area_hi FS.
Proof.
intros FS c pos Hc Hp. pose proof (fs_frame_range FS c pos Hc Hp) as [A B]. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE, kFsClasses in *.
split; [nia|]. assert ((c + 1) * 2 ^ 20 <= 11 * 2 ^ 20) by nia. change (2 ^ 20) with 0x100000 in *. lia.
Qed.

Lemma fs_frame_inj : forall FS c p p', 0 <= c -> fs_frame FS c p = fs_frame FS c p' -> p = p'.
Proof.
intros FS c p p' Hc E. unfold fs_frame in E. assert (0 < ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia). nia.
Qed.

Lemma fs_frame_apart : forall FS c p p', 0 <= c -> p <> p' ->
fs_frame FS c p + ff_size c <= fs_frame FS c p' \/ fs_frame FS c p' + ff_size c <= fs_frame FS c p.
Proof.
intros FS c p p' Hc Hne. unfold fs_frame. assert (0 < ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
destruct (Z.lt_ge_cases p p'); [left| right]; nia.
Qed.

Lemma fs_frame_apart_cls : forall FS c p c' p', 0 <= c < kFsClasses -> 0 <= c' < kFsClasses -> c <> c' ->
0 <= p < fs_N c -> 0 <= p' < fs_N c' ->
fs_frame FS c p + ff_size c <= fs_frame FS c' p' \/ fs_frame FS c' p' + ff_size c' <= fs_frame FS c p.
Proof.
intros FS c p c' p' Hc Hc' Hne Hp Hp'.
pose proof (fs_frame_range FS c p Hc Hp) as [A B]. pose proof (fs_frame_range FS c' p' Hc' Hp') as [A' B'].
destruct (Z.lt_ge_cases c c'); [left| right].
- assert ((c + 1) * 2 ^ 20 <= c' * 2 ^ 20) by nia. lia.
- assert ((c' + 1) * 2 ^ 20 <= c * 2 ^ 20) by nia. lia.
Qed.

Lemma fs_frame_align : forall FS c pos, FS mod 4096 = 0 -> 0 <= c -> fs_frame FS c pos mod 64 = 0.
Proof.
intros FS c pos HF Hc. unfold fs_frame, ff_size.
assert (Hq : exists q, FS = 4096 * q) by (exists (FS / 4096); Z.div_mod_to_equations; lia). destruct Hq as [q ->].
replace (4096 * q + 0x9000 + c * 2 ^ 20 + pos * (64 * 2 ^ c)) with ((64 * q + 576 + c * 16384 + pos * 2 ^ c) * 64)
by (change (2 ^ 20) with (16384 * 64); lia).
apply Z_mod_mult.
Qed.

Definition live_b (FS0 : list fframe) (c f : Z) : bool :=
existsb (fun fr => (ff_cls fr =? c) && (ff_addr fr =? f)) FS0.

Lemma live_b_true : forall FS0 c f, live_b FS0 c f = true <-> In (c, f) FS0.
Proof.
intros FS0 c f. unfold live_b. rewrite existsb_exists. split.
- intros ([c' f'] & Hin & Hb). apply andb_prop in Hb as [H1 H2]. cbn in H1, H2. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. exact Hin.
- intros Hin. exists (c, f). split; [exact Hin|]. cbn. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma live_b_false : forall FS0 c f, live_b FS0 c f = false <-> ~ In (c, f) FS0.
Proof.
intros FS0 c f. rewrite <- live_b_true. destruct (live_b FS0 c f); split; intros H.
- discriminate. - exfalso; apply H; reflexivity. - discriminate. - reflexivity.
Qed.

Definition flags_of (FS0 : list fframe) (FS c : Z) : list byte :=
map (fun i => b8 (Z.b2z (live_b FS0 c (fs_frame FS c (Z.of_nat i))))) (seq 0 (Z.to_nat (fs_N c))).

Lemma flags_of_length : forall FS0 FS c, length (flags_of FS0 FS c) = Z.to_nat (fs_N c).
Proof. intros. unfold flags_of. rewrite map_length, seq_length. reflexivity. Qed.

Lemma flags_of_nth : forall FS0 FS c pos, 0 <= pos < fs_N c ->
nth_error (flags_of FS0 FS c) (Z.to_nat pos) = Some (b8 (Z.b2z (live_b FS0 c (fs_frame FS c pos)))).
Proof.
intros FS0 FS c pos Hp. unfold flags_of. rewrite nth_error_map.
rewrite (nth_error_nth' (seq 0 (Z.to_nat (fs_N c))) 0%nat) by (rewrite seq_length; lia).
rewrite seq_nth by lia. cbn [option_map]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

Lemma flags_of_ext : forall FS0 FS1 FS c,
(forall f, In f FS0 <-> In f FS1) -> flags_of FS0 FS c = flags_of FS1 FS c.
Proof.
intros FS0 FS1 FS c HE. unfold flags_of. apply map_ext. intros i. f_equal. f_equal.
destruct (live_b FS0 c _) eqn:E0; destruct (live_b FS1 c _) eqn:E1; try reflexivity.
- apply live_b_true in E0. apply live_b_false in E1. exfalso. apply E1, HE, E0.
- apply live_b_false in E0. apply live_b_true in E1. exfalso. apply E0, HE, E1.
Qed.

Definition fs_shape (FS : Z) (FS0 : list fframe) : Prop :=
(forall f, In f FS0 -> 0 <= ff_cls f < kFsClasses /\ exists pos, 0 <= pos < fs_N (ff_cls f) /\ ff_addr f = fs_frame FS (ff_cls f) pos)
/\ List.NoDup (map ff_addr FS0).

Definition RFake {BAND : Band} (FS0 : list fframe) (RE : aentry) (X : rlay) (m : mem) : Prop :=
let FS := ae_fs_base RE in
FS mod 4096 = 0 /\ (lowhigh FS A_FS_MAP_SIZE /\ off_hull FS A_FS_MAP_SIZE) /\ FS + A_FS_MAP_SIZE <= band_lo
/\ fs_shape FS FS0
/\ ro_cells asegs m (FS + 88) [C8 (wz 20)]
/\ rw_cells asegs m (FS + 96) [C1 (b8 0)]
/\ (forall c, 0 <= c < kFsClasses -> exists h, rw_cells asegs m (fs_hint FS c) [C8 h])
/\ (forall c, 0 <= c < kFsClasses -> u8arr asegs m (fs_flag FS c 0) (flags_of FS0 FS c))
/\ (forall c pos, In (c, fs_frame FS c pos) FS0 -> 0 <= pos < fs_N c ->
rw_cells asegs m (fs_frame FS c pos + ff_size c - 8) [C8 (wz (fs_flag FS c pos))])
/\ hjunk m (fs_area_lo FS) (fs_area_hi FS)
/\ hjunk m (SH (fs_area_lo FS)) (SH (fs_area_hi FS)).

Section Laws.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma body_ge : forall FS0 a, fs_shape FS FS0 -> in_fframe_body FS0 a -> FS + 0x9000 <= a < FS + A_FS_MAP_SIZE.
Proof.
intros FS0 a [SH _] (f & Hin & Hr). destruct (SH f Hin) as (Hc & pos & Hp & E). rewrite E in Hr.
pose proof (fs_frame_in_area FS (ff_cls f) pos Hc Hp) as [A B]. unfold fs_area_lo, fs_area_hi in *. lia.
Qed.

Lemma fp_meta : forall FS0 a, fs_shape FS FS0 -> FS <= a < FS + 0x9000 -> fp_RFake FS0 RE X a.
Proof.
intros FS0 a SHP Ha. left. split; [split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia|].
intros Hb. pose proof (body_ge FS0 a SHP Hb). lia.
Qed.

Lemma fp_slot : forall FS0 c pos a, fs_shape FS FS0 -> In (c, fs_frame FS c pos) FS0 -> 0 <= pos < fs_N c ->
fs_frame FS c pos + ff_size c - 8 <= a < fs_frame FS c pos + ff_size c -> fp_RFake FS0 RE X a.
Proof.
intros FS0 c pos a SHP Hin Hp Ha. pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc & _). cbn [ff_cls fst] in Hc.
pose proof (fs_frame_in_area FS c pos Hc Hp) as [A B]. unfold fs_area_lo, fs_area_hi in *.
assert (64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
left. split; [split; cbn [fst snd]; lia|].
intros (f & Hf & Hr). destruct (SHf f Hf) as (Hc' & pos' & Hp' & E). rewrite E in Hr.
destruct (Z.eq_dec (ff_cls f) c) as [Ec|Nc].
- rewrite Ec in *. destruct (Z.eq_dec pos' pos) as [->|Np]; [lia|].
destruct (fs_frame_apart FS c pos' pos ltac:(lia) Np); lia.
- destruct (fs_frame_apart_cls FS (ff_cls f) pos' c pos Hc' Hc Nc Hp' Hp); lia.
Qed.

Lemma RFake_frame : forall FS0 m m', RFake FS0 RE X m -> wmono asegs m m' -> agree_on asegs (fp_RFake FS0 RE X) m m' -> RFake FS0 RE X m'.
Proof.
intros FS0 m m' (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2) WM AG.
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [exact SHP|].
split. { eapply ro_cells_agree; [exact AG| exact SSL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta FS0 a SHP). lia. }
split. { eapply rw_cells_agree; [exact AG| exact GC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_meta FS0 a SHP). lia. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold fs_hint, kFsClasses in *. apply (fp_meta FS0 a SHP). lia. }
split. { intros c Hc. pose proof (FL c Hc) as H. eapply u8arr_agree; [exact AG| exact H|].
intros a Ha. rewrite flags_of_length in Ha. pose proof (fs_flag_range FS c 0 Hc ltac:(pose proof (fs_N_pos c Hc); lia)).
pose proof (fs_foff_range c Hc). unfold fs_flag in *. apply (fp_meta FS0 a SHP). lia. }
split. { intros c pos Hin Hp. pose proof (SL c pos Hin Hp) as H. eapply rw_cells_agree; [exact AG| exact H|].
intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (fp_slot FS0 c pos a SHP Hin Hp). lia. }
split; eapply hjunk_wmono; eassumption.
Qed.

Lemma fs_shape_perm : forall FS0 FS1, fs_shape FS FS0 -> Permutation FS0 FS1 -> fs_shape FS FS1.
Proof.
intros FS0 FS1 [SHf ND] P. split.
- intros f Hf. apply SHf. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hf].
- eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND].
Qed.

Lemma RFake_perm : forall FS0 FS1 m, RFake FS0 RE X m -> Permutation FS0 FS1 -> RFake FS1 RE X m.
Proof.
intros FS0 FS1 m (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2) P.
assert (HE : forall f, In f FS0 <-> In f FS1) by (intros f; split; apply Permutation_in; [exact P| apply Permutation_sym; exact P]).
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [eapply fs_shape_perm; eassumption|].
split; [exact SSL|]. split; [exact GC|]. split; [exact HI|].
split; [intros c Hc; rewrite <- (flags_of_ext FS0 FS1 FS c HE); apply FL; exact Hc|].
split; [intros c pos Hin Hp; apply SL; [apply HE; exact Hin| exact Hp]|].
split; assumption.
Qed.

Lemma bytes_at_det : forall m a bs bs', bytes_at asegs m a bs -> bytes_at asegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros m a bs bs' (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)).
- rewrite <- H, <- H' by lia. reflexivity.
- rewrite (proj2 (nth_error_None bs i)), (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.

Lemma le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w E. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity. Qed.

Lemma ffs_remove_In : forall fa FS0 g, In g (ffs_remove fa FS0) <-> In g FS0 /\ ff_addr g <> fa.
Proof.
intros fa FS0 g. unfold ffs_remove. rewrite <- list_elem_of_In, list_elem_of_filter, list_elem_of_In.
unfold Is_true. destruct (Z.eqb_spec (ff_addr g) fa); cbn; intuition congruence.
Qed.

Lemma NoDup_map_filter : forall {A B} (g : A -> B) (P : A -> Prop) `{forall x, Decision (P x)} l,
List.NoDup (map g l) -> List.NoDup (map g (filter P l)).
Proof.
intros A B g P D l. induction l as [|x l IH]; intros ND; cbn; [constructor|].
cbn in ND. inversion ND as [|x' l' NI ND']; subst.
destruct (decide (P x)); cbn; [| apply IH; exact ND'].
constructor; [| apply IH; exact ND']. intros Hin. apply NI. apply in_map_iff in Hin as (y & E & Hy).
rewrite <- list_elem_of_In, list_elem_of_filter, list_elem_of_In in Hy. destruct Hy as [_ Hy].
rewrite <- E. apply in_map. exact Hy.
Qed.

Lemma fs_shape_remove : forall FS FS0 fa, fs_shape FS FS0 -> fs_shape FS (ffs_remove fa FS0).
Proof.
intros FS1 FS0 fa [SHf ND]. split.
- intros f Hf. apply ffs_remove_In in Hf as [Hf _]. exact (SHf f Hf).
- unfold ffs_remove. apply NoDup_map_filter. exact ND.
Qed.

Lemma fs_addr_unique : forall FS FS0 c c' f, fs_shape FS FS0 -> In (c, f) FS0 -> In (c', f) FS0 -> c = c'.
Proof.
intros FS1 FS0 c c' f [_ ND] H1 H2.
pose proof (NoDup_map_In_inj ff_addr FS0 (c, f) (c', f) ND H1 H2 eq_refl) as E. congruence.
Qed.

Lemma flags_of_clear_same : forall FS0 c pos fa,
fs_shape FS FS0 -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c -> fa = fs_frame FS c pos ->
flags_of (ffs_remove fa FS0) FS c = upd (flags_of FS0 FS c) (Z.to_nat pos) (b8 0).
Proof.
intros FS0 c pos fa SHP Hc Hp ->. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (Z.to_nat (fs_N c))) as [Hi|Hi].
2:{ rewrite (proj2 (nth_error_None _ i)) by (rewrite flags_of_length; lia).
rewrite (proj2 (nth_error_None _ i)) by (rewrite upd_length, flags_of_length; lia). reflexivity. }
replace i with (Z.to_nat (Z.of_nat i)) by lia. rewrite flags_of_nth by lia.
destruct (Nat.eq_dec i (Z.to_nat pos)) as [->|Ni].
- rewrite Z2Nat.id by lia. rewrite nth_error_upd_same by (rewrite flags_of_length; lia).
f_equal. f_equal. replace (live_b _ _ _) with false; [reflexivity|]. symmetry. apply live_b_false.
intros H. apply ffs_remove_In in H as [_ H]. apply H. reflexivity.
- rewrite nth_error_upd_other by lia. rewrite flags_of_nth by lia.
f_equal. f_equal. f_equal. destruct (live_b FS0 c _) eqn:E.
+ apply live_b_true. apply live_b_true in E. apply ffs_remove_In. split; [exact E|]. cbn [ff_addr snd].
intros EQ. apply fs_frame_inj in EQ; lia.
+ apply live_b_false. apply live_b_false in E. intros H. apply E. apply ffs_remove_In in H as [H _]. exact H.
Qed.

Lemma flags_of_clear_other : forall FS0 c fa c',
fs_shape FS FS0 -> In (c, fa) FS0 -> c' <> c -> flags_of (ffs_remove fa FS0) FS c' = flags_of FS0 FS c'.
Proof.
intros FS0 c fa c' SHP Hin Nc. unfold flags_of. apply map_ext. intros i. f_equal. f_equal.
destruct (live_b FS0 c' _) eqn:E.
- apply live_b_true. apply live_b_true in E. apply ffs_remove_In. split; [exact E|]. cbn [ff_addr snd].
intros EQ. rewrite EQ in E. pose proof (fs_addr_unique FS FS0 c' c _ SHP E Hin). lia.
- apply live_b_false. apply live_b_false in E. intros H. apply E. apply ffs_remove_In in H as [H _]. exact H.
Qed.

Lemma RFake_release0 : forall FS0 m f (flag : word),
(forall f', In f' FS0 -> fframe_rangeA RE (ff_cls f') (ff_addr f')) ->
RFake FS0 RE X m -> In (0, f) FS0 ->
bytes_at asegs m (f + ff_size 0 - 8) (le8 flag) ->
RFake (ffs_remove f FS0) RE X (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ fp_RFake FS0 RE X (bv_unsigned flag).
Proof.
intros FS0 m f flag _ RF Hin Hrd. pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2).
pose proof SHP as [SHf ND]. destruct (SHf _ Hin) as (Hc0 & pos & Hp & Ef). cbn [ff_cls ff_addr fst snd] in Hc0, Hp, Ef.
pose proof (SL 0 pos ltac:(rewrite <- Ef; exact Hin) Hp) as SLOT. rewrite <- Ef in SLOT.

assert (Eflag : flag = wz (fs_flag FS 0 pos)).
{ destruct SLOT as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
apply le8_inj. eapply bytes_at_det; [exact Hrd| exact BA| rewrite !length_le8; reflexivity]. }
subst flag.
pose proof (fs_flag_range FS 0 pos Hc0 Hp) as FR. pose proof (fs_foff_range 0 Hc0) as FO.
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
assert (UF : bv_unsigned (wz (fs_flag FS 0 pos)) = fs_flag FS 0 pos) by (apply unsigned_lit; lia).
assert (EA : wz (fs_flag FS 0 pos) = wa (fs_flag FS 0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
pose proof (fs_N_pos 0 Hc0) as N0.
split; [| split].
-
pose proof (wmono_write asegs m m (wz (fs_flag FS 0 pos)) [b8 0] (wmono_refl asegs m)) as WM.
rewrite EA in WM |- *.
assert (FRc : forall A cs, rw_cells asegs m A cs ->
A + Z.of_nat (cells_size cs) <= fs_flag FS 0 0 + pos \/ fs_flag FS 0 0 + pos + 1 <= A ->
rw_cells asegs (write_to_mem m (wa (fs_flag FS 0 0 + pos)) [b8 0]) A cs).
{ intros A cs H D. apply rw_cells_frame; [exact H| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; lia]. }
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [apply fs_shape_remove; exact SHP|].
split. { apply ro_cells_frame; [exact SSL| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia]. }
split. { apply FRc; [exact GC| cbn; unfold fs_flag in *; lia]. }
split. { intros c Hc. destruct (HI c Hc) as [h H]. exists h. apply FRc; [exact H| cbn; unfold fs_hint, fs_flag, kFsClasses in *; lia]. }
split. { intros c Hc. destruct (Z.eq_dec c 0) as [->|Nc].
- rewrite (flags_of_clear_same FS0 0 pos f SHP Hc0 Hp Ef). apply u8arr_write; [apply FL; exact Hc0| rewrite flags_of_length; lia].
- rewrite (flags_of_clear_other FS0 0 f c SHP Hin ltac:(lia)). apply u8arr_frame; [apply FL; exact Hc| unfold fs_flag in *; lia| cbn; unfold fs_flag in *; lia|].
rewrite flags_of_length. cbn [length]. pose proof (fs_N_pos c Hc).
destruct (Z.lt_ge_cases c 0); [lia|]. pose proof (fs_foff_mono 0 c ltac:(lia) ltac:(lia) ltac:(exact (proj2 Hc))). unfold fs_flag. lia. }
split. { intros c p Hcp Hpp. apply ffs_remove_In in Hcp as [Hcp Hne]. cbn [ff_addr snd] in Hne.
pose proof (SL c p Hcp Hpp) as H. destruct (SHf _ Hcp) as (Hcc & _). cbn [ff_cls fst] in Hcc.
pose proof (fs_frame_in_area FS c p Hcc Hpp) as [A1 A2]. unfold fs_area_lo in A1.
assert (64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
apply FRc; [exact H| cbn; unfold fs_flag in *; lia]. }
split; (eapply hjunk_wmono; [| exact WM]); assumption.
-
destruct (FL 0 Hc0) as [_ WR]. rewrite flags_of_length in WR.
replace (wz (fs_flag FS 0 pos)) with (wa (fs_flag FS 0 0 + pos)) by (unfold wa, fs_flag; f_equal; lia).
apply WR. lia.
- rewrite UF. apply (fp_meta FS0 _ SHP). lia.
Qed.

Lemma RFake_nodup : forall FS0 m, RFake FS0 RE X m -> List.NoDup (map ff_addr FS0).
Proof. intros FS0 m RF. pose proof RF as (_ & _ & _ & [_ ND] & _). exact ND. Qed.

End Laws.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) l, (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
intros A B f l INJ ND. induction ND as [|x l NI ND IH]; cbn; constructor.
- intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply NI. rewrite (INJ y x ltac:(right; exact Hy) ltac:(left; reflexivity) E) in Hy. exact Hy.
- apply IH. intros a b Ha Hb. apply INJ; right; assumption.
Qed.

Lemma all_live_count : forall FS0 FS c, 0 <= c ->
(forall pos, 0 <= pos < fs_N c -> live_b FS0 c (fs_frame FS c pos) = true) ->
fs_N c <= Z.of_nat (length (List.filter (fun f => ff_cls f =? c) FS0)).
Proof.
intros FS0 FS c Hc ALL. destruct (Z.lt_ge_cases (fs_N c) 0); [lia|].
set (L := map (fun i => (c, fs_frame FS c (Z.of_nat i))) (seq 0 (Z.to_nat (fs_N c)))).
assert (LEN : length L = Z.to_nat (fs_N c)) by (unfold L; rewrite map_length, seq_length; reflexivity).
assert (ND : List.NoDup L).
{ unfold L. apply NoDup_map_inj; [| apply seq_NoDup]. intros x y _ _ E. injection E as E. apply fs_frame_inj in E; lia. }
assert (INCL : incl L (List.filter (fun f => ff_cls f =? c) FS0)).
{ intros f Hf. unfold L in Hf. apply in_map_iff in Hf as (i & <- & Hi). apply in_seq in Hi.
apply filter_In. split; [| cbn; apply Z.eqb_refl]. apply live_b_true. apply ALL. lia. }
pose proof (NoDup_incl_length ND INCL) as HH. apply Nat2Z.inj_le in HH. rewrite LEN in HH. rewrite Z2Nat.id in HH by lia. exact HH.
Qed.

Lemma scan_exhausts : forall FS0 FS c u i, 0 <= c -> 0 < fs_N c -> 0 <= i ->
(forall j, 0 <= j < i -> live_b FS0 c (fs_frame FS c ((u + j) mod fs_N c)) = true) ->
fs_N c <= i ->
forall pos, 0 <= pos < fs_N c -> live_b FS0 c (fs_frame FS c pos) = true.
Proof.
intros FS0 FS c u i Hc HN Hi BUSY Hfull pos Hp.
set (j := (pos - u) mod fs_N c).
assert (Hj : 0 <= j < fs_N c) by (unfold j; apply Z.mod_pos_bound; lia).
replace pos with ((u + j) mod fs_N c); [apply BUSY; lia|].
unfold j. rewrite Zplus_mod, Zmod_mod, <- Zplus_mod. replace (u + (pos - u)) with pos by lia. apply Z.mod_small. lia.
Qed.

Lemma live_b_cons : forall FS0 c f c' g,
live_b ((c, f) :: FS0) c' g = ((c =? c') && (f =? g)) || live_b FS0 c' g.
Proof. intros. reflexivity. Qed.

Section Take.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma fs_take_fresh : forall FS0 c pos f, fs_shape FS FS0 -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c ->
f = fs_frame FS c pos -> live_b FS0 c f = false -> ~ In f (map ff_addr FS0).
Proof.
intros FS0 c pos f [SHf ND] Hc Hp Ef LB Hin. apply in_map_iff in Hin as ([c' g] & E & Hg). cbn in E. subst g.
destruct (SHf _ Hg) as (Hc' & pos' & Hp' & E'). cbn [ff_cls ff_addr fst snd] in Hc', Hp', E'.
destruct (Z.eq_dec c' c) as [->|NE].
- apply live_b_false in LB. exact (LB Hg).
- assert (0 < ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
assert (0 < ff_size c') by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c'); lia).
destruct (fs_frame_apart_cls FS c pos c' pos' Hc Hc' ltac:(lia) Hp Hp'); rewrite <- Ef, <- E' in *; lia.
Qed.

Lemma fs_shape_take : forall FS0 c pos f, fs_shape FS FS0 -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c ->
f = fs_frame FS c pos -> live_b FS0 c f = false -> fs_shape FS ((c, f) :: FS0).
Proof.
intros FS0 c pos f SHP Hc Hp Ef LB. pose proof SHP as [SHf ND]. split.
- intros g [<-|Hg]; [| exact (SHf g Hg)]. cbn [ff_cls ff_addr fst snd]. split; [exact Hc|]. exists pos. split; [exact Hp| exact Ef].
- cbn [map ff_addr snd]. constructor; [| exact ND]. exact (fs_take_fresh FS0 c pos f SHP Hc Hp Ef LB).
Qed.

Lemma flags_of_set_same : forall FS0 c pos f,
0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame FS c pos ->
flags_of ((c, f) :: FS0) FS c = upd (flags_of FS0 FS c) (Z.to_nat pos) (b8 1).
Proof.
intros FS0 c pos f Hc Hp ->. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (Z.to_nat (fs_N c))) as [Hi|Hi].
2:{ rewrite (proj2 (nth_error_None _ i)) by (rewrite flags_of_length; lia).
rewrite (proj2 (nth_error_None _ i)) by (rewrite upd_length, flags_of_length; lia). reflexivity. }
replace i with (Z.to_nat (Z.of_nat i)) by lia. rewrite flags_of_nth by lia. rewrite live_b_cons, Z.eqb_refl.
destruct (Nat.eq_dec i (Z.to_nat pos)) as [->|Ni].
- rewrite Z2Nat.id by lia. rewrite nth_error_upd_same by (rewrite flags_of_length; lia). rewrite Z.eqb_refl. reflexivity.
- rewrite nth_error_upd_other by lia. rewrite flags_of_nth by lia.
replace (fs_frame FS c pos =? fs_frame FS c (Z.of_nat i)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. intros E. apply fs_frame_inj in E; lia.
Qed.

Lemma flags_of_set_other : forall FS0 c f c', c' <> c -> flags_of ((c, f) :: FS0) FS c' = flags_of FS0 FS c'.
Proof.
intros FS0 c f c' NE. unfold flags_of. apply map_ext. intros i. rewrite live_b_cons.
replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Definition fs_touched (c pos f a : Z) : Prop :=
(fs_hint FS c <= a < fs_hint FS c + 8) \/ a = fs_flag FS c pos
\/ (f <= a < f + ff_size c) \/ (SH f <= a < SH f + ff_size c / 8).

Lemma RFake_take : forall FS0 m m' c pos f (h' : word),
RFake FS0 RE X m -> 0 <= c < kFsClasses -> 0 <= pos < fs_N c -> f = fs_frame FS c pos ->
live_b FS0 c f = false ->
wmono asegs m m' ->
agree_on asegs (fun a => fp_RFake FS0 RE X a /\ ~ fs_touched c pos f a) m m' ->
rw_cells asegs m' (fs_hint FS c) [C8 h'] ->
u8arr asegs m' (fs_flag FS c 0) (upd (flags_of FS0 FS c) (Z.to_nat pos) (b8 1)) ->
rw_cells asegs m' (f + ff_size c - 8) [C8 (wz (fs_flag FS c pos))] ->
RFake ((c, f) :: FS0) RE X m' /\ ~ In f (map ff_addr FS0).
Proof.
intros FS0 m m' c pos f h' RF Hc Hp Ef LB WM AG HINT' FL' SL'.
pose proof RF as (AL & K1 & K2 & SHP & SSL & GC & HI & FL & SL & J1 & J2). pose proof SHP as [SHf ND].
pose proof K1 as K1'. pose proof K2 as K2'. unfold A_FS_MAP_SIZE in K1', K2'.
pose proof (fs_frame_in_area FS c pos Hc Hp) as [A1 A2]. rewrite <- Ef in A1, A2. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in A1, A2.
assert (SZ : 64 <= ff_size c) by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c); lia).
assert (SHhi : 0x7fff8000 <= SH f /\ SH f + ff_size c / 8 <= SH band_lo) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
pose proof SH_band as SHB0.
pose proof (fs_flag_range FS c pos Hc Hp) as FR. pose proof (fs_foff_range c Hc) as FO.
assert (FRESH := fs_take_fresh FS0 c pos f SHP Hc Hp Ef LB).

assert (AGc : forall A cs, rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> fp_RFake FS0 RE X a /\ ~ fs_touched c pos f a) ->
rw_cells asegs m' A cs) by (intros A cs H P; eapply rw_cells_agree; [exact AG| exact H| exact P]).
split; [| exact FRESH].
split; [exact AL|]. split; [exact K1|]. split; [exact K2|]. split; [eapply fs_shape_take; eassumption|].
split. { eapply ro_cells_agree; [exact AG| exact SSL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
split; [apply (fp_meta RE X FS0 a SHP); lia|]. unfold fs_touched, fs_hint, kFsClasses in *. lia. }
split. { apply AGc; [exact GC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
split; [apply (fp_meta RE X FS0 a SHP); lia|]. unfold fs_touched, fs_hint, kFsClasses in *. lia. }
split. { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exists h'; exact HINT'|].
destruct (HI c' Hc') as [h H]. exists h. apply AGc; [exact H|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
unfold fs_hint, kFsClasses in *. split; [apply (fp_meta RE X FS0 a SHP); lia|]. unfold fs_touched, fs_hint. lia. }
split. { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
- rewrite (flags_of_set_same FS0 c pos f Hc Hp Ef). exact FL'.
- rewrite (flags_of_set_other FS0 c f c' NE). eapply u8arr_agree; [exact AG| apply FL; exact Hc'|].
intros a Ha. rewrite flags_of_length in Ha. pose proof (fs_N_pos c' Hc') as N'. rewrite Z2Nat.id in Ha by lia.
pose proof (fs_flag_range FS c' 0 Hc' ltac:(lia)) as FR'. pose proof (fs_foff_range c' Hc') as FO'.
split; [apply (fp_meta RE X FS0 a SHP); unfold fs_flag in *; lia|].
unfold fs_touched, fs_hint, fs_flag, kFsClasses in *.
assert (D : fs_foff c + pos < fs_foff c' \/ fs_foff c' + fs_N c' <= fs_foff c + pos).
{ destruct (Z.lt_ge_cases c c').
- left. pose proof (fs_foff_mono c c' ltac:(lia) ltac:(lia) ltac:(unfold kFsClasses; lia)). lia.
- right. pose proof (fs_foff_mono c' c ltac:(lia) ltac:(lia) ltac:(unfold kFsClasses; lia)). lia. }
lia. }
split. { intros c' p' Hin Hp'. destruct Hin as [E|Hin].
- injection E as E1 E2. subst c'. rewrite Ef in E2. symmetry in E2. apply fs_frame_inj in E2; [|lia]. subst p'. rewrite <- Ef. exact SL'.
- pose proof (SL c' p' Hin Hp') as H. destruct (SHf _ Hin) as (Hc' & _). cbn [ff_cls fst] in Hc'.
pose proof (fs_frame_in_area FS c' p' Hc' Hp') as [B1 B2]. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in B1, B2.
assert (SZ' : 64 <= ff_size c') by (unfold ff_size; pose proof (Z.pow_pos_nonneg 2 c'); lia).
assert (APART : fs_frame FS c' p' + ff_size c' <= f \/ f + ff_size c <= fs_frame FS c' p').
{ destruct (Z.eq_dec c' c) as [->|NE].
- assert (p' <> pos) by (intros ->; rewrite <- Ef in Hin; apply live_b_false in LB; exact (LB Hin)).
rewrite Ef. destruct (fs_frame_apart FS c p' pos ltac:(lia) ltac:(lia)); lia.
- rewrite Ef. destruct (fs_frame_apart_cls FS c' p' c pos Hc' Hc NE Hp' Hp); lia. }
apply AGc; [exact H|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
split; [apply (fp_slot RE X FS0 c' p' a SHP Hin Hp'); lia|].
unfold fs_touched, fs_hint, kFsClasses in *. lia. }
split; eapply hjunk_wmono; eassumption.
Qed.

End Take.

Section Drop.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

End Drop.

Section GconsFacts.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation FS := (ae_fs_base RE).

Lemma live_user_not_fs : forall x, in_live_user LB0 x -> FS <= x < FS + A_FS_MAP_SIZE -> False.
Proof.
intros x LU Hx.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (_ & K & CE & DP & _). cbn [fst snd] in K, CE. unfold iv_disjoint in DP. cbn [fst snd] in DP.
destruct (live_user_where _ _ _ _ _ _ GC x LU) as (p & A & n & Hb & Hx' & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
- pose proof (slot_prim _ _ _ _ _ _ GC c i _ Ht) as (P1 & P2 & _). unfold prim_hi, prim_lo in *.
change (2 ^ 37) with 137438953472 in *. lia.
- destruct (sec_facts _ _ _ _ _ _ GC e He) as (_ & _ & _ & _ & _ & _ & _ & _ & F).
pose proof (proj1 (List.Forall_forall _ _) F _ (fs_obj RE X)) as D. unfold iv_disjoint in D. cbn [fst snd] in D.
unfold kPage in *. lia.
Qed.

End GconsFacts.
