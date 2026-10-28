(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI1v UI4l UI21 UI2m UI3t UI5o UI5l YI6b UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI20 UI1d UI2l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o UI1l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma bv64_eq0_small : forall v, - 2 ^ 63 < v < 2 ^ 63 -> Z_to_bv 64 v = Z_to_bv 64 0 -> v = 0.
Proof.
intros v Hv E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 64) with (2 ^ 64) in E. rewrite (Z.mod_small 0) in E by lia.
destruct (Z_lt_le_dec v 0) as [l|l]; [| rewrite Z.mod_small in E by lia; exact E].
rewrite <- (Z.mod_add v 1 (2 ^ 64)), Z.mod_small in E by lia. lia.
Qed.
Lemma bv64_neq0 : forall v, v <> 0 -> - 2 ^ 63 < v < 2 ^ 63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
intros v Hnz Hv. destruct (bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0)) eqn:E; [| reflexivity].
exfalso. apply Hnz. apply (bv64_eq0_small v Hv). apply (proj1 (Fs.bv_eqb_eq _ _)). exact E.
Qed.
Lemma cmpPixel_fn_range : forall cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef ic ib,
- 256 < cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef ic ib < 256.
Proof.
intros. unfold cmpPixel_fn.
destruct (negb (Z.land cattr 4 =? 0) && (ic =? ctidx)); [lia|]. destruct (negb (Z.land battr 4 =? 0) && (ib =? btidx)); [lia|].
destruct ((ct_sel battr bnlp ngp <=? ib) || (ct_sel cattr cnlp ngp <=? ic)); [lia|]. apply memcmp_spec_range.
Qed.
Lemma cmp_run_forallb : forall (CMP : Z -> Z -> Z) (cmpm : Z -> Z -> bool) mem0 img fimg (IMG FIMG : list Z),
garr8 ubs0segs mem0 img IMG -> garr8 ubs0segs mem0 fimg FIMG -> length FIMG = length IMG ->
(forall a b, 0 <= a < 256 -> 0 <= b < 256 -> (CMP a b =? 0) = negb (cmpm a b)) ->
forall (n : nat) (k : Z), 0 <= k -> (Z.to_nat k + n = length IMG)%nat ->
cmp_run CMP mem0 img fimg k n = forallb (fun pq => negb (cmpm (fst pq) (snd pq))) (combine (skipn (Z.to_nat k) IMG) (skipn (Z.to_nat k) FIMG)).
Proof.
intros CMP cmpm mem0 img fimg IMG FIMG Hi Hf Hl Hc n. induction n as [|n IH]; intros k Hk Hn.
- cbn [cmp_run]. rewrite skipn_all2 by lia. cbn [combine forallb]. reflexivity.
- cbn [cmp_run]. rewrite (IH (k + 1)) by lia.
assert (Ek : Z.to_nat (k + 1) = Datatypes.S (Z.to_nat k)) by lia. rewrite Ek.
destruct (skipn (Z.to_nat k) IMG) as [|x xs] eqn:SI.
{ exfalso. apply (f_equal (@length Z)) in SI. rewrite length_skipn in SI. cbn in SI. lia. }
destruct (skipn (Z.to_nat k) FIMG) as [|y ys] eqn:SF.
{ exfalso. apply (f_equal (@length Z)) in SF. rewrite length_skipn in SF. cbn in SF. lia. }
assert (Hx : x = nth (Z.to_nat k) IMG 0).
{ pose proof (@nth_skipn Z (Z.to_nat k) IMG 0 0) as E. rewrite SI, Nat.add_0_r in E. cbn [nth] in E. exact E. }
assert (Hy : y = nth (Z.to_nat k) FIMG 0).
{ pose proof (@nth_skipn Z (Z.to_nat k) FIMG 0 0) as E. rewrite SF, Nat.add_0_r in E. cbn [nth] in E. exact E. }
assert (Hxs : xs = skipn (Datatypes.S (Z.to_nat k)) IMG).
{ change (Datatypes.S (Z.to_nat k)) with (1 + Z.to_nat k)%nat. rewrite <- skipn_skipn, SI. reflexivity. }
assert (Hys : ys = skipn (Datatypes.S (Z.to_nat k)) FIMG).
{ change (Datatypes.S (Z.to_nat k)) with (1 + Z.to_nat k)%nat. rewrite <- skipn_skipn, SF. reflexivity. }
rewrite <- Hxs, <- Hys. cbn [combine forallb fst snd]. f_equal.
rewrite (byte_at_garr8 mem0 img IMG k Hi) by lia. rewrite (byte_at_garr8 mem0 fimg FIMG k Hf) by lia.
rewrite <- Hx, <- Hy. apply Hc.
+ rewrite Hx. apply (proj2 (Hi (Z.to_nat k) ltac:(lia))).
+ rewrite Hy. apply (proj2 (Hf (Z.to_nat k) ltac:(lia))).
Qed.
Lemma list_eqb_true_iff : forall a b : list Z, length a = length b -> (YO07.list_eqb a b = true <-> a = b).
Proof.
intros a b Hl. split; intros H.
- destruct (list_eq_dec Z.eq_dec a b) as [E|NE]; [exact E|]. rewrite (list_eqb_neq a b NE Hl) in H. discriminate H.
- subst b. apply list_eqb_refl.
Qed.
Section c.
Variables (G : YO07.gcfg) (attr gen delay ctrans nlp : Z) (lpal img : list Z).
Lemma af_merged_head : forall gs (k : nat) hd, YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = Some hd ->
delay + YO07.f_delay hd <= 65535 -> YO07.flag (YO07.g_gen G) 1 = false ->
af_merged G attr gen delay ctrans nlp lpal img gs =
(if af_same G attr gen delay ctrans nlp lpal img hd then Some (YO07.q_set gs (Z.of_nat k) (Some (YO07.set_delay hd (delay + YO07.f_delay hd)))) else None).
Proof using.
intros gs k hd Hih Hk Hq Hfd Hg. unfold af_merged. rewrite Hih, (qslot_get gs k Hk), Hq, Hg.
replace (delay + YO07.f_delay hd <=? 65535) with true by (symmetry; apply Z.leb_le; exact Hfd). cbn [andb negb]. reflexivity.
Qed.
Lemma af_merged_none_empty : forall gs (k : nat), YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = None ->
af_merged G attr gen delay ctrans nlp lpal img gs = None.
Proof using. intros gs k Hih Hk Hq. unfold af_merged. rewrite Hih, (qslot_get gs k Hk), Hq. reflexivity. Qed.
Lemma af_merged_none_fd : forall gs (k : nat) hd, YO07.s_ihead gs = Z.of_nat k -> (k < 3)%nat -> qslot gs k = Some hd ->
65535 < delay + YO07.f_delay hd -> af_merged G attr gen delay ctrans nlp lpal img gs = None.
Proof using.
intros gs k hd Hih Hk Hq Hfd. unfold af_merged. rewrite Hih, (qslot_get gs k Hk), Hq.
replace (delay + YO07.f_delay hd <=? 65535) with false by (symmetry; apply Z.leb_gt; exact Hfd). reflexivity.
Qed.
Lemma af_merged_none_keep : forall gs, YO07.flag (YO07.g_gen G) 1 = true -> af_merged G attr gen delay ctrans nlp lpal img gs = None.
Proof using.
intros gs Hg. unfold af_merged. destruct (YO07.q_get gs (YO07.s_ihead gs)) as [hd|]; [| reflexivity].
rewrite Hg, Bool.andb_false_r. reflexivity.
Qed.
Lemma af_from_merge_none : forall gs, af_merged G attr gen delay ctrans nlp lpal img gs = None ->
af_from_merge G attr gen delay ctrans nlp lpal img gs = af_rest G attr gen delay ctrans nlp lpal img gs.
Proof using. intros gs H. unfold af_from_merge. rewrite H. reflexivity. Qed.
Lemma af_from_merge_same : forall gs gs', af_merged G attr gen delay ctrans nlp lpal img gs = Some gs' ->
af_from_merge G attr gen delay ctrans nlp lpal img gs = gs'.
Proof using. intros gs gs' H. unfold af_from_merge. rewrite H. reflexivity. Qed.
End c.
Lemma qcount_q_set_some : forall gs (k : nat) hd f, (k < 3)%nat -> qslot gs k = Some hd ->
qcount (YO07.q_set gs (Z.of_nat k) (Some f)) = qcount gs.
Proof.
intros gs k hd f Hk Hq. rewrite !qcount_slots.
destruct k as [|[|[|k]]]; [| | | lia]; cbn [qslot] in Hq; unfold YO07.q_set;
cbn [Z.of_nat Z.eqb Pos.of_succ_nat Pos.eqb Pos.succ qslot YO07.s_q0 YO07.s_q1 YO07.s_q2]; rewrite Hq; reflexivity.
Qed.
Lemma flag1_false_iff : forall x, YO07.flag x 1 = false <-> Z.land x 1 = 0.
Proof. intros x. unfold YO07.flag. destruct (Z.eqb_spec (Z.land x 1) 0); split; intros H; try reflexivity; try discriminate H; [exact e | exfalso; exact (n H)]. Qed.
Lemma flag1_true_iff : forall x, YO07.flag x 1 = true <-> Z.land x 1 <> 0.
Proof. intros x. unfold YO07.flag. destruct (Z.eqb_spec (Z.land x 1) 0); split; intros H; try reflexivity; try discriminate H; [exfalso; exact (H e) | exact n]. Qed.
Lemma U_add_smallAF : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Hx Hy Rx Ry Rs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. lia. Qed.
Lemma U_srl_litAF : forall E a k, 0 <= k < 64 -> U E (SAlu ALU_SRL a (SLit k)) = U E a / 2 ^ k.
Proof.
intros E a k Hk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k.
2:{ replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E a) as R. unfold M64 in R.
apply zcanon_id. unfold M64. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
