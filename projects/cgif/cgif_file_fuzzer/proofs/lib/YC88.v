(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP09 YP03 YN3v YI04 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YG0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YA0i YA0n YG00 YG0a YG01 YG0f YG0d YCbq YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma mbyte_of_frame_x : forall segs E rs (m m' : word -> option byte) a,
frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
(forall r, In r rs -> ~ (base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r)) ->
mbyte segs m' a = mbyte segs m a.
Proof.
intros segs E rs m m' a HF Ha Hout. unfold mbyte. rewrite HF; [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). exact (Hout r Hin Hr).
Qed.
Ltac nat_lt_lit_x := apply (proj1 (Nat.ltb_lt _ _)); reflexivity.
Ltac ew_havocX := repeat (rewrite ew_havoc_old; [|nat_lt_lit_x]).
Ltac mb_frame_x HF rng win :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
rewrite (mbyte_of_frame_x _ E rs m m' _ HF); [ | rng |
let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havocX; win |]);
[ .. | destruct Hr ] ]
end.
Lemma frame_of_outside : forall E rs (m m' : word -> option byte) lo hi (x : word),
frame_of E rs m m' ->
(forall r, In r rs -> r_whi r <= r_wlo r \/ (lo <= base_val E (r_base r) + r_wlo r /\ base_val E (r_base r) + r_whi r <= hi)) ->
(bv_unsigned x < lo \/ hi <= bv_unsigned x) -> m' x = m x.
Proof.
intros E rs m m' lo hi x HF Hrs Hx. apply HF. intros (r & Hin & Hr). destruct (Hrs r Hin) as [Hw | [H1 H2]]; lia.
Qed.
Section c.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Lemma aview_mbyte : forall H m a, aview segs H m a = option_map (fun b : byte => bv_unsigned b) (mbyte segs (mrestrict H m) a).
Proof. reflexivity. Qed.
Lemma mbyte_of_aview_eq : forall H H' (m m' : word -> option byte) a a',
aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma garr8_aview : forall H H' (m m' : word -> option byte) p p' L,
(forall i, 0 <= i < Z.of_nat (length L) -> aview segs H' m' (p' + i) = aview segs H m (p + i)) ->
garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H' m') p' L.
Proof.
intros H H' m m' p p' L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. cbn in Hk. pose proof (Hv k Hk) as Hb.
rewrite (mbyte_of_aview_eq H H' m m' (p + Z.of_nat j + Z.of_nat k) (p' + Z.of_nat j + Z.of_nat k)); [exact Hb|].
replace (p' + Z.of_nat j + Z.of_nat k) with (p' + (Z.of_nat j + Z.of_nat k)) by lia.
replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia.
apply HE. lia.
Qed.
Lemma garr8_aview_kept : forall H H' (m m' : word -> option byte) p L,
(forall a, p <= a < p + Z.of_nat (length L) -> aview segs H' m' a = aview segs H m a) ->
garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H' m') p L.
Proof.
intros H H' m m' p L HE HG. apply (garr8_aview H H' m m' p p L); [|exact HG].
intros i Hi. apply HE. lia.
Qed.
Lemma le_byte_1_0 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma val_mem1_of_aview : forall H m a v,
aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate]. injection Hv as <-.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
rewrite (le_byte_1_0 _ Hr). symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma garr8_one_of_aview : forall H m a v,
aview segs H m a = Some v -> garr8 segs (mrestrict H m) a [v].
Proof.
intros H m a v Hv. destruct (val_mem1_of_aview H m a v Hv) as [Hm Hr].
intros j Hj. cbn in Hj. destruct j; [|lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hm | exact Hr].
Qed.
Lemma garr8_of_memset : forall H m d x n,
0 <= n -> (forall i, 0 <= i < n -> aview segs H m (d + i) = Some (x mod 256)) ->
garr8 segs (mrestrict H m) d (repeat (x mod 256) (Z.to_nat n)).
Proof.
intros H m d x n Hn HE j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
destruct (val_mem1_of_aview H m (d + Z.of_nat j) (x mod 256) (HE (Z.of_nat j) ltac:(lia))) as [Hm Hr].
split; [exact Hm | exact Hr].
Qed.
Lemma garr8_sub_x : forall (m : word -> option byte) p L (a n : nat),
garr8 segs m p L -> (a + n <= length L)%nat -> garr8 segs m (p + Z.of_nat a) (firstn n (skipn a L)).
Proof.
intros m p L a n HG Hle j Hj. rewrite length_firstn, length_skipn in Hj.
rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn.
destruct (HG (a + j)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
replace (p + Z.of_nat a + Z.of_nat j) with (p + Z.of_nat (a + j)) by lia. exact Hv.
Qed.
Lemma garr8_cons_x : forall (m : word -> option byte) p v L,
val_mem segs m p 1 v -> 0 <= v < 256 -> garr8 segs m (p + 1) L -> garr8 segs m p (v :: L).
Proof.
intros m p v L Hv Hr HG j Hj. destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
- cbn [nth]. cbn in Hj. destruct (HG j ltac:(lia)) as [Hv' Hr']. split; [|exact Hr'].
replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.
Lemma val_mem_aview_kept_x : forall H H' (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HE Hv k Hk. rewrite (mbyte_of_aview_eq H H' m m' (a + Z.of_nat k) (a + Z.of_nat k) (HE (a + Z.of_nat k) ltac:(lia))). exact (Hv k Hk).
Qed.
End c.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma garr8_journal_block_x : forall segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k b m p L,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') ->
b <= p -> p + Z.of_nat (length L) <= b + req_size m ->
(forall a, p <= a < p + Z.of_nat (length L) -> ~ inFP FP a) ->
garr8 segs (mrestrict (w_H W0) mem0) p L -> garr8 segs (mrestrict (w_H W') mem') p L.
Proof.
intros segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k b m p L HJ Hb Hb' Hlo Hhi HnF HG.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (garr8_aview_kept segs (w_H W0) (w_H W') mem0 mem' p L); [|exact HG].
intros a Ha. replace a with (b + (a - b)) by lia. apply (F2 b m (a - b) Hb Hb'); [lia|].
replace (b + (a - b)) with a by lia. exact (HnF a Ha).
Qed.
End e.
