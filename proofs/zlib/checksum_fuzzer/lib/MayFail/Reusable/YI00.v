(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI00.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI0t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section c.
Variable segs : list Segment.
Definition garr8 (mem : word -> option byte) (base : Z) (l : list Z) : Prop :=
forall j, (j < length l)%nat -> val_mem segs mem (base + Z.of_nat j) 1 (nth j l 0) /\ 0 <= nth j l 0 < 256.
Definition bytes_ok (l : list Z) : Prop := Forall (fun b => 0 <= b < 256) l.
Lemma garr8_nil : forall mem base, garr8 mem base [].
Proof. intros mem base j Hj. cbn in Hj. lia. Qed.
Lemma garr8_nthZ : forall mem base l i, garr8 mem base l -> 0 <= i -> (Z.to_nat i < length l)%nat ->
val_mem segs mem (base + i) 1 (nth (Z.to_nat i) l 0) /\ 0 <= nth (Z.to_nat i) l 0 < 256.
Proof. intros mem base l i H Hi Hlt. rewrite <- (Z2Nat.id i) at 1 by exact Hi. exact (H _ Hlt). Qed.
Lemma garr8_bytes_ok : forall mem base l, garr8 mem base l -> bytes_ok l.
Proof.
intros mem base l H. unfold bytes_ok. apply Forall_forall. intros x Hx. destruct (In_nth l x 0 Hx) as (j & Hj & <-). exact (proj2 (H j Hj)).
Qed.
Lemma garr8_mbyte : forall mem base l j, garr8 mem base l -> (j < length l)%nat -> mbyte segs mem (base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)).
Proof.
intros mem base l j H Hj. destruct (H j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. rewrite Hv. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma garr8_frame : forall mem mem' base l, garr8 mem base l ->
(forall a, base <= a < base + Z.of_nat (length l) -> mbyte segs mem' a = mbyte segs mem a) -> garr8 mem' base l.
Proof.
intros mem mem' base l H Hfr j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite Hfr; [apply Hv; exact Hk|]. cbn in Hk. lia.
Qed.
Lemma garr8_zeros : forall mem base n,
(forall a, base <= a < base + Z.of_nat n -> mbyte segs mem a = Some (Z_to_bv 8 0)) -> garr8 mem base (repeat 0 n).
Proof.
intros mem base n Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
intros k Hk. rewrite Hz by lia. f_equal. destruct k as [|k]; [reflexivity | lia].
Qed.
Lemma garr8_upd : forall mem mem' base l i v,
garr8 mem base l -> (i < length l)%nat -> val_mem segs mem' (base + Z.of_nat i) 1 v -> 0 <= v < 256 ->
(forall a, base <= a < base + Z.of_nat (length l) -> a <> base + Z.of_nat i -> mbyte segs mem' a = mbyte segs mem a) ->
garr8 mem' base (YI0t.updn l i v).
Proof.
intros mem mem' base l i v H Hi Hv Hr Hfr j Hj. rewrite YI0t.updn_length in Hj. rewrite YI0t.nth_updn.
destruct (Nat.eqb_spec j i) as [-> | NE].
- apply Nat.ltb_lt in Hi. rewrite Hi. cbn [andb]. split; [exact Hv | exact Hr].
- cbn [andb]. destruct (H j Hj) as [Hv0 Hr0]. split; [|exact Hr0].
intros k Hk. rewrite Hfr; [apply Hv0; exact Hk | cbn in Hk; lia | cbn in Hk; lia].
Qed.
Lemma garr8_app : forall mem base l1 l2, garr8 mem base (l1 ++ l2) <-> garr8 mem base l1 /\ garr8 mem (base + Z.of_nat (length l1)) l2.
Proof.
intros mem base l1 l2. split.
- intros H. split; intros j Hj.
+ specialize (H j ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by exact Hj. exact H.
+ specialize (H (length l1 + j)%nat ltac:(rewrite length_app; lia)). rewrite app_nth2 in H by lia.
replace (length l1 + j - length l1)%nat with j in H by lia. replace (base + Z.of_nat (length l1 + j)) with (base + Z.of_nat (length l1) + Z.of_nat j) in H by lia. exact H.
- intros [H1 H2] j Hj. rewrite length_app in Hj. destruct (Nat.lt_ge_cases j (length l1)) as [Hlt | Hge].
+ rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
+ rewrite app_nth2 by exact Hge. specialize (H2 (j - length l1)%nat ltac:(lia)).
replace (base + Z.of_nat (length l1) + Z.of_nat (j - length l1)) with (base + Z.of_nat j) in H2 by lia. exact H2.
Qed.
Lemma garr8_app1 : forall mem mem' base l v,
garr8 mem base l -> val_mem segs mem' (base + Z.of_nat (length l)) 1 v -> 0 <= v < 256 ->
(forall a, base <= a < base + Z.of_nat (length l) -> mbyte segs mem' a = mbyte segs mem a) -> garr8 mem' base (l ++ [v]).
Proof.
intros mem mem' base l v H Hv Hr Hfr. apply garr8_app. split; [eapply garr8_frame; [exact H | exact Hfr]|].
intros [|j] Hj; cbn in Hj; [|lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
Qed.
Lemma garr8_of_present : forall mem base n,
(forall a, base <= a < base + Z.of_nat n -> present mem a) -> exists l, length l = n /\ garr8 mem base l.
Proof.
intros mem base n. revert base. induction n as [|n IH]; intros base Hp.
- exists []. split; [reflexivity | apply garr8_nil].
- destruct (val_mem1 segs mem base) as (x & Hx & HV); [apply Hp; lia|].
destruct (IH (base + 1)) as (l & Hlen & Hl); [intros a Ha; apply Hp; lia|].
exists (x :: l). split; [cbn; lia|]. intros [|j] Hj.
+ cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact HV | change (2 ^ 8) with 256 in Hx; exact Hx].
+ cbn [nth]. destruct (Hl j ltac:(cbn in Hj; lia)) as [Hv Hr]. split; [|exact Hr].
replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia. exact Hv.
Qed.
End c.
