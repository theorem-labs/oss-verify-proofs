(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation TOK_SZ := 72 (only parsing).
Notation TSTACK_SZ := 1024 (only parsing).
Notation TOK_DEPTH := 32 (only parsing).

Record tlevel := TL {
tl_st : Z; tl_ss : Z;
tl_cur : Z; tl_cs : option jshape; tl_cbs : list blk;
tl_name : Z; tl_nbs : list blk
}.

Definition lvl_blocks (l : tlevel) : list blk := tl_cbs l ++ tl_nbs l.

Definition srec_cells (l : tlevel) : list cell :=
[C4 (wz (tl_st l)); C4 (wz (tl_ss l)); C8 (wz 0); C8 (wz (tl_cur l)); C8 (wz (tl_name l))].

Definition lvl_clean (l : tlevel) : Prop :=
tl_cur l = 0 /\ tl_cs l = None /\ tl_cbs l = [] /\ tl_name l = 0 /\ tl_nbs l = [].

Definition lvl_zero : tlevel := TL 0 0 0 None [] 0 [].
Lemma lvl_zero_clean : lvl_clean lvl_zero. Proof. repeat split. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Notation rw_cells := (rw_cells segs).

Definition lvl_ok (m : word -> option byte) (l : tlevel) : Prop :=
jopt segs fn (tl_cs l) m (tl_cbs l) (tl_cur l) /\
((tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])).

#[using="Type"] Lemma lvl_clean_ok : forall m l, lvl_clean l -> lvl_ok m l.
Proof. intros m l (H1 & H2 & H3 & H4 & H5). split; [| left; auto]. rewrite H2, H3, H1. cbn. auto. Qed.

#[using="Type"] Lemma lvl_clean_blocks : forall l, lvl_clean l -> lvl_blocks l = [].
Proof. intros l (H1 & H2 & H3 & H4 & H5). unfold lvl_blocks. rewrite H3, H5. reflexivity. Qed.

Definition tstack (m : word -> option byte) (stack : Z) (levels : list tlevel) : Prop :=
forall i l, nth_error levels i = Some l -> rw_cells m (stack + 32 * Z.of_nat i) (srec_cells l).

Record tscal := TS { ts_isd : word; ts_stpos : word; ts_choff : word; ts_err : word;
ts_ucs : word; ts_high : word; ts_quote : byte }.

Definition tok_cells (pb depth stack : Z) (x : tscal) : list cell :=
[C8 (wz 0); C8 (wz pb); C4 (wz TOK_DEPTH); C4 (wz depth);
C4 (ts_isd x); C4 (ts_stpos x); C4 (ts_choff x); C4 (ts_err x);
C4 (ts_ucs x); C4 (ts_high x); C1 (ts_quote x); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (wz stack); C4 (wz 0); C4 (wz 0)].

Definition tokrep_with (m : word -> option byte) (BS : list blk) (tk : Z)
(stack pb depth : Z) (PBS : list blk) (levels : list tlevel) (x : tscal) : Prop :=
BS = (tk, TOK_SZ) :: (stack, TSTACK_SZ) :: PBS ++ concat (map lvl_blocks levels) /\
Z.of_nat (length levels) = TOK_DEPTH /\ 0 <= depth < TOK_DEPTH /\
rw_cells m tk (tok_cells pb depth stack x) /\
pbuf segs m PBS pb /\ pb <> 0 /\
tstack m stack levels /\
(forall i l, nth_error levels i = Some l -> Z.of_nat i <= depth -> lvl_ok m l) /\
(forall i l, nth_error levels i = Some l -> depth < Z.of_nat i -> lvl_clean l).

Definition tokrep (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb depth PBS levels x, tokrep_with m BS tk stack pb depth PBS levels x.

Definition lvl_reset : tlevel := TL 0 1 0 None [] 0 [].

Definition tok_fresh (m : word -> option byte) (BS : list blk) (tk : Z) : Prop :=
exists stack pb PBS,
BS = [(tk, TOK_SZ); (stack, TSTACK_SZ)] ++ PBS /\
rw_cells m tk (tok_cells pb 0 stack (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) /\
pbuf segs m PBS pb /\ pb <> 0 /\
tstack m stack (lvl_reset :: repeat lvl_zero 31).

#[using="Type"] Lemma nth_error_Some_length : forall {A} {l : list A} {i : nat} {x : A}, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply (proj1 (nth_error_Some l i)). congruence. Qed.

#[using="Type"] Lemma nth_error_repeat_some : forall {A} (a : A) n i x, nth_error (repeat a n) i = Some x -> x = a.
Proof.
intros A a n i x H. assert (Hi : (i < n)%nat) by (apply nth_error_Some_length in H; rewrite repeat_length in H; exact H).
rewrite nth_error_repeat in H by exact Hi. congruence.
Qed.

#[using="Type"] Lemma tok_fresh_tokrep : forall m BS tk, tok_fresh m BS tk -> tokrep m BS tk.
Proof.
intros m BS tk (stack & pb & PBS & HBS & HT & HP & Hpb & HS).
exists stack, pb, 0, PBS, (lvl_reset :: repeat lvl_zero 31), (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- rewrite HBS. cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app].
replace (concat (map lvl_blocks (repeat lvl_zero 31))) with (@nil blk) by reflexivity.
rewrite app_nil_r. reflexivity.
- reflexivity.
- lia.
- exact HT.
- exact HP.
- exact Hpb.
- exact HS.
- intros i l Hl Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn in Hl. injection Hl as <-.
split; [cbn; auto | left; cbn; auto].
- intros i l Hl Hi. destruct i as [|i]; [cbn in Hi; lia|]. cbn [nth_error] in Hl.
apply nth_error_repeat_some in Hl. subst l. apply lvl_zero_clean.
Qed.

#[using="Type"] Lemma tstack_get : forall m stack levels i l,
tstack m stack levels -> nth_error levels i = Some l -> rw_cells m (stack + 32 * Z.of_nat i) (srec_cells l).
Proof. intros m stack levels i l H Hl. exact (H i l Hl). Qed.

Fixpoint lupd {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => x :: t
| h :: t, S i' => h :: lupd t i' x
end.

#[using="Type"] Lemma lupd_length : forall {A} (l : list A) i x, length (lupd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.

#[using="Type"] Lemma nth_error_lupd_eq : forall {A} (l : list A) i x, (i < length l)%nat -> nth_error (lupd l i x) i = Some x.
Proof. induction l; intros [|i] x Hi; cbn in *; try lia; auto. apply IHl. lia. Qed.

#[using="Type"] Lemma nth_error_lupd_neq : forall {A} (l : list A) i j x, i <> j -> nth_error (lupd l i x) j = nth_error l j.
Proof. induction l; intros [|i] [|j] x Hij; cbn; auto; try congruence. Qed.

#[using="Type"] Lemma srec_cells_size : forall l, cells_size (srec_cells l) = 32%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma tstack_put : forall m m' stack levels i l' W,
tstack m stack levels ->
(i < length levels)%nat ->
munch ((stack + 32 * Z.of_nat i, stack + 32 * Z.of_nat i + 32) :: W) m m' -> wmono segs m m' ->
(forall j, (j < length levels)%nat -> j <> i -> disjoint_from W (stack + 32 * Z.of_nat j) 32) ->
rw_cells m' (stack + 32 * Z.of_nat i) (srec_cells l') ->
tstack m' stack (lupd levels i l').
Proof.
intros m m' stack levels i l' W HS Hi MU WM HW Hl' j l Hl.
destruct (PeanoNat.Nat.eq_dec j i) as [->|Hne].
- rewrite nth_error_lupd_eq in Hl by exact Hi. injection Hl as <-. exact Hl'.
- rewrite nth_error_lupd_neq in Hl by congruence.
pose proof (nth_error_Some_length Hl) as Hj.
eapply rw_cells_transport; [exact (HS j l Hl) | exact MU | exact WM |].
rewrite srec_cells_size. cbn [disjoint_from Z.of_nat]. split.
+ nia.
+ apply (HW j Hj Hne).
Qed.

#[using="Type"] Lemma tstack_transport : forall m m' stack levels W,
tstack m stack levels -> munch W m m' -> wmono segs m m' ->
(forall j, (j < length levels)%nat -> disjoint_from W (stack + 32 * Z.of_nat j) 32) ->
tstack m' stack levels.
Proof.
intros m m' stack levels W HS MU WM HW j l Hl.
eapply rw_cells_transport; [exact (HS j l Hl) | exact MU | exact WM |]. rewrite srec_cells_size.
apply HW. exact (nth_error_Some_length Hl).
Qed.

End WithSegs.
