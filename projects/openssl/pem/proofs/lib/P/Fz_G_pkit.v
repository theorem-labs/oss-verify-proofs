(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ZBridge SysStep Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks ClientOwn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition wp_box (P : Prop) : Prop := P.
Definition wp_apbox (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma wp_apart_st : forall X n Y m off k m',
  wp_apbox (X + n <= Y \/ Y + m <= X) -> (0 <=? off) = true -> (off + k <=? n) = true -> (m' <=? m) = true ->
  Y + m' <= X + off \/ X + off + k <= Y.
Proof. unfold wp_apbox. intros X n Y m off k m' AP H1 H2 H3. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia. Qed.

(* [comment removed for export] *)
Lemma wp_apart_sym : forall X n Y m k m',
  wp_apbox (X + n <= Y \/ Y + m <= X) -> (k <=? n) = true -> (m' <=? m) = true -> Y + m' <= X \/ X + k <= Y.
Proof. unfold wp_apbox. intros X n Y m k m' AP H1 H2. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. Qed.

Lemma wp_apart_same : forall X n Y m n' m',
  wp_apbox (X + n <= Y \/ Y + m <= X) -> (n' <=? n) = true -> (m' <=? m) = true -> X + n' <= Y \/ Y + m' <= X.
Proof. unfold wp_apbox. intros X n Y m n' m' AP H1 H2. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. Qed.

(* [comment removed for export] *)
Lemma wp_img_lo : forall A n G c k n',
  wp_box (A + n <= 65536 \/ G <= A) -> (65536 <=? c) = true -> (c + k <=? G) = true -> (n' <=? n) = true -> c + k <= A \/ A + n' <= c.
Proof. unfold wp_box. intros A n G c k n' H H1 H2 H3. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia. Qed.

Lemma wp_img_hi : forall A n G c k n',
  wp_box (A + n <= 65536 \/ G <= A) -> (65536 <=? c) = true -> (c + k <=? G) = true -> (n' <=? n) = true -> A + n' <= c \/ c + k <= A.
Proof. unfold wp_box. intros A n G c k n' H H1 H2 H3. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia. Qed.

(* [comment removed for export] *)
Lemma wp_nodup_apart : forall (pre LB : list block) (i j : nat) (b1 b2 : block),
  List.NoDup (map blk_id (pre ++ LB)) -> nth_error pre i = Some b1 -> nth_error pre j = Some b2 -> i <> j -> blk_id b1 <> blk_id b2.
Proof.
  intros pre LB i j b1 b2 ND E1 E2 NE EQ. apply NE.
  assert (L1 : (i < length pre)%nat) by (apply (proj1 (nth_error_Some pre i)); rewrite E1; discriminate).
  assert (L2 : (j < length pre)%nat) by (apply (proj1 (nth_error_Some pre j)); rewrite E2; discriminate).
  apply (NoDup_nth_error (map blk_id (pre ++ LB))) with (i := i) (j := j).
  - exact ND.
  - rewrite length_map, length_app. lia.
  - rewrite !nth_error_map. rewrite !nth_error_app1 by assumption. rewrite E1, E2. cbn [option_map]. f_equal. exact EQ.
Qed.

(* [comment removed for export] *)
Lemma wp_zero_rw_CB : forall segs m q n,
  bytes_at segs m q (repeat (Z_to_bv 8 0) (Z.to_nat n)) -> wr_at segs m q n -> 0 <= n ->
  rw_cells segs m q [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
  intros segs m q n BA WR Hn. split.
  - split; [cbn; split; [apply repeat_length | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by exact Hn. exact WR.
Qed.

(* [comment removed for export] *)
Lemma wp_cells_congr : forall segs m A cs cs',
  cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' -> rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' EB ES WF [[_ B] W]. split; [split; [exact WF | rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

(* [comment removed for export] *)
Lemma wp_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wp_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wp_land15 : forall x, 0 <= x -> Z.land x 15 = x mod 16.
Proof. intros x Hx. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma wp_lxor_ones : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (L : x = 0 \/ Z.log2 x < 64). { destruct (Z.eq_dec x 0) as [->|]; [left; reflexivity| right; apply Z.log2_lt_pow2; lia]. }
  assert (LG : x = 0 -> Z.log2 x < 64) by (intros ->; cbn; lia).
  assert (LL : Z.log2 x < 64) by (destruct L as [E|L']; [apply LG; exact E | exact L']).
  rewrite <- Z.ldiff_ones_l_low; [| lia | exact LL].
  symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; [lia | exact LL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wp_in_lit := cbn [In]; repeat first [ left; reflexivity | right ].
(* [comment removed for export] *)
Ltac wp_wnorm1 f := match goal with |- context [f ?n] => let v := eval vm_compute in (f n) in lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end; change (f n) with v end.
Ltac wp_wnorm := repeat (wp_wnorm1 wA); repeat (wp_wnorm1 wB); repeat (wp_wnorm1 wBig).
(* [comment removed for export] *)
Ltac wp_ro_lit := cbn [ro_bytes ro_byte app]; repeat split; vm_compute; reflexivity.
Ltac wp_not_in_lit := vm_compute; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH.
Ltac wp_box1 H := lazymatch type of H with ?T => change T with (wp_box T) in H end.
Ltac wp_box_aps := repeat match goal with H : (_ + _ <= _ \/ _ + _ <= _)%Z |- _ => lazymatch type of H with ?T => change T with (wp_apbox T) in H end end.
Ltac wp_clear_aps := repeat match goal with H : wp_apbox _ |- _ => clear H end.

(* [comment removed for export] *)
Ltac wp_ap :=
  match goal with
  | AP : wp_apbox (?X + _ <= ?Y \/ ?Y + _ <= ?X) |- (?Y + _ <= ?X + _ \/ ?X + _ + _ <= ?Y) => apply (wp_apart_st _ _ _ _ _ _ _ AP); reflexivity
  | AP : wp_apbox (?X + _ <= ?Y \/ ?Y + _ <= ?X) |- (?Y + _ <= ?X \/ ?X + _ <= ?Y) => apply (wp_apart_sym _ _ _ _ _ _ AP); reflexivity
  | AP : wp_apbox (?X + _ <= ?Y \/ ?Y + _ <= ?X) |- (?X + _ <= ?Y \/ ?Y + _ <= ?X) => apply (wp_apart_same _ _ _ _ _ _ AP); reflexivity
  | AP : wp_box (?A + _ <= 65536 \/ _ <= ?A) |- (_ <= ?A \/ ?A + _ <= _) => apply (wp_img_lo _ _ _ _ _ _ AP); reflexivity
  | AP : wp_box (?A + _ <= 65536 \/ _ <= ?A) |- (?A + _ <= _ \/ _ <= ?A) => apply (wp_img_hi _ _ _ _ _ _ AP); reflexivity
  end.
(* [comment removed for export] *)
Ltac wp_ap2 := match goal with AP : wp_apbox _ |- _ => unfold wp_apbox in AP; lia | AP : wp_box _ |- _ => unfold wp_box in AP; lia end.
Ltac wp_lia := first [ wp_ap | apply Z.le_refl | lia | wp_ap2 ].
Ltac wp_tslia := lazymatch goal with |- True => exact I | |- (_ /\ _) => split; wp_tslia | |- _ => first [ wp_ap | tlia | wp_ap2 ] end.

(* [comment removed for export] *)
Ltac wp_na := match goal with H : wp_box (~ _) |- _ => exact H end.

(* [comment removed for export] *)
Ltac wp_mi := lazymatch goal with H : mem_inv _ ?mm |- mem_inv _ ?mm => exact H end.
(* [comment removed for export] *)
Ltac wp_stk := rewrite ?unsigned_lit by wp_lia;
  match goal with H : stk _ ?mm _ _ |- stk _ ?mm _ _ => first [exact H | rewrite unsigned_lit in H by wp_lia; exact H] end.
Ltac wp_cells := match goal with H : rw_cells _ ?mm ?a _ |- rw_cells _ ?mm ?a _ => exact H end.
Ltac wp_hyp := match goal with
  | H : mem_inv _ ?mm |- mem_inv _ ?mm => exact H
  | H : stk _ ?mm _ _ |- stk _ ?mm _ _ => first [exact H | rewrite unsigned_lit in H by wp_lia; exact H]
  | H : rw_cells _ ?mm ?a _ |- rw_cells _ ?mm ?a _ => exact H
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wp_notin_pos {A} (l : list A) (i : nat) (x : A) (js : list nat) (ys : list A) :
  List.NoDup l -> nth_error l i = Some x -> map (nth_error l) js = map Some ys -> existsb (Nat.eqb i) js = false -> ~ In x ys.
Proof.
  intros ND Hi. revert ys. induction js as [|j js IH]; intros [|y ys] Hm Hex Hin; cbn in Hm; try discriminate; [exact Hin|].
  injection Hm as Hy Hm'. cbn in Hex. apply Bool.orb_false_iff in Hex. destruct Hex as [Hne Hex].
  destruct Hin as [->|Hin]; [| exact (IH ys Hm' Hex Hin)].
  apply Nat.eqb_neq in Hne. apply Hne. apply (proj1 (NoDup_nth_error l) ND).
  - destruct (Nat.lt_ge_cases i (length l)) as [H|H]; [exact H|]. apply (proj2 (nth_error_None l i)) in H. congruence.
  - congruence.
Qed.

Ltac wp_ubs K := rewrite ?unsigned_lit in K by wp_lia; rewrite ?wp_land7, ?wp_land3, ?wp_land15, ?wp_lxor_ones in K by wp_lia.
Ltac wp_refute K := exfalso; rewrite ?unsigned_lit in K by wp_lia; try wp_ubs K; wp_lia.
Ltac wp_brT := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let K := fresh "K" in if_cases K; try wp_ubs K; zify_cond K; [clear K | wp_refute K] | |- _ => idtac end.
Ltac wp_brF := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => let K := fresh "K" in if_cases K; try wp_ubs K; zify_cond K; [wp_refute K | clear K] | |- _ => idtac end.
