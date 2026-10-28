(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Export WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel.
Import ListNotations.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
Module DecAuxB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import Stdlib.Lists.List. Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition len_ok (l : list byte) (ng alpha : Z) : Prop :=
  forall t i, (0 <= t < ng)%Z -> (0 <= i < alpha)%Z ->
    exists b, nth_error l (Z.to_nat (258 * t + i)) = Some b /\ (1 <= bv_unsigned b <= 20)%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section ZHelpers.
Local Open Scope Z_scope.

Lemma land64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma land64_neg : forall x, -18446744073709551616 <= x < 0 -> Z.land x 18446744073709551615 = x + 18446744073709551616.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64) with 18446744073709551616.
  rewrite <- (Z_mod_plus_full x 1 18446744073709551616). apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zb64_addM : forall x, Z_to_bv 64 (18446744073709551615 + x) = Z_to_bv 64 (x - 1).
Proof.
  intros x. rewrite <- (Z_to_bv_mod64 (18446744073709551615 + x)), <- (Z_to_bv_mod64 (x - 1)). f_equal.
  replace (18446744073709551615 + x) with ((x - 1) + 1 * 2^64) by lia. apply Z_mod_plus_full.
Qed.
End ZHelpers.

End ACeilS1.
End DecAuxB.

Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation swrap32_id := swrap32_small (only parsing).
Notation signed_lit := signed_lit_small (only parsing).
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)

Lemma word_urange : forall x : word, (0 <= bv_unsigned x < 2^64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
Lemma lxor_sign_small : forall y, (0 <= y < 2^63)%Z -> Z.lxor y 9223372036854775808 = (y + 9223372036854775808)%Z.
Proof. intros y Hy. change 9223372036854775808%Z with (2^63)%Z. apply zb_lxor_pow2_small; lia. Qed.
(* [comment removed for export] *)
Lemma swrap32_eqm : forall x y, (x mod 2^32 = y mod 2^32)%Z -> bv_swrap 32 x = bv_swrap 32 y.
Proof. intros x y H. rewrite <- (swrap32_mod x), <- (swrap32_mod y), H. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sx32_of_Z : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply sx32_small. rewrite unsigned_lit; lia. Qed.
(* [comment removed for export] *)
Lemma zx32_of_Z : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sx32_signed : forall w : word, bv_signed (sx32 w) = bv_swrap 32 (bv_unsigned w).
Proof. intros w. unfold sx32. apply signed_lit. pose proof (swrap32_range (bv_unsigned w)). lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma byte_urange : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b0 : byte := Z_to_bv 8 0.
(* [comment removed for export] *)
Definition sv32 (ws : list word) (i : Z) : Z := bv_swrap 32 (bv_unsigned (wnth ws i)).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uv8 (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs b0).

Lemma sv32_nth : forall ws i w, nth_error ws (Z.to_nat i) = Some w -> sv32 ws i = bv_swrap 32 (bv_unsigned w).
Proof. intros ws i w H. unfold sv32, wnth. erewrite nth_error_nth by exact H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma uv8_nth : forall bs i b, nth_error bs (Z.to_nat i) = Some b -> uv8 bs i = bv_unsigned b.
Proof. intros bs i b H. unfold uv8. erewrite nth_error_nth by exact H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nth_error_ok : forall {A} (l : list A) (i : Z) (n : nat),
  length l = n -> (0 <= i < Z.of_nat n)%Z -> exists x, nth_error l (Z.to_nat i) = Some x.
Proof.
  intros A l i n L Hi. destruct (nth_error l (Z.to_nat i)) as [x|] eqn:E; [exists x; reflexivity|].
  apply nth_error_None in E. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ag32s (ws : list word) (f : Z -> Z) (n : Z) : Prop :=
  forall i, (0 <= i < n)%Z -> sv32 ws i = f i.
(* [comment removed for export] *)

Lemma ag32s_refl : forall ws n, ag32s ws (sv32 ws) n.
Proof. intros ws n i Hi. reflexivity. Qed.
(* [comment removed for export] *)

Lemma wnth_upd_same : forall ws i v, (0 <= i)%Z -> (Z.to_nat i < length ws)%nat -> wnth (upd ws (Z.to_nat i) v) i = v.
Proof. intros ws i v Hi Hl. unfold wnth. apply nth_error_nth. apply nth_error_upd_same. exact Hl. Qed.
Lemma wnth_upd_other : forall ws i j v, (0 <= i)%Z -> (0 <= j)%Z -> i <> j -> wnth (upd ws (Z.to_nat i) v) j = wnth ws j.
Proof.
  intros ws i j v Hi Hj Hij. unfold wnth.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length ws)) as [L|G].
  - apply nth_error_nth. rewrite nth_error_upd_other by lia. apply nth_error_nth'. exact L.
  - rewrite !nth_overflow; [reflexivity| exact G| rewrite upd_length; exact G].
Qed.

(* [comment removed for export] *)
Lemma sv32_lit : forall e, (- 2^31 <= e < 2^31)%Z -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 e)) = e.
Proof.
  intros e He. rewrite <- swrap32_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^32 * 2^32)%Z.
  rewrite Zaux.Zmod_mod_mult by lia. rewrite swrap32_mod. apply swrap32_small. exact He.
Qed.

Lemma ag32s_upd : forall ws f n i e,
  ag32s ws f n -> (0 <= i < n)%Z -> (Z.to_nat i < length ws)%nat -> (- 2^31 <= e < 2^31)%Z ->
  ag32s (upd ws (Z.to_nat i) (Z_to_bv 64 e)) (BzModel.zfupd f i e) n.
Proof.
  intros ws f n i e AG Hi Hl He j Hj. unfold sv32. rewrite BzModel.zfupd_eq.
  destruct (Z.eqb_spec j i) as [->|NE].
  - rewrite wnth_upd_same by lia. apply sv32_lit. exact He.
  - rewrite wnth_upd_other by lia. apply AG. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma ag32s_upd_w : forall ws f n i (v : word) e,
  ag32s ws f n -> (0 <= i < n)%Z -> (Z.to_nat i < length ws)%nat -> bv_swrap 32 (bv_unsigned v) = e ->
  ag32s (upd ws (Z.to_nat i) v) (BzModel.zfupd f i e) n.
Proof.
  intros ws f n i v e AG Hi Hl He j Hj. unfold sv32. rewrite BzModel.zfupd_eq.
  destruct (Z.eqb_spec j i) as [->|NE].
  - rewrite wnth_upd_same by lia. exact He.
  - rewrite wnth_upd_other by lia. apply AG. exact Hj.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ArrSplit.
  Variable segs : list Segment.

  Lemma wr_at_app : forall m A n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
    wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
  Proof.
    intros m A n1 n2 H1 H2. unfold wr_at. split.
    - cps_intros (Ha & Hb & H). repeat split; try lia.
      + intros i Hi. apply H. lia.
      + intros i Hi. replace (A + n1 + i)%Z with (A + (n1 + i))%Z by lia. apply H. lia.
    - intros ((Ha & Hb & Hx) & (Ha2 & Hb2 & Hy)). repeat split; try lia.
      intros i Hi. destruct (Z_lt_le_dec i n1).
      + apply Hx. lia.
      + replace (A + i)%Z with (A + n1 + (i - n1))%Z by lia. apply Hy. lia.
  Qed.

  Lemma u8arr_app : forall m A xs ys,
    u8arr segs m A (xs ++ ys) <-> u8arr segs m A xs /\ u8arr segs m (A + Z.of_nat (length xs)) ys.
  Proof.
    intros m A xs ys. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
  Qed.

  Lemma u32arr_app : forall m A xs ys,
    u32arr segs m A (xs ++ ys) <-> u32arr segs m A xs /\ u32arr segs m (A + 4 * Z.of_nat (length xs)) ys.
  Proof.
    intros m A xs ys. unfold u32arr. rewrite u32s_app, bytes_at_app, u32s_length, length_app.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. change (Z.of_nat 4) with 4%Z.
    rewrite Z.mul_add_distr_l, wr_at_app by lia. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma u32arr_window : forall m A ws (i k : nat), (i + k <= length ws)%nat ->
    u32arr segs m A ws <->
    u32arr segs m A (firstn i ws) /\
    u32arr segs m (A + 4 * Z.of_nat i) (firstn k (skipn i ws)) /\
    u32arr segs m (A + 4 * Z.of_nat (i + k)) (skipn (i + k) ws).
  Proof.
    intros m A ws i k Hik.
    rewrite <- (firstn_skipn i ws) at 1. rewrite u32arr_app, firstn_length_le by lia.
    rewrite <- (firstn_skipn k (skipn i ws)) at 1. rewrite u32arr_app, firstn_length_le by (rewrite skipn_length; lia).
    rewrite skipn_skipn, (Nat.add_comm k i).
    replace (A + 4 * Z.of_nat i + 4 * Z.of_nat k)%Z with (A + 4 * Z.of_nat (i + k))%Z by lia. tauto.
  Qed.

  Lemma u8arr_window : forall m A bs (i k : nat), (i + k <= length bs)%nat ->
    u8arr segs m A bs <->
    u8arr segs m A (firstn i bs) /\
    u8arr segs m (A + Z.of_nat i) (firstn k (skipn i bs)) /\
    u8arr segs m (A + Z.of_nat (i + k)) (skipn (i + k) bs).
  Proof.
    intros m A bs i k Hik.
    rewrite <- (firstn_skipn i bs) at 1. rewrite u8arr_app, firstn_length_le by lia.
    rewrite <- (firstn_skipn k (skipn i bs)) at 1. rewrite u8arr_app, firstn_length_le by (rewrite skipn_length; lia).
    rewrite skipn_skipn, (Nat.add_comm k i).
    replace (A + Z.of_nat i + Z.of_nat k)%Z with (A + Z.of_nat (i + k))%Z by lia. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma u32arr_to_CB : forall m A ws,
    u32arr segs m A ws -> rw_cells segs m A [CB (4 * length ws) (u32s ws)].
  Proof.
    intros m A ws [Hb Hw]. split.
    - split. { cbn. rewrite u32s_length. split; [reflexivity| exact I]. }
      cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.inj_mul. exact Hw.
  Qed.

  Lemma u32arr_of_CB : forall m A n ws,
    rw_cells segs m A [CB n (u32s ws)] -> u32arr segs m A ws.
  Proof.
    intros m A n ws H. apply u8arr_of_rw_cells in H. destruct H as [Hb Hw].
    split; [exact Hb|]. rewrite u32s_length, Nat2Z.inj_mul in Hw. exact Hw.
  Qed.

  (* [comment removed for export] *)
  Lemma u32s_repeat_zero : forall k, u32s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (4 * k).
  Proof.
    induction k as [|k IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH.
    replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. reflexivity.
  Qed.
End ArrSplit.

(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac strip_mod64_in_swrap :=
  repeat match goal with
  | |- context [bv_swrap 32 ?e] =>
      match e with
      | context C [Z.modulo ?a 18446744073709551616] =>
          let e' := context C [a] in
          replace (bv_swrap 32 e) with (bv_swrap 32 e') by (apply swrap32_eqm; mlia)
      end
  end.

(* [comment removed for export] *)
Ltac bz32 :=
  strip_mod64_in_swrap;
  repeat match goal with
  | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
  | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
  | |- context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296)
  | |- context [Z.modulo ?e 4294967296] => rewrite (Z.mod_small e 4294967296) by mlia
  | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by mlia
  | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by mlia
  | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by mlia
  | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by mlia
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit_small e) by mlia
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by mlia
  | |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_of_Z e) by mlia
  | |- context [zx32 (Z_to_bv 64 ?e)] => rewrite (zx32_of_Z e) by mlia
  end; zb_fold_lits.

Ltac bz32_in H :=
  repeat match type of H with
  | context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) in H by lia
  | context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) in H by lia
  | context [bv_wrap 32 ?e] => change (bv_wrap 32 e) with (Z.modulo e 4294967296) in H
  | context [Z.modulo ?e 4294967296] => rewrite (Z.mod_small e 4294967296) in H by mlia
  | context [bv_swrap 32 ?e] => rewrite (swrap32_id e) in H by mlia
  | context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) in H by mlia
  | context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) in H by mlia
  | context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) in H by mlia
  | context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit_small e) in H by mlia
  | context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) in H by mlia
  end; zb_fold_lits_in H.

(* [comment removed for export] *)
Ltac wstep := zstep; bz32.

(* [comment removed for export] *)
Ltac flags := decide_tests; cbn [Z.b2z]; zb_fold_lits.
(* [comment removed for export] *)
Ltac fstep := wstep; flags.

(* [comment removed for export] *)
Ltac solve_cond_m :=
  first [ reflexivity
        | apply Z.ltb_lt; mlia | apply Z.ltb_ge; mlia
        | apply Z.leb_le; mlia | apply Z.leb_gt; mlia
        | apply Z.eqb_eq; mlia | apply Z.eqb_neq; mlia ].
Ltac solve_cond_mrec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_mrec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_mrec
  | _ => solve_cond_m
  end.
Ltac cond_z := symmetry; unfold_cond; fold_lit_ux; zsimp; bz32; zb_masks; solve_cond_mrec.
Ltac if_false_z :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota| cond_z]
  end.
Ltac if_true_z :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota| cond_z]
  end.
(* [comment removed for export] *)
Ltac if_rew H :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => rewrite H; cbv iota
  end.
(* [comment removed for export] *)
Ltac notrap := first [ if_false_z | if_true_z ].

(* [comment removed for export] *)
Ltac st_eq :=
  cbv delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with
                 | |- @eq Z _ _ => lia
                 | |- Z_to_bv _ _ = Z_to_bv _ _ => f_equal
                 | |- _ => progress f_equal
                 end ].

(* [comment removed for export] *)
Tactic Notation "enter_with" uconstr(L) :=
  eapply evt_eq; [ | eapply L ].

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => (Z_to_bv 64 0) end)
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
