(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import FillWinModel BitsModel TreeModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition upd4 (s : deflate_state) (pb : arr) (pd bb bv : Z) : deflate_state :=
  set_bi_valid (set_bi_buf (set_pending (set_pending_buf s pb) pd) bb) bv.

Lemma send_bits_shape : forall s v l,
  send_bits s v l = upd4 s (ds_pending_buf (send_bits s v l)) (ds_pending (send_bits s v l))
                           (ds_bi_buf (send_bits s v l)) (ds_bi_valid (send_bits s v l)).
Proof.
  intros s v l. unfold send_bits, put_short, put_byte, upd4.
  destruct (Buf_size - l <? ds_bi_valid s); reflexivity.
Qed.

Lemma upd4_tree_fc : forall s pb pd bb bv t, tree_fc (upd4 s pb pd bb bv) t = tree_fc s t.
Proof. intros s pb pd bb bv [| |]; reflexivity. Qed.
Lemma upd4_tree_dl : forall s pb pd bb bv t, tree_dl (upd4 s pb pd bb bv) t = tree_dl s t.
Proof. intros s pb pd bb bv [| |]; reflexivity. Qed.

Lemma sb_tree_fc : forall s v l t, tree_fc (send_bits s v l) t = tree_fc s t.
Proof. intros. rewrite send_bits_shape. apply upd4_tree_fc. Qed.
Lemma sb_tree_dl : forall s v l t, tree_dl (send_bits s v l) t = tree_dl s t.
Proof. intros. rewrite send_bits_shape. apply upd4_tree_dl. Qed.
Lemma sb_Len : forall s v l t n, Len (send_bits s v l) t n = Len s t n.
Proof. intros. unfold Len. rewrite sb_tree_dl. reflexivity. Qed.
Lemma sb_Code : forall s v l t n, Code (send_bits s v l) t n = Code s t n.
Proof. intros. unfold Code. rewrite sb_tree_fc. reflexivity. Qed.
Lemma sb_pbl : forall s v l, arr_len (ds_pending_buf (send_bits s v l)) = arr_len (ds_pending_buf s).
Proof.
  intros s v l. unfold send_bits, put_short, put_byte.
  destruct (Buf_size - l <? ds_bi_valid s); dsred; rewrite ?arr_len_set; reflexivity.
Qed.
Lemma sb_lens : forall s v l, tree_lens s -> tree_lens (send_bits s v l).
Proof. intros s v l H. rewrite send_bits_shape. unfold upd4, tree_lens in *. dsred. exact H. Qed.




Definition BINV (PBL : Z) (s : deflate_state) : Prop :=
  0 <= ds_bi_valid s <= 16 /\ 0 <= ds_bi_buf s < 2 ^ 16 /\ 0 <= ds_pending s <= PBL.

Definition sb_room (PBL : Z) (s : deflate_state) (l : Z) : Prop :=
  Buf_size - l < ds_bi_valid s -> ds_pending s + 2 <= PBL.

Lemma wrap16_range' : forall z, 0 <= wrap16 z < 2 ^ 16.
Proof. intros z. rewrite wrap16_mod'. apply Z.mod_pos_bound. lia. Qed.

Lemma send_bits_BINV : forall PBL s v l,
  BINV PBL s -> 0 <= l <= 16 -> sb_room PBL s l -> BINV PBL (send_bits s v l).
Proof.
  intros PBL s v l (Hbv & Hbb & Hpd) Hl Hroom. unfold sb_room, Buf_size in *.
  unfold send_bits, Buf_size, put_short, put_byte, BINV.
  destruct (Z.ltb_spec (16 - l) (ds_bi_valid s)) as [C|C]; dsred.
  - specialize (Hroom C). split; [lia|]. split; [|lia].
    pose proof (wrap16_range' v) as W. rewrite Z.shiftr_div_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 (16 - ds_bi_valid s) ltac:(lia) ltac:(lia)).
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
  - split; [lia|]. split; [apply wrap16_range'|]. lia.
Qed.


Fixpoint sbs_run (s : deflate_state) (cs : list (Z * Z)) : deflate_state :=
  match cs with
  | [] => s
  | (v, l) :: r => sbs_run (send_bits s v l) r
  end.

Fixpoint sbs_ok (PBL : Z) (s : deflate_state) (cs : list (Z * Z)) : Prop :=
  match cs with
  | [] => True
  | (v, l) :: r => 0 <= l <= 16 /\ sb_room PBL s l /\ sbs_ok PBL (send_bits s v l) r
  end.

Lemma sbs_run_app : forall s a b, sbs_run s (a ++ b) = sbs_run (sbs_run s a) b.
Proof. intros s a. revert s. induction a as [|[v l] a IH]; intros; [reflexivity|]. cbn. apply IH. Qed.

Lemma sbs_ok_app : forall PBL s a b, sbs_ok PBL s (a ++ b) <-> sbs_ok PBL s a /\ sbs_ok PBL (sbs_run s a) b.
Proof.
  intros PBL s a. revert s. induction a as [|[v l] a IH]; intros; cbn; [tauto|].
  rewrite IH. tauto.
Qed.

Lemma sbs_BINV : forall PBL cs s, BINV PBL s -> sbs_ok PBL s cs -> BINV PBL (sbs_run s cs).
Proof.
  induction cs as [|[v l] cs IH]; intros s HB Hok; [exact HB|].
  cbn in *. destruct Hok as (Hl & Hr & Hok). apply IH; [apply send_bits_BINV; assumption | exact Hok].
Qed.

Lemma sbs_tree_fc : forall cs s t, tree_fc (sbs_run s cs) t = tree_fc s t.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_tree_fc. Qed.
Lemma sbs_tree_dl : forall cs s t, tree_dl (sbs_run s cs) t = tree_dl s t.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_tree_dl. Qed.
Lemma sbs_Len : forall cs s t n, Len (sbs_run s cs) t n = Len s t n.
Proof. intros. unfold Len. rewrite sbs_tree_dl. reflexivity. Qed.
Lemma sbs_Code : forall cs s t n, Code (sbs_run s cs) t n = Code s t n.
Proof. intros. unfold Code. rewrite sbs_tree_fc. reflexivity. Qed.
Lemma sbs_pbl : forall cs s, arr_len (ds_pending_buf (sbs_run s cs)) = arr_len (ds_pending_buf s).
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply sb_pbl. Qed.
Lemma sbs_lens : forall cs s, tree_lens s -> tree_lens (sbs_run s cs).
Proof. induction cs as [|[v l] cs IH]; intros s H; [exact H|]. cbn. apply IH. apply sb_lens. exact H. Qed.


Definition blc (s : deflate_state) (c : Z) : Z * Z := (Code s TB c, Len s TB c).

Definition st_calls (s : deflate_state) (mn curlen prevlen count : Z) : list (Z * Z) :=
  if count <? mn then repeat (blc s curlen) (Z.to_nat count)
  else if negb (curlen =? 0) then
    (if negb (curlen =? prevlen) then [blc s curlen] else [])
      ++ [blc s REP_3_6; ((if negb (curlen =? prevlen) then count - 1 else count) - 3, 2)]
  else if count <=? 10 then [blc s REPZ_3_10; (count - 3, 3)]
  else [blc s REPZ_11_138; (count - 11, 7)].

Lemma send_tree_rep_sbs : forall k s c count,
  (1 <= k)%nat -> count = Z.of_nat k ->
  send_tree_rep k s c count = sbs_run s (repeat (blc s c) k).
Proof.
  induction k as [|k IH]; intros s c count Hk Hc; [lia|].
  cbn [send_tree_rep repeat sbs_run]. unfold send_dcode, blc.
  destruct k as [|k'].
  - cbn [repeat sbs_run]. replace (count - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (count - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    rewrite (IH _ c (count - 1)) by lia.
    unfold blc. rewrite sb_Code, sb_Len. reflexivity.
Qed.

Lemma send_loop_S : forall f s t mc n prevlen nextlen count mx mn,
  1 <= mn ->
  send_tree_loop (S f) s t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len s t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        send_tree_loop f s t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        send_tree_loop f (sbs_run s (st_calls s mn curlen prevlen count')) t mc (n + 1)
                       curlen nextlen' 0 mx' mn'
    else s.
Proof.
  intros f s t mc n prevlen nextlen count mx mn Hmn. intros. cbn [send_tree_loop].
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((count + 1 <? mx) && (nextlen =? Len s t (n + 1))); [reflexivity|].
  unfold st_calls.
  destruct (Z.ltb_spec (count + 1) mn) as [C1|C1].
  - destruct (Z_le_gt_dec 0 count).
    + rewrite (send_tree_rep_sbs (Z.to_nat (count + 1)) s nextlen (count + 1)) by lia. reflexivity.
    +
      replace (Z.to_nat (count + 1)) with 0%nat by lia. reflexivity.
  - destruct (negb (nextlen =? 0)).
    + unfold send_dcode, blc. destruct (negb (nextlen =? prevlen)); cbn [sbs_run app]; rewrite ?sb_Code, ?sb_Len; reflexivity.
    + unfold send_dcode, blc. destruct (count + 1 <=? 10); cbn [sbs_run]; reflexivity.
Qed.

Lemma send_loop_out : forall f s t mc n p q c mx mn, mc < n -> send_tree_loop f s t mc n p q c mx mn = s.
Proof.
  intros [|f] s t mc n p q c mx mn H; [reflexivity|]. cbn [send_tree_loop].
  destruct (Z.leb_spec n mc); [lia | reflexivity].
Qed.

Fixpoint send_tree_ok (PBL : Z) (fuel : nat) (s : deflate_state) (t : tree_id) (mc n : Z)
         (prevlen nextlen count mx mn : Z) : Prop :=
  match fuel with
  | O => True
  | S f =>
      if n <=? mc then
        let curlen := nextlen in
        let nextlen' := Len s t (n + 1) in
        let count' := count + 1 in
        if (count' <? mx) && (curlen =? nextlen') then
          send_tree_ok PBL f s t mc (n + 1) prevlen nextlen' count' mx mn
        else
          let cs := st_calls s mn curlen prevlen count' in
          let '(mx', mn') := tree_counts curlen nextlen' in
          sbs_ok PBL s cs
          /\ send_tree_ok PBL f (sbs_run s cs) t mc (n + 1) curlen nextlen' 0 mx' mn'
      else True
  end.

Lemma send_loop_tree_fc : forall f s t mc n p q c mx mn t', 1 <= mn ->
  tree_fc (send_tree_loop f s t mc n p q c mx mn) t' = tree_fc s t'
  /\ tree_dl (send_tree_loop f s t mc n p q c mx mn) t' = tree_dl s t'
  /\ arr_len (ds_pending_buf (send_tree_loop f s t mc n p q c mx mn)) = arr_len (ds_pending_buf s)
  /\ (tree_lens s -> tree_lens (send_tree_loop f s t mc n p q c mx mn)).
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn t' Hmn; [cbn; tauto|].
  rewrite send_loop_S by exact Hmn.
  destruct (n <=? mc); [|tauto]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:E.
  pose proof (tree_counts_range _ _ _ _ E) as [_ Hmn'].
  destruct (IH (sbs_run s (st_calls s mn q p (c + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' t' ltac:(lia))
    as (A & B & C & D).
  rewrite A, B, C, sbs_tree_fc, sbs_tree_dl, sbs_pbl.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros HL0. apply D. apply sbs_lens. exact HL0.
Qed.
