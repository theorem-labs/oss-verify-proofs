(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface DeflateState Trees DeflateLz DeflateBlk Deflate RefDeflateHdr4
  InflateState Inflate InflateSync HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zlib_header_rc : forall s s' rc, deflate_zlib_header s = (s', Some rc) -> rc = Z_OK.
Proof.
  intros s s' rc. unfold deflate_zlib_header. cbv zeta.
  match goal with |- context [if negb (ds_pending ?X =? 0) then _ else _] => destruct (negb (ds_pending X =? 0)) end;
  intros H; [injection H; auto | discriminate H].
Qed.
Lemma gzip_header_rc : forall s s' rc, deflate_gzip_header s = (s', Some rc) -> rc = Z_OK.
Proof.
  intros s s' rc. unfold deflate_gzip_header. cbv zeta.
  match goal with |- context [if negb (ds_pending ?X =? 0) then _ else _] => destruct (negb (ds_pending X =? 0)) end;
  intros H; [injection H; auto | discriminate H].
Qed.
Lemma blocks_rc : forall s f s' rc, deflate_blocks s f = (s', Some rc) -> rc = Z_OK.
Proof.
  intros s f s' rc. unfold deflate_blocks.
  match goal with |- context [if ?c then _ else (s, None)] => destruct c end; [|intros H; discriminate H].
  destruct (run_compress_func s f) as [s1 bs].
  set (s2 := if block_state_eqb bs finish_started || block_state_eqb bs finish_done then set_status s1 FINISH_STATE else s1). clearbody s2.
  destruct (block_state_eqb bs need_more || block_state_eqb bs finish_started).
  { intros H. injection H. auto. }
  destruct (block_state_eqb bs block_done); [|intros H; discriminate H].
  match goal with |- context [flush_pending ?X] => set (s3 := flush_pending X) end. clearbody s3.
  destruct (cs_avail_out (ds_strm s3) =? 0); intros H; [injection H; auto | discriminate H].
Qed.
Lemma trailer_rc' : forall s, snd (deflate_trailer s) = Z_OK \/ snd (deflate_trailer s) = Z_STREAM_END.
Proof.
  intros s. unfold deflate_trailer. cbv zeta.
  match goal with |- context [negb (ds_pending ?X =? 0)] => destruct (negb (ds_pending X =? 0)) end; cbn [snd]; [left | right]; reflexivity.
Qed.

Lemma deflate_core_rc : forall s f,
  deflateStateCheck s = false -> 0 <= f <= Z_BLOCK ->
  ds_status s <> FINISH_STATE -> cs_avail_out (ds_strm s) <> 0 -> (cs_avail_in (ds_strm s) <> 0 \/ f = Z_FINISH) ->
  snd (deflate_core s f) = Z_OK \/ (snd (deflate_core s f) = Z_STREAM_END /\ f = Z_FINISH).
Proof.
  intros s f CK Hf NS AO AI. unfold deflate_core.
  rewrite CK. cbn [orb]. replace (Z_BLOCK <? f) with false by (symmetry; apply Z.ltb_ge; lia). replace (f <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  replace (ds_status s =? FINISH_STATE) with false by (symmetry; apply Z.eqb_neq; exact NS). cbn [andb].
  replace (cs_avail_out (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AO).
  cbv zeta.
  assert (E1 : ds_status (set_last_flush s f) = ds_status s) by (destruct s; reflexivity).
  assert (E2 : ds_strm (set_last_flush s f) = ds_strm s) by (destruct s; reflexivity).
  match goal with |- context [let '(s0, r) := ?P in _] =>
    assert (PRE : snd P = Some Z_OK \/ (snd P = None /\ ds_status (fst P) = ds_status s)) end.
  { destruct (negb (ds_pending (set_last_flush s f) =? 0)).
    - destruct (cs_avail_out (ds_strm (flush_pending (set_last_flush s f))) =? 0); cbn [fst snd]; [left; reflexivity|].
      right. split; [reflexivity|]. rewrite (proj1 (flush_pending_keeps _)). exact E1.
    - rewrite E2. destruct AI as [AI|EF0].
      + replace (cs_avail_in (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AI). cbn [andb fst snd]. right. split; [reflexivity | exact E1].
      + rewrite EF0. change (negb (Z_FINISH =? Z_FINISH)) with false. rewrite Bool.andb_false_r. cbn [fst snd]. right. split; [reflexivity | exact E1]. }
  match goal with |- context [let '(s0, r) := ?P in _] => destruct P as [s1 [rc1|]] end; cbn [fst snd] in PRE.
  { destruct PRE as [X|[X _]]; [injection X as <-; left; reflexivity | discriminate X]. }
  destruct PRE as [X|[_ S1]]; [discriminate X|].
  rewrite S1. replace (ds_status s =? FINISH_STATE) with false by (symmetry; apply Z.eqb_neq; exact NS). cbn [andb].
  match goal with |- context [let '(s0, r) := (if ?c then deflate_zlib_header ?X else _) in _] =>
    destruct c; [destruct (deflate_zlib_header X) as [s3 [rc3|]] eqn:EH; [apply zlib_header_rc in EH; subst rc3; left; reflexivity|] |] end.
  all: match goal with |- context [let '(s0, r) := (if ?c then deflate_gzip_header ?X else _) in _] =>
    destruct c; [destruct (deflate_gzip_header X) as [s4 [rc4|]] eqn:EG; [apply gzip_header_rc in EG; subst rc4; left; reflexivity|] |] end.
  all: match goal with |- context [let '(s0, r) := deflate_blocks ?X ?F in _] =>
    destruct (deflate_blocks X F) as [s5 [rc5|]] eqn:EB; [apply blocks_rc in EB; subst rc5; left; reflexivity|] end.
  all: match goal with |- context [negb (?F =? Z_FINISH)] => destruct (Z.eqb_spec F Z_FINISH) as [EF|NF]; cbn [negb]; [| left; reflexivity] end.
  all: match goal with |- context [if ?c then (_, Z_STREAM_END) else _] => destruct c; [right; split; [reflexivity | exact EF]|] end.
  all: destruct (trailer_rc' s5) as [T|T]; rewrite T; [left; reflexivity | right; split; [reflexivity | exact EF]].
Qed.

Lemma fl_clen_CLEN : forall n, 0 <= n <= 2 ^ 20 -> fl_clen n = CLEN n.
Proof.
  intros n Hn. unfold fl_clen, CLEN, compressBound_m, cbound. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096. change (2 ^ 14) with 16384. change (2 ^ 25) with 33554432.
  assert (n / 4096 <= 2 ^ 8) by (apply Z.div_le_upper_bound; lia).
  assert (n / 16384 <= 2 ^ 6) by (apply Z.div_le_upper_bound; lia).
  rewrite (Z.div_small n 33554432) by lia.
  pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos n 16384 ltac:(lia) ltac:(lia)).
  rewrite (wrap64_id (n + n / 4096 + n / 16384 + 0 + 13)) by lia.
  apply wrap64_id. lia.
Qed.
Lemma fl_clen_range : forall n, 0 <= n <= 2 ^ 20 -> 126 <= fl_clen n < 2 ^ 22.
Proof. intros n Hn. rewrite fl_clen_CLEN by lia. pose proof (CLEN_ge n ltac:(lia)). pose proof (CLEN_lt32 n Hn). lia. Qed.
Lemma wrap32_fl_clen : forall n, 0 <= n <= 2 ^ 20 -> wrap32 (fl_clen n) = fl_clen n.
Proof. intros n Hn. pose proof (fl_clen_range n Hn). apply wrap32_id. lia. Qed.

Lemma fl_ds1_scalars : forall d,
  ds_status (fl_ds1 d) = INIT_STATE /\ ds_pending (fl_ds1 d) = 0 /\ ds_last_flush (fl_ds1 d) = -2 /\ ds_wrap (fl_ds1 d) = 1
  /\ ds_level (fl_ds1 d) = 6 /\ ds_strategy (fl_ds1 d) = 0
  /\ cs_avail_in (ds_strm (fl_ds1 d)) = 3 /\ cs_avail_out (ds_strm (fl_ds1 d)) = wrap32 (fl_clen (zlength d))
  /\ cs_next_in (ds_strm (fl_ds1 d)) = 0 /\ cs_out_rev (ds_strm (fl_ds1 d)) = [].
Proof.
  intros d. repeat split; reflexivity.
Qed.

Theorem flush1_rc : forall d, 0 <= zlength d <= 2 ^ 20 -> snd (deflate_core (fl_ds1 d) Z_FULL_FLUSH) = Z_OK.
Proof.
  intros d Hn. pose proof (fl_ds1_scalars d) as (ST & _ & _ & _ & _ & _ & AI & AO & _).
  destruct (deflate_core_rc (fl_ds1 d) Z_FULL_FLUSH) as [R|[_ X]].
  - unfold deflateStateCheck. rewrite ST. reflexivity.
  - unfold Z_FULL_FLUSH, Z_BLOCK. lia.
  - rewrite ST. discriminate.
  - rewrite AO, wrap32_fl_clen by lia. pose proof (fl_clen_range (zlength d) Hn). lia.
  - left. rewrite AI. lia.
  - exact R.
  - discriminate X.
Qed.


Definition flush2_entry_stmt : Prop :=
  forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
    deflateStateCheck (fl_ds2 d) = false /\ ds_status (fl_ds2 d) <> FINISH_STATE /\ cs_avail_out (ds_strm (fl_ds2 d)) <> 0.

Theorem flush2_rc_of : flush2_entry_stmt -> forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  snd (deflate_core (fl_ds2 d) Z_FINISH) = Z_OK \/ snd (deflate_core (fl_ds2 d) Z_FINISH) = Z_STREAM_END.
Proof.
  intros HE d Hn Hb. destruct (HE d Hn Hb) as (CK & NS & AO).
  destruct (deflate_core_rc (fl_ds2 d) Z_FINISH CK ltac:(unfold Z_FINISH, Z_BLOCK; lia) NS AO ltac:(right; reflexivity)) as [R|[R _]]; [left | right]; exact R.
Qed.

Corollary flush2_zr_rc_of : flush2_entry_stmt -> forall d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun b => 0 <= b < 256) d ->
  zr_rc (fl_r2 d) = Z_OK \/ zr_rc (fl_r2 d) = Z_STREAM_END.
Proof.
  intros HE d Hn Hb. unfold fl_r2. rewrite fl_call2_core. pose proof (flush2_rc_of HE d Hn Hb) as R.
  destruct (deflate_core (fl_ds2 d) Z_FINISH) as [s rc]. cbn [snd] in R |- *. exact R.
Qed.


Lemma zr0_strm : zr_strm zr0 = {| zs_total_in := 0; zs_total_out := 0; zs_adler := 1; zs_data_type := 2; zs_msg := -1 |}.
Proof. reflexivity. Qed.
Lemma fl_iz0_eq : fl_iz0 = {| zs_total_in := 0; zs_total_out := 0; zs_adler := 1; zs_data_type := 0; zs_msg := -1 |}.
Proof. reflexivity. Qed.
Lemma fl_zc1_eq : forall d, fl_zc1 d = mkZCall (arr_slice (arr_of_list d) 0 3) (wrap32 (fl_clen (zlength d))) (zr_strm zr0).
Proof. reflexivity. Qed.
Lemma fl_zc2_eq : forall d, fl_zc2 d = mkZCall (arr_slice (arr_of_list d) (0 + zr_consumed (fl_r1 d)) (wrap32 (wrap32 (zlength d) - 3)))
                                           (wrap32 (fl_clen (zlength d)) - zlength (zr_output (fl_r1 d))) (zr_strm (fl_r1 d)).
Proof. reflexivity. Qed.
Lemma fl_izc1_eq : forall c n, fl_izc1 c n = mkZCall (arr_slice c 0 2) (wrap32 n) fl_iz0.
Proof. reflexivity. Qed.
Lemma fl_izc2_eq : forall c clen n, fl_izc2 c clen n = mkZCall (arr_slice c (0 + zr_consumed (fl_ir1 c n)) (wrap32 (wrap32 clen - 2)))
                                                        (wrap32 n - zlength (zr_output (fl_ir1 c n))) (zr_strm (fl_ir1 c n)).
Proof. reflexivity. Qed.
Lemma fl_izc3_eq : forall c clen n, fl_izc3 c clen n = mkZCall (arr_slice c (0 + zr_consumed (fl_ir1 c n) + zr_consumed (fl_ir2 c clen n)) (wrap32 (wrap32 clen - 2) - zr_consumed (fl_ir2 c clen n)))
                                                        (wrap32 n - zlength (zr_output (fl_ir1 c n)) - zlength (zr_output (fl_ir2 c clen n))) (zr_strm (fl_ir2 c clen n)).
Proof. reflexivity. Qed.
Lemma Forall_arr_slice : forall (P : Z -> Prop) (a : arr) ofs n, (forall i, P (arr_get a i)) -> Forall P (arr_slice a ofs n).
Proof.
  intros P a ofs n H. unfold arr_slice. generalize ofs. induction (Z.to_nat n) as [|k IH]; intros o; cbn [arr_slice_nat]; constructor; [apply H | apply IH].
Qed.
Lemma arr_get_of_list_byte : forall l i, Forall (fun b => 0 <= b < 256) l -> 0 <= arr_get (arr_of_list l) i < 256.
Proof.
  intros l i H. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  destruct (_ && _ && _).
  - destruct (Nat.lt_ge_cases (Z.to_nat (i - 0)) (length l)) as [L|L].
    + exact (proj1 (Forall_nth _ _) H _ 0 L).
    + rewrite nth_overflow by exact L. lia.
  - rewrite arr_get_make. lia.
Qed.
Lemma Forall_arr_slice_of_list : forall l o n, Forall (fun b => 0 <= b < 256) l -> Forall (fun b => 0 <= b < 256) (arr_slice (arr_of_list l) o n).
Proof. intros l o n H. apply Forall_arr_slice. intros i. apply arr_get_of_list_byte. exact H. Qed.
Lemma arr_slice_of_list_firstn : forall l n, 0 <= n -> (Z.to_nat n <= length l)%nat -> arr_slice (arr_of_list l) 0 n = firstn (Z.to_nat n) l.
Proof.
  intros l n Hn Hl. apply (nth_ext _ _ 0 0); [unfold arr_slice; rewrite arr_slice_nat_length, length_firstn; lia|].
  intros k Hk.
  unfold arr_slice in *. rewrite arr_slice_nat_length in Hk. rewrite arr_slice_nat_nth by exact Hk.
    rewrite (nth_firstn (Z.to_nat n) l k 0). replace (k <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
    unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 _ 0). unfold arr_inb. rewrite arr_len_make.
    replace ((0 <=? 0 + Z.of_nat k) && (0 + Z.of_nat k <? 0 + zlength l) && ((0 <=? 0 + Z.of_nat k) && (0 + Z.of_nat k <? zlength l)))%bool with true.
    2:{ unfold zlength. symmetry. rewrite !Bool.andb_true_iff. rewrite !Z.leb_le, !Z.ltb_lt. lia. }
    f_equal. lia.
Qed.
