(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_slow_model Z_slow_frame Zg_slow_frame.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk DeflateOverlay FlushBlockModel FillWinModel
  SendModel RefFlushBlk13 RefDeflFast1 RefDeflFastM RefDeflFast2 RefDeflFast3 RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma SF_ins_str : forall s str, SF (ins_str s str) = SF s. Proof. reflexivity. Qed.

Lemma SF_tlit1 : forall s, SF (tlit1 s) = SF s. Proof. reflexivity. Qed.
Lemma SF_noins_st : forall s, SF (noins_st s) = SF s. Proof. reflexivity. Qed.
Lemma SF_insl_stf : forall s, SF (insl_st s) = SF s. Proof. reflexivity. Qed.

Lemma SF_fast_insert : forall n s, SF (deflate_fast_insert n s) = SF s.
Proof.
  induction n as [|n IH]; intros s; [reflexivity|].
  rewrite deflate_fast_insert_step. cbv zeta. destruct (negb _); [rewrite IH|]; apply SF_insl_stf.
Qed.

Lemma SF_st_ins : forall s, SF (st_ins s) = SF s.
Proof.
  intros s. unfold st_ins. cbv zeta.
  match goal with |- SF (set_strstart ?U _) = _ => transitivity (SF U); [generalize U; intros U0; reflexivity|] end.
  rewrite SF_fast_insert. reflexivity.
Qed.

Lemma SF_st_noins : forall s, SF (st_noins s) = SF s.
Proof. intros s. rewrite noins_eq. apply SF_noins_st. Qed.

Lemma SF_st_hash : forall s, SF (fst (st_hash s)) = SF s.
Proof. intros s. unfold st_hash. destruct (MIN_MATCH <=? _); [rewrite ins_str_eq; reflexivity| reflexivity]. Qed.

Lemma SF_st_match : forall s hh, SF (st_match s hh) = SF s.
Proof.
  intros s hh. unfold st_match. destruct (lm_cond s hh); [|reflexivity].
  destruct (longest_match_ms s hh) as (ms & E).
  destruct (longest_match s hh) as [s' ml] eqn:EL. cbn [fst] in E. subst s'. reflexivity.
Qed.

Lemma SF_st_dist : forall s, SF (fst (st_dist s)) = SF s.
Proof.
  intros s. rewrite (proj1 (tally_dist_eq s)). cbv zeta.
  destruct (ins_cond _); [rewrite SF_st_ins | rewrite SF_st_noins]; reflexivity.
Qed.

Lemma SF_st_lit : forall s, SF (fst (st_lit s)) = SF s.
Proof. intros s. rewrite tally_lit_eq. reflexivity. Qed.

Lemma SF_st_tally : forall s, SF (fst (st_tally s)) = SF s.
Proof. intros s. unfold st_tally. destruct (MIN_MATCH <=? _); [apply SF_st_dist| apply SF_st_lit]. Qed.

Lemma st_tally_snd : forall s, snd (st_tally s) = (ds_sym_next s + 3 =? ds_sym_end s).
Proof.
  intros s. unfold st_tally. destruct (MIN_MATCH <=? _); [exact (proj2 (tally_dist_eq s))| rewrite tally_lit_eq; reflexivity].
Qed.

Lemma fbody_frameg : forall inp X flush, SCFGg inp X -> trip_ok 32768 32768 X flush ->
  SCFGg inp (fst (st_body X flush)) /\ (OUT X <= OUT (fst (st_body X flush)))%nat.
Proof.
  intros inp X flush C (_ & FW & _ & HOK). destruct (fill_frameg inp X flush C FW) as [C1 O1]. rewrite st_body_eq2.
  destruct (snd (st_fill X flush)) as [o|] eqn:EO; cbn [fst]; [split; [exact C1| rewrite O1; apply le_n]|].
  specialize (HOK eq_refl). rewrite <- O1. set (X1 := fst (st_fill X flush)) in *. clearbody X1.
  destruct HOK as (_ & _ & _ & TOK). unfold st_rest.
  set (X3 := st_match (fst (st_hash X1)) (snd (st_hash X1))) in *.
  assert (E3 : SF X3 = SF X1) by (unfold X3; rewrite SF_st_match; apply SF_st_hash). clearbody X3.
  destruct TOK as (_ & _ & _ & _ & FOK).
  pose proof (SF_st_tally X3) as E7. set (X7 := fst (st_tally X3)) in *. clearbody X7.
  assert (E71 : SF X7 = SF X1) by (rewrite E7; exact E3).
  pose proof (SCFGg_SF _ _ _ E71 C1) as C7. pose proof (OUT_SF _ _ E71) as O7.
  rewrite st_bflush_fst. destruct (snd (st_tally X3)).
  - split; [apply SCFGg_fbo; [exact C7| exact (FOK eq_refl)]|]. rewrite <- O7. apply fbo_out_mono.
  - split; [exact C7| rewrite O7; apply le_n].
Qed.

Definition fast_tailres (s1 : deflate_state) (flush : Z) : deflate_state * block_state :=
  deflate_tail (tail_st s1) flush.

Definition fast_res (flush : Z) (f : nat) (X : deflate_state) : deflate_state * block_state :=
  match snd (deflate_fast_loop f X flush) with
  | Some bs => (fst (deflate_fast_loop f X flush), bs)
  | None => fast_tailres (fst (deflate_fast_loop f X flush)) flush
  end.

Lemma deflate_fast_res : forall s flush, deflate_fast s flush = fast_res flush (lz_fuel s) s.
Proof. intros s flush. rewrite deflate_fast_eq. unfold fast_res, fast_tailres. destruct (snd _); reflexivity. Qed.

Lemma floop_step' : forall f s flush,
  deflate_fast_loop (S f) s flush
  = match snd (st_body s flush) with
    | LCont => deflate_fast_loop f (fst (st_body s flush)) flush
    | LBreak => (fst (st_body s flush), None)
    | LRet bs => (fst (st_body s flush), Some bs)
    end.
Proof.
  intros f s flush. cbn [deflate_fast_loop]. rewrite deflate_fast_body_eq.
  destruct (st_body s flush) as [s' o]. cbn [fst snd]. destruct o; reflexivity.
Qed.

Lemma fast_res_S : forall flush f X,
  fast_res flush (S f) X = match snd (st_body X flush) with
                           | LCont => fast_res flush f (fst (st_body X flush))
                           | LBreak => fast_tailres (fst (st_body X flush)) flush
                           | LRet bs => (fst (st_body X flush), bs)
                           end.
Proof. intros flush f X. unfold fast_res. rewrite floop_step'. destruct (snd (st_body X flush)); reflexivity. Qed.

Definition ftail_safe (flush : Z) (f : nat) (X : deflate_state) : Prop :=
  match snd (deflate_fast_loop f X flush) with Some _ => True | None => tail_ok 32768 (fst (deflate_fast_loop f X flush)) flush end.

Lemma ftail_safe_S : forall flush f X,
  ftail_safe flush (S f) X = match snd (st_body X flush) with
                             | LCont => ftail_safe flush f (fst (st_body X flush))
                             | LBreak => tail_ok 32768 (fst (st_body X flush)) flush
                             | LRet bs => True
                             end.
Proof. intros flush f X. unfold ftail_safe. rewrite floop_step'. destruct (snd (st_body X flush)); reflexivity. Qed.

Lemma fast_safe_open : forall d flush, fast_safe d flush -> ds_w_size d = 32768 -> ds_hash_size d = 32768 ->
  DWF d /\ loop_ok 32768 32768 (lz_fuel d) d flush /\ ftail_safe flush (lz_fuel d) d.
Proof. intros d flush (W & LK & T) E1 E2. rewrite E1, E2 in LK. rewrite E1 in T. split; [exact W|]. split; [exact LK| exact T]. Qed.

Lemma OUT_tail_st : forall s, OUT (tail_st s) = OUT s. Proof. reflexivity. Qed.

Lemma SCFGg_tail_st : forall inp s, SCFGg inp s -> SCFGg inp (tail_st s).
Proof. intros inp s [H1 H2 H3 H5 H4 H9 H6 H7 H8]. constructor; assumption. Qed.

Lemma OUT_ftailres : forall s1 flush, (OUT s1 <= OUT (fst (fast_tailres s1 flush)))%nat.
Proof.
  intros s1 flush. unfold fast_tailres. rewrite <- (OUT_tail_st s1). generalize (tail_st s1). intros t. unfold deflate_tail.
  destruct (flush =? Z_FINISH).
  - pose proof (fbo_out_mono t 1) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 1) as [s' [bs|]]; exact M.
  - destruct (negb (ds_sym_next t =? 0)); [|apply le_n].
    pose proof (fbo_out_mono t 0) as M. rewrite <- flush_block_fst' in M. destruct (flush_block t 0) as [s' [bs|]]; exact M.
Qed.

Lemma OUT_fres : forall inp flush f X, SCFGg inp X -> loop_ok 32768 32768 f X flush ->
  (OUT X <= OUT (fst (fast_res flush f X)))%nat.
Proof.
  intros inp flush. induction f as [|f IH]; intros X C LOK; [destruct LOK|].
  rewrite loop_ok_S in LOK. destruct LOK as [TOK LOK]. rewrite fast_res_S.
  destruct (fbody_frameg inp X flush C TOK) as [C' O'].
  destruct (snd (st_body X flush)) as [| |bs].
  - eapply Nat.le_trans; [exact O'| apply IH; assumption].
  - eapply Nat.le_trans; [exact O'| apply OUT_ftailres].
  - exact O'.
Qed.

Definition ILIF (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2^31 /\ ds_hash_mask X = 32767 /\ ds_w_mask X = 32767 /\ 0 <= ds_hash_shift X < 32
  /\ (forall j, 0 <= j < 65536 -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < 32768 -> 0 <= arr_get (ds_head X) j < 65536).

Lemma ILIF_step : forall X, ILIF X ->
  ILIF (insl_st X) /\ ds_strstart (insl_st X) = ds_strstart X + 1 /\ ds_match_length (insl_st X) = ds_match_length X - 1.
Proof.
  intros X (Hs & Hih & Hhm & Hwm & Hsh & Hwb & Hhb).
  unfold ILIF, insl_st, ins_str. cbv zeta. dsred.
  pose proof (update_hash_range (set_strstart X (ds_strstart X + 1)) (ds_ins_h X) (arr_get (ds_window X) (ds_strstart X + 1 + 2)) ltac:(dsred; lia)) as Hh.
  dsred in Hh. rewrite Hhm in Hh.
  set (h := update_hash _ _ _) in *.
  repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try reflexivity.
  intros j Hj; rewrite arr_get_set; destruct (_ && _); [pose proof (wrap16_range (ds_strstart X + 1)); lia | apply Hhb; exact Hj].
Qed.

Lemma fast_insert_last : forall X, ds_match_length X = 1 -> deflate_fast_insert 1 X = insl_st X.
Proof.
  intros X H. rewrite deflate_fast_insert_step. cbv zeta.
  replace (ds_match_length (insl_st X)) with 0 by (unfold insl_st; dsred; lia). reflexivity.
Qed.

Lemma fast_insert_more : forall n X, ds_match_length X = Z.of_nat (S (S n)) ->
  deflate_fast_insert (S (S n)) X = deflate_fast_insert (S n) (insl_st X).
Proof.
  intros n X H. rewrite deflate_fast_insert_step. cbv zeta.
  replace (ds_match_length (insl_st X) =? 0) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. unfold insl_st. dsred. lia.
Qed.

Lemma insl_st_strstart : forall X, ds_strstart (insl_st X) = ds_strstart X + 1. Proof. reflexivity. Qed.
Lemma insl_st_match_length : forall X, ds_match_length (insl_st X) = ds_match_length X - 1. Proof. reflexivity. Qed.

Lemma fast_insert_strstart : forall n Y, ds_match_length Y = Z.of_nat n -> (1 <= n)%nat ->
  ds_strstart (deflate_fast_insert n Y) = ds_strstart Y + Z.of_nat n /\ ds_match_length (deflate_fast_insert n Y) = 0.
Proof.
  induction n as [|n IH]; intros Y ML N1; [lia|].
  destruct n as [|n'].
  - rewrite (fast_insert_last Y ML). rewrite insl_st_strstart, insl_st_match_length. split; lia.
  - rewrite (fast_insert_more n' Y ML).
    destruct (IH (insl_st Y) ltac:(rewrite insl_st_match_length, ML; lia) ltac:(lia)) as [E1 E2].
    rewrite E1, E2, insl_st_strstart. split; lia.
Qed.

Lemma st_ins_eq : forall T,
  st_ins T = (let Yf := deflate_fast_insert (Z.to_nat (ds_match_length T - 1)) (set_match_length T (ds_match_length T - 1)) in
              set_strstart Yf (ds_strstart Yf + 1)).
Proof. reflexivity. Qed.
