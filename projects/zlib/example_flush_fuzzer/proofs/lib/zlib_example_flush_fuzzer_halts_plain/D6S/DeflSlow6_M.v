(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr FillWinMem TreeMem BitsModel BitsModel2 FlushBlockModel DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel DeflFastModel DeflSlowModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import DeflSlow6_2 DeflSlow6_3 DeflSlow6_5 DeflSlow6_6 DeflSlow6_7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.
Definition st_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
    let s := fill_window s in
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
    else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition st_hash (s : deflate_state) : deflate_state * Z :=
  if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL).

Definition st_bflush (s : deflate_state) (bflush : bool) : deflate_state * loop_out :=
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont).

Definition tail_st (s : deflate_state) : deflate_state :=
  set_insert s (if Z.ltb (ds_strstart s) (MIN_MATCH - 1) then ds_strstart s else MIN_MATCH - 1).

Lemma MIN_LOOKAHEAD_eq : MIN_LOOKAHEAD = 262.
Proof. reflexivity. Qed.

Lemma st_fill_hi : forall s flush, 262 <= ds_lookahead s -> st_fill s flush = (s, None).
Proof.
  intros s flush H. unfold st_fill. rewrite MIN_LOOKAHEAD_eq.
  destruct (Z.ltb_spec (ds_lookahead s) 262); [lia | reflexivity].
Qed.

Definition fill_out (s1 : deflate_state) (flush : Z) : option loop_out :=
  if Z.ltb (ds_lookahead s1) 262 && Z.eqb flush 0 then Some (LRet need_more)
  else if Z.eqb (ds_lookahead s1) 0 then Some LBreak else None.

Lemma st_fill_lo : forall s flush, ds_lookahead s < 262 ->
  st_fill s flush = (fill_window s, fill_out (fill_window s) flush).
Proof.
  intros s flush H. unfold st_fill, fill_out, Z_NO_FLUSH. rewrite MIN_LOOKAHEAD_eq.
  destruct (Z.ltb_spec (ds_lookahead s) 262); [| lia].
  destruct (_ && _); [reflexivity|]. destruct (_ =? 0); reflexivity.
Qed.

Definition hash_hh (s1 : deflate_state) : Z :=
  arr_get (ds_head s1) (update_hash s1 (ds_ins_h s1) (arr_get (ds_window s1) (ds_strstart s1 + 2))).

Lemma st_hash_hi : forall s1, 3 <= ds_lookahead s1 -> st_hash s1 = (ins_str s1 (ds_strstart s1), hash_hh s1).
Proof.
  intros s1 H. unfold st_hash, MIN_MATCH, hash_hh. destruct (Z.leb_spec 3 (ds_lookahead s1)); [| lia].
  rewrite ins_str_eq. reflexivity.
Qed.

Lemma st_hash_lo : forall s1, ds_lookahead s1 < 3 -> st_hash s1 = (s1, NIL).
Proof. intros s1 H. unfold st_hash, MIN_MATCH. destruct (Z.leb_spec 3 (ds_lookahead s1)); [lia | reflexivity]. Qed.


Definition sl_lm_cond (s : deflate_state) (hh : Z) : bool :=
  negb (hh =? 0) && (ds_prev_length s <? ds_max_lazy_match s) && (wrap32 (ds_strstart s - hh) <=? ds_w_size s - 262).

Definition sl_filter (s : deflate_state) : bool :=
  (ds_match_length s <=? 5) && ((ds_strategy s =? 1) || ((ds_match_length s =? 3) && (4096 <? wrap32 (ds_strstart s - ds_match_start s)))).

Definition st_lm (s : deflate_state) (hh : Z) : deflate_state :=
  if sl_lm_cond s hh then
    let s1 := set_match_length (fst (longest_match s hh)) (snd (longest_match s hh)) in
    if sl_filter s1 then set_match_length s1 2 else s1
  else s.

Definition dist_cond (s : deflate_state) : bool := (3 <=? ds_prev_length s) && (ds_match_length s <=? ds_prev_length s).

Definition st_sdist (s : deflate_state) : deflate_state * bool :=
  let mi := wrap32 (ds_strstart s + ds_lookahead s - 3) in
  let '(s1, b) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - 3) in
  let s2 := set_lookahead s1 (wrap32 (ds_lookahead s1 - (ds_prev_length s1 - 1))) in
  let s3 := set_prev_length s2 (ds_prev_length s2 - 2) in
  let s4 := deflate_slow_insert (Z.to_nat (ds_prev_length s3)) s3 mi in
  let s5 := set_match_available s4 0 in
  let s6 := set_match_length s5 2 in
  (set_strstart s6 (ds_strstart s6 + 1), b).

Definition st_slit (s : deflate_state) : deflate_state * loop_out :=
  let '(s1, b) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
  let s2 := if b then flush_block_only s1 0 else s1 in
  let s3 := set_lookahead (set_strstart s2 (ds_strstart s2 + 1)) (ds_lookahead s2 - 1) in
  (s3, if cs_avail_out (ds_strm s3) =? 0 then LRet need_more else LCont).

Definition st_avail (s : deflate_state) : deflate_state * loop_out :=
  (set_lookahead (set_strstart (set_match_available s 1) (ds_strstart s + 1)) (ds_lookahead s - 1), LCont).

Definition st_decide (s4 : deflate_state) : deflate_state * loop_out :=
  if dist_cond s4 then st_bflush (fst (st_sdist s4)) (snd (st_sdist s4))
  else if negb (ds_match_available s4 =? 0) then st_slit s4
  else st_avail s4.

Definition st_srest (s1 : deflate_state) : deflate_state * loop_out :=
  st_decide (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))).

Lemma prev_st_eq : forall s,
  set_match_length (set_prev_match (set_prev_length s (ds_match_length s)) (ds_match_start (set_prev_length s (ds_match_length s)))) (MIN_MATCH - 1)
  = prev_st s.
Proof. intros s. unfold prev_st, MIN_MATCH. dsred. reflexivity. Qed.

Lemma st_decide_eq : forall s4 : deflate_state, sdispatch s4 = st_decide s4.
Proof.
  intros s4. unfold sdispatch, st_decide, dist_cond, st_sdist, st_slit, st_avail, st_bflush, MIN_MATCH.
  destruct (_ && _).
  - destruct (tr_tally_dist _ _ _) as [s5 b]. cbn [fst snd]. replace (3 - 1) with 2 by reflexivity.
    destruct b; [| reflexivity]. destruct (flush_block _ 0) as [s11 [bs|]]; reflexivity.
  - destruct (negb _); [| dsred; reflexivity].
    destruct (tr_tally_lit _ _) as [s5 b]. dsred. destruct (cs_avail_out _ =? 0); reflexivity.
Qed.

Lemma slow_p1_eq : forall s1, slow_p1 s1 = st_srest s1.
Proof.
  intros s1. unfold slow_p1, st_srest, st_hash. destruct (if MIN_MATCH <=? ds_lookahead s1 then _ else _) as [s2 hh]. cbn [fst snd].
  unfold slow_p2. cbv zeta. rewrite prev_st_eq. generalize (prev_st s2); intros s3.
  rewrite st_decide_eq. unfold st_lm, sl_lm_cond, sl_filter, NIL, Z_FILTERED, TOO_FAR, MIN_MATCH. rewrite MIN_LOOKAHEAD_eq.
  destruct (negb (hh =? 0) && _ && _); [| reflexivity].
  destruct (longest_match s3 hh) as [s4 ml]. cbn [fst snd]. reflexivity.
Qed.

Lemma deflate_slow_body_eq : forall s flush,
  deflate_slow_body s flush = match snd (st_fill s flush) with
                              | Some o => (fst (st_fill s flush), o)
                              | None => st_srest (fst (st_fill s flush))
                              end.
Proof.
  intros s flush. rewrite DeflSlowModel.deflate_slow_body_eq. unfold st_fill.
  destruct (ds_lookahead s <? MIN_LOOKAHEAD).
  - destruct (_ && _); [reflexivity|]. destruct (_ =? 0); [reflexivity|]. cbn [fst snd]. apply slow_p1_eq.
  - cbn [fst snd]. apply slow_p1_eq.
Qed.



Lemma hash_hi_eq : forall s1, 3 <= ds_lookahead s1 ->
  prev_st (fst (st_hash s1)) = hash_st s1 /\ snd (st_hash s1) = hash_hh s1.
Proof.
  intros s1 H. rewrite (st_hash_hi s1 H). cbn [fst snd]. split; [| reflexivity].
  unfold prev_st, hash_st, ins_str. dsred. reflexivity.
Qed.

Lemma hash_lo_eq : forall s1, ds_lookahead s1 < 3 -> prev_st (fst (st_hash s1)) = prev_st s1 /\ snd (st_hash s1) = 0.
Proof. intros s1 H. rewrite (st_hash_lo s1 H). split; reflexivity. Qed.

Lemma st_lm_false : forall s hh, sl_lm_cond s hh = false -> st_lm s hh = s.
Proof. intros s hh H. unfold st_lm. rewrite H. reflexivity. Qed.

Lemma st_lm_true : forall s hh, sl_lm_cond s hh = true ->
  st_lm s hh = (let s1 := set_match_length (fst (longest_match s hh)) (snd (longest_match s hh)) in
                if sl_filter s1 then set_match_length s1 2 else s1).
Proof. intros s hh H. unfold st_lm. rewrite H. reflexivity. Qed.


Lemma sl_filter_eq : forall X ms ml,
  sl_filter (set_match_length (set_match_start X ms) ml)
  = ((ml <=? 5) && ((ds_strategy X =? 1) || ((ml =? 3) && (4096 <? wrap32 (ds_strstart X - ms)))))%bool.
Proof. intros. unfold sl_filter. dsred. reflexivity. Qed.

Lemma sl_lm_cond_0 : forall s, sl_lm_cond s 0 = false.
Proof. reflexivity. Qed.

Lemma wrap16_wrap32 : forall x, wrap16 (wrap32 x) = x mod 65536.
Proof.
  intros x. rewrite wrap16_mod', wrap32_mod. change 65536 with (2 ^ 16). apply mod_pow2_le. lia.
Qed.

End FXG.
Ltac leaf_eq :=
  first [ lazymatch goal with |- ?a = ?b => constr_eq a b; reflexivity end
        | lazymatch goal with |- ?a = ?b => lazymatch type of a with Z => lia end end
        | progress f_equal; leaf_eq ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Lemma tdist_D16 : forall a b, wrap16 (wrap16 (wrap32 (a - 1 - b)) - 1) = (a - b + -2) mod 2 ^ 16.
Proof.
  intros a b. rewrite wrap16_wrap32, wrap16_mod'. change 65536 with (2 ^ 16).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sdist_tally_eq : forall X, 3 <= ds_prev_length X <= 258 ->
  set_prev_length
    (set_lookahead (fst (tr_tally_dist X (wrap32 (ds_strstart X - 1 - ds_prev_match X)) (ds_prev_length X - 3)))
                   (ds_lookahead X + 1 - ds_prev_length X))
    (ds_prev_length X - 2)
  = dist_st X
  /\ snd (tr_tally_dist X (wrap32 (ds_strstart X - 1 - ds_prev_match X)) (ds_prev_length X - 3)) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X Hpl. unfold tr_tally_dist, LITERALS, dist_st, sdist, sdist_D, set_Freq, Freq, sym_buf_set. cbv zeta.
  cbn [tree_fc set_tree_fc fst snd].
  rewrite tdist_D16.
  destruct X; cbn in Hpl; cbv -[Z.add Z.sub Z.mul Z.div Z.modulo Z.pow Z.shiftr Z.ltb Z.leb Z.eqb Z.opp arr_set arr_get wrap8 wrap16 wrap32 d_code length_code_a].
  match goal with |- context [wrap8 (?pl - 3)] =>
    let E8 := fresh "E8" in
    assert (E8 : wrap8 (pl - 3) = pl - 3) by (rewrite wrap8_mod'; apply Z.mod_small; lia); rewrite !E8 end.
  split; [| f_equal; lia].
  match goal with |- context [arr_get length_code_a ?l + 256 + 1] =>
    replace (arr_get length_code_a l + 256 + 1) with (arr_get length_code_a l + 257) by lia end.
  match goal with |- context [?lb + (?n + 1 + 1)] =>
    replace (lb + (n + 1 + 1)) with (lb + n + 2) by lia;
    replace (lb + (n + 1)) with (lb + n + 1) by lia;
    replace (n + 1 + 1 + 1) with (n + 3) by lia;
    replace (n + 1 + 1) with (n + 2) by lia end.
  lazymatch goal with |- ?a = ?b => tryif constr_eq a b then reflexivity else (idtac "DISTNEQ" a b; fail) end.
Qed.

Lemma deflate_slow_insert_step : forall n s mi,
  deflate_slow_insert (S n) s mi = (let s' := insl_st s mi in if negb (ds_prev_length s' =? 0) then deflate_slow_insert n s' mi else s').
Proof.
  intros n s mi. rewrite DeflSlowModel.deflate_slow_insert_step. unfold sistep, insl_st. dsred.
  destruct (ds_strstart s + 1 <=? mi); [rewrite ins_str_eq; cbn [fst]; unfold ins_str; dsred|]; reflexivity.
Qed.

Lemma sdist_eq : forall X,
  3 <= ds_prev_length X <= 258 -> ds_prev_length X - 1 <= ds_lookahead X -> ds_lookahead X < 2 ^ 31 -> 3 <= ds_strstart X + ds_lookahead X -> ds_strstart X + ds_lookahead X < 2 ^ 32 ->
  fst (st_sdist X) = exit_st (deflate_slow_insert (Z.to_nat (ds_prev_length X - 2)) (dist_st X) (ds_strstart X + ds_lookahead X - 3))
  /\ snd (st_sdist X) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X Hpl3 Hpl Hlk Hsl Hsl2. unfold st_sdist.
  destruct (sdist_tally_eq X Hpl3) as [E1 E2].
  destruct (tr_tally_dist X _ _) as [s1 b] eqn:ET. cbn [fst snd] in E1, E2 |- *. subst b. split; [| reflexivity].
  assert (V : ds_lookahead s1 = ds_lookahead X /\ ds_prev_length s1 = ds_prev_length X /\ ds_strstart s1 = ds_strstart X).
  { pose proof (stally_core_keeps X ltac:(lia)) as K. unfold stally_core, MIN_MATCH in K. rewrite ET in K. cbn [fst] in K.
    destruct K as (_ & _ & K1 & K2 & K3 & _). repeat split; assumption. }
  destruct V as (Vl & Vp & Vs).
  replace (wrap32 (ds_strstart X + ds_lookahead X - 3)) with (ds_strstart X + ds_lookahead X - 3)
    by (rewrite wrap32_mod; symmetry; apply Z.mod_small; lia).
  assert (ED : set_prev_length (set_lookahead s1 (wrap32 (ds_lookahead s1 - (ds_prev_length s1 - 1)))) (ds_prev_length (set_lookahead s1 (wrap32 (ds_lookahead s1 - (ds_prev_length s1 - 1)))) - 2) = dist_st X).
  { rewrite <- E1. dsred. rewrite Vl, Vp. rewrite wrap32_mod, Z.mod_small by lia. f_equal. f_equal. lia. }
  rewrite ED. replace (ds_prev_length (dist_st X)) with (ds_prev_length X - 2) by (unfold dist_st; dsred; lia).
  generalize (deflate_slow_insert (Z.to_nat (ds_prev_length X - 2)) (dist_st X) (ds_strstart X + ds_lookahead X - 3)); intros U.
  unfold exit_st. dsred. reflexivity.
Qed.

Lemma slit_tally_eq : forall X,
  fst (tr_tally_lit X (arr_get (ds_window X) (ds_strstart X - 1))) = slit1 X
  /\ snd (tr_tally_lit X (arr_get (ds_window X) (ds_strstart X - 1))) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X. unfold tr_tally_lit. cbv zeta. unfold set_Freq, Freq, sym_buf_set. cbn [tree_fc set_tree_fc fst snd].
  split; [| dsred; f_equal; lia].
  unfold slit1. cbv zeta. dsred.
  replace (ds_sym_next X + 1 + 1) with (ds_sym_next X + 2) by lia.
  replace (ds_sym_next X + 2 + 1) with (ds_sym_next X + 3) by lia.
  replace (ds_lit_bufsize X + (ds_sym_next X + 1)) with (ds_lit_bufsize X + ds_sym_next X + 1) by lia.
  replace (ds_lit_bufsize X + (ds_sym_next X + 2)) with (ds_lit_bufsize X + ds_sym_next X + 2) by lia.
  reflexivity.
Qed.

Lemma st_slit_eq : forall X,
  st_slit X = (let s2 := if Z.eqb (ds_sym_next X + 3) (ds_sym_end X) then flush_block_only (slit1 X) 0 else slit1 X in
               (ltail_st s2, if cs_avail_out (ds_strm (ltail_st s2)) =? 0 then LRet need_more else LCont)).
Proof.
  intros X. unfold st_slit. destruct (slit_tally_eq X) as [E1 E2].
  destruct (tr_tally_lit X _) as [s1 b]. cbn [fst snd] in E1, E2. subst s1 b. cbv zeta. unfold ltail_st.
  reflexivity.
Qed.

Lemma st_avail_eq : forall X, st_avail X = (avail0_st X, LCont).
Proof. intros X. unfold st_avail, avail0_st. dsred. reflexivity. Qed.

Lemma break2_tail : forall X, break2_st X = tail_st X.
Proof.
  intros X. unfold break2_st, tail_st, MIN_MATCH. replace (3 - 1) with 2 by reflexivity. reflexivity.
Qed.

Lemma deflate_slow_eq : forall s flush,
  deflate_slow s flush
  = match snd (deflate_slow_loop (lz_fuel s) s flush) with
    | Some bs => (fst (deflate_slow_loop (lz_fuel s) s flush), bs)
    | None =>
        let s1 := fst (deflate_slow_loop (lz_fuel s) s flush) in
        let s2 := if negb (ds_match_available s1 =? 0) then break1_st s1 else s1 in
        deflate_tail (tail_st s2) flush
    end.
Proof.
  intros s flush. unfold deflate_slow, tail_st. destruct (deflate_slow_loop _ _ _) as [s1 [bs|]]; [reflexivity|]. cbn [fst snd].
  destruct (negb _); [| reflexivity].
  destruct (slit_tally_eq s1) as [E1 _]. destruct (tr_tally_lit s1 _) as [s' b]. cbn [fst] in E1. subst s'.
  unfold break1_st. reflexivity.
Qed.

Lemma sloop_step : forall f s flush,
  deflate_slow_loop (S f) s flush
  = match snd (deflate_slow_body s flush) with
    | LCont => deflate_slow_loop f (fst (deflate_slow_body s flush)) flush
    | LBreak => (fst (deflate_slow_body s flush), None)
    | LRet bs => (fst (deflate_slow_body s flush), Some bs)
    end.
Proof. intros f s flush. cbn [deflate_slow_loop]. destruct (deflate_slow_body s flush) as [s' o]. reflexivity. Qed.

Definition st_sbody (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  match snd (st_fill s flush) with Some o => (fst (st_fill s flush), o) | None => st_srest (fst (st_fill s flush)) end.

Lemma st_sbody_eq : forall s flush, deflate_slow_body s flush = st_sbody s flush.
Proof. intros. rewrite deflate_slow_body_eq. reflexivity. Qed.

Lemma sloop_step' : forall f s flush,
  deflate_slow_loop (S f) s flush
  = match snd (st_sbody s flush) with
    | LCont => deflate_slow_loop f (fst (st_sbody s flush)) flush
    | LBreak => (fst (st_sbody s flush), None)
    | LRet bs => (fst (st_sbody s flush), Some bs)
    end.
Proof. intros. rewrite sloop_step, st_sbody_eq. reflexivity. Qed.

Lemma st_srest_hi : forall s1, 3 <= ds_lookahead s1 -> st_srest s1 = st_decide (st_lm (hash_st s1) (hash_hh s1)).
Proof. intros s1 H. unfold st_srest. destruct (hash_hi_eq s1 H) as [E1 E2]. rewrite E1, E2. reflexivity. Qed.

Lemma st_srest_lo : forall s1, ds_lookahead s1 < 3 -> st_srest s1 = st_decide (st_lm (prev_st s1) 0).
Proof. intros s1 H. unfold st_srest. destruct (hash_lo_eq s1 H) as [E1 E2]. rewrite E1, E2. reflexivity. Qed.

Lemma flush_block_fst : forall s last, fst (flush_block s last) = flush_block_only s last.
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.

Lemma flush_block_snd : forall s last,
  snd (flush_block s last)
  = (if cs_avail_out (ds_strm (fst (flush_block s last))) =? 0
     then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof.
  intros s last. unfold flush_block. cbv zeta.
  destruct (cs_avail_out (ds_strm (flush_block_only s last)) =? 0) eqn:E; cbn [fst snd]; rewrite E; reflexivity.
Qed.

Lemma flush_block_only_eq : forall X last,
  flush_block_only X last
  = (let s1 := tr_flush_bits (set_block_start (tr_flush_block X
        (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None)
        (wrap64 (ds_strstart X - ds_block_start X)) last)
        (ds_strstart (tr_flush_block X (if 0 <=? ds_block_start X then Some (wrap32 (ds_block_start X)) else None)
        (wrap64 (ds_strstart X - ds_block_start X)) last))) in
     if fp_len s1 =? 0 then s1 else fp_tail s1 (fp_len s1)).
Proof.
  intros X last. unfold flush_block_only. cbv zeta. rewrite DeflM.flush_pending_eq. reflexivity.
Qed.


Definition flush_ok6 (FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop) (s : deflate_state) (last : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  let buf := if Z.leb 0 (ds_block_start s) then Some (wrap32 (ds_block_start s)) else None in
  let len := wrap64 (ds_strstart s - ds_block_start s) in
  FBSAFE s buf len last /\ BINV PBL s /\ 0 <= ds_strstart s - ds_block_start s < 2 ^ 32
  /\ - 2 ^ 63 <= ds_block_start s /\ 0 <= ds_strstart s <= 2 * ds_w_size s /\ ds_strstart s < 2 ^ 31
  /\ (forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256)
  /\ let s8 := tr_flush_block s buf len last in
     0 <= ds_strstart s8 <= 2 * ds_w_size s
     /\ let s9 := set_block_start s8 (ds_strstart s8) in
        BINV PBL s9 /\ ds_pending (tr_flush_bits s9) <= PBL
        /\ let s10 := tr_flush_bits s9 in
           0 <= ds_pending s10 < 2 ^ 31 /\ 0 <= ds_pending_out s10 /\ ds_pending_out s10 + fp_len s10 <= PBL
           /\ 0 <= cs_total_out (ds_strm s10) < 2 ^ 64.


Record strip_inv (s : deflate_state) : Prop := {
  si_str : 0 <= ds_strstart s;
  si_sl : ds_strstart s + ds_lookahead s <= 2 * ds_w_size s;
  si_look : 0 <= ds_lookahead s;
  si_ih : 0 <= ds_ins_h s < 2 ^ 31;
  si_hm : ds_hash_mask s = ds_hash_size s - 1;
  si_wm : ds_w_mask s = ds_w_size s - 1;
  si_hs : 0 <= ds_hash_shift s < 32;
  si_ml : 0 <= ds_match_length s <= 258;
  si_ms : 0 <= ds_match_start s < 2 ^ 32;
  si_pl : 0 <= ds_prev_length s <= 258;
  si_pm : 0 <= ds_prev_match s < 2 ^ 32;
  si_ma : 0 <= ds_match_available s <= 1;
  si_strat : 0 <= ds_strategy s <= 4;
  si_lazy : 0 <= ds_max_lazy_match s < 2 ^ 31;
  si_sn : 0 <= ds_sym_next s /\ ds_sym_next s + 3 <= 3 * ds_lit_bufsize s;
  si_se : 0 <= ds_sym_end s < 2 ^ 18;
  si_wb : forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256;
  si_hb : forall j, 0 <= j < ds_hash_size s -> 0 <= arr_get (ds_head s) j < 65536;
  si_pb : forall j, 0 <= j < ds_w_size s -> 0 <= arr_get (ds_prev s) j < 65536;
  si_lh : arr_len (ds_head s) = ds_hash_size s;
  si_lfc : forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536;
  si_dfc : forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc s) i < 65536 }.

Definition lm_ok6 (s : deflate_state) (cur : Z) : Prop :=
  (forall i, 0 <= i < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) i < 256)
  /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536)
  /\ 0 <= ds_strstart s /\ ds_strstart s + 258 < 2 * ds_w_size s /\ ds_w_mask s = ds_w_size s - 1
  /\ 1 <= ds_prev_length s <= 258 /\ 0 <= ds_nice_match s <= 258 /\ 0 <= ds_lookahead s < 2 ^ 31
  /\ 0 <= ds_good_match s < 2 ^ 31 /\ 0 <= ds_max_chain_length s < 2 ^ 31
  /\ 1 <= (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
  /\ 0 <= cur < 2 ^ 31 /\ Forall (fun c => 0 <= c < ds_strstart s) (lm_visited s cur)
  /\ 0 <= snd (longest_match s cur) <= 258.

Section P.
  Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
  Variables (ws hs : Z).
  Local Abbreviation flush_ok := (flush_ok6 FBSAFE).

  Definition sdist_ok (s4 : deflate_state) : Prop :=
    ds_prev_length s4 - 1 <= ds_lookahead s4 /\ 3 <= ds_strstart s4 + ds_lookahead s4 /\ sdist_D s4 < 32768
    /\ (snd (st_sdist s4) = true -> flush_ok (fst (st_sdist s4)) 0).

  Definition slit_ok6 (s4 : deflate_state) : Prop :=
    1 <= ds_strstart s4
    /\ (Z.eqb (ds_sym_next s4 + 3) (ds_sym_end s4) = true -> flush_ok (slit1 s4) 0)
    /\ let s2 := if Z.eqb (ds_sym_next s4 + 3) (ds_sym_end s4) then flush_block_only (slit1 s4) 0 else slit1 s4 in
       0 <= ds_strstart s2 /\ 1 <= ds_lookahead s2 /\ ds_strstart s2 + ds_lookahead s2 <= 2 * ws.

  Definition sdec_ok (s4 : deflate_state) : Prop :=
    strip_inv s4 /\ 1 <= ds_lookahead s4 <= 2 * ws
    /\ if dist_cond s4 then sdist_ok s4
       else if negb (ds_match_available s4 =? 0) then slit_ok6 s4 else True.

  Definition shash_ok (s1 : deflate_state) : Prop :=
    strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
    /\ (sl_lm_cond (prev_st (fst (st_hash s1))) (snd (st_hash s1)) = true -> lm_ok6 (prev_st (fst (st_hash s1))) (snd (st_hash s1)))
    /\ sdec_ok (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))).

  Definition strip_ok (s : deflate_state) (flush : Z) : Prop :=
    0 <= ds_lookahead s <= 2 * ws /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf ws hs s /\ ds_wrap s = 1)
    /\ 0 <= ds_lookahead (fst (st_fill s flush)) <= 2 * ws
    /\ (snd (st_fill s flush) = None -> shash_ok (fst (st_fill s flush))).

  Fixpoint sloop_ok (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
    match fuel with
    | O => False
    | S f => strip_ok s flush
             /\ match snd (st_sbody s flush) with
                | LCont => sloop_ok f (fst (st_sbody s flush)) flush
                | _ => True
                end
    end.

  Lemma sloop_ok_S : forall f s flush,
    sloop_ok (S f) s flush
    = (strip_ok s flush /\ match snd (st_sbody s flush) with LCont => sloop_ok f (fst (st_sbody s flush)) flush | _ => True end).
  Proof. reflexivity. Qed.

  Definition stail_ok (s : deflate_state) (flush : Z) : Prop :=
    strip_inv s /\ 0 <= ds_strstart s <= 2 * ws
    /\ (ds_match_available s <> 0 -> 1 <= ds_strstart s)
    /\ let s2 := if negb (ds_match_available s =? 0) then break1_st s else s in
       0 <= ds_strstart s2 < 2 ^ 31 /\ - 2 ^ 63 <= ds_block_start s2 < 2 ^ 63 /\ 0 <= ds_sym_next s2 < 2 ^ 31
       /\ (flush = Z_FINISH -> flush_ok (tail_st s2) 1)
       /\ (flush <> Z_FINISH -> ds_sym_next s2 <> 0 -> flush_ok (tail_st s2) 0).
End P.

Definition slow_safe6 (FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop) (ds : deflate_state) (flush : Z) : Prop :=
  sloop_ok FBSAFE (ds_w_size ds) (ds_hash_size ds) (lz_fuel ds) ds flush
  /\ match snd (deflate_slow_loop (lz_fuel ds) ds flush) with
     | Some _ => True
     | None => stail_ok FBSAFE (ds_w_size ds) (fst (deflate_slow_loop (lz_fuel ds) ds flush)) flush
     end.

Lemma shash_ok_hi : forall FBSAFE ws s1, shash_ok FBSAFE ws s1 -> 3 <= ds_lookahead s1 ->
  strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (sl_lm_cond (hash_st s1) (hash_hh s1) = true -> lm_ok6 (hash_st s1) (hash_hh s1))
  /\ sdec_ok FBSAFE ws (st_lm (hash_st s1) (hash_hh s1)).
Proof.
  intros FBSAFE ws s1 (A & B & C & D) Hl. destruct (hash_hi_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in C, D.
  exact (conj A (conj B (conj C D))).
Qed.

Lemma shash_ok_lo : forall FBSAFE ws s1, shash_ok FBSAFE ws s1 -> ds_lookahead s1 < 3 ->
  strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (sl_lm_cond (prev_st s1) 0 = true -> lm_ok6 (prev_st s1) 0)
  /\ sdec_ok FBSAFE ws (st_lm (prev_st s1) 0).
Proof.
  intros FBSAFE ws s1 (A & B & C & D) Hl. destruct (hash_lo_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in C, D.
  exact (conj A (conj B (conj C D))).
Qed.
End FXG.
