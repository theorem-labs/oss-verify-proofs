(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Definition st_sdist (s : deflate_state) : deflate_state * bool :=
  let mi := wrap32 (ds_strstart s + ds_lookahead s - 3) in
  let '(s1, b) := tr_tally_dist s (wrap32 (ds_strstart s - 1 - ds_prev_match s)) (ds_prev_length s - 3) in
  let s2 := set_lookahead s1 (wrap32 (ds_lookahead s1 - (ds_prev_length s1 - 1))) in
  let s3 := set_prev_length s2 (ds_prev_length s2 - 2) in
  let s4 := deflate_slow_insert (Z.to_nat (ds_prev_length s3)) s3 mi in
  let s5 := set_match_available s4 0 in
  let s6 := set_match_length s5 2 in
  (set_strstart s6 (ds_strstart s6 + 1), b).

(* [comment removed for export] *)
Definition st_slit (s : deflate_state) : deflate_state * loop_out :=
  let '(s1, b) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s - 1)) in
  let s2 := if b then flush_block_only s1 0 else s1 in
  let s3 := set_lookahead (set_strstart s2 (ds_strstart s2 + 1)) (ds_lookahead s2 - 1) in
  (s3, if cs_avail_out (ds_strm s3) =? 0 then LRet need_more else LCont).

(* [comment removed for export] *)
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

Lemma st_decide_eq : forall s4 : deflate_state,
  (if (MIN_MATCH <=? ds_prev_length s4) && (ds_match_length s4 <=? ds_prev_length s4) then
    let max_insert := wrap32 (ds_strstart s4 + ds_lookahead s4 - MIN_MATCH) in
    let '(s0, bflush) := tr_tally_dist s4 (wrap32 (ds_strstart s4 - 1 - ds_prev_match s4)) (ds_prev_length s4 - MIN_MATCH) in
    let s5 := set_lookahead s0 (wrap32 (ds_lookahead s0 - (ds_prev_length s0 - 1))) in
    let s6 := set_prev_length s5 (ds_prev_length s5 - 2) in
    let s7 := deflate_slow_insert (Z.to_nat (ds_prev_length s6)) s6 max_insert in
    let s8 := set_match_available s7 0 in
    let s9 := set_match_length s8 (MIN_MATCH - 1) in
    let s10 := set_strstart s9 (ds_strstart s9 + 1) in
    if bflush then let '(s11, r) := flush_block s10 0 in match r with Some bs => (s11, LRet bs) | None => (s11, LCont) end
    else (s10, LCont)
   else if negb (ds_match_available s4 =? 0) then
    let '(s0, bflush) := tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1)) in
    let s5 := if bflush then flush_block_only s0 0 else s0 in
    let s6 := set_strstart s5 (ds_strstart s5 + 1) in
    let s7 := set_lookahead s6 (ds_lookahead s6 - 1) in
    if cs_avail_out (ds_strm s7) =? 0 then (s7, LRet need_more) else (s7, LCont)
   else
    let s0 := set_match_available s4 1 in
    let s5 := set_strstart s0 (ds_strstart s0 + 1) in
    let s6 := set_lookahead s5 (ds_lookahead s5 - 1) in (s6, LCont))
  = st_decide s4.
Proof.
  intros s4. unfold st_decide, dist_cond, st_sdist, st_slit, st_avail, st_bflush, MIN_MATCH.
  destruct (_ && _).
  - destruct (tr_tally_dist _ _ _) as [s5 b]. cbn [fst snd]. replace (3 - 1) with 2 by reflexivity.
    destruct b; [| reflexivity]. destruct (flush_block _ 0) as [s11 [bs|]]; reflexivity.
  - destruct (negb _); [| dsred; reflexivity].
    destruct (tr_tally_lit _ _) as [s5 b]. dsred. destruct (cs_avail_out _ =? 0); reflexivity.
Qed.

Lemma deflate_slow_body_eq : forall s flush,
  deflate_slow_body s flush = match snd (st_fill s flush) with
                              | Some o => (fst (st_fill s flush), o)
                              | None => st_srest (fst (st_fill s flush))
                              end.
Proof.
  intros s flush.
  assert (REST : forall s1,
    (let '(s2, hash_head) := (if MIN_MATCH <=? ds_lookahead s1 then insert_string s1 (ds_strstart s1) else (s1, NIL)) in
     let s3 := set_prev_length s2 (ds_match_length s2) in
     let s3 := set_prev_match s3 (ds_match_start s3) in
     let s3 := set_match_length s3 (MIN_MATCH - 1) in
     let s4 :=
       if negb (hash_head =? NIL) && (ds_prev_length s3 <? ds_max_lazy_match s3)
          && (wrap32 (ds_strstart s3 - hash_head) <=? ds_w_size s3 - MIN_LOOKAHEAD)
       then
         let '(s, ml) := longest_match s3 hash_head in
         let s := set_match_length s ml in
         if (ds_match_length s <=? 5)
            && ((ds_strategy s =? Z_FILTERED)
                || ((ds_match_length s =? MIN_MATCH) && (TOO_FAR <? wrap32 (ds_strstart s - ds_match_start s))))
         then set_match_length s (MIN_MATCH - 1)
         else s
       else s3 in
     (if (MIN_MATCH <=? ds_prev_length s4) && (ds_match_length s4 <=? ds_prev_length s4) then
       let max_insert := wrap32 (ds_strstart s4 + ds_lookahead s4 - MIN_MATCH) in
       let '(s0, bflush) := tr_tally_dist s4 (wrap32 (ds_strstart s4 - 1 - ds_prev_match s4)) (ds_prev_length s4 - MIN_MATCH) in
       let s5 := set_lookahead s0 (wrap32 (ds_lookahead s0 - (ds_prev_length s0 - 1))) in
       let s6 := set_prev_length s5 (ds_prev_length s5 - 2) in
       let s7 := deflate_slow_insert (Z.to_nat (ds_prev_length s6)) s6 max_insert in
       let s8 := set_match_available s7 0 in
       let s9 := set_match_length s8 (MIN_MATCH - 1) in
       let s10 := set_strstart s9 (ds_strstart s9 + 1) in
       if bflush then let '(s11, r) := flush_block s10 0 in match r with Some bs => (s11, LRet bs) | None => (s11, LCont) end
       else (s10, LCont)
      else if negb (ds_match_available s4 =? 0) then
       let '(s0, bflush) := tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1)) in
       let s5 := if bflush then flush_block_only s0 0 else s0 in
       let s6 := set_strstart s5 (ds_strstart s5 + 1) in
       let s7 := set_lookahead s6 (ds_lookahead s6 - 1) in
       if cs_avail_out (ds_strm s7) =? 0 then (s7, LRet need_more) else (s7, LCont)
      else
       let s0 := set_match_available s4 1 in
       let s5 := set_strstart s0 (ds_strstart s0 + 1) in
       let s6 := set_lookahead s5 (ds_lookahead s5 - 1) in (s6, LCont)))
    = st_srest s1).
  { intros s1. unfold st_srest, st_hash. destruct (if MIN_MATCH <=? ds_lookahead s1 then _ else _) as [s2 hh]. cbn [fst snd].
    cbv zeta. rewrite prev_st_eq. generalize (prev_st s2); intros s3.
    rewrite <- st_decide_eq. unfold st_lm, sl_lm_cond, sl_filter, NIL, Z_FILTERED, TOO_FAR, MIN_MATCH. rewrite MIN_LOOKAHEAD_eq.
    destruct (negb (hh =? 0) && _ && _); [| reflexivity].
    destruct (longest_match s3 hh) as [s4 ml]. cbn [fst snd]. reflexivity. }
  unfold deflate_slow_body, st_fill.
  destruct (ds_lookahead s <? MIN_LOOKAHEAD).
  - destruct (_ && _); [reflexivity|]. destruct (_ =? 0); [reflexivity|]. cbn [fst snd]. apply REST.
  - cbn [fst snd]. apply REST.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swap_pl_pm : forall s a b, set_prev_match (set_prev_length s a) b = set_prev_length (set_prev_match s b) a.
Proof. intros s a b. destruct s; reflexivity. Qed.
Lemma swap_str_ml : forall s a b, set_strstart (set_match_length s a) b = set_match_length (set_strstart s b) a.
Proof. intros s a b. destruct s; reflexivity. Qed.
Lemma swap_ma_str : forall s a b, set_strstart (set_match_available s a) b = set_match_available (set_strstart s b) a.
Proof. intros s a b. destruct s; reflexivity. Qed.
Lemma swap_ma_lk : forall s a b, set_lookahead (set_match_available s a) b = set_match_available (set_lookahead s b) a.
Proof. intros s a b. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ins_str_same : forall X str, RefDeflSlow2.ins_str X str = RefDeflFast2.ins_str X str.
Proof. reflexivity. Qed.

Lemma hash_hi_eq : forall s1, 3 <= ds_lookahead s1 ->
  prev_st (fst (st_hash s1)) = hash_st s1 /\ snd (st_hash s1) = hash_hh s1.
Proof.
  intros s1 H. rewrite (st_hash_hi s1 H). cbn [fst snd]. split; [| reflexivity].
  unfold prev_st, hash_st. rewrite <- ins_str_same. rewrite swap_pl_pm. unfold RefDeflSlow2.ins_str. dsred. reflexivity.
Qed.

Lemma hash_lo_eq : forall s1, ds_lookahead s1 < 3 -> prev_st (fst (st_hash s1)) = prev_st s1 /\ snd (st_hash s1) = 0.
Proof. intros s1 H. rewrite (st_hash_lo s1 H). split; reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma sdist_tally_eq : forall X,
  fst (tr_tally_dist X (wrap32 (ds_strstart X - 1 - ds_prev_match X)) (ds_prev_length X - 3)) = sdist2 (sdist1 X) (d_code (sdist_D X))
  /\ snd (tr_tally_dist X (wrap32 (ds_strstart X - 1 - ds_prev_match X)) (ds_prev_length X - 3)) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X. unfold tr_tally_dist, LITERALS. cbv zeta.
  unfold set_Freq, Freq, sym_buf_set. cbn [tree_fc set_tree_fc fst snd].
  split; [| dsred; f_equal; lia].
  unfold sdist2, sdist1, sdist, sdist_D. cbv zeta. dsred. symmetry. mpeel.
Qed.

(* [comment removed for export] *)
Lemma deflate_slow_insert_step : forall n s mi,
  deflate_slow_insert (S n) s mi = (let s' := insl_st s mi in if negb (ds_prev_length s' =? 0) then deflate_slow_insert n s' mi else s').
Proof.
  intros n s mi. cbn [deflate_slow_insert]. unfold insl_st. dsred.
  destruct (ds_strstart s + 1 <=? mi); [rewrite RefDeflSlow2.ins_str_eq; cbn [fst]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sdist_eq : forall X,
  3 <= ds_prev_length X -> ds_prev_length X - 1 <= ds_lookahead X -> ds_lookahead X < 2 ^ 31 -> 3 <= ds_strstart X + ds_lookahead X -> ds_strstart X + ds_lookahead X < 2 ^ 32 ->
  fst (st_sdist X) = exit_st (deflate_slow_insert (Z.to_nat (ds_prev_length X - 2))
                                (dist2_st (sdist2 (sdist1 X) (d_code (sdist_D X)))) (ds_strstart X + ds_lookahead X - 3))
  /\ snd (st_sdist X) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X Hpl3 Hpl Hlk Hsl Hsl2. unfold st_sdist.
  destruct (sdist_tally_eq X) as [E1 E2].
  destruct (tr_tally_dist X _ _) as [s1 b]. cbn [fst snd] in E1, E2 |- *. subst s1 b. split; [| reflexivity].
  assert (V : ds_lookahead (sdist2 (sdist1 X) (d_code (sdist_D X))) = ds_lookahead X
              /\ ds_prev_length (sdist2 (sdist1 X) (d_code (sdist_D X))) = ds_prev_length X
              /\ ds_strstart (sdist2 (sdist1 X) (d_code (sdist_D X))) = ds_strstart X).
  { unfold sdist2, sdist1. dsred. repeat split; reflexivity. }
  destruct V as (Vl & Vp & Vs). generalize dependent (sdist2 (sdist1 X) (d_code (sdist_D X))). intros T Vl Vp Vs.
  replace (wrap32 (ds_strstart X + ds_lookahead X - 3)) with (ds_strstart X + ds_lookahead X - 3)
    by (rewrite wrap32_mod; symmetry; apply Z.mod_small; lia).
  assert (ED : set_prev_length (set_lookahead T (wrap32 (ds_lookahead T - (ds_prev_length T - 1)))) (ds_prev_length (set_lookahead T (wrap32 (ds_lookahead T - (ds_prev_length T - 1)))) - 2) = dist2_st T).
  { unfold dist2_st. dsred. rewrite Vl, Vp. rewrite wrap32_mod, Z.mod_small by lia. f_equal. f_equal. lia. }
  rewrite ED. replace (ds_prev_length (dist2_st T)) with (ds_prev_length X - 2) by (unfold dist2_st; dsred; lia).
  generalize (deflate_slow_insert (Z.to_nat (ds_prev_length X - 2)) (dist2_st T) (ds_strstart X + ds_lookahead X - 3)); intros U.
  unfold exit_st. dsred. rewrite swap_str_ml. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma slit_tally_eq : forall X,
  fst (tr_tally_lit X (arr_get (ds_window X) (ds_strstart X - 1))) = slit1 X
  /\ snd (tr_tally_lit X (arr_get (ds_window X) (ds_strstart X - 1))) = Z.eqb (ds_sym_next X + 3) (ds_sym_end X).
Proof.
  intros X. unfold tr_tally_lit. cbv zeta. unfold set_Freq, Freq, sym_buf_set. cbn [tree_fc set_tree_fc fst snd].
  split; [| dsred; f_equal; lia].
  unfold slit1. cbv zeta. dsred. symmetry. mpeel.
Qed.

Lemma st_slit_eq : forall X,
  st_slit X = (let s2 := if Z.eqb (ds_sym_next X + 3) (ds_sym_end X) then flush_block_only (slit1 X) 0 else slit1 X in
               (ltail_st s2, if cs_avail_out (ds_strm (ltail_st s2)) =? 0 then LRet need_more else LCont)).
Proof.
  intros X. unfold st_slit. destruct (slit_tally_eq X) as [E1 E2].
  destruct (tr_tally_lit X _) as [s1 b]. cbn [fst snd] in E1, E2. subst s1 b. cbv zeta. unfold ltail_st. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma st_avail_eq : forall X, st_avail X = (avail0_st X, LCont).
Proof. intros X. unfold st_avail, avail0_st. rewrite swap_ma_str, swap_ma_lk. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition break1_st (X : deflate_state) : deflate_state := set_match_available (slit1 X) 0.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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
  si_lfc : forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536;
  si_dfc : forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc s) i < 65536 }.

(* [comment removed for export] *)
Definition sdist_ok (ws : Z) (s4 : deflate_state) : Prop :=
  ds_prev_length s4 - 1 <= ds_lookahead s4 /\ 3 <= ds_strstart s4 + ds_lookahead s4 /\ sdist_D s4 < 32768
  /\ 0 <= ds_lookahead (fst (st_sdist s4)) <= 2 * ws
  /\ (snd (st_sdist s4) = true -> flush_ok (fst (st_sdist s4)) 0).

(* [comment removed for export] *)
Definition slit_ok (ws : Z) (s4 : deflate_state) : Prop :=
  1 <= ds_strstart s4
  /\ (Z.eqb (ds_sym_next s4 + 3) (ds_sym_end s4) = true -> flush_ok (slit1 s4) 0)
  /\ let s2 := if Z.eqb (ds_sym_next s4 + 3) (ds_sym_end s4) then flush_block_only (slit1 s4) 0 else slit1 s4 in
     0 <= ds_strstart s2 /\ 1 <= ds_lookahead s2 /\ ds_strstart s2 + ds_lookahead s2 <= 2 * ws.

(* [comment removed for export] *)
Definition sdec_ok (ws : Z) (s4 : deflate_state) : Prop :=
  strip_inv s4 /\ 1 <= ds_lookahead s4 <= 2 * ws
  /\ if dist_cond s4 then sdist_ok ws s4
     else if negb (ds_match_available s4 =? 0) then slit_ok ws s4 else True.

(* [comment removed for export] *)
Definition shash_ok (ws : Z) (s1 : deflate_state) : Prop :=
  strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (sl_lm_cond (prev_st (fst (st_hash s1))) (snd (st_hash s1)) = true -> lm_ok (prev_st (fst (st_hash s1))) (snd (st_hash s1)))
  /\ sdec_ok ws (st_lm (prev_st (fst (st_hash s1))) (snd (st_hash s1))).

Definition strip_ok (ws hs : Z) (s : deflate_state) (flush : Z) : Prop :=
  0 <= ds_lookahead s <= 2 * ws /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf ws hs s)
  /\ 0 <= ds_lookahead (fst (st_fill s flush)) <= 2 * ws
  /\ (snd (st_fill s flush) = None -> shash_ok ws (fst (st_fill s flush))).

Definition st_sbody (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  match snd (st_fill s flush) with Some o => (fst (st_fill s flush), o) | None => st_srest (fst (st_fill s flush)) end.

Fixpoint sloop_ok (ws hs : Z) (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => strip_ok ws hs s flush
           /\ match snd (st_sbody s flush) with
              | LCont => sloop_ok ws hs f (fst (st_sbody s flush)) flush
              | _ => True
              end
  end.

Lemma sloop_ok_S : forall ws hs f s flush,
  sloop_ok ws hs (S f) s flush
  = (strip_ok ws hs s flush /\ match snd (st_sbody s flush) with LCont => sloop_ok ws hs f (fst (st_sbody s flush)) flush | _ => True end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition stail_ok (ws : Z) (s : deflate_state) (flush : Z) : Prop :=
  strip_inv s /\ 0 <= ds_strstart s <= 2 * ws
  /\ (ds_match_available s <> 0 -> 1 <= ds_strstart s)
  /\ let s2 := if negb (ds_match_available s =? 0) then break1_st s else s in
     0 <= ds_strstart s2 <= 2 * ws /\ 0 <= ds_sym_next s2 < 2 ^ 18
     /\ (flush = Z_FINISH -> flush_ok (tail_st s2) 1)
     /\ (flush <> Z_FINISH -> ds_sym_next s2 <> 0 -> flush_ok (tail_st s2) 0).

(* [comment removed for export] *)
Definition slow_safe (ds : deflate_state) (flush : Z) : Prop :=
  DWF ds /\ sloop_ok (ds_w_size ds) (ds_hash_size ds) (lz_fuel ds) ds flush
  /\ match snd (deflate_slow_loop (lz_fuel ds) ds flush) with
     | Some _ => True
     | None => stail_ok (ds_w_size ds) (fst (deflate_slow_loop (lz_fuel ds) ds flush)) flush
     end.

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

(* [comment removed for export] *)
Lemma shash_ok_hi : forall ws s1, shash_ok ws s1 -> 3 <= ds_lookahead s1 ->
  strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (sl_lm_cond (hash_st s1) (hash_hh s1) = true -> lm_ok (hash_st s1) (hash_hh s1))
  /\ sdec_ok ws (st_lm (hash_st s1) (hash_hh s1)).
Proof.
  intros ws s1 (A & B & C & D) Hl. destruct (hash_hi_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in C, D.
  exact (conj A (conj B (conj C D))).
Qed.

Lemma shash_ok_lo : forall ws s1, shash_ok ws s1 -> ds_lookahead s1 < 3 ->
  strip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (sl_lm_cond (prev_st s1) 0 = true -> lm_ok (prev_st s1) 0)
  /\ sdec_ok ws (st_lm (prev_st s1) 0).
Proof.
  intros ws s1 (A & B & C & D) Hl. destruct (hash_lo_eq s1 Hl) as [E1 E2]. rewrite E1, E2 in C, D.
  exact (conj A (conj B (conj C D))).
Qed.

Lemma st_srest_hi : forall s1, 3 <= ds_lookahead s1 -> st_srest s1 = st_decide (st_lm (hash_st s1) (hash_hh s1)).
Proof. intros s1 H. unfold st_srest. destruct (hash_hi_eq s1 H) as [E1 E2]. rewrite E1, E2. reflexivity. Qed.

Lemma st_srest_lo : forall s1, ds_lookahead s1 < 3 -> st_srest s1 = st_decide (st_lm (prev_st s1) 0).
Proof. intros s1 H. unfold st_srest. destruct (hash_lo_eq s1 H) as [E1 E2]. rewrite E1, E2. reflexivity. Qed.

Lemma sl_lm_cond_0 : forall s, sl_lm_cond s 0 = false.
Proof. reflexivity. Qed.
