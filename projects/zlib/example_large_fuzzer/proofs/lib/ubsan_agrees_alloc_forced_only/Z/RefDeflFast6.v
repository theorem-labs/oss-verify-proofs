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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition st_fill (s : deflate_state) (flush : Z) : deflate_state * option loop_out :=
  if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD then
    let s := fill_window s in
    if Z.ltb (ds_lookahead s) MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH then (s, Some (LRet need_more))
    else if Z.eqb (ds_lookahead s) 0 then (s, Some LBreak)
    else (s, None)
  else (s, None).

Definition st_hash (s : deflate_state) : deflate_state * Z :=
  if Z.leb MIN_MATCH (ds_lookahead s) then insert_string s (ds_strstart s) else (s, NIL).

Definition lm_cond (s : deflate_state) (hash_head : Z) : bool :=
  negb (Z.eqb hash_head NIL) && Z.leb (wrap32 (ds_strstart s - hash_head)) (ds_w_size s - MIN_LOOKAHEAD).

Definition st_match (s : deflate_state) (hash_head : Z) : deflate_state :=
  if lm_cond s hash_head then let '(s, ml) := longest_match s hash_head in set_match_length s ml else s.

Definition ins_cond (s : deflate_state) : bool :=
  Z.leb (ds_match_length s) (ds_max_lazy_match s) && Z.leb MIN_MATCH (ds_lookahead s).

(* [comment removed for export] *)
Definition st_noins (s : deflate_state) : deflate_state :=
  let s := set_strstart s (ds_strstart s + ds_match_length s) in
  let s := set_match_length s 0 in
  let s := set_ins_h s (arr_get (ds_window s) (ds_strstart s)) in
  set_ins_h s (update_hash s (ds_ins_h s) (arr_get (ds_window s) (ds_strstart s + 1))).

(* [comment removed for export] *)
Definition st_ins (s : deflate_state) : deflate_state :=
  let s := set_match_length s (ds_match_length s - 1) in
  let s := deflate_fast_insert (Z.to_nat (ds_match_length s)) s in
  set_strstart s (ds_strstart s + 1).

Definition st_dist (s : deflate_state) : deflate_state * bool :=
  let '(s, bflush) := tr_tally_dist s (wrap32 (ds_strstart s - ds_match_start s)) (ds_match_length s - MIN_MATCH) in
  let s := set_lookahead s (ds_lookahead s - ds_match_length s) in
  let s := if ins_cond s then st_ins s else st_noins s in
  (s, bflush).

Definition st_lit (s : deflate_state) : deflate_state * bool :=
  let '(s, bflush) := tr_tally_lit s (arr_get (ds_window s) (ds_strstart s)) in
  let s := set_lookahead s (ds_lookahead s - 1) in
  let s := set_strstart s (ds_strstart s + 1) in
  (s, bflush).

Definition st_tally (s : deflate_state) : deflate_state * bool :=
  if Z.leb MIN_MATCH (ds_match_length s) then st_dist s else st_lit s.

Definition st_bflush (s : deflate_state) (bflush : bool) : deflate_state * loop_out :=
  if bflush then
    let '(s, r) := flush_block s 0 in
    match r with Some bs => (s, LRet bs) | None => (s, LCont) end
  else (s, LCont).

Definition st_body (s : deflate_state) (flush : Z) : deflate_state * loop_out :=
  let '(s1, early) := st_fill s flush in
  match early with
  | Some o => (s1, o)
  | None =>
      let '(s2, hh) := st_hash s1 in
      let s3 := st_match s2 hh in
      let '(s7, bflush) := st_tally s3 in
      st_bflush s7 bflush
  end.

Lemma deflate_fast_body_eq : forall s flush, deflate_fast_body s flush = st_body s flush.
Proof.
  intros s flush. unfold deflate_fast_body, st_body, st_fill.
  destruct (ds_lookahead s <? MIN_LOOKAHEAD).
  - destruct (_ && _); [reflexivity|]. destruct (ds_lookahead (fill_window s) =? 0); [reflexivity|].
    unfold st_hash. destruct (MIN_MATCH <=? _).
    + destruct (insert_string _ _) as [s2 hh]. unfold st_match, lm_cond. destruct (_ && _).
      * destruct (longest_match s2 hh) as [s3 ml]. unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
        destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
      * unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
        destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
    + unfold st_match, lm_cond. cbn [negb Z.eqb NIL andb].
      unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
      destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
  - unfold st_hash. destruct (MIN_MATCH <=? _).
    + destruct (insert_string _ _) as [s2 hh]. unfold st_match, lm_cond. destruct (_ && _).
      * destruct (longest_match s2 hh) as [s3 ml]. unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
        destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
      * unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
        destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
    + unfold st_match, lm_cond. cbn [negb Z.eqb NIL andb].
      unfold st_tally, st_dist, st_lit, ins_cond, st_ins, st_noins, st_bflush.
      destruct (MIN_MATCH <=? _); [destruct (tr_tally_dist _ _ _) as [s4 b] | destruct (tr_tally_lit _ _) as [s4 b]]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swap_pb_sn : forall s v a, set_pending_buf (set_sym_next s v) a = set_sym_next (set_pending_buf s a) v.
Proof. intros s v a. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Ltac mleaf := first [ reflexivity | lia | rewrite distm1_eq; mleaf | progress f_equal; mleaf ].
Ltac mpeel :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [mpeel | mleaf]
  | |- @eq deflate_state (set_pending_buf (set_sym_next _ _) _) (set_sym_next _ _) =>
      etransitivity; [apply swap_pb_sn|]; mpeel
  | |- @eq deflate_state (set_sym_next (set_pending_buf _ _) _) (set_pending_buf _ _) =>
      etransitivity; [symmetry; apply swap_pb_sn|]; mpeel
  end.

Lemma insl_eq : forall X, insl_st X =
  set_match_length (fst (insert_string (set_strstart X (ds_strstart X + 1)) (ds_strstart X + 1))) (ds_match_length X - 1).
Proof. intros X. unfold insl_st. rewrite ins_str_eq. cbn [fst]. dsred. reflexivity. Qed.

Lemma deflate_fast_insert_step : forall n s,
  deflate_fast_insert (S n) s = (let s' := insl_st s in if negb (ds_match_length s' =? 0) then deflate_fast_insert n s' else s').
Proof.
  intros n s. cbn [deflate_fast_insert]. rewrite insl_eq. rewrite ins_str_eq. cbn [fst]. unfold ins_str. dsred. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lz_view (s : deflate_state) :=
  (ds_strstart s, ds_lookahead s, ds_block_start s, ds_match_length s, ds_window s, ds_w_size s).
Lemma keeps_lz_view : keeps lz_view true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma tfb_lz_view : forall s buf len last, lz_view (tr_flush_block s buf len last) = lz_view s.
Proof. intros. rewrite (k_tr_flush_block lz_view keeps_lz_view). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Record trip_inv (s : deflate_state) : Prop := {
  ti_str : 0 <= ds_strstart s;
  ti_sl : ds_strstart s + ds_lookahead s <= 2 * ds_w_size s;
  ti_look : 0 <= ds_lookahead s;
  ti_ih : 0 <= ds_ins_h s < 2 ^ 31;
  ti_hm : ds_hash_mask s = ds_hash_size s - 1;
  ti_wm : ds_w_mask s = ds_w_size s - 1;
  ti_hs : 0 <= ds_hash_shift s < 32;
  ti_ml : 0 <= ds_match_length s <= 258;
  ti_ms : 0 <= ds_match_start s < 2 ^ 32;
  ti_lazy : 0 <= ds_max_lazy_match s < 2 ^ 31;
  ti_sn : 0 <= ds_sym_next s /\ ds_sym_next s + 3 <= 3 * ds_lit_bufsize s;
  ti_se : 0 <= ds_sym_end s < 2 ^ 18;
  ti_wb : forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256;
  ti_hb : forall j, 0 <= j < ds_hash_size s -> 0 <= arr_get (ds_head s) j < 65536;
  ti_pb : forall j, 0 <= j < ds_w_size s -> 0 <= arr_get (ds_prev s) j < 65536;
  ti_lfc : forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536;
  ti_dfc : forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc s) i < 65536 }.

(* [comment removed for export] *)
Definition lm_ok (s : deflate_state) (cur : Z) : Prop :=
  (forall i, 0 <= i < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) i < 256)
  /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536)
  /\ 0 <= ds_strstart s /\ ds_strstart s + 258 < 2 * ds_w_size s /\ ds_w_mask s = ds_w_size s - 1
  /\ 1 <= ds_prev_length s <= 258 /\ 0 <= ds_nice_match s <= 258 /\ 0 <= ds_lookahead s < 2 ^ 31
  /\ 0 <= ds_good_match s < 2 ^ 31 /\ 0 <= ds_max_chain_length s < 2 ^ 31
  /\ 1 <= (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
  /\ 0 <= cur < 2 ^ 32 /\ Forall (fun c => 0 <= c < ds_strstart s) (lm_visited s cur)
  /\ 0 <= snd (longest_match s cur) <= 258.

(* [comment removed for export] *)
Definition dist_ok (s : deflate_state) : Prop :=
  ds_match_length s <= ds_lookahead s /\ tdist_D s < 32768
  /\ ds_strstart s + ds_match_length s + 2 <= 2 * ds_w_size s.

(* [comment removed for export] *)
Definition flush_ok (s : deflate_state) (last : Z) : Prop :=
  let PBL := ds_lit_bufsize s * 4 in
  let buf := if Z.leb 0 (ds_block_start s) then Some (wrap32 (ds_block_start s)) else None in
  let len := wrap64 (ds_strstart s - ds_block_start s) in
  fb_safe s buf len last /\ BINV PBL s /\ 0 <= ds_strstart s - ds_block_start s < 2 ^ 32
  /\ - 2 ^ 63 <= ds_block_start s /\ 0 <= ds_strstart s <= 2 * ds_w_size s /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
  /\ (forall j, 0 <= j < 2 * ds_w_size s -> 0 <= arr_get (ds_window s) j < 256)
  /\ let s8 := tr_flush_block s buf len last in
     let s9 := set_block_start s8 (ds_strstart s8) in
     BINV PBL s9 /\ ds_pending (tr_flush_bits s9) <= PBL
     /\ let s10 := tr_flush_bits s9 in
        0 <= ds_pending s10 < 2 ^ 31 /\ 0 <= ds_pending_out s10 /\ ds_pending_out s10 + fp_len s10 <= PBL
        /\ 0 <= cs_total_out (ds_strm s10) < 2 ^ 64.

(* [comment removed for export] *)
Definition tally_ok (ws : Z) (s3 : deflate_state) : Prop :=
  trip_inv s3 /\ 1 <= ds_lookahead s3 <= 2 * ws /\ (MIN_MATCH <= ds_match_length s3 -> dist_ok s3)
  /\ 0 <= ds_lookahead (fst (st_tally s3)) <= 2 * ws
  /\ (snd (st_tally s3) = true -> flush_ok (fst (st_tally s3)) 0).

(* [comment removed for export] *)
Definition hash_ok (ws : Z) (s1 : deflate_state) : Prop :=
  trip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ws
  /\ (lm_cond (fst (st_hash s1)) (snd (st_hash s1)) = true -> lm_ok (fst (st_hash s1)) (snd (st_hash s1)))
  /\ tally_ok ws (st_match (fst (st_hash s1)) (snd (st_hash s1))).

(* [comment removed for export] *)
Definition trip_ok (ws hs : Z) (s : deflate_state) (flush : Z) : Prop :=
  0 <= ds_lookahead s <= 2 * ws /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf ws hs s)
  /\ 0 <= ds_lookahead (fst (st_fill s flush)) <= 2 * ws
  /\ (snd (st_fill s flush) = None -> hash_ok ws (fst (st_fill s flush))).

Fixpoint loop_ok (ws hs : Z) (fuel : nat) (s : deflate_state) (flush : Z) : Prop :=
  match fuel with
  | O => False
  | S f => trip_ok ws hs s flush
           /\ match snd (st_body s flush) with
              | LCont => loop_ok ws hs f (fst (st_body s flush)) flush
              | _ => True
              end
  end.

Lemma loop_ok_S : forall ws hs f s flush,
  loop_ok ws hs (S f) s flush
  = (trip_ok ws hs s flush /\ match snd (st_body s flush) with LCont => loop_ok ws hs f (fst (st_body s flush)) flush | _ => True end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition tail_st (s : deflate_state) : deflate_state :=
  set_insert s (if Z.ltb (ds_strstart s) (MIN_MATCH - 1) then ds_strstart s else MIN_MATCH - 1).

Definition tail_ok (ws : Z) (s : deflate_state) (flush : Z) : Prop :=
  0 <= ds_strstart s <= 2 * ws /\ 0 <= ds_sym_next s < 2 ^ 31
  /\ (flush = Z_FINISH -> flush_ok (tail_st s) 1)
  /\ (flush <> Z_FINISH -> ds_sym_next s <> 0 -> flush_ok (tail_st s) 0).

(* [comment removed for export] *)
Definition fast_safe (ds : deflate_state) (flush : Z) : Prop :=
  DWF ds /\ loop_ok (ds_w_size ds) (ds_hash_size ds) (lz_fuel ds) ds flush
  /\ match snd (deflate_fast_loop (lz_fuel ds) ds flush) with
     | Some _ => True
     | None => tail_ok (ds_w_size ds) (fst (deflate_fast_loop (lz_fuel ds) ds flush)) flush
     end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition st_rest (s1 : deflate_state) : deflate_state * loop_out :=
  st_bflush (fst (st_tally (st_match (fst (st_hash s1)) (snd (st_hash s1)))))
            (snd (st_tally (st_match (fst (st_hash s1)) (snd (st_hash s1))))).

Lemma st_body_eq2 : forall s flush,
  st_body s flush = match snd (st_fill s flush) with
                    | Some o => (fst (st_fill s flush), o)
                    | None => st_rest (fst (st_fill s flush))
                    end.
Proof.
  intros s flush. unfold st_body, st_rest. destruct (st_fill s flush) as [s1 e]. cbn [fst snd].
  destruct e as [o|]; [reflexivity|]. destruct (st_hash s1) as [s2 hh]. cbn [fst snd].
  destruct (st_tally (st_match s2 hh)) as [s7 b]. reflexivity.
Qed.

Lemma MIN_LOOKAHEAD_eq : MIN_LOOKAHEAD = 262.
Proof. reflexivity. Qed.

Definition fill_out (s1 : deflate_state) (flush : Z) : option loop_out :=
  if Z.ltb (ds_lookahead s1) 262 && Z.eqb flush 0 then Some (LRet need_more)
  else if Z.eqb (ds_lookahead s1) 0 then Some LBreak else None.

(* [comment removed for export] *)
Definition hash_hh (s1 : deflate_state) : Z :=
  arr_get (ds_head s1) (update_hash s1 (ds_ins_h s1) (arr_get (ds_window s1) (ds_strstart s1 + 2))).

Lemma st_hash_hi : forall s1, 3 <= ds_lookahead s1 -> st_hash s1 = (ins_str s1 (ds_strstart s1), hash_hh s1).
Proof.
  intros s1 H. unfold st_hash, MIN_MATCH, hash_hh. destruct (Z.leb_spec 3 (ds_lookahead s1)); [| lia].
  rewrite ins_str_eq. reflexivity.
Qed.

Lemma st_hash_lo : forall s1, ds_lookahead s1 < 3 -> st_hash s1 = (s1, NIL).
Proof. intros s1 H. unfold st_hash, MIN_MATCH. destruct (Z.leb_spec 3 (ds_lookahead s1)); [lia | reflexivity]. Qed.

Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof. reflexivity. Qed.

Lemma st_bflush_true : forall s,
  st_bflush s true = (fst (flush_block s 0), match snd (flush_block s 0) with Some bs => LRet bs | None => LCont end).
Proof. intros s. unfold st_bflush. destruct (flush_block s 0) as [s' [bs|]]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma loop_step : forall f s flush,
  deflate_fast_loop (S f) s flush
  = match snd (st_body s flush) with
    | LCont => deflate_fast_loop f (fst (st_body s flush)) flush
    | LBreak => (fst (st_body s flush), None)
    | LRet bs => (fst (st_body s flush), Some bs)
    end.
Proof.
  intros f s flush. cbn [deflate_fast_loop]. rewrite deflate_fast_body_eq.
  destruct (st_body s flush) as [s' o]. reflexivity.
Qed.

(* [comment removed for export] *)

