(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition upd_used (s : deflate_state) (used : Z) : deflate_state :=
  if ds_w_size s <=? used then upd_big s
  else upd_cp (if ds_window_size s - ds_strstart s <=? used then upd_slide s else s) used.

Definition used_post (ain0 : Z) (s : deflate_state) : deflate_state :=
  let used := sused ain0 s in
  hwpost (if negb (used =? 0) then set_block_start (upd_used s used) (ds_strstart (upd_used s used)) else s).




Lemma strstart_set_block_start : forall s v, ds_strstart (set_block_start s v) = ds_strstart s.
Proof. intros s v. destruct s; reflexivity. Qed.







Section Tail.
Variables (ws hs PBL ILEN OCAP : Z).
Variables (flush mb : Z).
Hypothesis Hflush : 0 <= flush <= 5.
Hypothesis Hmb : 0 <= mb < 2 ^ 18.

Local Notation outlen st := (Z.of_nat (length (cs_out_rev st))).



Definition used_ok (ain0 : Z) (s : deflate_state) : Prop :=
  let ain := cs_avail_in (ds_strm s) in
  let used := sused ain0 s in
  let s1 := (if ds_window_size s - ds_strstart s <=? used then upd_slide s else s) in
  let s2 := (if negb (used =? 0) then set_block_start (upd_used s used) (ds_strstart (upd_used s used)) else s) in
  0 <= ain < 2 ^ 32 /\ 0 <= ain0 < 2 ^ 32 /\ 0 <= ds_strstart s <= 2 * ws /\ ds_window_size s = 2 * ws
  /\ (used <> 0 ->
        used <= cs_next_in (ds_strm s) /\ cs_next_in (ds_strm s) <= ILEN
        /\ (forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm s)) j < 256)
        /\ (used < ws -> ds_window_size s - ds_strstart s <= used ->
               (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window s) j < 256)
               /\ 0 <= ds_matches s < 2 ^ 32 /\ 0 <= ds_insert s < 2 ^ 32)
        /\ (used < ws ->
               used <= cs_next_in (ds_strm s1) /\ cs_next_in (ds_strm s1) <= ILEN
               /\ (forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm s1)) j < 256)
               /\ 0 <= ds_strstart s1 /\ ds_strstart s1 + used <= 2 * ws /\ 0 <= ds_insert s1 <= 2 * ws))
  /\ 0 <= ds_strstart s2 < 2 ^ 31 /\ 0 <= ds_high_water s2 < 2 ^ 64.

Definition fin_emit (s1 : deflate_state) : deflate_state :=
  let s2 := tr_stored_block s1 (Some (ds_block_start s1)) (tlen s1) (tlast flush s1) in
  flush_pending (set_block_start s2 (ds_block_start s2 + tlen s1)).

Lemma ds_used_eq : forall s u, deflate_stored_used s u = used_post u s.
Proof.
  intros s u. cbv delta [deflate_stored_used used_post hwpost upd_used upd_big upd_slide upd_cp sused]. cbv beta. cbv zeta.
  reflexivity.
Qed.

Lemma ds_fin_eq : forall s,
  0 <= ds_block_start (hwpost s) <= ds_strstart (hwpost s) -> ds_strstart (hwpost s) < 2 ^ 32 ->
  deflate_stored_fin s flush = (if tcond1 (hwpost s) || tcond2 flush (hwpost s)
                    then (fin_emit (hwpost s), if negb (tlast flush (hwpost s) =? 0) then finish_started else need_more)
                    else (hwpost s, need_more)).
Proof.
  intros s Hbs Hss. cbv delta [deflate_stored_fin]. cbv beta.
  replace (if Z.ltb (ds_high_water s) (ds_strstart s) then set_high_water s (ds_strstart s) else s) with (hwpost s) by reflexivity.
  cbv zeta. rewrite hdrb_model. rewrite (wrap32_id (ds_strstart (hwpost s) - ds_block_start (hwpost s))) by lia.
  cbv delta [fin_emit tcond1 tcond2 tlast tlen tleft tmb thave]. cbv beta. cbv zeta.
  reflexivity.
Qed.

Definition fin_ok (s : deflate_state) : Prop :=
  let s1 := hwpost s in
  let len := tlen s1 in
  let last := tlast flush s1 in
  let s2 := tr_stored_block s1 (Some (ds_block_start s1)) len last in
  let s3 := set_block_start s2 (ds_block_start s2 + len) in
  0 <= ds_strstart s < 2 ^ 31 /\ 0 <= ds_high_water s < 2 ^ 64
  /\ 0 <= ds_bi_valid s1 <= 16 /\ 7 <= ds_pending_buf_size s1 < 2 ^ 31
  /\ 0 <= ds_block_start s1 <= ds_strstart s1 /\ ds_strstart s1 < 2 ^ 31
  /\ 0 <= cs_avail_in (ds_strm s1) < 2 ^ 32
  /\ (tcond1 s1 || tcond2 flush s1 = true ->
        BINV PBL s1 /\ ds_pending s2 <= PBL /\ ds_block_start s1 + len <= 2 * ws
        /\ (forall j, ds_block_start s1 <= j < ds_block_start s1 + len -> 0 <= arr_get (ds_window s1) j < 256)
        /\ 0 <= ds_block_start s2 < 2 ^ 31
        /\ fp_ok PBL OCAP s3).

Definition rbw (s : deflate_state) (n : Z) : deflate_state :=
  let sa := set_strm s (cset_avail_in (ds_strm s) (cs_avail_in (ds_strm s) - n)) in
  let bytes := arr_slice (cs_input (ds_strm sa)) (cs_next_in (ds_strm s)) n in
  let sb := set_window sa (arr_upd (ds_window sa) (ds_strstart s) bytes) in
  rbc3post (ckpost sb bytes) n.

Lemma rbw_eq : forall s n, 0 < n -> n <= cs_avail_in (ds_strm s) ->
  (let '(s1, _) := read_buf s (RB_window (ds_strstart s)) n in
   let s1 := set_strstart s1 (ds_strstart s1 + n) in
   set_insert s1 (ds_insert s1 + MIN n (wrap32 (ds_w_size s1 - ds_insert s1))))
  = rbw s n.
Proof.
  intros s n Hn Hle. unfold read_buf, rbw, rbc3post, ckpost, ckv.
  assert (E : (if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) = n)
    by (destruct (Z.ltb_spec n (cs_avail_in (ds_strm s))); lia).
  rewrite E. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct s as [ ]. cbn -[adler32_upd crc32_upd arr_slice arr_upd wrap64 wrap32 MIN Z.add Z.sub Z.eqb].
  destruct ds_strm. cbn -[adler32_upd crc32_upd arr_slice arr_upd wrap64 wrap32 MIN Z.add Z.sub Z.eqb].
  destruct (ds_wrap =? 1); [reflexivity|]. destruct (ds_wrap =? 2); reflexivity.
Qed.


Lemma w_size_slide2 : forall s, ds_w_size (slide2 s) = ds_w_size s.
Proof.
  intros s. unfold slide2. destruct (Z.ltb _ 2); destruct (Z.ltb _ _); destruct s; reflexivity.
Qed.

Lemma slide_eq : forall s have,
  deflate_stored_slide s have = (slide2 s, wrap32 (have + ds_w_size s)).
Proof.
  intros s have. rewrite <- (w_size_slide2 s). unfold deflate_stored_slide, slide2.
  destruct (Z.ltb (ds_matches _) 2); destruct (Z.ltb _ _); destruct s; reflexivity.
Qed.

Lemma strm_slide2 : forall s, ds_strm (slide2 s) = ds_strm s.
Proof.
  intros s. unfold slide2. destruct (Z.ltb _ 2); destruct (Z.ltb _ _); destruct s; reflexivity.
Qed.

Definition mid_hv (s : deflate_state) : Z := ds_window_size s - ds_strstart s.

Definition mid_c (s : deflate_state) : bool :=
  (mid_hv s <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s).

Definition mid_s2 (s : deflate_state) : deflate_state := if mid_c s then slide2 s else s.

Definition mid_hv2 (s : deflate_state) : Z := if mid_c s then mid_hv s + ds_w_size s else mid_hv s.

Definition mid_n (s : deflate_state) : Z :=
  if cs_avail_in (ds_strm (mid_s2 s)) <? mid_hv2 s then cs_avail_in (ds_strm (mid_s2 s)) else mid_hv2 s.

Definition mid_post (s : deflate_state) : deflate_state :=
  if negb (mid_n s =? 0) then rbw (mid_s2 s) (mid_n s) else mid_s2 s.

Lemma mid_n_range : forall s, 0 <= mid_hv2 s -> 0 <= cs_avail_in (ds_strm (mid_s2 s)) ->
  0 <= mid_n s <= mid_hv2 s /\ mid_n s <= cs_avail_in (ds_strm (mid_s2 s)).
Proof. intros s H1 H2. unfold mid_n. destruct (Z.ltb_spec (cs_avail_in (ds_strm (mid_s2 s))) (mid_hv2 s)); lia. Qed.

Lemma mid_eq : forall s,
  0 <= mid_hv s < 2 ^ 32 -> 0 <= mid_hv s + ds_w_size s < 2 ^ 32 -> 0 <= cs_avail_in (ds_strm s) ->
  deflate_stored_mid s flush = deflate_stored_fin (mid_post s) flush.
Proof.
  intros s Hhv Hhv2 Hai.
  cbv delta [deflate_stored_mid]. cbv beta. cbv zeta.
  rewrite (wrap32_id (ds_window_size s - ds_strstart s)) by (unfold mid_hv in Hhv; lia).
  rewrite slide_eq.
  unfold mid_post, mid_n, mid_hv2, mid_s2, mid_c, mid_hv in *.
  destruct ((ds_window_size s - ds_strstart s <? cs_avail_in (ds_strm s)) && (ds_w_size s <=? ds_block_start s)).
  - rewrite (wrap32_id (ds_window_size s - ds_strstart s + ds_w_size s)) by lia.
    apply (f_equal (fun x => deflate_stored_fin x flush)).
    match goal with |- (if negb (?n =? 0) then _ else _) = _ => destruct (Z.eqb_spec n 0) as [E|E] end; cbn [negb].
    + reflexivity.
    + rewrite strm_slide2 in *.
      apply rbw_eq; rewrite ?strm_slide2; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (ds_window_size s - ds_strstart s + ds_w_size s)); lia.
  - apply (f_equal (fun x => deflate_stored_fin x flush)).
    match goal with |- (if negb (?n =? 0) then _ else _) = _ => destruct (Z.eqb_spec n 0) as [E|E] end; cbn [negb].
    + reflexivity.
    + apply rbw_eq; destruct (Z.ltb_spec (cs_avail_in (ds_strm s)) (ds_window_size s - ds_strstart s)); lia.
Qed.

Definition mid_ok (s : deflate_state) : Prop :=
  let s2 := mid_s2 s in
  let n := mid_n s in
  0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ ds_window_size s = 2 * ws /\ 0 <= ds_strstart s <= 2 * ws
  /\ 0 <= ds_block_start s < 2 ^ 63
  /\ (mid_c s = true ->
        ds_block_start s <= ds_strstart s
        /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window s) j < 256)
        /\ 0 <= ds_matches s < 2 ^ 32 /\ 0 <= ds_insert s < 2 ^ 32)
  /\ 0 <= ds_block_start s2 < 2 ^ 63 /\ 0 <= ds_strstart s2 < 2 ^ 31
  /\ (n <> 0 ->
        0 <= cs_next_in (ds_strm s2) /\ cs_next_in (ds_strm s2) + n <= ILEN
        /\ (forall j, 0 <= j < ILEN -> 0 <= arr_get (cs_input (ds_strm s2)) j < 256)
        /\ -2 <= ds_wrap s2 <= 2 /\ (ds_wrap s2 = 1 -> adler_canon (cs_adler (ds_strm s2)))
        /\ (ds_wrap s2 = 2 -> 0 <= cs_adler (ds_strm s2) < 2 ^ 64)
        /\ 0 <= cs_total_in (ds_strm s2) < 2 ^ 64 /\ ds_strstart s2 + n <= 2 * ws /\ 0 <= ds_insert s2 <= 2 * ws).

End Tail.
