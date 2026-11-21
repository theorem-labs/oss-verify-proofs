(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  TreeModel FillWinModel SendModel BitsModel RefFlushPend1 RefDeflateEnd1 RefDeflateHdrKit RefDeflateTrl1 RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition f3_spec (s : deflate_state) : deflate_state * option Z :=
  let s := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
  let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
  match r with
  | Some rc => (s, Some rc)
  | None => if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None)
  end.

Definition blocks_cond (s : deflate_state) (flush : Z) : bool :=
  negb (Z.eqb (cs_avail_in (ds_strm s)) 0) || negb (Z.eqb (ds_lookahead s) 0)
  || (negb (Z.eqb flush Z_NO_FLUSH) && negb (Z.eqb (ds_status s) FINISH_STATE)).

Definition blocks_body (s : deflate_state) (flush : Z) : deflate_state * option Z :=
  let '(s, bstate) := run_compress_func s flush in
  let s := if block_state_eqb bstate finish_started || block_state_eqb bstate finish_done
           then set_status s FINISH_STATE else s in
  if block_state_eqb bstate need_more || block_state_eqb bstate finish_started then
    let s := if Z.eqb (cs_avail_out (ds_strm s)) 0 then set_last_flush s (-1) else s in
    (s, Some Z_OK)
  else if block_state_eqb bstate block_done then
    let s :=
      if Z.eqb flush Z_PARTIAL_FLUSH then tr_align s
      else if negb (Z.eqb flush Z_BLOCK) then
        let s := tr_stored_block s None 0 0 in
        if Z.eqb flush Z_FULL_FLUSH then
          let s := clear_hash s in
          if Z.eqb (ds_lookahead s) 0 then
            let s := set_strstart s 0 in
            let s := set_block_start s 0 in
            set_insert s 0
          else s
        else s
      else s in
    let s := flush_pending s in
    if Z.eqb (cs_avail_out (ds_strm s)) 0 then (set_last_flush s (-1), Some Z_OK) else (s, None)
  else (s, None).

Definition core_tail (s : deflate_state) (flush : Z) : deflate_state * Z :=
  if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
  else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
  else deflate_trailer s.

Lemma deflate_blocks_eq : forall s flush,
  deflate_blocks s flush = if blocks_cond s flush then blocks_body s flush else (s, None).
Proof. intros s flush. reflexivity. Qed.

Inductive front_out : Type :=
  | FrontRet (s' : deflate_state) (rc : Z)
  | FrontBlocks (s' : deflate_state)
  | FrontIdle (s' : deflate_state).

Definition blocks_or_idle (s : deflate_state) (flush : Z) : front_out :=
  if blocks_cond s flush then FrontBlocks s
  else if Z.eqb flush Z_NO_FLUSH then FrontRet s Z_OK
  else FrontIdle s.

Definition front_spec (s : deflate_state) (flush : Z) : front_out :=
  match f1_spec s flush with
  | Some (s', rc) => FrontRet s' rc
  | None =>
    match f2_spec s flush with
    | F2Ret s' rc => FrontRet s' rc
    | F2Fin s' => blocks_or_idle s' flush
    | F2Hdr s' =>
      match f3_spec s' with
      | (s'', Some rc) => FrontRet s'' rc
      | (s'', None) => blocks_or_idle s'' flush
      end
    end
  end.

Lemma status_set_last_flush : forall s v, ds_status (set_last_flush s v) = ds_status s.
Proof. intros s v. destruct s; reflexivity. Qed.

Theorem deflate_core_front : forall s flush,
  deflate_core s flush =
    match front_spec s flush with
    | FrontRet s' rc => (s', rc)
    | FrontBlocks s' => let '(s2, r) := blocks_body s' flush in
                        match r with Some rc => (s2, rc) | None => core_tail s2 flush end
    | FrontIdle s' => core_tail s' flush
    end.
Proof.
  intros s flush. unfold deflate_core, front_spec, f1_spec, f2_spec, f3_spec.
  destruct (deflateStateCheck s || (Z_BLOCK <? flush) || (flush <? 0)); [reflexivity|].
  destruct ((ds_status s =? FINISH_STATE) && negb (flush =? Z_FINISH)) eqn:EF; [reflexivity|].
  destruct (cs_avail_out (ds_strm s) =? 0); [reflexivity|].
  cbv zeta.
  Local Ltac tail_tac flush s2 :=
    unfold blocks_or_idle, core_tail; rewrite (deflate_blocks_eq s2 flush);
    destruct (blocks_cond s2 flush); [destruct (blocks_body s2 flush) as [s3 [rc|]]; reflexivity|];
    unfold Z_NO_FLUSH, Z_FINISH; destruct (Z.eqb_spec flush 0) as [->|NZ]; reflexivity.
  Local Ltac cont_tac flush s0 :=
    destruct ((ds_status s0 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s0) =? 0)); [unfold err_return; reflexivity|];
    destruct (Z.eqb_spec (ds_status s0) FINISH_STATE) as [E6|E6];
    [
      rewrite E6; change (FINISH_STATE =? INIT_STATE) with false; cbn [andb];
      rewrite E6; change (FINISH_STATE =? INIT_STATE) with false; cbn [andb];
      rewrite E6; change (FINISH_STATE =? GZIP_STATE) with false; cbn [andb];
      tail_tac flush s0
    | destruct ((ds_status s0 =? INIT_STATE) && (ds_wrap s0 =? 0));
      [ change (ds_status (set_status s0 BUSY_STATE)) with BUSY_STATE; change (BUSY_STATE =? INIT_STATE) with false; cbn [andb];
        change (ds_status (set_status s0 BUSY_STATE)) with BUSY_STATE; change (BUSY_STATE =? GZIP_STATE) with false; cbn [andb];
        tail_tac flush (set_status s0 BUSY_STATE)
      | destruct (ds_status s0 =? INIT_STATE);
        [ destruct (deflate_zlib_header s0) as [s1 [rc|]]; [reflexivity|];
          destruct (ds_status s1 =? GZIP_STATE); [destruct (deflate_gzip_header s1) as [s2 [rc|]]; [reflexivity | tail_tac flush s2] | tail_tac flush s1]
        | destruct (ds_status s0 =? GZIP_STATE); [destruct (deflate_gzip_header s0) as [s2 [rc|]]; [reflexivity | tail_tac flush s2] | tail_tac flush s0] ] ] ].
  destruct (negb (ds_pending (set_last_flush s flush) =? 0)).
  - destruct (cs_avail_out (ds_strm (flush_pending (set_last_flush s flush))) =? 0); [reflexivity|].
    set (s0 := flush_pending (set_last_flush s flush)). clearbody s0. cont_tac flush s0.
  - destruct ((cs_avail_in (ds_strm (set_last_flush s flush)) =? 0) && (RANK flush <=? RANK (ds_last_flush s)) && negb (flush =? Z_FINISH));
      [unfold err_return; reflexivity|].
    set (s0 := set_last_flush s flush). clearbody s0. cont_tac flush s0.
Qed.

Lemma status_set_status : forall s v, ds_status (set_status s v) = v.
Proof. intros s v. destruct s; reflexivity. Qed.

Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s.
Proof. intros s v. destruct s; reflexivity. Qed.

Lemma wrap_set_status : forall s v, ds_wrap (set_status s v) = ds_wrap s.
Proof. intros s v. destruct s; reflexivity. Qed.




Section Hdr.
Variables (ws hs PBL ILEN OCAP : Z).
Variable flush : Z.
Hypothesis Hflush : 0 <= flush < 16.

Definition f3_ok (s : deflate_state) : Prop :=
  0 <= ds_status s < 2 ^ 10 /\ -2 <= ds_wrap s <= 2 /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ live_status (ds_status s)
  /\ (ds_status s = INIT_STATE -> ds_wrap s <> 0 -> zlib_ok PBL OCAP s)
  /\ (ds_status s = GZIP_STATE -> gzip_ok PBL OCAP s).

Definition b4_ok (s : deflate_state) : Prop :=
  0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ 0 <= ds_lookahead s < 2 ^ 32 /\ 0 <= ds_status s < 2 ^ 10.



Definition front_ok (s : deflate_state) : Prop :=
  (dstatus_ok (ds_status s) /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32
   /\ 0 <= cs_next_in (ds_strm s) <= ILEN)
  /\ (f1_spec s flush = None ->
      f2_ok PBL OCAP flush s
      /\ match f2_spec s flush with
         | F2Ret _ _ => True
         | F2Fin s' => b4_ok s'
         | F2Hdr s' => f3_ok s' /\ b4_ok (fst (f3_spec s'))
         end).

End Hdr.
