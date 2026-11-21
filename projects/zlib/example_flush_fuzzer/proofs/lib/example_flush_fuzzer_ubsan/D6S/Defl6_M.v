(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate FillWinModel
  RefFlushPend1 RefDeflateEnd1 RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5 RefDeflateTrl1.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Defl6_1 Defl6_2 Defl6_3 Defl6_4 Defl6_5 Defl6_6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Definition dlive (ds : deflate_state) (f : Z) : Prop :=
  (f = 0 \/ f = 3 \/ f = 4)
  /\ dstat_live (ds_status ds)
  /\ 0 < cs_avail_out (ds_strm ds) < 2 ^ 31
  /\ 0 <= cs_avail_in (ds_strm ds) < 2 ^ 31
  /\ (cs_avail_in (ds_strm ds) = 0 -> f = 4)
  /\ (ds_status ds = 666 -> cs_avail_in (ds_strm ds) = 0)
  /\ (ds_status ds = 42 -> ds_wrap ds = 1 /\ ds_pending ds = 0 /\ ds_strstart ds = 0)
  /\ ds_level ds = 6 /\ ds_strategy ds = 0 /\ ds_w_bits ds = 15
  /\ (ds_wrap ds = 1 \/ ds_wrap ds = -1)
  /\ 0 <= ds_pending ds < 2 ^ 31
  /\ cs_next_in (ds_strm ds) = 0
  /\ 0 <= cs_adler (ds_strm ds) < 2 ^ 32.


Definition bd_st (X : deflate_state) : deflate_state :=
  let s := tr_stored_block X None 0 0 in
  let s := clear_hash s in
  if ds_lookahead s =? 0 then set_insert (set_block_start (set_strstart s 0) 0) 0 else s.

Section Stages.
Variables (ds : deflate_state) (f : Z).

Definition X1 : deflate_state := set_last_flush ds f.
Definition X2 : deflate_state := flush_pending X1.
Definition X3 : deflate_state := if ds_pending ds =? 0 then X1 else X2.
Definition X4h : deflate_state := flush_pending (hdr_st X3).
Definition X4 : deflate_state := if ds_status ds =? 42 then X4h else X3.
Definition X5 : deflate_state := fst (deflate_slow X4 f).
Definition BS : block_state := snd (deflate_slow X4 f).
Definition X6 : deflate_state := bst_st X5 BS.
Definition X6d : deflate_state := bd_st X5.
Definition X6f : deflate_state := flush_pending X6d.
Definition X7 : deflate_state := if blocks_cond X4 f then X6 else X4.
Definition X8 : deflate_state := flush_pending (trl_st X7).

Definition live_tail (X : deflate_state) : deflate_state * Z :=
  if negb (f =? 4) then (X, Z_OK)
  else if ds_wrap X <=? 0 then (X, Z_STREAM_END)
  else let X8 := flush_pending (trl_st X) in (t2_st X8, if ds_pending X8 =? 0 then Z_STREAM_END else Z_OK).

Definition live_core : deflate_state * Z :=
  if negb (ds_pending ds =? 0) && (cs_avail_out (ds_strm X2) =? 0) then (set_last_flush X2 (-1), Z_OK)
  else if (ds_status ds =? 42) && negb (ds_pending X4h =? 0) then (set_last_flush X4h (-1), Z_OK)
  else if blocks_cond X4 f then
    match BS with
    | finish_done => live_tail X6
    | block_done => (if cs_avail_out (ds_strm X6f) =? 0 then set_last_flush X6f (-1) else X6f, Z_OK)
    | _ => (if cs_avail_out (ds_strm X6) =? 0 then set_last_flush X6 (-1) else X6, Z_OK)
    end
  else if f =? 0 then (X4, Z_OK) else live_tail X4.

End Stages.

End FXG.
Global Strategy expand [X1 X2 X3 X4h X4 X5 BS X6 X6d X6f X7 X8 live_tail live_core bd_st].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Global Strategy expand [hdr_st pend_pc bst_st bst_pc bc64_cond bc64_pc t1_pc t1_st trl_st t2_st Defl6_2.fpa_pc Defl6_2.avail_pc].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Section Safe.
Variable SSAFE : deflate_state -> Z -> Prop.

Definition fp_pre6 (PBL : Z) (X : deflate_state) : Prop :=
  let X1 := tr_flush_bits X in
  BINV PBL X /\ 0 <= ds_pending X1 <= PBL /\ ds_pending X1 < 2 ^ 31 /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + ds_pending X1 <= PBL
  /\ 0 <= cs_avail_out (ds_strm X1) < 2 ^ 31 /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64.

Definition G3 (ds : deflate_state) (f : Z) : Prop :=
  ds_pending ds <> 0 -> cs_avail_out (ds_strm (X3 ds f)) <> 0.
Definition G4 (ds : deflate_state) (f : Z) : Prop :=
  G3 ds f /\ (ds_status ds = 42 -> ds_pending (X4h ds f) = 0).
Definition G7 (ds : deflate_state) (f : Z) : Prop :=
  G4 ds f /\ ((blocks_cond (X4 ds f) f = false /\ f <> 0) \/ (blocks_cond (X4 ds f) f = true /\ BS ds f = finish_done)).

Definition dsafe6 (ds : deflate_state) (f : Z) : Prop :=
  let PBL := ds_lit_bufsize ds * 4 in
  dlive ds f
  /\ (ds_pending ds <> 0 ->
        fp_pre6 PBL (X1 ds f)
        /\ 0 <= cs_avail_out (ds_strm (X2 ds f)) < 2 ^ 31 /\ 0 <= ds_status (X2 ds f) < 2 ^ 31
        /\ ds_status (X2 ds f) = ds_status ds /\ cs_avail_in (ds_strm (X2 ds f)) = cs_avail_in (ds_strm ds))
  /\ (ds_status ds = 42 ->
        2 <= PBL /\ fp_pre6 PBL (hdr_st (X3 ds f))
        /\ 0 <= ds_pending (X4h ds f) < 2 ^ 63 /\ ds_status (X4h ds f) = 113)
  /\ 0 <= cs_avail_in (ds_strm (X4 ds f)) < 2 ^ 31 /\ 0 <= ds_lookahead (X4 ds f) < 2 ^ 31 /\ 0 <= ds_status (X4 ds f) < 2 ^ 31
  /\ ds_level (X4 ds f) = 6 /\ ds_strategy (X4 ds f) = 0
  /\ (ds_status ds = 666 -> cs_avail_in (ds_strm (X3 ds f)) = 0)
  /\ - 2 ^ 31 <= ds_wrap (X3 ds f) < 2 ^ 31 /\ ds_wrap (X3 ds f) <> 0
  /\ (G4 ds f -> blocks_cond (X4 ds f) f = true ->
        SSAFE (X4 ds f) f /\ 0 <= cs_avail_out (ds_strm (X5 ds f)) < 2 ^ 31
        /\ (BS ds f = block_done ->
              f = 3 /\ BINV PBL (X5 ds f) /\ ds_pending (tr_stored_block (X5 ds f) None 0 0) <= PBL
              /\ fp_pre6 PBL (X6d ds f) /\ 0 <= cs_avail_out (ds_strm (X6f ds f)) < 2 ^ 31
              /\ 0 <= ds_lookahead (X5 ds f) < 2 ^ 31 /\ ds_hash_size (X5 ds f) = 32768
              /\ ds_w_size (X5 ds f) = 32768 ))
  /\ (G7 ds f ->
        (ds_wrap (X7 ds f) = 1 \/ ds_wrap (X7 ds f) = -1)
        /\ 0 <= ds_pending (X7 ds f) /\ ds_pending (X7 ds f) + 4 <= PBL /\ 0 <= cs_adler (ds_strm (X7 ds f)) < 2 ^ 32
        /\ (f = 4 -> 0 < ds_wrap (X7 ds f) ->
              fp_pre6 PBL (trl_st (X7 ds f))
              /\ (ds_wrap (X8 ds f) = 1 \/ ds_wrap (X8 ds f) = -1) /\ 0 <= ds_pending (X8 ds f) < 2 ^ 63
              /\ 0 <= cs_total_in (ds_strm (X7 ds f))))
  /\ 0 <= arr_len (cs_input (ds_strm ds)).
End Safe.
End FXG.
Global Strategy expand [fp_pre6 dsafe6 dlive G3 G4 G7].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


End FXG.
Ltac peq := cbv beta iota zeta; apply (f_equal2 pair); [exact eq_refl | reflexivity].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma zhdr0_small : forall X, ds_w_bits X = 15 -> ds_level X = 6 -> ds_strategy X = 0 -> ds_strstart X = 0 -> zhdr0 X = 30848.
Proof using. intros X A B C D. unfold zhdr0. rewrite A, B, C, D. reflexivity. Qed.

Lemma zhdr_small : forall X, ds_w_bits X = 15 -> ds_level X = 6 -> ds_strategy X = 0 -> ds_strstart X = 0 -> zhdr X = 30876.
Proof using. intros X A B C D. unfold zhdr. rewrite (zhdr0_small X A B C D). reflexivity. Qed.

Lemma hdr_st_eq : forall X,
  ds_pending X = 0 -> ds_strstart X = 0 -> ds_w_bits X = 15 -> ds_level X = 6 -> ds_strategy X = 0 ->
  0 <= cs_adler (ds_strm X) < 2 ^ 32 ->
  zlib_s3_spec X = hdr_st X.
Proof using.
  intros X Hp Hs Hw Hl Hst Ha.
  rewrite (zlib_s3_spec_eq X ltac:(lia) Ha), (zhdr_small X Hw Hl Hst Hs).
  unfold zl_s3, zl_s2, zl_s1, put_byte, hdr_st, adler32_init, BUSY_STATE. change (30876 / 2 ^ 8) with 120.
  destruct X; cbn -[arr_set wrap8 Z.add] in Hp, Hs |- *. subst. cbn [Z.eqb negb Z.add]. reflexivity.
Qed.

Lemma trl_st_eq : forall X, ta_post X = trl_st X.
Proof using.
  intros X. unfold ta_post, trl_st, put_byte. destruct X; cbv -[arr_set wrap8 Z.add Z.div Z.pow].
  match goal with |- context [?a + 1 + 1 + 1 + 1] => replace (a + 1 + 1 + 1 + 1) with (a + 4) by lia end.
  repeat match goal with |- context [?a + 1 + 1 + 1] => replace (a + 1 + 1 + 1) with (a + 3) by lia end.
  repeat match goal with |- context [?a + 1 + 1] => replace (a + 1 + 1) with (a + 2) by lia end.
  match goal with |- ?a = ?b => constr_eq a b end. reflexivity.
Qed.

Lemma t2_st_td : forall X, td_post X = t2_st X.
Proof using. reflexivity. Qed.

Lemma bst_body : forall s f,
  (snd (run_compress_func s f) = block_done -> f = 3) ->
  blocks_body s f =
    (let X5 := fst (run_compress_func s f) in let bs := snd (run_compress_func s f) in let X6 := bst_st X5 bs in
     match bs with
     | finish_done => (X6, None)
     | block_done => (let X6f := flush_pending (bd_st X5) in
                      if cs_avail_out (ds_strm X6f) =? 0 then (set_last_flush X6f (-1), Some Z_OK) else (X6f, None))
     | _ => (if cs_avail_out (ds_strm X6) =? 0 then set_last_flush X6 (-1) else X6, Some Z_OK)
     end).
Proof using.
  intros s f Hbd. unfold blocks_body. destruct (run_compress_func s f) as [X5 bs]. cbn [fst snd] in *.
  unfold bst_st. destruct bs; cbn [block_state_eqb orb]; try reflexivity.
  rewrite (Hbd eq_refl). unfold Z_PARTIAL_FLUSH, Z_BLOCK, Z_FULL_FLUSH, bd_st.
  generalize (tr_stored_block X5 None 0 0). intro T.
  cbn [Z.eqb Pos.eqb negb]. reflexivity.
Qed.

Lemma run_compress_func_slow : forall s f, ds_level s = 6 -> ds_strategy s = 0 -> run_compress_func s f = deflate_slow s f.
Proof using. intros s f A B. unfold run_compress_func. rewrite A, B. reflexivity. Qed.

Lemma X1_keeps : forall ds f,
  ds_status (X1 ds f) = ds_status ds /\ ds_wrap (X1 ds f) = ds_wrap ds /\ ds_pending (X1 ds f) = ds_pending ds
  /\ ds_strstart (X1 ds f) = ds_strstart ds /\ ds_w_bits (X1 ds f) = ds_w_bits ds /\ ds_level (X1 ds f) = ds_level ds
  /\ ds_strategy (X1 ds f) = ds_strategy ds /\ ds_strm (X1 ds f) = ds_strm ds.
Proof using. intros ds f. unfold X1. destruct ds; repeat split; reflexivity. Qed.

Lemma core_tail_live : forall X f,
  (f = 4 -> 0 < ds_wrap X -> 0 <= cs_adler (ds_strm X) < 2 ^ 32 /\ 0 <= cs_total_in (ds_strm X) /\ (ds_wrap X = 1 \/ ds_wrap X = -1)) ->
  core_tail X f = live_tail f X.
Proof using.
  intros X f H. unfold core_tail, live_tail, Z_FINISH.
  destruct (Z.eqb_spec f 4) as [Ef|Ef]; cbn [negb]; [| peq].
  destruct (Z.leb_spec (ds_wrap X) 0) as [Hw|Hw]; [peq|].
  destruct (H Ef Hw) as (Ha & Ht & Hw1).
  rewrite (deflate_trailer_eq X Ha Ht). cbv zeta.
  replace (ds_wrap X =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite trl_st_eq, pending_td_post, t2_st_td.
  destruct (ds_pending (flush_pending (trl_st X)) =? 0); peq.
Qed.

Lemma blocks_live : forall X f,
  ds_level X = 6 -> ds_strategy X = 0 ->
  (blocks_cond X f = true -> snd (deflate_slow X f) = block_done -> f = 3) ->
  (let X7 := if blocks_cond X f then bst_st (fst (deflate_slow X f)) (snd (deflate_slow X f)) else X in
   ((blocks_cond X f = false /\ f <> 0) \/ (blocks_cond X f = true /\ snd (deflate_slow X f) = finish_done)) ->
   f = 4 -> 0 < ds_wrap X7 -> 0 <= cs_adler (ds_strm X7) < 2 ^ 32 /\ 0 <= cs_total_in (ds_strm X7) /\ (ds_wrap X7 = 1 \/ ds_wrap X7 = -1)) ->
  match blocks_or_idle X f with
  | FrontRet s' rc => (s', rc)
  | FrontBlocks s' => let '(s2, r) := blocks_body s' f in match r with Some rc => (s2, rc) | None => core_tail s2 f end
  | FrontIdle s' => core_tail s' f
  end
  = if blocks_cond X f then
      match snd (deflate_slow X f) with
      | finish_done => live_tail f (bst_st (fst (deflate_slow X f)) (snd (deflate_slow X f)))
      | block_done => (if cs_avail_out (ds_strm (flush_pending (bd_st (fst (deflate_slow X f))))) =? 0
                       then set_last_flush (flush_pending (bd_st (fst (deflate_slow X f)))) (-1)
                       else flush_pending (bd_st (fst (deflate_slow X f))), Z_OK)
      | _ => (if cs_avail_out (ds_strm (bst_st (fst (deflate_slow X f)) (snd (deflate_slow X f)))) =? 0
              then set_last_flush (bst_st (fst (deflate_slow X f)) (snd (deflate_slow X f))) (-1)
              else bst_st (fst (deflate_slow X f)) (snd (deflate_slow X f)), Z_OK)
      end
    else if f =? 0 then (X, Z_OK) else live_tail f X.
Proof using.
  intros X f Hlv Hsg Hbd Htr. unfold blocks_or_idle, Z_NO_FLUSH. cbv zeta in Htr.
  destruct (blocks_cond X f) eqn:Ebc.
  - rewrite (bst_body X f) by (rewrite run_compress_func_slow by assumption; exact (Hbd eq_refl)).
    rewrite (run_compress_func_slow X f Hlv Hsg). cbv zeta.
    destruct (snd (deflate_slow X f)) eqn:Ebs; [peq | | peq |].
    +
      pose proof (Hbd eq_refl eq_refl) as Ef3.
      destruct (cs_avail_out (ds_strm (flush_pending (bd_st (fst (deflate_slow X f))))) =? 0) eqn:Eao; [peq|].
      unfold core_tail, Z_FINISH. rewrite Ef3. cbn [Z.eqb Pos.eqb negb]. peq.
    + cbv beta iota zeta. apply (core_tail_live _ f). intros Ef Hw. exact (Htr (or_intror (conj eq_refl eq_refl)) Ef Hw).
  - destruct (Z.eqb_spec f 0) as [Ef0|Ef0]; [peq|]. apply (core_tail_live _ f). intros Ef Hw. exact (Htr (or_introl (conj eq_refl Ef0)) Ef Hw).
Qed.

Section Live.
Variable SSAFE : deflate_state -> Z -> Prop.

Theorem core_live : forall ds f, dsafe6 SSAFE ds f -> deflate_core ds f = live_core ds f.
Proof using.
  intros ds f HS.
  destruct HS as (HL & Hf2 & Hh & Hai4 & Hlk4 & Hst4 & Hlv4 & Hsg4 & Hai3 & Hw3 & Hw3' & Hblk & Htl & Hil).
  destruct HL as (Hf & Hstat & Hao & Hai & Haif & H666 & H42 & Hlv & Hsg & Hwb & Hwrap & Hpd & Hni & Had).
  rewrite deflate_core_front.
  assert (E1 : f1_spec ds f = None).
  { unfold f1_spec, deflateStateCheck, Z_BLOCK, Z_FINISH, FINISH_STATE, INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE.
    destruct Hstat as [E|[E|E]]; rewrite E; cbn [Z.eqb Pos.eqb orb negb andb];
      (replace (5 <? f) with false by (symmetry; apply Z.ltb_ge; lia));
      (replace (f <? 0) with false by (symmetry; apply Z.ltb_ge; lia)); cbn [orb];
      (replace (cs_avail_out (ds_strm ds) =? 0) with false by (symmetry; apply Z.eqb_neq; lia)); try reflexivity.
    replace (f =? 4) with true by (symmetry; apply Z.eqb_eq; apply Haif; apply H666; exact E). reflexivity. }
  unfold front_spec. rewrite E1.
  unfold f2_spec. fold (X1 ds f). change (ds_pending (X1 ds f)) with (ds_pending ds). fold (X2 ds f).
  change (cs_avail_in (ds_strm (X1 ds f))) with (cs_avail_in (ds_strm ds)).
  unfold live_core.
  assert (KX3 : forall s : deflate_state,
    ds_status s = ds_status ds -> cs_avail_in (ds_strm s) = cs_avail_in (ds_strm ds) ->
    (if (ds_status s =? FINISH_STATE) && negb (cs_avail_in (ds_strm s) =? 0)
     then let '(s0, rc) := err_return s Z_BUF_ERROR in F2Ret s0 rc
     else if ds_status s =? FINISH_STATE then F2Fin s else F2Hdr s)
    = (if ds_status ds =? 666 then F2Fin s else F2Hdr s)).
  { intros s Es Ea. rewrite Es, Ea. unfold FINISH_STATE.
    destruct (Z.eqb_spec (ds_status ds) 666) as [E6|E6]; cbn [andb]; [| reflexivity].
    rewrite (proj2 (Z.eqb_eq _ _) (H666 E6)). reflexivity. }
  assert (TAIL : forall X3v : deflate_state, G3 ds f -> X3v = X3 ds f ->
    match match (if ds_status ds =? 666 then F2Fin X3v else F2Hdr X3v) with
          | F2Ret s' rc => FrontRet s' rc
          | F2Hdr s' => match f3_spec s' with (s'', Some rc) => FrontRet s'' rc | (s'', None) => blocks_or_idle s'' f end
          | F2Fin s' => blocks_or_idle s' f
          end with
    | FrontRet s' rc => (s', rc)
    | FrontBlocks s' => let '(s2, r) := blocks_body s' f in match r with Some rc => (s2, rc) | None => core_tail s2 f end
    | FrontIdle s' => core_tail s' f
    end
    = if (ds_status ds =? 42) && negb (ds_pending (X4h ds f) =? 0) then (set_last_flush (X4h ds f) (-1), Z_OK)
      else if blocks_cond (X4 ds f) f then
        match BS ds f with
        | finish_done => live_tail f (X6 ds f)
        | block_done => (if cs_avail_out (ds_strm (X6f ds f)) =? 0 then set_last_flush (X6f ds f) (-1) else X6f ds f, Z_OK)
        | _ => (if cs_avail_out (ds_strm (X6 ds f)) =? 0 then set_last_flush (X6 ds f) (-1) else X6 ds f, Z_OK)
        end
      else if f =? 0 then (X4 ds f, Z_OK) else live_tail f (X4 ds f)).
  { intros X3v HG3 EX3.
    assert (E4 : X4 ds f = (if ds_status ds =? 42 then X4h ds f else X3v)) by (unfold X4; rewrite <- EX3; reflexivity).
    assert (E4h : X4h ds f = flush_pending (hdr_st X3v)) by (unfold X4h; rewrite <- EX3; reflexivity).
    assert (BL : forall X, G4 ds f -> X = X4 ds f ->
      match blocks_or_idle X f with
      | FrontRet s' rc => (s', rc)
      | FrontBlocks s' => let '(s2, r) := blocks_body s' f in match r with Some rc => (s2, rc) | None => core_tail s2 f end
      | FrontIdle s' => core_tail s' f
      end
      = if blocks_cond (X4 ds f) f then
          match BS ds f with
          | finish_done => live_tail f (X6 ds f)
          | block_done => (if cs_avail_out (ds_strm (X6f ds f)) =? 0 then set_last_flush (X6f ds f) (-1) else X6f ds f, Z_OK)
          | _ => (if cs_avail_out (ds_strm (X6 ds f)) =? 0 then set_last_flush (X6 ds f) (-1) else X6 ds f, Z_OK)
          end
        else if f =? 0 then (X4 ds f, Z_OK) else live_tail f (X4 ds f)).
    { intros X HG4 ->. unfold X6, X6f, X6d, X5, BS. apply (blocks_live (X4 ds f) f Hlv4 Hsg4).
      - intros Hb Hd. exact (proj1 (proj2 (proj2 (Hblk HG4 Hb)) Hd)).
      - cbv zeta. fold (X5 ds f) (BS ds f). fold (X6 ds f). fold (X7 ds f). intros Hcase Ef Hw.
        destruct (Htl (conj HG4 Hcase)) as (Hw7 & Hp7 & Hp74 & Ha7 & Htr).
        destruct (Htr Ef Hw) as (_ & _ & _ & Hti). exact (conj Ha7 (conj Hti Hw7)). }
    pose proof (X1_keeps ds f) as (K1s & K1w & K1p & K1ss & K1wb & K1lv & K1sg & K1st).
    assert (SX3 : ds_status X3v = ds_status ds).
    { rewrite EX3. unfold X3. destruct (Z.eqb_spec (ds_pending ds) 0) as [Hq|Hq]; [exact K1s | exact (proj1 (proj2 (proj2 (proj2 (Hf2 Hq)))))]. }
    destruct Hstat as [E42|[E113|E666]].
    +
      rewrite E42 in SX3 |- *. cbn [Z.eqb Pos.eqb andb].
      destruct (H42 E42) as (Hw1 & Hp00 & Hss).
      assert (EX3' : X3v = X1 ds f) by (rewrite EX3; unfold X3; rewrite (proj2 (Z.eqb_eq _ _) Hp00); reflexivity).
      unfold f3_spec. rewrite SX3. unfold INIT_STATE. cbn [Z.eqb Pos.eqb andb].
      replace (ds_wrap X3v =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite EX3; exact Hw3'). cbn [andb Z.eqb Pos.eqb].
      rewrite SX3. cbn [Z.eqb Pos.eqb].
      rewrite deflate_zlib_header_spec.
      rewrite (hdr_st_eq X3v) by (rewrite EX3'; rewrite ?K1p, ?K1ss, ?K1wb, ?K1lv, ?K1sg, ?K1st; first [assumption | lia]).
      rewrite <- E4h. cbv zeta.
      destruct (Z.eqb_spec (ds_pending (X4h ds f)) 0) as [Hq|Hq]; cbn [negb].
      * destruct (Hh E42) as (_ & _ & _ & Hs113). rewrite Hs113. unfold GZIP_STATE. cbn [Z.eqb Pos.eqb].
        apply BL; [split; [exact HG3 | intros _; exact Hq]|]. rewrite E4, E42, Z.eqb_refl. cbv beta iota. reflexivity.
      * peq.
    +
      rewrite E113 in SX3 |- *. cbn [Z.eqb Pos.eqb andb].
      unfold f3_spec. rewrite SX3. unfold INIT_STATE, GZIP_STATE. cbn [Z.eqb Pos.eqb andb].
      rewrite SX3. cbn [Z.eqb Pos.eqb andb]. rewrite SX3. cbn [Z.eqb Pos.eqb andb].
      apply BL; [split; [exact HG3 | intros E; rewrite E113 in E; discriminate E]|]. rewrite E4, E113. cbn [Z.eqb Pos.eqb]. reflexivity.
    +
      rewrite E666 in SX3 |- *. cbn [Z.eqb Pos.eqb andb].
      apply BL; [split; [exact HG3 | intros E; rewrite E666 in E; discriminate E]|]. rewrite E4, E666. cbn [Z.eqb Pos.eqb]. reflexivity. }
  destruct (Z.eqb_spec (ds_pending ds) 0) as [Hp0|Hp0]; cbn [negb andb].
  -
    replace ((cs_avail_in (ds_strm ds) =? 0) && (RANK f <=? RANK (ds_last_flush ds)) && negb (f =? Z_FINISH)) with false.
    2:{ symmetry. unfold Z_FINISH. destruct (Z.eqb_spec (cs_avail_in (ds_strm ds)) 0) as [Ea|Ea]; [| reflexivity].
        rewrite (proj2 (Z.eqb_eq _ _) (Haif Ea)). cbn. destruct (_ <=? _); reflexivity. }
    rewrite (KX3 (X1 ds f) eq_refl eq_refl).
    apply TAIL; [intros P; exfalso; exact (P Hp0)|]. unfold X3. rewrite (proj2 (Z.eqb_eq _ _) Hp0). cbv beta iota. reflexivity.
  -
    destruct (Z.eqb_spec (cs_avail_out (ds_strm (X2 ds f))) 0) as [Ho|Ho]; cbn [negb andb]; [peq|].
    destruct (Hf2 Hp0) as (_ & _ & _ & Es2 & Ea2).
    rewrite (KX3 (X2 ds f) Es2 Ea2).
    apply TAIL; [intros _; unfold X3; rewrite (proj2 (Z.eqb_neq _ _) Hp0); exact Ho|].
    unfold X3. rewrite (proj2 (Z.eqb_neq _ _) Hp0). cbv beta iota. reflexivity.
Qed.
End Live.
End FXG.
