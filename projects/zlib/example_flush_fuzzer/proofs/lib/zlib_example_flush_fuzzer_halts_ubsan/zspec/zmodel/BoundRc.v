(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInv DeflateInvKeep RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5
  DeflInvFbo DeflInvCore BoundInv BoundCore.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma status_putShortMSB : forall s b, ds_status (putShortMSB s b) = ds_status s.
Proof. intros. unfold putShortMSB. rewrite !status_put_byte. reflexivity. Qed.

Lemma trailer_status : forall s, ds_status (fst (deflate_trailer s)) = ds_status s.
Proof.
  intros s. unfold deflate_trailer. cbv zeta.
  match goal with |- context [flush_pending ?Y] => set (x := flush_pending Y); assert (E : ds_status x = ds_status s) end.
  { subst x. rewrite (proj1 (flush_pending_keeps _)).
    destruct (ds_wrap s =? 2); [rewrite !status_put_byte | rewrite !status_putShortMSB]; reflexivity. }
  clearbody x. cbn [fst]. destruct (0 <? ds_wrap x); [destruct x; exact E | exact E].
Qed.

Lemma trailer_rc : forall s, snd (deflate_trailer s) = Z_OK \/ snd (deflate_trailer s) = Z_STREAM_END.
Proof.
  intros s. unfold deflate_trailer. cbv zeta.
  match goal with |- context [negb (ds_pending ?X =? 0)] => destruct (negb (ds_pending X =? 0)) end; cbn [snd]; [left | right]; reflexivity.
Qed.

Section RC.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis TS : tfb_safe_stmt.
  Hypothesis TR : tfb_room_stmt.
  Hypothesis HPBL : 2048 <= PBL.
  Hypothesis HLBS : PBL = 4 * 16384.
  Variable flush : Z.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Let DCORE := dcore ws hs PBL ILEN OCAP tot0.

  Lemma HF16' : 0 <= flush < 16.
  Proof. destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia. Qed.
  Lemma HF5' : flush <= 5.
  Proof. destruct HFL as [-> | ->]; unfold Z_NO_FLUSH, Z_FINISH; lia. Qed.



  Lemma f2_rc : forall s, DCORE s -> cs_avail_out (ds_strm s) <> 0 ->
    (ds_status s = FINISH_STATE -> flush = Z_FINISH /\ cs_avail_in (ds_strm s) = 0) ->
    (flush = Z_NO_FLUSH -> cs_avail_in (ds_strm s) <> 0) ->
    match f2_spec s flush with
    | F2Ret s' rc => rc = Z_OK /\ ds_status s' = ds_status s
    | F2Hdr s' => ds_status s' = ds_status s
    | F2Fin s' => ds_status s' = ds_status s
    end.
  Proof.
    intros s D AO HFS HIN. unfold f2_spec.
    pose proof (flush_pending_keeps (set_last_flush s flush)) as (KS & KA & _).
    rewrite status_set_last_flush in KS.
    assert (KA0 : cs_avail_in (ds_strm (set_last_flush s flush)) = cs_avail_in (ds_strm s)) by (destruct s; reflexivity).
    rewrite KA0 in KA.
    assert (E2 : forall x, ds_status x = ds_status s -> cs_avail_in (ds_strm x) = cs_avail_in (ds_strm s) ->
                 (ds_status x =? FINISH_STATE) && negb (cs_avail_in (ds_strm x) =? 0) = false).
    { intros x -> ->. destruct (Z.eqb_spec (ds_status s) FINISH_STATE) as [SF|SF]; [|reflexivity]. destruct (HFS SF) as [_ ->]. reflexivity. }
    assert (CONT : forall x, ds_status x = ds_status s -> cs_avail_in (ds_strm x) = cs_avail_in (ds_strm s) ->
      match (if (ds_status x =? FINISH_STATE) && negb (cs_avail_in (ds_strm x) =? 0)
             then (let '(s0, rc) := err_return x Z_BUF_ERROR in F2Ret s0 rc)
             else if ds_status x =? FINISH_STATE then F2Fin x else F2Hdr x)
      with F2Ret s' rc => rc = Z_OK /\ ds_status s' = ds_status s | F2Hdr s' => ds_status s' = ds_status s | F2Fin s' => ds_status s' = ds_status s end).
    { intros x X1 X2. rewrite (E2 x X1 X2). destruct (ds_status x =? FINISH_STATE); exact X1. }
    cbv zeta. destruct (negb (ds_pending (set_last_flush s flush) =? 0)).
    - destruct (cs_avail_out (ds_strm (flush_pending (set_last_flush s flush))) =? 0); cbv beta iota.
      + split; [reflexivity|]. rewrite status_set_last_flush. exact KS.
      + exact (CONT _ KS KA).
    - rewrite KA0. assert (E3 : (cs_avail_in (ds_strm s) =? 0) && (RANK flush <=? RANK (ds_last_flush s)) && negb (flush =? Z_FINISH) = false).
      { destruct HFL as [F0|FF]; [| rewrite FF, Bool.andb_false_r; reflexivity].
        replace (cs_avail_in (ds_strm s) =? 0) with false by (symmetry; apply Z.eqb_neq; exact (HIN F0)). reflexivity. }
      rewrite E3. cbv beta iota. apply CONT; [apply status_set_last_flush | exact KA0].
  Qed.


  Lemma blocks_rc : forall s, ZB ws hs PBL ILEN OCAP tot0 s -> ds_status s = BUSY_STATE ->
    let '(s2, r) := blocks_body s flush in
    match r with
    | Some rc => rc = Z_OK /\ (ds_status s2 = FINISH_STATE -> flush = Z_FINISH)
    | None => (flush = Z_FINISH -> ds_status s2 = FINISH_STATE) /\ (ds_status s2 = FINISH_STATE -> flush = Z_FINISH)
    end.
  Proof.
    intros s Z SB. pose proof HF16' as HF16. pose proof HF5' as HF5.
    pose proof (blocks_inv ws hs PBL ILEN OCAP tot0 TS TR HPBL flush HF16 s Z SB HF5) as [_ BP].
    pose proof (cfunc_inv ws hs PBL ILEN OCAP tot0 TS TR HPBL flush HF16 s Z SB HF5) as [_ CP].
    revert BP. unfold blocks_body. destruct (run_compress_func s flush) as [s1 bs].
    destruct CP as (_ & SB1 & _ & R).
    destruct bs; cbn [block_state_eqb orb andb].
    - destruct (cs_avail_out (ds_strm s1) =? 0); intros _; (split; [reflexivity|]); rewrite ?status_set_last_flush, SB1; intros X; discriminate X.
    - destruct R as (_ & _ & _ & _ & _ & NF & NNF). exfalso. destruct HFL as [F|F]; [exact (NNF F) | exact (NF F)].
    - destruct R as (_ & _ & F4 & _). destruct (cs_avail_out _ =? 0); intros _; (split; [reflexivity | intros _; exact F4]).
    - destruct R as (_ & _ & _ & _ & F4). intros _. split; [intros _; reflexivity | intros _; exact F4].
  Qed.

End RC.
