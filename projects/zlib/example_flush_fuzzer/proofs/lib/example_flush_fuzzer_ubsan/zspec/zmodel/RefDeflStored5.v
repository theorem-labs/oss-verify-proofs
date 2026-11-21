(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk
  TreeModel FillWinModel SendModel BitsModel AdlerModel ZChkAdl SymEx2Expr RefFlushPend1 RefDeflStored2 RefDeflStored3 RefDeflStored4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition tripB (s : deflate_state) : deflate_state :=
  let len := slen s in
  let left := sleft s in
  let s1 := tr_stored_block s None 0 (slast s) in
  let s2 := hdr4 s1 len in
  let s3 := flush_pending s2 in
  let '(s4, len') := if negb (left =? 0) then (awpost s3 (sL s), len - sL s) else (s3, len) in
  if negb (len' =? 0) then rbpost s4 len' else s4.

Lemma body_eqB : forall mb s,
  0 <= ds_block_start s <= ds_strstart s -> ds_strstart s < 2 ^ 32 ->
  hdrb s <= cs_avail_out (ds_strm s) ->
  deflate_stored_body s Z_FINISH mb = if sbrkB mb s then (s, 0, true) else (tripB s, slast s, false).
Proof.
  intros mb s Hbs Hss Hh.
  unfold deflate_stored_body, sbrkB, slast, tripB, sL, slen, sL1, sleft, rbpost, awpost, hdr4, slast. rewrite hdrb_model.
  rewrite (proj2 (Z.ltb_ge _ _) Hh).
  rewrite (wrap32_id (ds_strstart s - ds_block_start s)) by lia.
  rewrite Z.eqb_refl. change (Z_FINISH =? Z_NO_FLUSH) with false. cbn [negb]. rewrite Bool.andb_false_r. cbn [andb orb].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct (negb (ds_strstart s - ds_block_start s =? 0)); reflexivity.
Qed.

Lemma slast_range : forall s, slast s = 0 \/ slast s = 1.
Proof. intros s. unfold slast. destruct (_ =? _); [right | left]; reflexivity. Qed.


Section LoopB.
Variables (ws hs PBL ILEN OCAP : Z).
Variables (flush mb : Z).
Hypothesis Hflush : 0 <= flush <= 5.
Hypothesis Hmb : 0 <= mb < 2 ^ 18.
Hypothesis Hf4 : flush = Z_FINISH.
Local Notation outlen st := (Z.of_nat (length (cs_out_rev st))).

Definition tripB_ok (s : deflate_state) : Prop :=
  let len := slen s in
  let left := sleft s in
  let s1 := tr_stored_block s None 0 (slast s) in
  let s2 := hdr4 s1 len in
  let s3 := flush_pending s2 in
  let L := sL s in
  let s4 := (if negb (left =? 0) then awpost s3 L else s3) in
  let len' := (if negb (left =? 0) then len - L else len) in
  tripA_wf s /\ BINV PBL s /\ 4 <= ds_pending s1 <= PBL /\ fp_ok PBL OCAP s2
  /\ (left <> 0 -> winA_ok ws OCAP s3 L) /\ rdA_ok ILEN OCAP s4 len'.

Fixpoint loopB_ok (fuel : nat) (s : deflate_state) : Prop :=
  match fuel with
  | O => tripA_wf s /\ cs_avail_out (ds_strm s) < hdrb s
  | Datatypes.S f => tripA_wf s /\ (hdrb s <= cs_avail_out (ds_strm s) ->
      tripB_ok s /\ (sbrkB mb s = false -> slast s = 0 -> loopB_ok f (tripB s)))
  end.

Lemma loopB_model : forall fuel s,
  0 <= ds_block_start s <= ds_strstart s -> ds_strstart s < 2 ^ 32 ->
  deflate_stored_loop (Datatypes.S fuel) s Z_FINISH mb =
    (if cs_avail_out (ds_strm s) <? hdrb s then (s, 0)
     else if sbrkB mb s then (s, 0)
     else if slast s =? 0 then deflate_stored_loop fuel (tripB s) Z_FINISH mb else (tripB s, slast s)).
Proof.
  intros fuel s Hbs Hss. cbn [deflate_stored_loop].
  destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) (hdrb s)) as [C|C].
  - rewrite (body_brkA Z_FINISH mb s C). reflexivity.
  - rewrite (body_eqB mb s Hbs Hss C). destruct (sbrkB mb s); reflexivity.
Qed.

End LoopB.
