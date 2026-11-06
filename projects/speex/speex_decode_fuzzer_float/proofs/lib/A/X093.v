(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X082 X06n X08y X091 X08x X08m X08o X0b1 X0bf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation unpackM := (@bits_unpack_unsigned_M pst bptr).
Local Notation peekM := (@bits_peek_M pst bptr).
Local Notation advanceM := (@bits_advance_M pst bptr).
Local Notation remainingM := (@bits_remaining_M pst bptr).
Local Notation DEC := (speex_decode (St := pst) p_notify unpackM peekM advanceM remainingM).
Local Notation SEARCH := (nb_mode_search (St := pst) p_notify unpackM advanceM remainingM).
Local Notation NBDEC := (nb_decode (St := pst) p_notify unpackM advanceM remainingM).

Lemma prun_remaining : forall (b : bits_st bptr) q, prun (remainingM b) q = Some (speex_bits_remaining b, q).
Proof. intros. unfold bits_remaining_M. apply prun_ret. Qed.
Lemma prun_advance : forall (b : bits_st bptr) n q, prun (advanceM b n) q = Some (speex_bits_advance b n, q).
Proof. intros. unfold bits_advance_M. apply prun_ret. Qed.
Lemma skip_prun : forall (b : bits_st bptr) q, prun (nb_skip_wb_layer unpackM advanceM b) q = Some (skip_bits b, q).
Proof. intros. unfold nb_skip_wb_layer, skip_bits. rewrite prun_bind, prun_unpack. cbn beta iota. apply prun_advance. Qed.
Lemma user_handler_prun : forall (b : bits_st bptr) q, prun (speex_default_user_handler unpackM advanceM b) q = Some ((0, user_handler_bits b), q).
Proof.
intros. unfold speex_default_user_handler, user_handler_bits. rewrite prun_bind, prun_unpack. cbn beta iota.
rewrite prun_bind, prun_advance. cbn beta iota. apply prun_ret.
Qed.
Lemma stereo_handler_prun : forall (b : bits_st bptr) q, prun (speex_std_stereo_request_handler unpackM b) q = Some ((0, stereo_handler_bits b), q).
Proof.
intros. unfold speex_std_stereo_request_handler, stereo_handler_bits. repeat (rewrite prun_bind, prun_unpack; cbn beta iota). apply prun_ret.
Qed.
Lemma inband_prun : forall (b : bits_st bptr) sc q, prun (speex_inband_handler unpackM advanceM b sc) q = Some ((0, inband_bits sc b), q).
Proof.
intros. unfold speex_inband_handler, inband_bits. rewrite prun_bind, prun_unpack. cbn beta iota. cbv zeta.
unfold X1rh.SPEEX_INBAND_STEREO, X069.SPEEX_INBAND_STEREO.
destruct (sc && _); [apply stereo_handler_prun|].
rewrite prun_bind, prun_advance. cbn beta iota. apply prun_ret.
Qed.

Definition search_res (o : @search_out bptr) (q : pst) : option (nb_search_res (ptr := bptr) * pst) :=
match o with
| SOunr => None
| SOret r b' => Some (NbReturn r b', q)
| SOmode m b' => Some (NbMode m b', q)
| SOnotify tw b' => Some (NbReturn (-2) b', p_app (notify_bytes (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE)) q)
end.
Lemma nb_search_prun : forall fuel (st : nb_state bptr) (b : bits_st bptr) q,
prun (SEARCH fuel st b) q = search_res (search_pure fuel (nb_stereo_cb st) b) q.
Proof.
induction fuel as [|fuel IH]; intros st b q; [reflexivity|].
cbn [nb_mode_search search_pure].
rewrite prun_bind, prun_remaining. cbn beta iota.
destruct (speex_bits_remaining b <? 5); [apply prun_ret|].
rewrite prun_bind, prun_unpack. cbn beta iota. cbv zeta.
rewrite prun_bind.
assert (TAILE : forall (bm : bits_st bptr) q0,
prun (rem <- remainingM bm;;
if rem <? 4 then mret (NbReturn (-1) bm) else
' (m, b0) <- unpackM bm 4;;
if m =? 15 then mret (NbReturn (-1) b0)
else if m =? 14 then ' (ret, b1) <- speex_inband_handler unpackM advanceM b0 (nb_stereo_cb st);; if negb (ret =? 0) then mret (NbReturn ret b1) else SEARCH fuel st b1
else if m =? 13 then ' (ret, b1) <- speex_default_user_handler unpackM advanceM b0;; if negb (ret =? 0) then mret (NbReturn ret b1) else SEARCH fuel st b1
else if 8 <? m then p_notify MSG_INVALID_MODE;;; mret (NbReturn (-2) b0) else mret (NbMode m b0)) q0
= search_res (if speex_bits_remaining bm <? 4 then SOret (-1) bm else
let m := uv bm 4 in let b6 := ub bm 4 in
if m =? 15 then SOret (-1) b6 else if m =? 14 then search_pure fuel (nb_stereo_cb st) (inband_bits (nb_stereo_cb st) b6)
else if m =? 13 then search_pure fuel (nb_stereo_cb st) (user_handler_bits b6) else if 8 <? m then SOnotify false b6 else SOmode m b6) q0).
{ intros bm q0. rewrite prun_bind, prun_remaining. cbn beta iota.
destruct (speex_bits_remaining bm <? 4); [apply prun_ret|].
rewrite prun_bind, prun_unpack. cbn beta iota. cbv zeta.
destruct (uv bm 4 =? 15); [apply prun_ret|].
destruct (uv bm 4 =? 14). { rewrite prun_bind, inband_prun. cbn beta iota. cbn [Z.eqb negb]. apply IH. }
destruct (uv bm 4 =? 13). { rewrite prun_bind, user_handler_prun. cbn beta iota. cbn [Z.eqb negb]. apply IH. }
destruct (8 <? uv bm 4); [| apply prun_ret].
rewrite prun_bind, prun_notify. cbn beta iota. rewrite prun_ret. reflexivity. }
destruct (negb (uv b 1 =? 0)).
2: { rewrite prun_ret. cbn beta iota. apply TAILE. }
rewrite prun_bind, skip_prun. cbn beta iota. rewrite prun_bind, prun_remaining. cbn beta iota.
destruct (speex_bits_remaining (skip_bits (ub b 1)) <? 5). { rewrite prun_ret. cbn beta iota. apply prun_ret. }
rewrite prun_bind, prun_unpack. cbn beta iota.
destruct (negb (uv (skip_bits (ub b 1)) 1 =? 0)).
2: { rewrite prun_ret. cbn beta iota. apply TAILE. }
rewrite prun_bind, skip_prun. cbn beta iota. rewrite prun_bind, prun_unpack. cbn beta iota.
destruct (negb (uv (skip_bits (ub (skip_bits (ub b 1)) 1)) 1 =? 0)).
- rewrite prun_bind, prun_notify. cbn beta iota. rewrite prun_ret. cbn beta iota. rewrite prun_ret. reflexivity.
- rewrite prun_ret. cbn beta iota. apply TAILE.
Qed.
Lemma ltp_unquant_prun : forall k start (b : bits_st bptr) q, prun (ltp_unquant unpackM k start b) q = Some ((ltp_pitch k start b, ltp_bits k b), q).
Proof.
intros [|p] start b q; cbn [ltp_unquant ltp_pitch ltp_bits]; unfold forced_pitch_unquant, pitch_unquant_3tap, ltp3_pitch, ltp3_bits.
- apply prun_ret.
- repeat (rewrite prun_bind, prun_unpack; cbn beta iota). apply prun_ret.
Qed.
Lemma subframe_prun : forall sm olp sub (st : nb_state bptr) (b : bits_st bptr) q,
prun (nb_decode_subframe unpackM sm olp sub st b) q = match subframe_pure sm olp sub st b with Some r => Some (r, q) | None => None end.
Proof.
intros sm olp sub st b q. unfold nb_decode_subframe, subframe_pure, hsg_bits. cbv zeta.
destruct (sm_ltp_unquant sm) as [k|]; [| rewrite prun_bind, prun_munr; reflexivity].
rewrite prun_bind, ltp_unquant_prun. cbn beta iota.
rewrite prun_bind.
assert (HS : forall b0 q0, prun (if sm_have_subframe_gain sm =? 3 then ' (_, b1) <- unpackM b0 3;; mret b1
else if sm_have_subframe_gain sm =? 1 then ' (_, b1) <- unpackM b0 1;; mret b1 else mret b0) q0
= Some ((if sm_have_subframe_gain sm =? 3 then ub b0 3 else if sm_have_subframe_gain sm =? 1 then ub b0 1 else b0), q0)).
{ intros b0 q0. destruct (sm_have_subframe_gain sm =? 3); [rewrite prun_bind, prun_unpack; cbn beta iota; apply prun_ret|].
destruct (sm_have_subframe_gain sm =? 1); [rewrite prun_bind, prun_unpack; cbn beta iota; apply prun_ret| apply prun_ret]. }
rewrite HS. cbn beta iota.
destruct (sm_innovation_unquant sm) as [ki|]; [| rewrite prun_bind, prun_munr; reflexivity].
rewrite prun_bind, innovation_unquant_prun. cbn beta iota. rewrite prun_bind.
destruct (negb (sm_double_codebook sm =? 0)).
- rewrite innovation_unquant_prun. cbn beta iota. rewrite prun_bind.
destruct (nb_submodeID st =? 1); [| rewrite prun_ret; cbn beta iota; apply prun_ret].
destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp); [rewrite prun_ret; cbn beta iota; apply prun_ret | rewrite prun_munr; reflexivity].
- rewrite prun_ret. cbn beta iota. rewrite prun_bind.
destruct (nb_submodeID st =? 1); [| rewrite prun_ret; cbn beta iota; apply prun_ret].
destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp); [rewrite prun_ret; cbn beta iota; apply prun_ret | rewrite prun_munr; reflexivity].
Qed.
Lemma subframes_prun : forall n sub sm olp (st : nb_state bptr) (b : bits_st bptr) q,
prun (nb_decode_subframes unpackM n sub sm olp st b) q = match subframes_pure n sub sm olp st b with Some r => Some (r, q) | None => None end.
Proof.
induction n as [|n IH]; intros sub sm olp st b q; cbn [nb_decode_subframes subframes_pure]; [apply prun_ret|].
rewrite prun_bind, subframe_prun. destruct (subframe_pure sm olp sub st b) as [[st1 b1]|]; [| reflexivity]. cbn beta iota. apply IH.
Qed.

Definition nb_rest_pure (st : nb_state bptr) (mo : Z) (b1 : bits_st bptr) : option (Z * nb_state bptr * bits_st bptr) :=
let st1 := set_nb_submodeID st mo in
match submode_at nb_submodes mo with
| None => Some (0, nb_null st1, b1)
| Some sm =>
let bL := lsp_bits (sm_lsp_unquant sm) b1 in
match subframes_pure 4 0 sm (segD_olp sm bL) (segD_st st1 sm bL) (segD_bits st1 sm bL) with
| Some (st2, b2) => Some (0, nb_end st2, b2)
| None => None
end
end.
Definition nb_decode_res (st : nb_state bptr) (b : bits_st bptr) (q : pst) : option ((Z * nb_state bptr * bits_st bptr) * pst) :=
match search_pure (nb_search_fuel b) (nb_stereo_cb st) b with
| SOunr => None
| SOret r b' => Some ((r, st, b'), q)
| SOnotify tw b' => Some ((-2, st, b'), p_app (notify_bytes (if tw then MSG_MORE_THAN_TWO_WB else MSG_INVALID_MODE)) q)
| SOmode mo b1 => match nb_rest_pure st mo b1 with Some r => Some (r, q) | None => None end
end.

Definition nb_decode_res_gen (st : nb_state bptr) (b : bits_st bptr) (q : pst) : option ((Z * nb_state bptr * bits_st bptr) * pst) :=
match (if negb (nb_encode_submode st =? 0) then search_res (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) q else Some (NbMode (nb_submodeID st) b, q)) with
| None => None
| Some (NbReturn r b', q') => Some ((r, st, b'), q')
| Some (NbMode mo b1, q') => match nb_rest_pure st mo b1 with Some r => Some (r, q') | None => None end
end.
Theorem nb_decode_prun_gen : forall (st : nb_state bptr) (b : bits_st bptr) q, prun (NBDEC st b) q = nb_decode_res_gen st b q.
Proof.
intros st b q. unfold nb_decode, nb_decode_res_gen. rewrite prun_bind.
assert (SR : prun (if negb (nb_encode_submode st =? 0) then SEARCH (nb_search_fuel b) st b else mret (NbMode (nb_submodeID st) b)) q
= (if negb (nb_encode_submode st =? 0) then search_res (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) q else Some (NbMode (nb_submodeID st) b, q))).
{ destruct (negb (nb_encode_submode st =? 0)); [apply nb_search_prun | apply prun_ret]. }
rewrite SR. clear SR.
destruct (if negb (nb_encode_submode st =? 0) then search_res (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) q else Some (NbMode (nb_submodeID st) b, q)) as [[[r b'|mo b1] q']|];
cbn beta iota; [apply prun_ret | | reflexivity].
unfold nb_rest_pure. cbv zeta. cbn [nb_submodeID set_nb_submodeID].
destruct (submode_at nb_submodes mo) as [sm|]; [| apply prun_ret].
rewrite prun_bind, lsp_unquant_prun. cbn beta iota. set (bL := lsp_bits (sm_lsp_unquant sm) b1).
unfold segD_olp, segD_st, segD_bits, segD_b3, segD_b2, segD_b1. cbn [nb_submodeID set_nb_submodeID].
destruct (negb (sm_lbr_pitch sm =? -1)); destruct (negb (sm_forced_pitch_gain sm =? 0)); destruct (Z.eqb_spec mo 1) as [-> | NE];
repeat (first [rewrite prun_bind | rewrite prun_unpack | rewrite prun_ret]; cbn beta iota);
cbn [nb_submodeID set_nb_dtx_enabled set_nb_submodeID Z.ltb Z.compare Pos.compare Pos.compare_cont];
unfold NB_PITCH_START; rewrite ?(Z.add_comm 17 (uv bL 7)); rewrite subframes_prun;
match goal with |- context [subframes_pure ?a ?b ?c ?d ?e ?f] => destruct (subframes_pure a b c d e f) as [[st2 b2]|] end;
first [reflexivity | cbn beta iota; rewrite prun_ret; reflexivity].
Qed.
Corollary nb_decode_prun : forall (st : nb_state bptr) (b : bits_st bptr) q, nb_encode_submode st = 1 -> prun (NBDEC st b) q = nb_decode_res st b q.
Proof.
intros st b q ES. rewrite nb_decode_prun_gen. unfold nb_decode_res_gen, nb_decode_res. rewrite ES. cbn [Z.eqb negb].
destruct (search_pure (nb_search_fuel b) (nb_stereo_cb st) b); reflexivity.
Qed.

Lemma dec_nb_prun : forall (st : nb_state bptr) (b : bits_st bptr) out q,
prun (DEC (DecNB st) b out) q = match prun (NBDEC st b) q with Some ((r, st', b'), q') => Some ((r, DecNB st', b'), q') | None => None end.
Proof.
intros. unfold speex_decode. cbn [dec_depth speex_decode_n]. rewrite prun_bind.
destruct (prun (NBDEC st b) q) as [[[[r st'] b'] q']|]; [cbn beta iota; apply prun_ret | reflexivity].
Qed.
Theorem nb_appends : forall st : nb_state bptr, dec_appends (DecNB st).
Proof.
intros st b q r q1 H. rewrite dec_nb_prun, nb_decode_prun_gen in H. unfold nb_decode_res_gen in H.
destruct (negb (nb_encode_submode st =? 0)).
- destruct (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) as [r0 b'|mo b1|tw b'|]; cbn [search_res] in H.
+ injection H as _ <-. exists []. symmetry. apply app_nil_r.
+ destruct (nb_rest_pure st mo b1) as [[[r1 st1] b2]|]; [| discriminate]. injection H as _ <-. exists []. symmetry. apply app_nil_r.
+ injection H as _ <-. eexists. reflexivity.
+ discriminate.
- destruct (nb_rest_pure st (nb_submodeID st) b) as [[[r1 st1] b2]|]; [| discriminate]. injection H as _ <-. exists []. symmetry. apply app_nil_r.
Qed.

Lemma smrec_submode : forall mo, 0 <= mo <= 8 ->
submode_at nb_submodes mo = match smrec_at mo with Some r => Some (smr_sm r) | None => None end.
Proof.
intros mo H. assert (C : mo = 0 \/ mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]; reflexivity.
Qed.
