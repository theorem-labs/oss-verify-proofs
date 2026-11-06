(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X082 X06n X08y.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Model.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition skip_bits b : bits_st ptr :=
speex_bits_advance (ub b SB_SUBMODE_BITS) (znth wb_skip_table (uv b SB_SUBMODE_BITS) - (SB_SUBMODE_BITS + 1)).

Lemma ub_size : forall b n, sb_buf_size (ub b n) = sb_buf_size b.
Proof. intros. unfold ub, speex_bits_unpack_unsigned. destruct (_ || _); reflexivity. Qed.
Lemma adv_size : forall b n, sb_buf_size (speex_bits_advance b n) = sb_buf_size b.
Proof. intros. unfold speex_bits_advance. destruct (_ || _); reflexivity. Qed.
Lemma ub_exact : forall b n, bits_ok b -> 0 <= n -> n <= speex_bits_remaining b ->
sb_overflow (ub b n) = 0 /\ bits_pos (ub b n) = bits_pos b + n /\ sb_nbBits (ub b n) = sb_nbBits b /\
speex_bits_remaining (ub b n) = speex_bits_remaining b - n.
Proof.
intros b n OK Hn Hr. unfold ub, speex_bits_unpack_unsigned, speex_bits_remaining in *.
unfold bits_ok, bits_pos in OK.
destruct (Z.eqb_spec (sb_overflow b) 0) as [E|E]; cbn [negb] in Hr |- *; [|lia].
destruct (Z.ltb_spec (sb_nbBits b) (bits_pos b + n)) as [L|L]; cbn [orb].
- exfalso. unfold bits_pos in *. lia.
- unfold set_pos, bits_pos; cbn [sb_overflow sb_charPtr sb_bitPtr sb_nbBits fst snd]. rewrite E. cbn [Z.eqb negb].
pose proof (Z.div_mod (sb_charPtr b * 8 + sb_bitPtr b + n) 8 ltac:(lia)). lia.
Qed.

Inductive search_out : Type :=
| SOret (r : Z) (b : bits_st ptr)
| SOmode (m : Z) (b : bits_st ptr)
| SOnotify (two_wb : bool) (b : bits_st ptr)
| SOunr.
Fixpoint search_pure (fuel : nat) (sc : bool) b : search_out :=
match fuel with
| O => SOunr
| S fuel' =>
if speex_bits_remaining b <? 5 then SOret (-1) b else
let w1 := uv b 1 in let b1 := ub b 1 in
match (if negb (w1 =? 0) then
let b2 := skip_bits b1 in
if speex_bits_remaining b2 <? 5 then inr (SOret (-1) b2) else
let w2 := uv b2 1 in let b3 := ub b2 1 in
if negb (w2 =? 0) then
let b4 := skip_bits b3 in
let w3 := uv b4 1 in let b5 := ub b4 1 in
if negb (w3 =? 0) then inr (SOnotify true b5) else inl b5
else inl b3
else inl b1) with
| inr o => o
| inl bm =>
if speex_bits_remaining bm <? 4 then SOret (-1) bm else
let m := uv bm 4 in let b6 := ub bm 4 in
if m =? 15 then SOret (-1) b6
else if m =? 14 then search_pure fuel' sc (inband_bits sc b6)
else if m =? 13 then search_pure fuel' sc (user_handler_bits b6)
else if 8 <? m then SOnotify false b6
else SOmode m b6
end
end.

Definition hsg_bits (sm : submode) b : bits_st ptr :=
if sm_have_subframe_gain sm =? 3 then ub b 3 else if sm_have_subframe_gain sm =? 1 then ub b 1 else b.
Definition subframe_pure (sm : submode) (olp sub : Z) (st : nb_state ptr) b : option (nb_state ptr * bits_st ptr) :=
match sm_ltp_unquant sm, sm_innovation_unquant sm with
| Some k, Some ki =>
let b1 := ltp_bits k b in
let b2 := hsg_bits sm b1 in
let b3 := innov_bits ki b2 in
let b4 := if negb (sm_double_codebook sm =? 0) then innov_bits ki b3 else b3 in
if nb_submodeID st =? 1 then
match voc_loop VOC_FUEL (nb_voc_offset st) olp with
| Some v => Some (set_nb_voc_offset st (v - NB_SUBFRAME_SIZE), b4)
| None => None
end
else Some (st, b4)
| _, _ => None
end.
Fixpoint subframes_pure (n : nat) (sub : Z) (sm : submode) (olp : Z) (st : nb_state ptr) b : option (nb_state ptr * bits_st ptr) :=
match n with
| O => Some (st, b)
| S n' => match subframe_pure sm olp sub st b with
| Some (st1, b1) => subframes_pure n' (sub + 1) sm olp st1 b1
| None => None
end
end.

Definition nb_end (st : nb_state ptr) : nb_state ptr :=
let idx := nb_pitch_gain_buf_idx st + 1 in
set_nb_pitch_gain_buf_idx (set_nb_count_lost (set_nb_first st 0) 0) (if 2 <? idx then 0 else idx).
Definition nb_null (st : nb_state ptr) : nb_state ptr := set_nb_count_lost (set_nb_first st 1) 0.
End Model.
