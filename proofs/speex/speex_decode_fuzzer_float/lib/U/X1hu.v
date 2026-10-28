(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Section Model.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Variable spx_notify : list Z -> M St unit.
Local Notation unpackM := (@bits_unpack_unsigned_M St ptr).
Local Notation advanceM := (@bits_advance_M St ptr).
Local Notation remainingM := (@bits_remaining_M St ptr).
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_eta : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. apply surjective_pairing. Qed.

Ltac mrun := unfold mbind, mret; cbn [fst snd];
repeat (first [ rewrite ebind_ret_ok | rewrite unpack_eta ]; cbn [fst snd]).

#[using="Type"] Lemma ub_size : forall b n, sb_buf_size (ub b n) = sb_buf_size b.
Proof. intros. unfold ub, speex_bits_unpack_unsigned. destruct (_ || _); reflexivity. Qed.
#[using="Type"] Lemma adv_size : forall b n, sb_buf_size (speex_bits_advance b n) = sb_buf_size b.
Proof. intros. unfold speex_bits_advance. destruct (_ || _); reflexivity. Qed.
#[using="Type"] Lemma user_handler_bits_size : forall b, sb_buf_size (user_handler_bits b) = sb_buf_size b.
Proof. intros. unfold user_handler_bits. rewrite adv_size, ub_size. reflexivity. Qed.
#[using="Type"] Lemma inband_bits_size : forall sc b, sb_buf_size (inband_bits sc b) = sb_buf_size b.
Proof.
intros. unfold inband_bits, stereo_handler_bits. cbv zeta.
destruct (_ && _); rewrite ?adv_size, ?ub_size; reflexivity.
Qed.
#[using="Type"] Lemma lsp_bits_size : forall k b, sb_buf_size (lsp_bits k b) = sb_buf_size b.
Proof. intros. destruct k; cbn [lsp_bits]; rewrite !ub_size; reflexivity. Qed.
#[using="Type"] Lemma ltp_bits_size : forall k b, sb_buf_size (ltp_bits k b) = sb_buf_size b.
Proof. intros. destruct k; cbn [ltp_bits]; unfold ltp3_bits; rewrite ?ub_size; reflexivity. Qed.
#[using="Type"] Lemma scb_bits_size : forall n hs sb b, sb_buf_size (scb_bits n hs sb b) = sb_buf_size b.
Proof.
induction n; intros; cbn [scb_bits]; [reflexivity|].
rewrite IHn, ub_size. destruct (negb _); rewrite ?ub_size; reflexivity.
Qed.
#[using="Type"] Lemma innov_bits_size : forall k b, sb_buf_size (innov_bits k b) = sb_buf_size b.
Proof. intros. destruct k; cbn [innov_bits]; [reflexivity| apply scb_bits_size]. Qed.

#[using="Type"] Lemma ub_exact : forall b n, bits_ok b -> 0 <= n -> n <= speex_bits_remaining b ->
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
#[using="Type"] Lemma remaining_pos : forall b, bits_ok b -> 0 <= speex_bits_remaining b ->
sb_overflow b = 0 /\ speex_bits_remaining b = sb_nbBits b - bits_pos b.
Proof.
intros b OK H. unfold speex_bits_remaining in *. unfold bits_ok in OK.
destruct (Z.eqb_spec (sb_overflow b) 0); cbn [negb] in H |- *; lia.
Qed.

Definition nbs_skip b : M St (bits_st ptr) :=
nb_skip_wb_layer unpackM advanceM b.
Definition nbs_tail (fuel : nat) (st : nb_state ptr) b : M St nb_search_res :=
rem <- remainingM b ;;
if rem <? 4 then mret (NbReturn (-1) b) else
' (m, b) <- unpackM b 4 ;;
if m =? 15 then mret (NbReturn (-1) b)
else if m =? 14 then
' (ret, b) <- speex_inband_handler unpackM advanceM b (nb_stereo_cb st) ;;
if negb (ret =? 0) then mret (NbReturn ret b) else nb_mode_search spx_notify unpackM advanceM remainingM fuel st b
else if m =? 13 then
' (ret, b) <- speex_default_user_handler unpackM advanceM b ;;
if negb (ret =? 0) then mret (NbReturn ret b) else nb_mode_search spx_notify unpackM advanceM remainingM fuel st b
else if 8 <? m then
spx_notify MSG_INVALID_MODE ;;; mret (NbReturn (-2) b)
else mret (NbMode m b).
Definition nbs_wb (wideband : Z) b : M St (bits_st ptr + nb_search_res) :=
if negb (wideband =? 0) then
b <- nbs_skip b ;;
rem <- remainingM b ;;
if rem <? 5 then mret (inr (NbReturn (-1) b)) else
' (wideband, b) <- unpackM b 1 ;;
if negb (wideband =? 0) then
b <- nbs_skip b ;;
' (wideband, b) <- unpackM b 1 ;;
if negb (wideband =? 0) then
spx_notify MSG_MORE_THAN_TWO_WB ;;; mret (inr (NbReturn (-2) b))
else mret (inl b)
else mret (inl b)
else mret (inl b).

#[using="Type"] Lemma nb_mode_search_S : forall fuel st b,
nb_mode_search spx_notify unpackM advanceM remainingM (S fuel) st b =
(rem <- remainingM b ;;
if rem <? 5 then mret (NbReturn (-1) b) else
' (wideband, b) <- unpackM b 1 ;;
wb <- nbs_wb wideband b ;;
match wb with
| inr res => mret res
| inl b => nbs_tail fuel st b
end).
Proof. intros. reflexivity. Qed.

Definition skip_bits b : bits_st ptr :=
speex_bits_advance (ub b SB_SUBMODE_BITS) (znth wb_skip_table (uv b SB_SUBMODE_BITS) - (SB_SUBMODE_BITS + 1)).
#[using="Type"] Lemma skip_bits_size : forall b, sb_buf_size (skip_bits b) = sb_buf_size b.
Proof. intros. unfold skip_bits. rewrite adv_size, ub_size. reflexivity. Qed.
#[using="Type"] Lemma nbs_skip_run : forall b s, nbs_skip b s = Ret (Ok (skip_bits b, s)).
Proof.
intros b s. unfold nbs_skip, nb_skip_wb_layer, bits_unpack_unsigned_M, bits_advance_M, skip_bits. mrun. reflexivity.
Qed.

#[using="Type"] Lemma user_handler_run : forall b s,
speex_default_user_handler unpackM advanceM b s = Ret (Ok ((0, user_handler_bits b), s)).
Proof.
intros b s. unfold speex_default_user_handler, bits_unpack_unsigned_M, bits_advance_M, user_handler_bits. mrun. reflexivity.
Qed.
#[using="Type"] Lemma stereo_handler_run : forall b s,
speex_std_stereo_request_handler unpackM b s = Ret (Ok ((0, stereo_handler_bits b), s)).
Proof.
intros b s. unfold speex_std_stereo_request_handler, bits_unpack_unsigned_M, stereo_handler_bits. mrun. reflexivity.
Qed.
#[using="Type"] Lemma inband_run : forall b sc s,
speex_inband_handler unpackM advanceM b sc s = Ret (Ok ((0, inband_bits sc b), s)).
Proof.
intros b sc s. unfold speex_inband_handler, bits_unpack_unsigned_M, bits_advance_M, inband_bits.
unfold mbind at 1. unfold mret at 1. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
destruct (sc && (uv b 4 =? SPEEX_INBAND_STEREO)); [apply stereo_handler_run| mrun; reflexivity].
Qed.
#[using="Type"] Lemma lsp_unquant_run : forall k b s, lsp_unquant unpackM k b s = Ret (Ok (lsp_bits k b, s)).
Proof.
intros k b s. destruct k; unfold lsp_unquant, lsp_unquant_lbr, lsp_unquant_nb, lsp_unquant_high, bits_unpack_unsigned_M, lsp_bits; mrun; reflexivity.
Qed.
#[using="Type"] Lemma ltp_unquant_run : forall k start b s,
ltp_unquant unpackM k start b s = Ret (Ok ((ltp_pitch k start b, ltp_bits k b), s)).
Proof.
intros k start b s. destruct k as [|p]; unfold ltp_unquant, forced_pitch_unquant, pitch_unquant_3tap, bits_unpack_unsigned_M,
ltp_pitch, ltp_bits, ltp3_pitch, ltp3_bits; mrun; reflexivity.
Qed.
#[using="Type"] Lemma split_cb_read_run : forall n hs sb b s,
split_cb_read unpackM n hs sb b s = Ret (Ok (scb_bits n hs sb b, s)).
Proof.
induction n as [|n IH]; intros hs sb b s; [reflexivity|].
cbn [split_cb_read scb_bits]. unfold bits_unpack_unsigned_M.
destruct (negb (hs =? 0)); mrun; apply IH.
Qed.
#[using="Type"] Lemma innovation_unquant_run : forall k b s,
innovation_unquant unpackM k b s = Ret (Ok (innov_bits k b, s)).
Proof.
intros k b s. destruct k as [|p]; unfold innovation_unquant, noise_codebook_unquant, split_cb_shape_sign_unquant, innov_bits.
- reflexivity.
- apply split_cb_read_run.
Qed.

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
#[using="Type"] Lemma nb_decode_subframe_run : forall sm olp sub st b s,
sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
nb_decode_subframe unpackM sm olp sub st b s =
match subframe_pure sm olp sub st b with Some p => Ret (Ok (p, s)) | None => Ret Unr end.
Proof.
intros sm olp sub st b s HK HI. unfold nb_decode_subframe, subframe_pure, hsg_bits.
destruct (sm_ltp_unquant sm) as [k|]; [|congruence]. destruct (sm_innovation_unquant sm) as [ki|]; [|congruence].
unfold mbind at 1. rewrite ltp_unquant_run, ebind_ret_ok. cbn [fst snd].
assert (HS : forall b', (if sm_have_subframe_gain sm =? 3 then ' (_, b0) <- unpackM b' 3;; mret b0
else if sm_have_subframe_gain sm =? 1 then ' (_, b0) <- unpackM b' 1;; mret b0 else mret b') s
= Ret (Ok ((if sm_have_subframe_gain sm =? 3 then ub b' 3 else if sm_have_subframe_gain sm =? 1 then ub b' 1 else b'), s))).
{ intros b'. unfold bits_unpack_unsigned_M. destruct (_ =? 3); [mrun; reflexivity|]. destruct (_ =? 1); [mrun; reflexivity| reflexivity]. }
unfold mbind at 1. rewrite HS, ebind_ret_ok. cbn [fst snd].
unfold mbind at 1. rewrite innovation_unquant_run, ebind_ret_ok. cbn [fst snd].
unfold mbind at 1.
assert (HD : forall b', (if negb (sm_double_codebook sm =? 0) then innovation_unquant unpackM ki b' else mret b') s
= Ret (Ok ((if negb (sm_double_codebook sm =? 0) then innov_bits ki b' else b'), s))).
{ intros b'. destruct (negb _); [apply innovation_unquant_run| reflexivity]. }
rewrite HD, ebind_ret_ok. cbn [fst snd].
unfold mbind at 1. destruct (nb_submodeID st =? 1).
- destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp); [| reflexivity]. unfold mret at 1. rewrite ebind_ret_ok. reflexivity.
- unfold mret at 1. rewrite ebind_ret_ok. reflexivity.
Qed.
#[using="Type"] Lemma nb_decode_subframes_run : forall n sub sm olp st b s,
sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
nb_decode_subframes unpackM n sub sm olp st b s =
match subframes_pure n sub sm olp st b with Some p => Ret (Ok (p, s)) | None => Ret Unr end.
Proof.
induction n as [|n IH]; intros sub sm olp st b s HK HI; [reflexivity|].
cbn [nb_decode_subframes subframes_pure]. unfold mbind at 1. rewrite nb_decode_subframe_run by assumption.
destruct (subframe_pure sm olp sub st b) as [[st1 b1]|].
- rewrite ebind_ret_ok. cbn [fst snd]. apply IH; assumption.
- rewrite ebind_ret_unr. reflexivity.
Qed.

Definition nb_end (st : nb_state ptr) : nb_state ptr :=
let idx := nb_pitch_gain_buf_idx st + 1 in
set_nb_pitch_gain_buf_idx (set_nb_count_lost (set_nb_first st 0) 0) (if 2 <? idx then 0 else idx).
Definition nb_null (st : nb_state ptr) : nb_state ptr := set_nb_count_lost (set_nb_first st 1) 0.

#[using="Type"] Lemma implM_eqM : forall {X} (c c' : M St X) s Q ms,
c s = c' s -> implM rsegs c' s Q ms -> implM rsegs c s Q ms.
Proof. intros X c c' s Q ms E H. unfold implM in *. rewrite E. exact H. Qed.
#[using="Type"] Lemma implM_retb : forall {X Y} (a : X) (f : X -> M St Y) s Q ms,
implM rsegs (f a) s Q ms -> implM rsegs (mbind (mret a) f) s Q ms.
Proof. intros X Y a f s Q ms H. unfold implM, mbind, mret in *. cbn. exact H. Qed.

#[using="Type"] Lemma implM_bind_run : forall {X Y} (c : M St X) (v : X) (f : X -> M St Y) s Q ms,
c s = Ret (Ok (v, s)) -> implM rsegs (f v) s Q ms -> implM rsegs (mbind c f) s Q ms.
Proof. intros X Y c v f s Q ms E H. unfold implM, mbind in *. rewrite E. cbn. exact H. Qed.
End Model.
