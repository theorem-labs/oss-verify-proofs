(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X082 X08y X0b1.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yt X0zq X11l.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation unpackM := (@bits_unpack_unsigned_M pst bptr).
Local Notation peekM := (@bits_peek_M pst bptr).
Local Notation advanceM := (@bits_advance_M pst bptr).
Local Notation remainingM := (@bits_remaining_M pst bptr).
Local Notation DEC := (speex_decode (St := pst) p_notify unpackM peekM advanceM remainingM).

Lemma unpack_eta : forall (b : bits_st bptr) n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

Lemma prun_unpack : forall (b : bits_st bptr) n q, prun (unpackM b n) q = Some ((uv b n, ub b n), q).
Proof. intros. unfold bits_unpack_unsigned_M. rewrite prun_ret, unpack_eta. reflexivity. Qed.

Lemma lsp_unquant_prun : forall k (b : bits_st bptr) q, prun (lsp_unquant unpackM k b) q = Some (lsp_bits k b, q).
Proof.
intros k b q. destruct k; cbn [lsp_unquant lsp_bits]; unfold lsp_unquant_lbr, lsp_unquant_nb, lsp_unquant_high;
repeat (rewrite prun_bind, prun_unpack; cbn beta iota); apply prun_ret.
Qed.

Lemma split_cb_read_prun : forall n hs sbits (b : bits_st bptr) q, prun (split_cb_read unpackM n hs sbits b) q = Some (scb_bits n hs sbits b, q).
Proof.
induction n as [|n IH]; intros hs sbits b q; cbn [split_cb_read scb_bits]; [apply prun_ret|].
destruct (negb (hs =? 0)).
- rewrite prun_bind, prun_bind, prun_unpack. cbn beta iota. rewrite prun_ret. cbn beta iota. rewrite prun_bind, prun_unpack. cbn beta iota. apply IH.
- rewrite prun_bind, prun_ret. cbn beta iota. rewrite prun_bind, prun_unpack. cbn beta iota. apply IH.
Qed.

Lemma innovation_unquant_prun : forall k (b : bits_st bptr) q, prun (innovation_unquant unpackM k b) q = Some (innov_bits k b, q).
Proof.
intros [|p] b q; cbn [innovation_unquant innov_bits]; [apply prun_ret|]. unfold split_cb_shape_sign_unquant. apply split_cb_read_prun.
Qed.

Lemma sb_decode_subframe_prun : forall sm (b : bits_st bptr) q, prun (sb_decode_subframe unpackM sm b) q = Some (sbsub_bits sm b, q).
Proof.
intros sm b q. unfold sb_decode_subframe, sbsub_bits. destruct (sm_innovation_unquant sm) as [k|].
- rewrite prun_bind, prun_unpack. cbn beta iota. rewrite prun_bind, innovation_unquant_prun. cbn beta iota.
destruct (negb (sm_double_codebook sm =? 0)); [apply innovation_unquant_prun | apply prun_ret].
- rewrite prun_bind, prun_unpack. cbn beta iota. apply prun_ret.
Qed.
Lemma sb_decode_subframes_prun : forall n sm (b : bits_st bptr) q, prun (sb_decode_subframes unpackM n sm b) q = Some (sbsubs_bits n sm b, q).
Proof.
induction n as [|n IH]; intros sm b q; cbn [sb_decode_subframes sbsubs_bits]; [apply prun_ret|].
rewrite prun_bind, sb_decode_subframe_prun. cbn beta iota. apply IH.
Qed.

Lemma ctl_keeps_depth : forall (d : dec_state bptr) r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof. intros. apply speex_decoder_ctl_depth. Qed.

Definition sb_outcome (s : sbd_state bptr) (low3 : dec_state bptr) (b1 : bits_st bptr) (q1 : pst)
(ret : Z) (d' : dec_state bptr) (b' : bits_st bptr) (q' : pst) : Prop :=
let id := sbw_id b1 in let s1 := set_sbd_submodeID s id in let b2 := sbw_bits b1 in
match submode_at (sbm_submodes (sbd_mode s)) id with
| None => if id =? 0 then ret = 0 /\ d' = DecSB (set_sbd_first s1 1) low3 /\ b' = b2 /\ q' = q1
else ret = -2 /\ d' = DecSB s1 low3 /\ b' = b2 /\ q' = p_app (notify_bytes MSG_INVALID_MODE) q1
| Some sm => let low5 := snd (speex_decoder_ctl (snd (speex_decoder_ctl low3 CtlGetPiGain)) CtlGetExc) in
ret = 0 /\ d' = DecSB (set_sbd_first s1 0) low5
/\ b' = sbsubs_bits (Z.to_nat (sbd_nbSubframes s)) sm (lsp_bits (sm_lsp_unquant sm) b2) /\ q' = q1
end.

Theorem sb_decode_prun : forall (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) q ret d' b' q',
sbd_encode_submode s = 1 ->
prun (DEC (DecSB s low) b 0) q = Some ((ret, d', b'), q') ->
let low1 := snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) in
exists retl low2 b1 q1,
prun (DEC low1 b 0) q = Some ((retl, low2, b1), q1)
/\ let low3 := snd (speex_decoder_ctl low2 CtlGetDtxStatus) in
(retl <> 0 -> ret = retl /\ d' = DecSB s low3 /\ b' = b1 /\ q' = q1)
/\ (retl = 0 -> sb_outcome s low3 b1 q1 ret d' b' q').
Proof.
intros s low b q ret d' b' q' ES H. cbv zeta.
unfold speex_decode in H. cbn [dec_depth speex_decode_n] in H.
rewrite prun_bind in H. unfold sb_decode in H.
destruct (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) as [v1 low1] eqn:E1. cbn [snd].
assert (D1 : dec_depth low1 = dec_depth low) by (pose proof (ctl_keeps_depth low (CtlSetInnovationSave (0 + sbd_frame_size s))) as X; rewrite E1 in X; exact X).
rewrite prun_bind in H.
destruct (prun (speex_decode_n p_notify unpackM peekM advanceM remainingM (dec_depth low) low1 b 0) q) as [[[[retl low2] b1] q1]|] eqn:EL; [| discriminate H].
exists retl, low2, b1, q1. split; [unfold speex_decode; rewrite D1; exact EL|].
cbn beta iota in H.
destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3] eqn:E3. cbn [snd].
split.
- intros NZ. replace (negb (retl =? 0)) with true in H by (symmetry; apply negb_true_iff, Z.eqb_neq; exact NZ).
rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
- intros ->. cbn [Z.eqb negb] in H. rewrite ES in H. cbn [Z.eqb negb] in H.
unfold sb_outcome. cbv zeta.
rewrite !prun_bind in H. unfold bits_remaining_M at 1 in H. rewrite prun_ret in H. cbn beta iota in H.
rewrite prun_bind in H.
assert (EW : prun (if 0 <? speex_bits_remaining b1 then peekM b1 else mret (0, b1)) q1 = Some (sbw_wb b1, q1)).
{ unfold sbw_wb. destruct (0 <? speex_bits_remaining b1); [unfold bits_peek_M|]; apply prun_ret. }
rewrite EW in H. cbn beta iota in H. clear EW.
unfold sbw_id, sbw_bits. unfold X1rh.SB_SUBMODE_BITS, X11l.SB_SUBMODE_BITS in *. destruct (sbw_wb b1) as [wb bw]. cbn beta iota in H.
rewrite prun_bind in H.
destruct (negb (wb =? 0)).
+ rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H.
set (id := uv (ub bw 1) 3) in *. set (b2 := ub (ub bw 1) 3) in *.
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
destruct (submode_at (sbm_submodes (sbd_mode s)) id) as [sm|] eqn:ESM.
* rewrite andb_false_r in H. rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
rewrite ESM in H.
destruct (speex_decoder_ctl low3 CtlGetPiGain) as [v4 low4]. cbn [snd]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5]. cbn [snd].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H.
replace (sbd_nbSubframes (set_sbd_submodeID s id)) with (sbd_nbSubframes s) in H by (destruct s; reflexivity).
injection H as <- <- <- <-. repeat split; reflexivity.
* rewrite andb_true_r in H. destruct (id =? 0) eqn:EID; cbn [negb] in H.
-- rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
rewrite ESM in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
-- rewrite prun_bind, prun_notify in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H.
injection H as <- <- <- <-. repeat split; reflexivity.
+ rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_submodeID (set_sbd_submodeID s 0)) with 0 in H by (destruct s; reflexivity).
cbn [Z.eqb negb andb] in H. rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s 0)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s 0)) with 0 in H by (destruct s; reflexivity).
assert (E0 : submode_at (sbm_submodes (sbd_mode s)) 0 = None) by (destruct (sbd_mode s); reflexivity).
rewrite E0 in H |- *. cbn [Z.eqb]. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
Qed.

Definition dec_appends (d : dec_state bptr) : Prop :=
forall b q r q1, prun (DEC d b 0) q = Some (r, q1) -> exists bs, p_err q1 = p_err q ++ bs.
Lemma sb_appends : forall (s : sbd_state bptr) (low : dec_state bptr), sbd_encode_submode s = 1 ->
(forall low', dec_depth low' = dec_depth low -> dec_appends low') -> dec_appends (DecSB s low).
Proof.
intros s low ES IH b q [[ret d'] b'] q' H.
destruct (sb_decode_prun s low b q ret d' b' q' ES H) as (retl & low2 & b1 & q1 & PRL & PNZ & PZ).
destruct (IH _ (ctl_keeps_depth low _) b q _ q1 PRL) as (bsl & E1).
destruct (Z.eq_dec retl 0) as [E|NE].
- specialize (PZ E). unfold sb_outcome in PZ. cbv zeta in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1)) as [sm|].
+ destruct PZ as (_ & _ & _ & ->). exists bsl. exact E1.
+ destruct (sbw_id b1 =? 0).
* destruct PZ as (_ & _ & _ & ->). exists bsl. exact E1.
* destruct PZ as (_ & _ & _ & ->). exists (bsl ++ notify_bytes MSG_INVALID_MODE). unfold p_app. cbn [p_err]. rewrite E1, app_assoc. reflexivity.
- destruct (PNZ NE) as (_ & _ & _ & ->). exists bsl. exact E1.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation unpackM := (@bits_unpack_unsigned_M pst bptr).
Local Notation peekM := (@bits_peek_M pst bptr).
Local Notation advanceM := (@bits_advance_M pst bptr).
Local Notation remainingM := (@bits_remaining_M pst bptr).
Local Notation DEC := (speex_decode (St := pst) p_notify unpackM peekM advanceM remainingM).

Lemma unpack_eta : forall (b : bits_st bptr) n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

Lemma prun_unpack : forall (b : bits_st bptr) n q, prun (unpackM b n) q = Some ((uv b n, ub b n), q).
Proof. intros. unfold bits_unpack_unsigned_M. rewrite prun_ret, unpack_eta. reflexivity. Qed.

Lemma lsp_unquant_prun : forall k (b : bits_st bptr) q, prun (lsp_unquant unpackM k b) q = Some (lsp_bits k b, q).
Proof.
intros k b q. destruct k; cbn [lsp_unquant lsp_bits]; unfold lsp_unquant_lbr, lsp_unquant_nb, lsp_unquant_high;
repeat (rewrite prun_bind, prun_unpack; cbn beta iota); apply prun_ret.
Qed.

Lemma split_cb_read_prun : forall n hs sbits (b : bits_st bptr) q, prun (split_cb_read unpackM n hs sbits b) q = Some (scb_bits n hs sbits b, q).
Proof.
induction n as [|n IH]; intros hs sbits b q; cbn [split_cb_read scb_bits]; [apply prun_ret|].
destruct (negb (hs =? 0)).
- rewrite prun_bind, prun_bind, prun_unpack. cbn beta iota. rewrite prun_ret. cbn beta iota. rewrite prun_bind, prun_unpack. cbn beta iota. apply IH.
- rewrite prun_bind, prun_ret. cbn beta iota. rewrite prun_bind, prun_unpack. cbn beta iota. apply IH.
Qed.

Lemma innovation_unquant_prun : forall k (b : bits_st bptr) q, prun (innovation_unquant unpackM k b) q = Some (innov_bits k b, q).
Proof.
intros [|p] b q; cbn [innovation_unquant innov_bits]; [apply prun_ret|]. unfold split_cb_shape_sign_unquant. apply split_cb_read_prun.
Qed.

Lemma sb_decode_subframe_prun : forall sm (b : bits_st bptr) q, prun (sb_decode_subframe unpackM sm b) q = Some (sbsub_bits sm b, q).
Proof.
intros sm b q. unfold sb_decode_subframe, sbsub_bits. destruct (sm_innovation_unquant sm) as [k|].
- rewrite prun_bind, prun_unpack. cbn beta iota. rewrite prun_bind, innovation_unquant_prun. cbn beta iota.
destruct (negb (sm_double_codebook sm =? 0)); [apply innovation_unquant_prun | apply prun_ret].
- rewrite prun_bind, prun_unpack. cbn beta iota. apply prun_ret.
Qed.
Lemma sb_decode_subframes_prun : forall n sm (b : bits_st bptr) q, prun (sb_decode_subframes unpackM n sm b) q = Some (sbsubs_bits n sm b, q).
Proof.
induction n as [|n IH]; intros sm b q; cbn [sb_decode_subframes sbsubs_bits]; [apply prun_ret|].
rewrite prun_bind, sb_decode_subframe_prun. cbn beta iota. apply IH.
Qed.

Lemma ctl_keeps_depth : forall (d : dec_state bptr) r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof. intros. apply speex_decoder_ctl_depth. Qed.

Definition sb_outcome (s : sbd_state bptr) (low3 : dec_state bptr) (b1 : bits_st bptr) (q1 : pst)
(ret : Z) (d' : dec_state bptr) (b' : bits_st bptr) (q' : pst) : Prop :=
let id := sbw_id b1 in let s1 := set_sbd_submodeID s id in let b2 := sbw_bits b1 in
match submode_at (sbm_submodes (sbd_mode s)) id with
| None => if id =? 0 then ret = 0 /\ d' = DecSB (set_sbd_first s1 1) low3 /\ b' = b2 /\ q' = q1
else ret = -2 /\ d' = DecSB s1 low3 /\ b' = b2 /\ q' = p_app (notify_bytes MSG_INVALID_MODE) q1
| Some sm => let low5 := snd (speex_decoder_ctl (snd (speex_decoder_ctl low3 CtlGetPiGain)) CtlGetExc) in
ret = 0 /\ d' = DecSB (set_sbd_first s1 0) low5
/\ b' = sbsubs_bits (Z.to_nat (sbd_nbSubframes s)) sm (lsp_bits (sm_lsp_unquant sm) b2) /\ q' = q1
end.

Theorem sb_decode_prun : forall (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) q ret d' b' q',
sbd_encode_submode s = 1 ->
prun (DEC (DecSB s low) b 0) q = Some ((ret, d', b'), q') ->
let low1 := snd (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) in
exists retl low2 b1 q1,
prun (DEC low1 b 0) q = Some ((retl, low2, b1), q1)
/\ let low3 := snd (speex_decoder_ctl low2 CtlGetDtxStatus) in
(retl <> 0 -> ret = retl /\ d' = DecSB s low3 /\ b' = b1 /\ q' = q1)
/\ (retl = 0 -> sb_outcome s low3 b1 q1 ret d' b' q').
Proof.
intros s low b q ret d' b' q' ES H. cbv zeta.
unfold speex_decode in H. cbn [dec_depth speex_decode_n] in H.
rewrite prun_bind in H. unfold sb_decode in H.
destruct (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) as [v1 low1] eqn:E1. cbn [snd].
assert (D1 : dec_depth low1 = dec_depth low) by (pose proof (ctl_keeps_depth low (CtlSetInnovationSave (0 + sbd_frame_size s))) as X; rewrite E1 in X; exact X).
rewrite prun_bind in H.
destruct (prun (speex_decode_n p_notify unpackM peekM advanceM remainingM (dec_depth low) low1 b 0) q) as [[[[retl low2] b1] q1]|] eqn:EL; [| discriminate H].
exists retl, low2, b1, q1. split; [unfold speex_decode; rewrite D1; exact EL|].
cbn beta iota in H.
destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3] eqn:E3. cbn [snd].
split.
- intros NZ. replace (negb (retl =? 0)) with true in H by (symmetry; apply negb_true_iff, Z.eqb_neq; exact NZ).
rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
- intros ->. cbn [Z.eqb negb] in H. rewrite ES in H. cbn [Z.eqb negb] in H.
unfold sb_outcome. cbv zeta.
rewrite !prun_bind in H. unfold bits_remaining_M at 1 in H. rewrite prun_ret in H. cbn beta iota in H.
rewrite prun_bind in H.
assert (EW : prun (if 0 <? speex_bits_remaining b1 then peekM b1 else mret (0, b1)) q1 = Some (sbw_wb b1, q1)).
{ unfold sbw_wb. destruct (0 <? speex_bits_remaining b1); [unfold bits_peek_M|]; apply prun_ret. }
rewrite EW in H. cbn beta iota in H. clear EW.
unfold sbw_id, sbw_bits. unfold X1rh.SB_SUBMODE_BITS, X0b1.SB_SUBMODE_BITS in *. destruct (sbw_wb b1) as [wb bw]. cbn beta iota in H.
rewrite prun_bind in H.
destruct (negb (wb =? 0)).
+ rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H.
set (id := uv (ub bw 1) 3) in *. set (b2 := ub (ub bw 1) 3) in *.
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
destruct (submode_at (sbm_submodes (sbd_mode s)) id) as [sm|] eqn:ESM.
* rewrite andb_false_r in H. rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
rewrite ESM in H.
destruct (speex_decoder_ctl low3 CtlGetPiGain) as [v4 low4]. cbn [snd]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5]. cbn [snd].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H.
replace (sbd_nbSubframes (set_sbd_submodeID s id)) with (sbd_nbSubframes s) in H by (destruct s; reflexivity).
injection H as <- <- <- <-. repeat split; reflexivity.
* rewrite andb_true_r in H. destruct (id =? 0) eqn:EID; cbn [negb] in H.
-- rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s id)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s id)) with id in H by (destruct s; reflexivity).
rewrite ESM in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
-- rewrite prun_bind, prun_notify in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H.
injection H as <- <- <- <-. repeat split; reflexivity.
+ rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_submodeID (set_sbd_submodeID s 0)) with 0 in H by (destruct s; reflexivity).
cbn [Z.eqb negb andb] in H. rewrite prun_ret in H. cbn beta iota in H.
replace (sbd_mode (set_sbd_submodeID s 0)) with (sbd_mode s) in H by (destruct s; reflexivity).
replace (sbd_submodeID (set_sbd_submodeID s 0)) with 0 in H by (destruct s; reflexivity).
assert (E0 : submode_at (sbm_submodes (sbd_mode s)) 0 = None) by (destruct (sbd_mode s); reflexivity).
rewrite E0 in H |- *. cbn [Z.eqb]. rewrite prun_ret in H. cbn beta iota in H. rewrite prun_ret in H. injection H as <- <- <- <-. repeat split; reflexivity.
Qed.

Definition dec_appends (d : dec_state bptr) : Prop :=
forall b q r q1, prun (DEC d b 0) q = Some (r, q1) -> exists bs, p_err q1 = p_err q ++ bs.
Lemma sb_appends : forall (s : sbd_state bptr) (low : dec_state bptr), sbd_encode_submode s = 1 ->
(forall low', dec_depth low' = dec_depth low -> dec_appends low') -> dec_appends (DecSB s low).
Proof.
intros s low ES IH b q [[ret d'] b'] q' H.
destruct (sb_decode_prun s low b q ret d' b' q' ES H) as (retl & low2 & b1 & q1 & PRL & PNZ & PZ).
destruct (IH _ (ctl_keeps_depth low _) b q _ q1 PRL) as (bsl & E1).
destruct (Z.eq_dec retl 0) as [E|NE].
- specialize (PZ E). unfold sb_outcome in PZ. cbv zeta in PZ.
destruct (submode_at (sbm_submodes (sbd_mode s)) (sbw_id b1)) as [sm|].
+ destruct PZ as (_ & _ & _ & ->). exists bsl. exact E1.
+ destruct (sbw_id b1 =? 0).
* destruct PZ as (_ & _ & _ & ->). exists bsl. exact E1.
* destruct PZ as (_ & _ & _ & ->). exists (bsl ++ notify_bytes MSG_INVALID_MODE). unfold p_app. cbn [p_err]. rewrite E1, app_assoc. reflexivity.
- destruct (PNZ NE) as (_ & _ & _ & ->). exists bsl. exact E1.
Qed.
