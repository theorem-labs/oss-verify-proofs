(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X082 X08y X0b1 X0bf X093.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation unpackM := (@bits_unpack_unsigned_M pst bptr).
Local Notation peekM := (@bits_peek_M pst bptr).
Local Notation advanceM := (@bits_advance_M pst bptr).
Local Notation remainingM := (@bits_remaining_M pst bptr).
Local Notation DEC := (speex_decode (St := pst) p_notify unpackM peekM advanceM remainingM).

Lemma sb_appends_gen : forall (s : sbd_state bptr) (low : dec_state bptr),
(forall low', dec_depth low' = dec_depth low -> dec_appends low') -> dec_appends (DecSB s low).
Proof.
intros s low IH b q [[ret d'] b'] q' H.
destruct (Z.eq_dec (sbd_encode_submode s) 1) as [ES|NES]; [exact (sb_appends s low ES IH b q _ q' H)|].
unfold speex_decode in H. cbn [dec_depth speex_decode_n] in H.
rewrite prun_bind in H. unfold sb_decode in H.
destruct (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) as [v1 low1] eqn:E1.
assert (D1 : dec_depth low1 = dec_depth low)
by (pose proof (ctl_keeps_depth low (CtlSetInnovationSave (0 + sbd_frame_size s))) as X; rewrite E1 in X; exact X).
rewrite prun_bind in H.
destruct (prun (speex_decode_n p_notify unpackM peekM advanceM remainingM (dec_depth low) low1 b 0) q) as [[[[retl low2] b1] q1]|] eqn:EL; [| discriminate H].
destruct (IH low1 D1 b q _ q1 ltac:(unfold speex_decode; rewrite D1; exact EL)) as (bsl & EB).
cbn beta iota in H.
destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3].
destruct (negb (retl =? 0)).
{ repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB. }
rewrite !prun_bind in H.
destruct (negb (sbd_encode_submode s =? 0)).
- rewrite !prun_bind in H. unfold bits_remaining_M at 1 in H. rewrite prun_ret in H. cbn beta iota in H.
rewrite prun_bind in H.
assert (EW : prun (if 0 <? speex_bits_remaining b1 then peekM b1 else mret (0, b1)) q1 = Some (sbw_wb b1, q1)).
{ unfold sbw_wb. destruct (0 <? speex_bits_remaining b1); [unfold bits_peek_M|]; apply prun_ret. }
rewrite EW in H. cbn beta iota in H. clear EW.
destruct (sbw_wb b1) as [wb bw]. cbn beta iota in H.
rewrite prun_bind in H.
destruct (negb (wb =? 0)).
+ rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_bind, prun_unpack in H. cbn beta iota in H. rewrite prun_ret in H. cbn beta iota in H.
destruct (negb (sbd_submodeID _ =? 0) && _).
* rewrite prun_bind, prun_notify in H. cbn beta iota in H. repeat (rewrite prun_ret in H; cbn beta iota in H).
injection H as _ _ _ <-. exists (bsl ++ notify_bytes MSG_INVALID_MODE). unfold p_app. cbn [p_err]. rewrite EB, app_assoc. reflexivity.
* rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
-- destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
-- repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
+ rewrite prun_ret in H. cbn beta iota in H.
destruct (negb (sbd_submodeID _ =? 0) && _).
* rewrite prun_bind, prun_notify in H. cbn beta iota in H. repeat (rewrite prun_ret in H; cbn beta iota in H).
injection H as _ _ _ <-. exists (bsl ++ notify_bytes MSG_INVALID_MODE). unfold p_app. cbn [p_err]. rewrite EB, app_assoc. reflexivity.
* rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
-- destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
-- repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
- rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
+ destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
+ repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ _ _ <-. exists bsl. exact EB.
Qed.

Theorem dec_appends_all : forall d : dec_state bptr, dec_appends d.
Proof.
assert (H : forall n (d : dec_state bptr), (dec_depth d <= n)%nat -> dec_appends d).
{ induction n as [|n IH]; intros d Hd.
- destruct d; cbn [dec_depth] in Hd; lia.
- destruct d as [st | s low]; [apply nb_appends|].
apply sb_appends_gen. intros low' E. apply IH. cbn [dec_depth] in Hd. lia. }
intros d. exact (H _ d (le_n _)).
Qed.
