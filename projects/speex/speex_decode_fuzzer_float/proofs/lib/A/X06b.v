(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X082 X08y X091 X08o X0b1 X0bf X093 X068.
Import ListNotations.
Open Scope Z_scope.

Local Notation unpackM := (@bits_unpack_unsigned_M pst bptr).
Local Notation peekM := (@bits_peek_M pst bptr).
Local Notation advanceM := (@bits_advance_M pst bptr).
Local Notation remainingM := (@bits_remaining_M pst bptr).
Local Notation DEC := (speex_decode (St := pst) p_notify unpackM peekM advanceM remainingM).

Lemma sb_isave_pres : forall (s : sbd_state bptr) (low : dec_state bptr) b q ret d' b' q',
prun (DEC (DecSB s low) b 0) q = Some ((ret, d', b'), q') -> isave_ok (DecSB s low) -> isave_ok d'.
Proof.
intros s low b q ret d' b' q' H ISV.
unfold speex_decode in H. cbn [dec_depth speex_decode_n] in H.
rewrite prun_bind in H. unfold sb_decode in H.
destruct (speex_decoder_ctl low (CtlSetInnovationSave (0 + sbd_frame_size s))) as [v1 low1] eqn:E1.
rewrite prun_bind in H.
destruct (prun (speex_decode_n p_notify unpackM peekM advanceM remainingM (dec_depth low) low1 b 0) q) as [[[[retl low2] b1] q1]|] eqn:EL; [| discriminate H].
cbn beta iota in H.
destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3].
destruct (negb (retl =? 0)).
{ repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV. }
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
injection H as _ <- _ _. exact ISV.
* rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
-- destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
-- repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
+ rewrite prun_ret in H. cbn beta iota in H.
destruct (negb (sbd_submodeID _ =? 0) && _).
* rewrite prun_bind, prun_notify in H. cbn beta iota in H. repeat (rewrite prun_ret in H; cbn beta iota in H).
injection H as _ <- _ _. exact ISV.
* rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
-- destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
-- repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
- rewrite prun_ret in H. cbn beta iota in H.
destruct (submode_at _ _) as [sm|].
+ destruct (speex_decoder_ctl _ CtlGetPiGain) as [v4 low4]. destruct (speex_decoder_ctl low4 CtlGetExc) as [v5 low5].
rewrite prun_bind, lsp_unquant_prun in H. cbn beta iota in H. rewrite prun_bind, sb_decode_subframes_prun in H. cbn beta iota in H.
repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
+ repeat (rewrite prun_ret in H; cbn beta iota in H). injection H as _ <- _ _. exact ISV.
Qed.

Lemma subframes_isave : forall n sub sm olp (st : nb_state bptr) b st' b', subframes_pure n sub sm olp st b = Some (st', b') -> nb_innov_save st' = nb_innov_save st.
Proof.
induction n as [|n IH]; intros sub sm olp st b st' b' H; cbn [subframes_pure] in H; [injection H as <- _; reflexivity|].
destruct (subframe_pure sm olp sub st b) as [[st1 b1]|] eqn:E1; [| discriminate H].
rewrite (IH _ _ _ _ _ _ _ H). unfold subframe_pure in E1.
destruct (sm_ltp_unquant sm); [| discriminate E1]. destruct (sm_innovation_unquant sm); [| discriminate E1].
destruct (nb_submodeID st =? 1).
- destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp); [| discriminate E1]. injection E1 as <- _. reflexivity.
- injection E1 as <- _. reflexivity.
Qed.

Lemma nb_rest_isave : forall (st : nb_state bptr) mo b1 r st' b2, nb_rest_pure st mo b1 = Some (r, st', b2) -> nb_innov_save st' = nb_innov_save st.
Proof.
intros st mo b1 r st' b2 H. unfold nb_rest_pure in H. cbv zeta in H.
destruct (submode_at nb_submodes mo) as [sm|].
- match type of H with context [subframes_pure ?n ?sub ?sm0 ?olp ?st0 ?bb] => destruct (subframes_pure n sub sm0 olp st0 bb) as [[st2 b3]|] eqn:E2 end; [| discriminate H].
injection H as _ <- _. apply subframes_isave in E2. transitivity (nb_innov_save st2); [reflexivity|]. rewrite E2. unfold segD_st.
destruct (nb_submodeID _ =? 1); [reflexivity|]. destruct (1 <? nb_submodeID _); reflexivity.
- injection H as _ <- _. reflexivity.
Qed.

Lemma nb_isave_pres : forall (st : nb_state bptr) b q ret d' b' q',
prun (DEC (DecNB st) b 0) q = Some ((ret, d', b'), q') -> isave_ok (DecNB st) -> isave_ok d'.
Proof.
intros st b q ret d' b' q' H ISV. rewrite dec_nb_prun, nb_decode_prun_gen in H. unfold nb_decode_res_gen in H.
destruct (negb (nb_encode_submode st =? 0)).
- destruct (search_pure (nb_search_fuel b) (nb_stereo_cb st) b) as [r0 b0|mo b1|tw b0|]; cbn [search_res] in H.
+ injection H as _ <- _ _. exact ISV.
+ destruct (nb_rest_pure st mo b1) as [[[r1 st1] b2]|] eqn:E; [| discriminate H]. injection H as _ <- _ _.
cbn [isave_ok]. rewrite (nb_rest_isave _ _ _ _ _ _ E). exact ISV.
+ injection H as _ <- _ _. exact ISV.
+ discriminate H.
- destruct (nb_rest_pure st (nb_submodeID st) b) as [[[r1 st1] b2]|] eqn:E; [| discriminate H]. injection H as _ <- _ _.
cbn [isave_ok]. rewrite (nb_rest_isave _ _ _ _ _ _ E). exact ISV.
Qed.

Theorem dec_isave_pres : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Proof. intros [st | s low] d' b q ret b' q' H; [exact (nb_isave_pres st b q ret d' b' q' H) | exact (sb_isave_pres s low b q ret d' b' q' H)]. Qed.
