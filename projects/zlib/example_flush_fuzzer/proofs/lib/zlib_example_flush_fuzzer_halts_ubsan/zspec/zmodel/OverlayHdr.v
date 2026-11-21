(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflRoom HuffSend OverlayRace.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import SendModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Hdr.
  Variable s : deflate_state.
  Hypothesis BL7 : forall y, 0 <= y <= 18 -> 0 <= Len s TB y <= 7.

  Lemma st_calls_le7 : forall mn cu pr ct, 0 <= cu <= 15 -> 3 <= mn -> 1 <= ct ->
    sumlen (st_calls s mn cu pr ct) <= 7 * ct.
  Proof.
    intros mn cu pr ct Hcu Hmn Hct. unfold st_calls, blc, REP_3_6, REPZ_3_10, REPZ_11_138.
    pose proof (BL7 cu ltac:(lia)). pose proof (BL7 16 ltac:(lia)). pose proof (BL7 17 ltac:(lia)). pose proof (BL7 18 ltac:(lia)).
    destruct (Z.ltb_spec ct mn).
    - rewrite sumlen_repeat. replace (Z.of_nat (Z.to_nat ct)) with ct by lia. nia.
    - destruct (cu =? 0); cbn [negb].
      + destruct (ct <=? 10); cbn [sumlen]; lia.
      + destruct (cu =? pr); cbn [negb app sumlen]; lia.
  Qed.

  Lemma st_calls_lens_ok : forall mn cu pr ct, 0 <= cu <= 18 -> lens_ok (st_calls s mn cu pr ct).
  Proof.
    intros mn cu pr ct Hcu. unfold st_calls, blc, REP_3_6, REPZ_3_10, REPZ_11_138, lens_ok.
    pose proof (BL7 cu ltac:(lia)). pose proof (BL7 16 ltac:(lia)). pose proof (BL7 17 ltac:(lia)). pose proof (BL7 18 ltac:(lia)).
    destruct (ct <? mn).
    - induction (Z.to_nat ct); cbn; constructor; [cbn; lia| exact IHn].
    - destruct (cu =? 0); cbn [negb].
      + destruct (ct <=? 10); repeat constructor; cbn; lia.
      + destruct (cu =? pr); cbn [negb app]; repeat constructor; cbn; lia.
  Qed.

  Fixpoint cover (E : list (Z * Z * Z * Z)) : Z :=
    match E with [] => 0 | (_, _, _, ct) :: r => ct + cover r end.

  Lemma emits_cover : forall f lens mc n p q c mx mn, 0 <= c -> n <= mc + 1 ->
    cover (emits f lens mc n p q c mx mn) <= (mc + 1 - n) + c
    /\ Forall (fun e => 1 <= snd e) (emits f lens mc n p q c mx mn).
  Proof.
    induction f as [|f IH]; intros lens mc n p q c mx mn Hc Hn; cbn [emits]; [split; [cbn; lia| constructor]|].
    destruct (Z.leb_spec n mc); [| split; [cbn; lia| constructor]]. cbv zeta.
    destruct ((c + 1 <? mx) && (q =? lens (n + 1))).
    - destruct (IH lens mc (n + 1) p (lens (n + 1)) (c + 1) mx mn ltac:(lia) ltac:(lia)) as [A B]. split; [lia| exact B].
    - destruct (tree_counts q (lens (n + 1))) as [mx' mn'].
      destruct (IH lens mc (n + 1) q (lens (n + 1)) 0 mx' mn' ltac:(lia) ltac:(lia)) as [A B].
      cbn [cover]. split; [lia|]. constructor; [cbn; lia| exact B].
  Qed.

  Lemma emits_shape : forall f lens mc n p q c mx mn,
    (mn = 3 \/ mn = 4) -> (forall i, 0 <= i <= mc -> 0 <= lens i <= 15) -> (n <= mc -> q = lens n) -> 0 <= n ->
    Forall (fun e => let '(mn0, cu, pr, ct) := e in (mn0 = 3 \/ mn0 = 4) /\ 0 <= cu <= 15) (emits f lens mc n p q c mx mn).
  Proof.
    induction f as [|f IH]; intros lens mc n p q c mx mn Hmn HL Hq Hn; cbn [emits]; [constructor|].
    destruct (Z.leb_spec n mc); [|constructor]. cbv zeta. specialize (Hq ltac:(lia)).
    destruct ((c + 1 <? mx) && (q =? lens (n + 1))).
    - apply IH; auto; lia.
    - destruct (tree_counts q (lens (n + 1))) as [mx' mn'] eqn:TC.
      pose proof (ScanModel.tree_counts_range _ _ _ _ TC) as [_ Hmn'].
      constructor; [| apply IH; auto; lia]. pose proof (HL n ltac:(lia)). subst q. split; [exact Hmn| lia].
  Qed.

  Lemma emits_bits_le7 : forall E,
    Forall (fun e => let '(mn0, cu, pr, ct) := e in (mn0 = 3 \/ mn0 = 4) /\ 0 <= cu <= 15) E ->
    Forall (fun e => 1 <= snd e) E ->
    sumlen (flat_map (em_calls s) E) <= 7 * cover E /\ lens_ok (flat_map (em_calls s) E).
  Proof.
    induction E as [|[[[mn0 cu] pr] ct] E IH]; intros SH CT; cbn [flat_map cover]; [split; [cbn; lia| constructor]|].
    inversion SH; subst. inversion CT; subst. cbn [snd] in *. destruct H1 as [M C].
    destruct (IH H2 H4) as [A B].
    rewrite sumlen_app. change (em_calls s (mn0, cu, pr, ct)) with (st_calls s mn0 cu pr ct).
    pose proof (st_calls_le7 mn0 cu pr ct C ltac:(lia) ltac:(lia)).
    split; [lia|]. apply lens_ok_app; [apply st_calls_lens_ok; lia| exact B].
  Qed.

  Theorem send_tree_bits_le : forall lens mc mx mn,
    0 <= mc -> (mn = 3 \/ mn = 4) -> (forall i, 0 <= i <= mc -> 0 <= lens i <= 15) ->
    let E := emits (Z.to_nat (mc + 1)) lens mc 0 (-1) (lens 0) 0 mx mn in
    sumlen (flat_map (em_calls s) E) <= 7 * (mc + 1) /\ lens_ok (flat_map (em_calls s) E).
  Proof.
    intros lens mc mx mn Hmc Hmn HL. cbv zeta.
    destruct (emits_cover (Z.to_nat (mc + 1)) lens mc 0 (-1) (lens 0) 0 mx mn ltac:(lia) ltac:(lia)) as [CV CT].
    pose proof (emits_shape (Z.to_nat (mc + 1)) lens mc 0 (-1) (lens 0) 0 mx mn Hmn HL ltac:(intros; reflexivity) ltac:(lia)) as SH.
    destruct (emits_bits_le7 _ SH CT) as [A B]. split; [lia| exact B].
  Qed.
End Hdr.

