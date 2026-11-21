(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lmb_best : forall s cur ch bl nice limit se1 se s' b' se1' se' cur' ch' cont,
  0 <= ds_strstart s ->
  longest_match_body s cur ch bl nice limit se1 se = (s', b', se1', se', cur', ch', cont) ->
  (s' = s /\ b' = bl) \/ (s' = set_match_start s cur /\ bl < b' /\ 2 <= b' <= MAX_MATCH).
Proof.
  intros s cur ch bl nice limit se1 se s' b' se1' se' cur' ch' cont Hstr E.
  unfold longest_match_body in E. cbv zeta in E.
  destruct (_ || _ || _ || _).
  - left. destruct (_ <? _); [destruct (negb _)|]; injection E as <- <- <- <- <- <- <-; split; reflexivity.
  - set (sc' := lm_cmp_loop 33 (ds_window s) (ds_strstart s + 2) (cur + 2) (ds_strstart s + MAX_MATCH)) in E.
    assert (Hsc : ds_strstart s + 2 <= sc' <= ds_strstart s + MAX_MATCH).
    { subst sc'. apply lm_cmp_loop_bound; unfold MAX_MATCH; [lia|]. replace (ds_strstart s + 258 - (ds_strstart s + 2)) with 256 by lia. reflexivity. }
    destruct (Z.ltb_spec bl (MAX_MATCH - (ds_strstart s + MAX_MATCH - sc'))) as [C|C].
    + right. destruct (nice <=? _).
      * injection E as <- <- <- <- <- <- <-. unfold MAX_MATCH in *. split; [reflexivity | lia].
      * change (ds_prev (set_match_start s cur)) with (ds_prev s) in E. change (ds_w_mask (set_match_start s cur)) with (ds_w_mask s) in E.
        destruct (_ <? _); [destruct (negb _)|]; injection E as <- <- <- <- <- <- <-; unfold MAX_MATCH in *; (split; [reflexivity | lia]).
    + left. destruct (_ <? _); [destruct (negb _)|]; injection E as <- <- <- <- <- <- <-; split; reflexivity.
Qed.

Lemma lm_loop_facts : forall f s cur ch bl nice limit se1 se,
  0 <= ds_strstart s -> 0 <= bl <= MAX_MATCH ->
  let r := longest_match_loop f s cur ch bl nice limit se1 se in
  exists (ms : option Z) b, r = (match ms with Some m => set_match_start s m | None => s end, b)
    /\ bl <= b <= MAX_MATCH
    /\ (bl < b -> exists m, ms = Some m /\ In m (lm_curs f s cur ch bl nice limit se1 se))
    /\ (ms = None \/ exists m, ms = Some m /\ In m (lm_curs f s cur ch bl nice limit se1 se)).
Proof.
  induction f as [|f IH]; intros s cur ch bl nice limit se1 se Hstr Hbl r; subst r.
  - cbn [longest_match_loop lm_curs]. exists None, bl. split; [reflexivity|]. split; [lia|]. split; [intros; lia | left; reflexivity].
  - cbn [longest_match_loop lm_curs].
    destruct (longest_match_body s cur ch bl nice limit se1 se) as [[[[[[s' b'] se1'] se'] cur'] ch'] cont] eqn:E.
    pose proof (lmb_best _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hstr E) as HB.
    destruct cont.
    + assert (Hstr' : 0 <= ds_strstart s') by (destruct HB as [[-> _]|[-> _]]; [exact Hstr | exact Hstr]).
      assert (Hbl' : 0 <= b' <= MAX_MATCH) by (destruct HB as [[_ ->]|[_ [? ?]]]; lia).
      destruct (IH s' cur' ch' b' nice limit se1' se' Hstr' Hbl') as (ms & b & Er & Hb & Hup & Hms).
      destruct HB as [[Es Eb]|[Es [Hlt Hr]]].
      * subst s' b'. exists ms, b. split; [exact Er|]. split; [lia|].
        split; [intros H; destruct (Hup H) as (m & -> & Hin); exists m; split; [reflexivity | right; exact Hin]|].
        destruct Hms as [-> | (m & -> & Hin)]; [left; reflexivity | right; exists m; split; [reflexivity | right; exact Hin]].
      * subst s'. exists (match ms with Some m => Some m | None => Some cur end), b.
        split.
        { rewrite Er. destruct ms as [m|]; [| reflexivity]. rewrite set_ms_twice. reflexivity. }
        split; [lia|].
        split.
        { intros _. destruct Hms as [-> | (m & -> & Hin)]; [exists cur; split; [reflexivity | left; reflexivity]|].
          exists m. split; [reflexivity|]. right. revert Hin. generalize (lm_curs f (set_match_start s cur) cur' ch' b' nice limit se1' se'). intros l Hin. exact Hin. }
        destruct Hms as [-> | (m & -> & Hin)]; right; [exists cur; split; [reflexivity | left; reflexivity]|].
        exists m. split; [reflexivity|]. right. exact Hin.
    + destruct HB as [[-> ->]|[-> [Hlt Hr]]].
      * exists None, bl. split; [reflexivity|]. split; [lia|]. split; [intros; lia | left; reflexivity].
      * exists (Some cur), b'. split; [reflexivity|]. split; [lia|].
        split; [intros _; exists cur; split; [reflexivity | left; reflexivity]|]. right. exists cur. split; [reflexivity | left; reflexivity].
Qed.

Lemma longest_match_facts : forall s cur,
  0 <= ds_strstart s -> 0 <= ds_prev_length s <= MAX_MATCH -> 0 <= ds_lookahead s ->
  let r := longest_match s cur in
  exists ms : option Z, fst r = (match ms with Some m => set_match_start s m | None => s end)
    /\ 0 <= snd r <= MAX_MATCH /\ snd r <= ds_lookahead s
    /\ (ds_prev_length s < snd r -> exists m, ms = Some m /\ In m (lm_visited s cur))
    /\ (ms = None \/ exists m, ms = Some m /\ In m (lm_visited s cur)).
Proof.
  intros s cur Hstr Hpl Hlook r. subst r. unfold longest_match, lm_visited. cbv zeta.
  match goal with |- context [longest_match_loop ?f s cur ?ch ?bl ?nice ?limit ?se1 ?se] =>
    destruct (lm_loop_facts f s cur ch bl nice limit se1 se Hstr Hpl) as (ms & b & Er & Hb & Hup & Hms);
    rewrite Er end.
  exists ms.
  assert (El : ds_lookahead (match ms with Some m => set_match_start s m | None => s end) = ds_lookahead s) by (destruct ms; reflexivity).
  rewrite El. destruct (Z.leb_spec b (ds_lookahead s)); cbn [fst snd].
  - split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hup | exact Hms].
  - split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [intros H'; apply Hup; lia | exact Hms].
Qed.
