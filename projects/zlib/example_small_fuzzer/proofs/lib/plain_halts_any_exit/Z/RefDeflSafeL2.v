(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.

Module RefDeflSafeLM.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
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
End RefDeflSafeLM.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.

Module RefDeflSafeL0.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored7.RefDeflStored6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Local Ltac bytes_tac Hbb :=
  intros i Hi; rewrite !arr_get_set;
  repeat (match goal with |- 0 <= (if ?c then _ else _) < 256 => destruct c end; [apply wrap8_range|]); apply Hbb; exact Hi.

Lemma SV_aout0 : forall c0 s, C0OK c0 -> SV c0 s -> 0 <= cs_avail_out (ds_strm s) < 2 ^ 32.
Proof.
  intros c0 s HC0 V.
  pose proof (sv_out _ _ V) as Ou. pose proof (sv_aout _ _ V) as Ao. pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0.
  rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou. pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl. lia.
Qed.


Definition SF (s : deflate_state) :=
  ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
   (ds_ins_h s, ds_match_length s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_match_start s, ds_lookahead s, ds_sym_next s),
   (ds_wrap s, ds_status s, ds_lit_bufsize s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s, ds_dyn_ltree_fc s, ds_dyn_dtree_fc s),
   (ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
   (ds_head s, ds_prev s, ds_last_flush s, KV s, ds_sym_end s, ds_window_size s, ds_w_size s),
   (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_heap s)).

Lemma SF_fields : forall a b, SF b = SF a ->
  (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
   /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
  /\ (ds_ins_h b = ds_ins_h a /\ ds_match_length b = ds_match_length a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
      /\ ds_prev_match b = ds_prev_match a /\ ds_match_start b = ds_match_start a /\ ds_lookahead b = ds_lookahead a /\ ds_sym_next b = ds_sym_next a)
  /\ (ds_wrap b = ds_wrap a /\ ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a
      /\ ds_bl_tree_fc b = ds_bl_tree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a
      /\ ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a)
  /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
      /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
  /\ (ds_head b = ds_head a /\ ds_prev b = ds_prev a /\ ds_last_flush b = ds_last_flush a /\ KV b = KV a /\ ds_sym_end b = ds_sym_end a
      /\ ds_window_size b = ds_window_size a /\ ds_w_size b = ds_w_size a)
  /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
      /\ ds_method b = ds_method a /\ ds_heap b = ds_heap a).
Proof.
  intros a b E. unfold SF in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma DC_SF_transfer : forall c0 a b, DC c0 a -> dmode a = 0 -> SF b = SF a ->
  arr_len (ds_window b) = 2 * ds_w_size a -> (forall i, 0 <= i < 2 * ds_w_size a -> 0 <= arr_get (ds_window b) i < 256) ->
  0 <= ds_block_start b <= ds_strstart b -> ds_strstart b <= 2 * ds_w_size a ->
  0 <= ds_insert b <= ds_strstart b -> ds_insert b <= ds_w_size a ->
  0 <= ds_matches b <= 2 -> 0 <= ds_high_water b < 2 ^ 64 -> ds_high_water b <= ds_window_size a ->
  arr_len (ds_pending_buf b) = ds_lit_bufsize a * 4 -> (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get (ds_pending_buf b) i < 256) ->
  0 <= ds_pending_out b -> 0 <= ds_pending b -> ds_pending_out b + ds_pending b <= ds_lit_bufsize a * 4 ->
  (ds_pending b = 0 -> ds_pending_out b = 0) ->
  0 <= ds_bi_valid b <= 7 -> 0 <= ds_bi_buf b < 2 ^ 16 ->
  SV c0 b ->
  DC c0 b.
Proof.
  intros c0 a b [[D X] V] Hm E Hwl Hwb Hbs Hstr Hins Hinsw Hmat Hhw Hhww Hpbl Hpbb Hpo Hpd Hpp Hpo0 Hbv Hbb Vb.
  pose proof (dwf_sizes a D) as (Sw & Sh & Sl & _).
  pose proof (SF_fields a b E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eml & Epl & Ema & Epm & Ems & Elook & Esn) & (Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl & Elfc & Edfc)
                                   & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Ehd & Epv & Elf & EKV & Ese & Ewsz & Ews) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
  pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB).
  assert (Em : dmode b = 0) by (unfold dmode; rewrite Elv, Esy; exact Hm).
  destruct (dx_st0 _ X Hm) as (Hl0 & Hbs0 & Hsn0 & Hmt0).
  split; [split|]; [| | exact Vb].
  - pose proof (df_tl _ D) as TL.
    destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Elfc, ?Edfc, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Elf, ?Ese, ?Ewb, ?Ehb, ?Epbs,
        ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Ewsz, ?Ehd, ?Epv, ?Eih, ?Ems, ?Elook, ?Hwl, ?Hpbl; try assumption.
    + unfold deflateStateCheck in *. rewrite Est. assumption.
    + congruence.
    + congruence.
    + congruence.
    + congruence.
    + reflexivity.
    + reflexivity.
    + unfold tree_lens in *. rewrite Elfc, Edfc, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. assumption.
    + clear - Hbs Hstr Sw. lia.
    + clear - Hbs Hstr Hl0. lia.
    + clear - Hpo Hpd Hpp. lia.
    + clear - Hbv Hbb. lia.
  - apply DX_join.
    + pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (DX_DXX a X) as XX.
      destruct XX; constructor; rewrite ?Em, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eih, ?Eml, ?Epl, ?Ema, ?Epm, ?Ems, ?Elook, ?Esn, ?Ewr, ?Est, ?Elbs, ?Ews, ?Ewsz, ?Edep, ?Eblc;
        try assumption.
      * intros HH. discriminate HH.
      * intros _. apply xx_notslow. rewrite Hm. clear; lia.
      * intros HH. discriminate HH.
      * intros _. rewrite Hl0. split; [reflexivity|]. split; [exact Hbs|]. split; [exact Hsn0 | clear - Hmat; lia].
      * intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
      * intros Hm'. exfalso. exact (Hm' eq_refl).
    + pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_hist _ X) as XH.
      assert (En : nsym b = 0) by (unfold nsym; rewrite Esn, Hsn0; reflexivity).
      assert (Ena : nsym a = 0) by (unfold nsym; rewrite Hsn0; reflexivity).
      constructor; rewrite ?En, ?Em, ?Esn, ?Elbs, ?Eol, ?Esl; try assumption.
      * clear - Sl. lia.
      * intros j Hj. exfalso. clear - Hj. lia.
      * unfold freq_hist in *. rewrite En. rewrite Ena in XH. rewrite Elfc, Edfc, Ebl. exact XH.
      * exact (dx_opt _ X).
      * exact (dx_stat _ X).
      * intros Hm'. exfalso. exact (Hm' eq_refl).
      * intros t i. destruct t; cbn [tree_fc]; rewrite ?Elfc, ?Edfc, ?Ebl; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
      * clear - Hbv. lia.
    + split; [intros Hm'; exfalso; exact (Hm' Em) | apply SLOW3_mode; rewrite Em; clear; lia].
Qed.

Section Stored.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition SI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ dmode s = 0 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s /\ ds_pending s = 0.

  Lemma SI_facts : forall s, SI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 2048 <= ds_lit_bufsize s <= 32768 /\ ds_pending_buf_size s = ds_lit_bufsize s * 4
    /\ ds_lookahead s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_sym_next s = 0 /\ 0 <= ds_matches s <= 2
    /\ ds_strstart s <= 2 * ds_w_size s /\ ds_window_size s = 2 * ds_w_size s /\ 0 <= ds_wrap s <= 2
    /\ ds_pending_out s = 0 /\ 0 <= ds_bi_valid s <= 7 /\ 0 <= ds_bi_buf s < 2 ^ 16
    /\ 0 <= cs_avail_out (ds_strm s) < 2 ^ 32 /\ 0 <= cs_avail_in (ds_strm s) < 2 ^ 32
    /\ 0 <= ds_insert s <= ds_strstart s /\ ds_insert s <= ds_w_size s /\ 0 <= ds_high_water s < 2 ^ 64.
  Proof.
    intros s (HDC & HK & Hm & Hst & Ho & Hp). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & _).
    destruct (dx_st0 _ X Hm) as (Hl0 & Hbs & Hsn & Hmt). pose proof (RefDeflSafeI1.dx_matches _ X) as Hmt'.
    pose proof (df_sl _ D) as Hsl. pose proof (df_wrap _ D) as Hwr. pose proof (dx_wrapneg _ X) as Hwn.
    pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_biv _ X) as Hbv7.
    split; [exact D|]. split; [exact X|]. split; [exact V|]. split; [exact Sw|]. split; [exact Sl|]. split; [exact (df_pbs _ D)|].
    split; [exact Hl0|]. split; [exact Hbs|]. split; [exact Hsn|]. split; [clear - Hmt Hmt'; lia|].
    split; [clear - Hsl Hl0; lia|]. split; [exact (df_wsz _ D)|].
    split; [destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; exact (Hst (Hwn l)) | clear - Hwr l; lia]|].
    split; [exact (dx_pout0 _ X Hp)|]. split; [clear - Hbv Hbv7; lia|]. split; [exact Hbb|].
    split; [exact (SV_aout0 c0 s HC0w V)|]. split; [exact (sv_ain _ _ V)|].
    split; [exact (df_ins _ D)|]. split; [exact (dx_ins _ X) | exact (df_hw _ D)].
  Qed.

  Lemma SI_st_entry : forall s, SI s -> st_entry s.
  Proof.
    intros s HS. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts s HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    constructor; [| exact Hp | exact Hpo | exact Hbb | exact Epbs | exact Hao].
    constructor; try assumption.
    - pose proof (df_bi _ D). lia.
    - exact (sv_nin _ _ V).
    - rewrite (sv_inlen _ _ V), (sv_input _ _ V). lia.
    - exact (sv_ib _ _ V).
    - exact (sv_tin _ _ V).
    - rewrite (sv_tout _ _ V). apply wrap64_range'.
    - intros _. exact (sv_adler _ _ V).
    - clear - Hins Hinsw. lia.
    - clear - Hmt. lia.
    - rewrite Epbs. clear - Sl. lia.
    - exact (df_wb _ D).
  Qed.

  Definition LZS (s : deflate_state) := (ds_window s, ds_strstart s, ds_insert s, ds_matches s, ds_high_water s).

  Lemma SF_upd4 : forall s a p b v, SF (upd4 s a p b v) = SF s. Proof. reflexivity. Qed.
  Lemma SF_fp_tail : forall s len, SF (fp_tail s len) = SF s.
  Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma LZS_upd4 : forall s a p b v, LZS (upd4 s a p b v) = LZS s. Proof. reflexivity. Qed.
  Lemma LZS_fp_tail : forall s len, LZS (fp_tail s len) = LZS s.
  Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
  Lemma LZS_fields : forall a b, LZS b = LZS a ->
    ds_window b = ds_window a /\ ds_strstart b = ds_strstart a /\ ds_insert b = ds_insert a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a.
  Proof.
    intros a b E. unfold LZS in E.
    repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end. repeat split; assumption.
  Qed.

  Lemma emit_stage : forall t, SI t -> sb_hdr t <= cs_avail_out (ds_strm t) ->
    let t' := st_emit1 t flush in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - sb_hdr t
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t HS Hroom t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
    pose proof (sb_hdr_eq' t ltac:(clear - Hbv; lia)) as EP. rewrite Hp in EP.
    pose proof (sb_hdr_eq t ltac:(clear - Hbv; lia)) as [_ Hhdr7]. pose proof (proj1 (sb_hdr_eq t ltac:(clear - Hbv; lia))) as Ehdr. rewrite <- Ehdr in Hhdr7.
    pose proof (tsb_hP_range t) as HP. rewrite Hp in HP.
    unfold st_emit1. rewrite (tr_stored_block_eq t None 0 (sb_lastv t flush) ltac:(clear - Hbv; lia) Hbb). unfold tsb_tail. cbn [negb Z.eqb].
    set (A := tsb_lenA (tsb_hA t (sb_lastv t flush)) (tsb_hP t) 0).
    set (P := tsb_hP t + 1 + 1 + 1 + 1 + 0).
    set (len := sb_len t).
    set (A' := arr_set (arr_set (arr_set (arr_set A (P - 4) (wrap8 len)) (P - 3) (wrap8 (Z.shiftr len 8))) (P - 2) (wrap8 (Z.lnot len))) (P - 1) (wrap8 (Z.shiftr (wrap32 (Z.lnot len)) 8))).
    assert (E1 : sb_patch (upd4 t A P 0 0) len = upd4 t A' P 0 0) by reflexivity.
    rewrite E1.
    assert (HA : forall i, 3 <= i -> arr_get (tsb_hA t (sb_lastv t flush)) i = arr_get (ds_pending_buf t) i).
    { intros i Hi. unfold tsb_hA. rewrite Hp. destruct (_ <=? 5); [| destruct (_ <=? 13)]; rewrite !arr_get_set_other' by lia; reflexivity. }
    assert (HAb : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get (tsb_hA t (sb_lastv t flush)) i < 256).
    { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
    assert (HA'b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A' i < 256).
    { subst A' A. unfold tsb_lenA. bytes_tac HAb. }
    assert (HA'hi : forall i, ds_lit_bufsize t <= i -> arr_get A' i = arr_get (ds_pending_buf t) i).
    { intros i Hi. subst A' A P. unfold tsb_lenA. rewrite !arr_get_set_other' by lia. apply HA. lia. }
    assert (HA'len : arr_len A' = arr_len (ds_pending_buf t)) by (subst A' A; unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len).
    destruct (DC_upd4 c0 t A' P 0 0 HDC Hpo HA'len HA'b HA'hi ltac:(subst P; clear - HP Sl; lia) ltac:(clear; lia) ltac:(clear; lia)) as (DC1 & KV1 & Estrm1).
    set (X1 := upd4 t A' P 0 0) in *.
    assert (EP' : P = sb_hdr t) by (subst P; clear - EP; lia).
    assert (Efp : flush_pending X1 = fp_tail X1 P).
    { rewrite flush_pending_eq. cbv zeta. rewrite (tr_flush_bits_0 X1) by reflexivity.
      rewrite (fp_len_all X1) by (change (ds_pending X1) with P; change (ds_strm X1) with (ds_strm t); clear - HP Hroom EP' Sl; lia).
      change (ds_pending X1) with P. replace (P =? 0) with false by (symmetry; apply Z.eqb_neq; clear - HP; lia). reflexivity. }
    pose proof (DC_flush_pending c0 X1 HC0w DC1) as FPF. cbv zeta in FPF. rewrite Efp in FPF.
    destruct FPF as (DC2 & KV2 & Ho2 & _).
    pose proof (fp_tail_facts X1 P eq_refl) as TF. cbv zeta in TF.
    destruct TF as (Tpd & Tpo & _ & _ & Tao & Tai & Tni & Tin & _).
    change (ds_strm X1) with (ds_strm t) in Tao, Tai, Tni, Tin.
    assert (ESF : SF (fp_tail X1 P) = SF t) by (rewrite SF_fp_tail; subst X1; apply SF_upd4).
    pose proof (SF_fields _ _ ESF) as ((_ & _ & _ & _ & Elv & Esy) & _ & (_ & Est & _) & _).
    rewrite Efp. split.
    { split; [exact DC2|]. split; [rewrite KV2, KV1; exact HK|]. split; [unfold dmode; rewrite Elv, Esy; exact Hm|].
      split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ t); [exact Ho | apply (OUTLE_trans _ X1); [apply OUTLE_strm; exact Estrm1 | exact Ho2]]|]. exact Tpd. }
    split; [exact ESF|]. split; [rewrite LZS_fp_tail; subst X1; apply LZS_upd4|].
    split; [etransitivity; [apply (f_equal ds_block_start (eq_refl _)) |]; unfold fp_tail; destruct (_ =? 0); reflexivity|].
    split; [rewrite Tao, EP'; reflexivity|]. split; [exact Tai|]. split; [exact Tni | exact Tin].
  Qed.

  Lemma dmode_SF : forall a b, SF b = SF a -> dmode b = dmode a.
  Proof. intros a b E. pose proof (SF_fields _ _ E) as ((_ & _ & _ & _ & Elv & Esy) & _). unfold dmode. rewrite Elv, Esy. reflexivity. Qed.

  Lemma SV_emit : forall t l (src : arr) ofs,
    SV c0 t -> 0 <= l <= cs_avail_out (ds_strm t) -> (forall i, ofs <= i < ofs + l -> 0 <= arr_get src i < 256) ->
    forall st, cs_input st = cs_input (ds_strm t) -> cs_next_in st = cs_next_in (ds_strm t) -> cs_avail_in st = cs_avail_in (ds_strm t) ->
    cs_out_rev st = rev_append (arr_slice src ofs l) (cs_out_rev (ds_strm t)) -> cs_avail_out st = cs_avail_out (ds_strm t) - l ->
    cs_total_in st = cs_total_in (ds_strm t) -> cs_total_out st = wrap64 (cs_total_out (ds_strm t) + l) ->
    cs_adler st = cs_adler (ds_strm t) -> cs_data_type st = cs_data_type (ds_strm t) ->
    forall t', ds_strm t' = st -> SV c0 t' /\ OUTLE t t'.
  Proof.
    intros t l src ofs V Hl Hsrc st Ein Eni Eai Eout Eao Eti Eto Ead Edt t' Est.
    assert (Hlen : Z.of_nat (length (cs_out_rev st)) = Z.of_nat (length (cs_out_rev (ds_strm t))) + l).
    { rewrite Eout, rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
    split.
    - constructor; rewrite ?Est, ?Ein, ?Eni, ?Eai, ?Eao, ?Eti, ?Eto, ?Ead, ?Edt.
      + exact (sv_input _ _ V).
      + exact (sv_nin _ _ V).
      + exact (sv_inlen _ _ V).
      + exact (sv_ain _ _ V).
      + unfold zlen in *. rewrite Hlen. pose proof (sv_out _ _ V) as Ou. unfold zlen in Ou. lia.
      + lia.
      + pose proof (sv_grow _ _ V). rewrite Eout, rev_append_rev, length_app. lia.
      + rewrite Eout. apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_arr_slice. exact Hsrc.
      + exact (sv_tin _ _ V).
      + rewrite (sv_tout _ _ V), wrap64_add_l. f_equal. unfold zlen in *. rewrite Hlen. lia.
      + exact (sv_adler _ _ V).
      + exact (sv_dt _ _ V).
      + intros i Hi. apply (sv_ib _ _ V). exact Hi.
    - apply (OUTLE_emit _ _ (arr_slice src ofs l)). rewrite Est. exact Eout.
  Qed.

  Lemma lcopy_stage : forall t l, SI t -> 0 <= l -> ds_block_start t + l <= ds_strstart t -> l <= cs_avail_out (ds_strm t) ->
    let t' := st_lcopy t l in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t + l
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - l
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t l HS Hl Hbl Hla t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold st_lcopy.
    match goal with |- context [set_strm t ?st] => set (ST := st) end.
    destruct (SV_emit t l (ds_window t) (ds_block_start t) V ltac:(clear - Hl Hla; lia) ltac:(intros i Hi; apply (df_wb _ D); clear - Hi Hbs Hbl Hstr; lia)
                ST eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (set_block_start (set_strm t ST) (ds_block_start t + l)) eq_refl) as [V' Ho'].
    split.
    { split.
      { apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
        all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
                   | clear - Hbs Hl Hbl; lia | clear - Hp Hpo Sl; lia | intros _; exact Hpo]. }
      split; [exact HK|]. split; [exact Hm|]. split; [exact Hst|]. split; [exact (OUTLE_trans _ _ _ Ho Ho') | exact Hp]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. dsred. cbn. repeat split; reflexivity.
  Qed.

  Lemma input_slice_bytes : forall t ofs n, SV c0 t -> 0 <= ofs -> ofs + n <= arr_len (cs_input (ds_strm t)) ->
    forall b, In b (arr_slice (cs_input (ds_strm t)) ofs n) -> 0 <= b < 256.
  Proof. intros t ofs n V Ho Hn b Hb. eapply arr_slice_In; [| exact Hb]. intros i Hi. apply (sv_ib _ _ V). lia. Qed.

  Lemma rdo_stage : forall t n, SI t -> 0 < n <= cs_avail_in (ds_strm t) -> n <= cs_avail_out (ds_strm t) ->
    let t' := st_rdo t n in
    SI t' /\ SF t' = SF t /\ LZS t' = LZS t /\ ds_block_start t' = ds_block_start t
    /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t) - n
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) - n /\ cs_next_in (ds_strm t') = cs_next_in (ds_strm t) + n /\ cs_input (ds_strm t') = cs_input (ds_strm t).
  Proof.
    intros t n HS Hn Hna t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    assert (Hb : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n) -> 0 <= b < 256)
      by (apply input_slice_bytes; [exact V | exact Hni | clear - Hil Hn; lia]).
    set (bytes := arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n) in *.
    set (ad := if ds_wrap t =? 1 then adler32_upd (cs_adler (ds_strm t)) bytes else if ds_wrap t =? 2 then crc32_upd (cs_adler (ds_strm t)) bytes else cs_adler (ds_strm t)).
    assert (Had : 0 <= ad < 2 ^ 64).
    { subst ad. destruct (ds_wrap t =? 1); [apply adler32_upd_range; exact Hb|]. destruct (ds_wrap t =? 2); [pose proof (crc32_upd_range (cs_adler (ds_strm t)) _ Hb); lia|]. exact (sv_adler _ _ V). }
    set (ST := mkCS (cs_input (ds_strm t)) (cs_next_in (ds_strm t) + n) (cs_avail_in (ds_strm t) - n) (rev_append bytes (cs_out_rev (ds_strm t)))
                    (cs_avail_out (ds_strm t) - n) (wrap64 (cs_total_in (ds_strm t) + n)) (wrap64 (cs_total_out (ds_strm t) + n)) (cs_msg (ds_strm t)) (cs_data_type (ds_strm t)) ad).
    assert (Erdo : st_rdo t n = set_strm t ST).
    { unfold st_rdo, read_buf. replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm t)) Hn). replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota beta.
      subst ST ad bytes. unfold cs_emit. destruct (ds_wrap t =? 1); [| destruct (ds_wrap t =? 2)]; destruct t; cbn; destruct ds_strm; cbn; reflexivity. }
    rewrite Erdo.
    assert (Hlen : Z.of_nat (length (rev_append bytes (cs_out_rev (ds_strm t)))) = Z.of_nat (length (cs_out_rev (ds_strm t))) + n).
    { rewrite rev_append_rev, length_app, length_rev. subst bytes. unfold arr_slice. rewrite arr_slice_nat_length. lia. }
    assert (V' : SV c0 (set_strm t ST)).
    { constructor; cbn.
      - exact (sv_input _ _ V).
      - clear - Hni Hn. lia.
      - rewrite (sv_input _ _ V) in Hil. clear - Hil. lia.
      - clear - Hai Hn. lia.
      - unfold zlen in *. rewrite Hlen. pose proof (sv_out _ _ V) as Ou. unfold zlen in Ou. lia.
      - clear - Hna Hn Hao. lia.
      - pose proof (sv_grow _ _ V). rewrite rev_append_rev, length_app. lia.
      - apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_forall. exact Hb.
      - apply wrap64_range'.
      - rewrite (sv_tout _ _ V), wrap64_add_l. f_equal. unfold zlen in *. rewrite Hlen. lia.
      - exact Had.
      - exact (sv_dt _ _ V).
      - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
    split.
    { split.
      { apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
        all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
                   | clear - Hp Hpo Sl; lia | intros _; exact Hpo]. }
      split; [exact HK|]. split; [exact Hm|]. split; [exact Hst|]. split; [| exact Hp].
      apply (OUTLE_trans _ t); [exact Ho|]. eapply OUTLE_emit. cbn. reflexivity. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. cbn. repeat split; reflexivity.
  Qed.

  Lemma window_upd_bytes : forall t ofs l, dwf t -> (forall b, In b l -> 0 <= b < 256) ->
    arr_len (arr_upd (ds_window t) ofs l) = 2 * ds_w_size t /\ (forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get (arr_upd (ds_window t) ofs l) j < 256).
  Proof.
    intros t ofs l D Hl. split; [rewrite arr_len_upd; exact (df_wl _ D)|]. apply arr_upd_bytes; [exact (df_wb _ D) | exact Hl].
  Qed.
  Lemma window_blit_bytes : forall t dofs sofs n, dwf t ->
    arr_len (arr_blit (ds_window t) dofs (ds_window t) sofs n) = 2 * ds_w_size t
    /\ ((forall j, dofs <= j < dofs + n -> 0 <= sofs + (j - dofs) < 2 * ds_w_size t) ->
        forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get (arr_blit (ds_window t) dofs (ds_window t) sofs n) j < 256).
  Proof.
    intros t dofs sofs n D. split; [rewrite arr_len_blit; exact (df_wl _ D)|].
    intros Hs j Hj. rewrite arr_get_blit. destruct (_ && _) eqn:E; [| apply (df_wb _ D); exact Hj].
    apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply (df_wb _ D). apply Hs. lia.
  Qed.

  Lemma wupd_stage : forall t used, SI t -> 0 <= used <= cs_next_in (ds_strm t) ->
    let t' := st_wupd t used in
    SI t' /\ ds_strm t' = ds_strm t /\ (used <> 0 -> ds_block_start t' = ds_strstart t').
  Proof.
    intros t used HS Hu t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    assert (GEN : forall w str ins mat,
      arr_len w = 2 * ds_w_size t -> (forall j, 0 <= j < 2 * ds_w_size t -> 0 <= arr_get w j < 256) ->
      0 <= str <= 2 * ds_w_size t -> 0 <= ins <= str -> ins <= ds_w_size t -> 0 <= mat <= 2 ->
      SI (set_block_start (set_insert (set_strstart (set_matches (set_window t w) mat) str) ins) str)).
    { intros w str ins mat Hwl Hwb Hs Hi Hiw Hmat'. split; [| split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]].
      apply (DC_SF_transfer c0 t _ HDC Hm); dsred; try reflexivity; try assumption.
      all: first [clear - Hs; lia | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hpo; lia | clear - Hp; lia | clear - Hp Hpo Sl; lia | intros _; exact Hpo
                 | apply (SV_strm c0 t); [reflexivity | exact V]]. }
    unfold st_wupd.
    destruct (Z.eqb_spec used 0) as [U0|U0]; cbn [negb].
    { split; [exact HS|]. split; [reflexivity|]. intros HH; exfalso; exact (HH U0). }
    destruct (Z.leb_spec (ds_w_size t) used) as [C1|C1].
    -
      dsred.
      destruct (window_upd_bytes t 0 (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - ds_w_size t) (ds_w_size t)) D
                  ltac:(apply input_slice_bytes; [exact V | clear - Hu C1; lia | clear - Hu Hil Hai; lia])) as [Wl Wb].
      split; [| split; reflexivity].
      match goal with |- SI ?x => change x with (set_block_start (set_insert (set_strstart (set_matches (set_window t
        (arr_upd (ds_window t) 0 (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - ds_w_size t) (ds_w_size t)))) 2) (ds_w_size t)) (ds_w_size t)) (ds_w_size t)) end.
      apply GEN; try assumption; clear - Sw; lia.
    - assert (INS : forall ins, 0 <= ins <= ds_w_size t ->
        ins <= ins + MIN used (wrap32 (ds_w_size t - ins)) <= ds_w_size t /\ ins + MIN used (wrap32 (ds_w_size t - ins)) <= ins + used).
      { intros ins Hi. pose proof (ins_add_eq ins used (ds_w_size t) Hi ltac:(clear - Sw; lia) ltac:(clear - Hu; lia)) as [E R]. unfold ins_add in E, R.
        rewrite E in R |- *. destruct (Z.ltb_spec used (ds_w_size t - ins)) as [l|l]; clear - Hi R Hu l; lia. }
      destruct (Z.leb_spec (ds_window_size t - ds_strstart t) used) as [C2|C2].
      +
        rewrite Ewsz in C2.
        pose proof (window_blit_bytes t 0 (ds_w_size t) (ds_strstart t - ds_w_size t) D) as [Bl Bb].
        specialize (Bb ltac:(intros j Hj; clear - Hj C1 C2 Hstr Sw; lia)).
        assert (Hsl : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) -> 0 <= b < 256)
          by (apply input_slice_bytes; [exact V | clear - Hu; lia | clear - Hu Hil Hai; lia]).
        dsred. destruct (Z.ltb_spec (ds_matches t) 2) as [C3|C3]; dsred; destruct (Z.ltb_spec (ds_strstart t - ds_w_size t) (ds_insert t)) as [C4|C4]; dsred;
          (split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption
                         | split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]]
                 | split; [reflexivity | intros _; reflexivity]]);
          try (rewrite arr_len_upd; exact Bl); try (apply arr_upd_bytes; [exact Bb | exact Hsl]).
        all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo). all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
        all: try (clear - C1 C2 C3 C4 Hstr Sw Hu Hmt Hp Hpo Sl; lia).
        all: first [pose proof (INS (ds_strstart t - ds_w_size t) ltac:(clear - C1 C2 Hstr Sw; lia)); clear - H C1 C2 Hstr Sw Hu; lia
                   | pose proof (INS (ds_insert t) ltac:(clear - Hins Hinsw; lia)); clear - H C1 C2 C4 Hstr Sw Hu Hins; lia
                   | match goal with |- ?g => idtac "GOAL" g end].
      +
        rewrite Ewsz in C2.
        assert (Hsl : forall b, In b (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) -> 0 <= b < 256)
          by (apply input_slice_bytes; [exact V | clear - Hu; lia | clear - Hu Hil Hai; lia]).
        destruct (window_upd_bytes t (ds_strstart t) (arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t) - used) used) D Hsl) as [Wl Wb].
        dsred. split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption
                              | split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]]]
                      | split; [reflexivity | intros _; reflexivity]]; try exact Wl; try exact Wb.
        all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo). all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
        all: try (clear - C2 Hbs Hu Hmt Hp Hpo Sl; lia).
        all: first [pose proof (INS (ds_insert t) ltac:(clear - Hins Hinsw; lia)); clear - H Hins Hu; lia
                   | match goal with |- ?g => idtac "GOAL" g end].
  Qed.

  Local Ltac si_rest HK Hm Hst Ho Hp := split; [exact HK | split; [exact Hm | split; [exact Hst | split; [exact Ho | exact Hp]]]].

  Lemma hw_stage : forall t, SI t -> SI (hw_st t) /\ ds_strm (hw_st t) = ds_strm t /\ ds_strstart (hw_st t) = ds_strstart t
    /\ ds_block_start (hw_st t) = ds_block_start t /\ ds_window_size (hw_st t) = ds_window_size t /\ ds_w_size (hw_st t) = ds_w_size t /\ ds_insert (hw_st t) = ds_insert t.
  Proof.
    intros t HS. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold hw_st. destruct (Z.ltb_spec (ds_high_water t) (ds_strstart t)) as [C|C]; [| split; [exact HS | repeat split; reflexivity]].
    dsred. split; [| repeat split; reflexivity].
    split; [| si_rest HK Hm Hst Ho Hp].
    match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hbs Hstr Sw; lia | rewrite Ewsz; clear - Hstr; lia
               | clear - Hp Hpo Sl; lia | intros _; exact Hpo | apply (SV_strm c0 t); [reflexivity | exact V]].
  Qed.

  Lemma slide3_stage : forall t have, SI t -> have = 2 * ds_w_size t - ds_strstart t ->
    let r := st_slide3 t have in
    SI (fst r) /\ ds_strm (fst r) = ds_strm t /\ snd r = 2 * ds_w_size t - ds_strstart (fst r) /\ ds_w_size (fst r) = ds_w_size t.
  Proof.
    intros t have HS Hhave r. subst r. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold st_slide3.
    destruct (Z.ltb_spec have (cs_avail_in (ds_strm t))) as [C1|C1]; [| cbn [andb fst snd]; split; [exact HS | repeat split; try reflexivity; exact Hhave]].
    destruct (Z.leb_spec (ds_w_size t) (ds_block_start t)) as [C2|C2]; cbn [andb fst snd]; [| split; [exact HS | repeat split; try reflexivity; exact Hhave]].
    pose proof (window_blit_bytes t 0 (ds_w_size t) (ds_strstart t - ds_w_size t) D) as [Bl Bb].
    specialize (Bb ltac:(intros j Hj; clear - Hj C2 Hbs Hstr Sw; lia)).
    dsred. destruct (Z.ltb_spec (ds_matches t) 2) as [C3|C3]; dsred; destruct (Z.ltb_spec (ds_strstart t - ds_w_size t) (ds_insert t)) as [C4|C4]; dsred;
      (split; [split; [match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption | si_rest HK Hm Hst Ho Hp]
             | split; [reflexivity | split; [rewrite wrap32_id by (clear - Hhave Hstr Hbs C2 Sw; lia); clear - Hhave; lia | reflexivity]]]).
    all: try exact Bl. all: try exact Bb. all: try exact (dx_hw _ X). all: try exact (df_bl _ D). all: try exact (df_bb _ D). all: try (intros _; exact Hpo).
    all: try (apply (SV_strm c0 t); [reflexivity | exact V]).
    all: clear - C1 C2 C3 C4 Hstr Hbs Sw Hmt Hp Hpo Sl Hins Hinsw; lia.
  Qed.

  Lemma fillw_stage : forall t n, SI t -> 0 <= n <= cs_avail_in (ds_strm t) -> n <= 2 * ds_w_size t - ds_strstart t ->
    let t' := st_fillw t n in
    SI t' /\ ds_strstart t' = ds_strstart t + n /\ ds_block_start t' = ds_block_start t /\ ds_w_size t' = ds_w_size t
    /\ cs_avail_in (ds_strm t') = cs_avail_in (ds_strm t) - n /\ cs_avail_out (ds_strm t') = cs_avail_out (ds_strm t)
    /\ ds_bi_valid t' = ds_bi_valid t /\ ds_pending_buf_size t' = ds_pending_buf_size t.
  Proof.
    intros t n HS Hn Hroom t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (sv_nin _ _ V) as Hni. pose proof (sv_inlen _ _ V) as Hil. rewrite <- (sv_input _ _ V) in Hil.
    unfold st_fillw.
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    { split; [exact HS|]. rewrite N0, Z.add_0_r, Z.sub_0_r. repeat split; reflexivity. }
    unfold read_buf. cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm t))) by (clear - Hn N0; lia).
    replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0). cbv iota beta.
    set (bytes := arr_slice (cs_input (ds_strm t)) (cs_next_in (ds_strm t)) n).
    assert (Hb : forall b, In b bytes -> 0 <= b < 256) by (subst bytes; apply input_slice_bytes; [exact V | exact Hni | clear - Hil Hn; lia]).
    set (ad := if ds_wrap t =? 1 then adler32_upd (cs_adler (ds_strm t)) bytes else if ds_wrap t =? 2 then crc32_upd (cs_adler (ds_strm t)) bytes else cs_adler (ds_strm t)).
    assert (Had : 0 <= ad < 2 ^ 64).
    { subst ad. destruct (ds_wrap t =? 1); [apply adler32_upd_range; exact Hb|]. destruct (ds_wrap t =? 2); [pose proof (crc32_upd_range (cs_adler (ds_strm t)) _ Hb); lia|]. exact (sv_adler _ _ V). }
    set (ST := mkCS (cs_input (ds_strm t)) (cs_next_in (ds_strm t) + n) (cs_avail_in (ds_strm t) - n) (cs_out_rev (ds_strm t))
                    (cs_avail_out (ds_strm t)) (wrap64 (cs_total_in (ds_strm t) + n)) (cs_total_out (ds_strm t)) (cs_msg (ds_strm t)) (cs_data_type (ds_strm t)) ad).
    set (w := arr_upd (ds_window t) (ds_strstart t) bytes).
    match goal with |- SI ?x /\ _ => assert (Ex : x = set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)));
      [subst ST ad w; unfold ins_add; dsred; destruct (ds_wrap t =? 1); [| destruct (ds_wrap t =? 2)]; destruct t; cbn; destruct ds_strm; reflexivity | rewrite Ex] end.
    destruct (window_upd_bytes t (ds_strstart t) bytes D Hb) as [Wl Wb]. fold w in Wl, Wb.
    pose proof (ins_add_eq (ds_insert t) n (ds_w_size t) ltac:(clear - Hins Hinsw; lia) ltac:(clear - Sw; lia) ltac:(clear - Hn; lia)) as [Ei Ri].
    assert (Ri2 : ins_add (ds_insert t) n (ds_w_size t) <= ds_insert t + n) by (rewrite Ei; destruct (Z.ltb_spec n (ds_w_size t - ds_insert t)) as [l|l]; clear - Hins l Hn; lia).
    assert (V' : SV c0 (set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)))).
    { constructor; cbn.
      - exact (sv_input _ _ V).
      - clear - Hni Hn. lia.
      - rewrite (sv_input _ _ V) in Hil. clear - Hil. lia.
      - clear - Hai Hn. lia.
      - exact (sv_out _ _ V).
      - exact (sv_aout _ _ V).
      - exact (sv_grow _ _ V).
      - exact (sv_outb _ _ V).
      - apply wrap64_range'.
      - exact (sv_tout _ _ V).
      - exact Had.
      - exact (sv_dt _ _ V).
      - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
    dsred. split; [| cbn; repeat split; reflexivity].
    assert (Ho' : OUTLE s0 (set_insert (set_strstart (set_strm (set_window t w) ST) (ds_strstart t + n)) (ins_add (ds_insert t) n (ds_w_size t)))) by (apply (OUTLE_trans _ t); [exact Ho | apply OUTLE_out; cbn; reflexivity]).
    split; [| si_rest HK Hm Hst Ho' Hp].
    match goal with |- DC _ ?x => apply (DC_SF_transfer c0 t x HDC Hm) end; dsred; try reflexivity; try assumption.
    all: first [clear - Hbs Hn; lia | clear - Hroom Hn Hstr; lia | clear - Ri Ri2 Hins Hn; lia | clear - Ri; lia | exact (dx_hw _ X)
               | exact (df_bl _ D) | exact (df_bb _ D) | clear - Hp Hpo Sl; lia | intros _; exact Hpo].
  Qed.

  Lemma DC_upd4_st0 : forall a A P, SI a ->
    arr_len A = arr_len (ds_pending_buf a) -> (forall i, 0 <= i < ds_lit_bufsize a * 4 -> 0 <= arr_get A i < 256) -> 0 <= P <= ds_lit_bufsize a * 4 ->
    DC c0 (upd4 a A P 0 0) /\ SF (upd4 a A P 0 0) = SF a /\ ds_strm (upd4 a A P 0 0) = ds_strm a.
  Proof.
    intros a A P HS HlenA HbA HP. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts a HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    split; [| split; reflexivity].
    apply (DC_SF_transfer c0 a (upd4 a A P 0 0) HDC Hm); unfold upd4; dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | rewrite HlenA; exact (df_bl _ D) | clear - Hpo; lia | clear - HP; lia
               | clear - HP Hpo; lia | intros _; exact Hpo | clear; lia | apply (SV_strm c0 a); [reflexivity | exact V]].
  Qed.

  Lemma SI_set_block_start : forall a v, SI a -> 0 <= v <= ds_strstart a -> DC c0 (set_block_start a v) /\ SF (set_block_start a v) = SF a.
  Proof.
    intros a v HS Hv. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts a HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    split; [| reflexivity].
    apply (DC_SF_transfer c0 a (set_block_start a v) HDC Hm); dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
               | clear - Hp Hpo Sl; lia | intros _; exact Hpo | apply (SV_strm c0 a); [reflexivity | exact V]].
  Qed.

  Lemma DC_set_block_start : forall a v, DC c0 a -> dmode a = 0 -> 0 <= v <= ds_strstart a -> DC c0 (set_block_start a v).
  Proof.
    intros a v HDC Hm Hv. pose proof HDC as [[D X] V]. pose proof (dwf_sizes a D) as (Sw & Sh & Sl & _).
    destruct (dx_st0 _ X Hm) as (Hl0 & Hbs & Hsn & Hmt). pose proof (df_sl _ D) as Hsl. pose proof (df_pend _ D) as Hpd. pose proof (df_bi _ D) as Hbi.
    pose proof (RefDeflSafeI1.dx_matches _ X) as M. unfold nsym in M. rewrite Hsn in M. change (0 / 3 + 2) with 2 in M.
    pose proof (dx_biv _ X) as B7.
    apply (DC_SF_transfer c0 a (set_block_start a v) HDC Hm); dsred; try reflexivity; try assumption.
    all: first [exact (df_wl _ D) | exact (df_wb _ D) | exact (df_ins _ D) | exact (dx_ins _ X) | exact (df_hw _ D) | exact (dx_hw _ X) | exact (df_bl _ D) | exact (df_bb _ D)
               | exact (dx_pout0 _ X) | apply (SV_strm c0 a); [reflexivity | exact V] | clear - Hsl Hl0 Hpd Hbi B7; lia].
  Qed.

  Lemma final_stage : forall t, SI t ->
    let r := st_final t flush in
    DC c0 (fst r) /\ KV (fst r) = KV s0 /\ OUTLE s0 (fst r) /\ ds_lookahead (fst r) = 0
    /\ (snd r = finish_started \/ snd r = need_more).
  Proof.
    intros t HS r. subst r. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
    unfold st_final. cbv zeta.
    match goal with |- context [if ?c then _ else (t, need_more)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [exact HDC|]. split; [exact HK|]. split; [exact Ho|]. split; [exact Hl0 | right; reflexivity]. }
    pose proof (t_have_eq t ltac:(clear - Hbv; lia) ltac:(rewrite Epbs; clear - Sl; lia)) as (Eh & Rh & Rhdr).
    assert (Hleft : wrap32 (ds_strstart t - ds_block_start t) = ds_strstart t - ds_block_start t) by (apply wrap32_id; clear - Hbs Hstr Sw; lia).
    rewrite Hleft.
    assert (Hhv : t_have t <= ds_pending_buf_size t - (ds_bi_valid t + 42) / 2 ^ 3).
    { rewrite Eh. destruct (Z.ltb_spec (ds_pending_buf_size t - (ds_bi_valid t + 42) / 2 ^ 3) 65536) as [l|l]; clear - l Rhdr Epbs Sl; lia. }
    set (len := MIN (ds_strstart t - ds_block_start t) (t_have t)).
    assert (Hlen : 0 <= len <= t_have t /\ len <= ds_strstart t - ds_block_start t).
    { subst len. unfold MIN. destruct (Z.ltb_spec (t_have t) (ds_strstart t - ds_block_start t)) as [l|l]; clear - l Rh Hbs; lia. }
    set (last := if (flush =? Z_FINISH) && (cs_avail_in (ds_strm t) =? 0) && (len =? ds_strstart t - ds_block_start t) then 1 else 0). clearbody last.
    pose proof (tsb_hP_range t) as HP. rewrite Hp in HP.
    pose proof (sb_hdr_eq' t ltac:(clear - Hbv; lia)) as EP. rewrite Hp in EP. pose proof (proj1 (sb_hdr_eq t ltac:(clear - Hbv; lia))) as Ehdr.
    rewrite (tr_stored_block_eq t (Some (ds_block_start t)) len last ltac:(clear - Hbv; lia) Hbb). unfold tsb_tail. cbv zeta.
    set (A2 := tsb_lenA (tsb_hA t last) (tsb_hP t) len).
    set (A3 := if negb (len =? 0) then arr_blit A2 (tsb_hP t + 1 + 1 + 1 + 1) (ds_window t) (ds_block_start t) len else A2).
    set (P := tsb_hP t + 1 + 1 + 1 + 1 + len).
    assert (HAb : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get (tsb_hA t last) i < 256).
    { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
    assert (HA2b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A2 i < 256) by (subst A2; unfold tsb_lenA; bytes_tac HAb).
    assert (HA3b : forall i, 0 <= i < ds_lit_bufsize t * 4 -> 0 <= arr_get A3 i < 256).
    { subst A3. destruct (negb (len =? 0)); [| exact HA2b]. intros i Hi. rewrite arr_get_blit.
      match goal with |- 0 <= (if ?c then _ else _) < 256 => destruct c eqn:E end; [| apply HA2b; exact Hi].
      apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply (df_wb _ D). clear - E1 E2 Hlen Hbs Hstr. lia. }
    assert (HA3len : arr_len A3 = arr_len (ds_pending_buf t)).
    { subst A3 A2. destruct (negb (len =? 0)); rewrite ?arr_len_blit; unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len. }
    destruct (DC_upd4_st0 t A3 P HS HA3len HA3b ltac:(subst P; clear - HP Hlen Hhv Epbs EP Ehdr; rewrite Ehdr in EP; lia)) as (DC1 & ESF1 & Estrm1).
    set (X1 := upd4 t A3 P 0 0) in *.
    assert (DC2 : DC c0 (set_block_start X1 (ds_block_start X1 + len))).
    { apply (DC_set_block_start X1 _ DC1 ltac:(rewrite (dmode_SF _ _ ESF1); exact Hm)). subst X1; unfold upd4; dsred. clear - Hbs Hlen. lia. }
    set (X2 := set_block_start X1 (ds_block_start X1 + len)) in *.
    pose proof (DC_flush_pending c0 X2 HC0w DC2) as FPF. cbv zeta in FPF.
    destruct FPF as (DC3 & KV3 & Ho3 & Ecore & _).
    pose proof (dx_core2_fields _ _ Ecore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elook3 & _).
    cbn [fst snd]. split; [exact DC3|].
    split; [rewrite KV3; subst X2 X1; unfold upd4; dsred; exact HK|].
    split; [apply (OUTLE_trans _ X2); [apply (OUTLE_trans _ t); [exact Ho | apply OUTLE_strm; subst X2 X1; reflexivity] | exact Ho3]|].
    split; [rewrite Elook3; subst X2 X1; unfold upd4; dsred; exact Hl0|].
    destruct (negb (last =? 0)); [left | right]; reflexivity.
  Qed.
  Lemma rdo_stage0 : forall t n, SI t -> 0 <= n <= cs_avail_in (ds_strm t) -> n <= cs_avail_out (ds_strm t) ->
    SI (st_rdo t n) /\ cs_avail_in (ds_strm (st_rdo t n)) = cs_avail_in (ds_strm t) - n.
  Proof.
    intros t n HS Hn Hna. destruct (Z.eq_dec n 0) as [N0|N0].
    - subst n. unfold st_rdo. cbn [negb Z.eqb]. split; [exact HS | lia].
    - pose proof (rdo_stage t n HS ltac:(lia) Hna) as R. cbv zeta in R. destruct R as (R1 & _ & _ & _ & _ & R6 & _). exact (conj R1 R6).
  Qed.

  Lemma trip_stage : forall t mb, SI t -> sb_broke t flush mb = false ->
    let t' := st_trip t flush in SI t' /\ cs_avail_in (ds_strm t') <= cs_avail_in (ds_strm t).
  Proof.
    intros t mb HS Hb t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold sb_broke in Hb. apply Bool.orb_false_iff in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb.
    pose proof (sb_len_range t ltac:(clear - Hai; lia) Hb) as (Rl1 & Rl2 & Rl3).
    pose proof (sb_len1_eq t ltac:(clear - Hai; lia)) as (_ & _ & Rl4).
    assert (Eleft : sb_left t = ds_strstart t - ds_block_start t) by (unfold sb_left; apply wrap32_id; clear - Hbs Hstr Sw; lia).
    unfold st_trip.
    pose proof (emit_stage t HS Hb) as E. cbv zeta in E. destruct E as (HS3 & ESF3 & ELZ3 & Ebs3 & Eao3 & Eai3 & Eni3 & Ein3).
    pose proof (LZS_fields _ _ ELZ3) as (Ew3 & Estr3 & _).
    set (t3 := st_emit1 t flush) in *. clearbody t3.
    unfold st_copy. rewrite Eleft in Rl4 |- *.
    destruct (Z.eqb_spec (ds_strstart t - ds_block_start t) 0) as [L0|L0]; cbn [negb fst snd].
    - destruct (rdo_stage0 t3 (sb_len t) HS3 ltac:(rewrite Eai3; clear - Rl1 Rl3 Rl4 L0; lia) ltac:(rewrite Eao3; exact Rl2)) as [HS5 Eai5].
      split; [exact HS5|]. rewrite Eai5, Eai3. clear - Rl1. lia.
    - set (l := lc_len (ds_strstart t - ds_block_start t) (sb_len t)).
      assert (Hl : 0 <= l <= sb_len t /\ l <= ds_strstart t - ds_block_start t /\ sb_len t - l <= cs_avail_in (ds_strm t)).
      { subst l. unfold lc_len. destruct (Z.ltb_spec (sb_len t) (ds_strstart t - ds_block_start t)) as [l0|l0]; clear - l0 Rl1 Rl3 Rl4 Hbs Hai; lia. }
      pose proof (lcopy_stage t3 l HS3 ltac:(clear - Hl; lia) ltac:(rewrite Ebs3, Estr3; clear - Hl; lia) ltac:(rewrite Eao3; clear - Hl Rl2; lia)) as C. cbv zeta in C.
      destruct C as (HS4 & _ & _ & _ & Eao4 & Eai4 & _).
      set (t4 := st_lcopy t3 l) in *. clearbody t4.
      destruct (rdo_stage0 t4 (sb_len t - l) HS4 ltac:(rewrite Eai4, Eai3; clear - Hl; lia) ltac:(rewrite Eao4, Eao3; clear - Hl Rl2; lia)) as [HS5 Eai5].
      split; [exact HS5|]. rewrite Eai5, Eai4, Eai3. clear - Hl. lia.
  Qed.

  Lemma loop_stage : forall fuel t mb, SI t ->
    SI (fst (deflate_stored_loop fuel t flush mb)) /\ cs_avail_in (ds_strm (fst (deflate_stored_loop fuel t flush mb))) <= cs_avail_in (ds_strm t).
  Proof.
    induction fuel as [|f IH]; intros t mb HS.
    - cbn [deflate_stored_loop fst]. split; [exact HS | lia].
    - rewrite sloop_S'. destruct (sb_broke t flush mb) eqn:Hb; [cbn [fst]; split; [exact HS | lia]|].
      pose proof (trip_stage t mb HS Hb) as T. cbv zeta in T. destruct T as [HS1 Hai1].
      destruct (sb_lastv t flush =? 0).
      + destruct (IH (st_trip t flush) mb HS1) as [HS2 Hai2]. split; [exact HS2 | lia].
      + cbn [fst]. split; [exact HS1 | exact Hai1].
  Qed.

End Stored.


Theorem stored_bf_spec : BF_SPEC 0 stored_safe deflate_stored.
Proof.
  intros c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm. pose proof (c0'_ok _ HC0) as HC0w.
  assert (HS : SI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hm|]. split; [exact Hst|]. split; [apply OUTLE_refl | exact Hp]. }
  pose proof HDC as [[D X] V].
  pose proof (SI_facts c0 s HC0 s HS) as (_ & _ & _ & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & _).
  split; [exact (stored_safe_intro s flush (SI_st_entry c0 s HC0 s HS) (dwf_DWF s D Hao))|].
  rewrite deflate_stored_eq. cbv zeta.
  set (mb := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))). clearbody mb.
  set (fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1)). clearbody fuel.
  destruct (loop_stage c0 s flush HC0 fuel s mb HS) as [HSL HaiL].
  set (sL := fst (deflate_stored_loop fuel s flush mb)) in *. clearbody sL.
  set (last := snd (deflate_stored_loop fuel s flush mb)). clearbody last.
  pose proof (SI_facts c0 s HC0 sL HSL) as (DL & XL & VL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HaiL2 & _).
  assert (Eused : wrap32 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) = cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))
    by (apply wrap32_id; clear - HaiL Hai HaiL2; lia).
  rewrite Eused.
  pose proof (sv_inlen _ _ V) as Il. pose proof (sv_inlen _ _ VL) as IlL. pose proof (sv_nin _ _ V) as Ni.
  pose proof (wupd_stage c0 s HC0 sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) HSL ltac:(clear - HaiL Il IlL Ni; lia)) as W. cbv zeta in W.
  destruct W as (HSW & EstrmW & HbsW).
  set (sW := st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))) in *. clearbody sW.
  pose proof (hw_stage c0 s HC0 sW HSW) as (HS2 & Estrm2 & Estr2 & Ebs2 & Ewsz2 & Ews2 & _).
  set (s2 := hw_st sW) in *. clearbody s2.
  pose proof HS2 as (HDC2 & HK2 & Hm2 & Hst2 & Ho2 & Hp2).
  pose proof (SI_facts c0 s HC0 s2 HS2) as (D2 & X2 & V2 & Sw2 & _ & _ & Hl02 & Hbs2 & _ & _ & Hstr2 & Ewsz2' & _ & _ & _ & _ & _ & Hai2 & _).
  destruct (negb (last =? 0)).
  { unfold BFPOST; cbn [fst snd]. split; [exact HDC2|]. split; [exact HK2|]. split; [exact Ho2|].
    split; [intros HH; discriminate HH|]. split; [intros _; exact Hl02|]. intros _. exact Hp2. }
  match goal with |- context [if ?c then (s2, block_done) else _] => destruct c eqn:Hcond end.
  { unfold BFPOST; cbn [fst snd]. split; [exact HDC2|]. split; [exact HK2|]. split; [exact Ho2|].
    split.
    - intros _. split; [exact Hp2|]. split; [| exact (dx_notslow _ X2 ltac:(rewrite Hm2; lia))].
      apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [_ Hcond].
      intros F4. rewrite F4 in Hcond. cbn in Hcond. discriminate Hcond.
    - split; [intros [HH|HH]; discriminate HH | intros HH; discriminate HH]. }
  assert (Ehave : wrap32 (ds_window_size s2 - ds_strstart s2) = 2 * ds_w_size s2 - ds_strstart s2) by (rewrite Ewsz2'; apply wrap32_id; clear - Hstr2 Hbs2 Sw2; lia).
  rewrite Ehave.
  pose proof (slide3_stage c0 s HC0 s2 _ HS2 eq_refl) as SL3. cbv zeta in SL3. destruct SL3 as (HS3 & Estrm3 & Ehave3 & Ews3).
  destruct (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2)) as [s3 have]. cbn [fst snd] in *.
  pose proof (SI_facts c0 s HC0 s3 HS3) as (_ & _ & _ & _ & _ & _ & _ & Hbs3 & _ & _ & Hstr3 & _ & _ & _ & _ & _ & _ & Hai3 & _).
  assert (Hfm : 0 <= fmin have (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3) /\ fmin have (cs_avail_in (ds_strm s3)) <= 2 * ds_w_size s3 - ds_strstart s3).
  { unfold fmin. rewrite Ehave3, Ews3. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) (2 * ds_w_size s2 - ds_strstart s3)) as [l|l]; clear - l Hai3 Hstr3 Hbs3 Ews3; lia. }
  pose proof (fillw_stage c0 s HC0 s3 (fmin have (cs_avail_in (ds_strm s3))) HS3 (proj1 Hfm) (proj2 Hfm)) as FW. cbv zeta in FW. destruct FW as (HS4 & _).
  set (s4 := st_fillw s3 (fmin have (cs_avail_in (ds_strm s3)))) in *. clearbody s4.
  pose proof (hw_stage c0 s HC0 s4 HS4) as (HS5 & _).
  set (s5 := hw_st s4) in *. clearbody s5.
  pose proof (final_stage c0 s flush HC0 s5 HS5) as FN. cbv zeta in FN. destruct FN as (DCf & KVf & Hof & Hlf & Hbsf).
  destruct (st_final s5 flush) as [sf bs]. cbn [fst snd] in *.
  unfold BFPOST; cbn [fst snd]. split; [exact DCf|]. split; [exact KVf|]. split; [exact Hof|].
  split; [intros ->; destruct Hbsf as [HH|HH]; discriminate HH|].
  split; [intros _; exact Hlf|]. intros ->. destruct Hbsf as [HH|HH]; discriminate HH.
Qed.
End RefDeflSafeL0.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma fw_rest_fields : forall s s', fw_rest s' = fw_rest s ->
  (ds_status s' = ds_status s /\ ds_pending_buf s' = ds_pending_buf s /\ ds_pending_buf_size s' = ds_pending_buf_size s
   /\ ds_pending_out s' = ds_pending_out s /\ ds_pending s' = ds_pending s /\ ds_wrap s' = ds_wrap s /\ ds_gzhead s' = ds_gzhead s
   /\ ds_gzindex s' = ds_gzindex s /\ ds_method s' = ds_method s /\ ds_last_flush s' = ds_last_flush s /\ ds_w_size s' = ds_w_size s
   /\ ds_w_bits s' = ds_w_bits s /\ ds_w_mask s' = ds_w_mask s /\ ds_window_size s' = ds_window_size s /\ ds_hash_size s' = ds_hash_size s
   /\ ds_hash_bits s' = ds_hash_bits s /\ ds_hash_mask s' = ds_hash_mask s /\ ds_hash_shift s' = ds_hash_shift s
   /\ ds_match_length s' = ds_match_length s /\ ds_prev_match s' = ds_prev_match s /\ ds_match_available s' = ds_match_available s
   /\ ds_prev_length s' = ds_prev_length s)
  /\ (ds_max_chain_length s' = ds_max_chain_length s /\ ds_max_lazy_match s' = ds_max_lazy_match s /\ ds_level s' = ds_level s
      /\ ds_strategy s' = ds_strategy s /\ ds_good_match s' = ds_good_match s /\ ds_nice_match s' = ds_nice_match s
      /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
      /\ ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s /\ ds_bl_tree_fc s' = ds_bl_tree_fc s /\ ds_bl_tree_dl s' = ds_bl_tree_dl s
      /\ ds_l_max_code s' = ds_l_max_code s /\ ds_d_max_code s' = ds_d_max_code s /\ ds_bl_max_code s' = ds_bl_max_code s
      /\ ds_bl_count s' = ds_bl_count s /\ ds_heap s' = ds_heap s /\ ds_heap_len s' = ds_heap_len s /\ ds_heap_max s' = ds_heap_max s
      /\ ds_depth s' = ds_depth s /\ ds_lit_bufsize s' = ds_lit_bufsize s /\ ds_sym_next s' = ds_sym_next s /\ ds_sym_end s' = ds_sym_end s
      /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s /\ ds_matches s' = ds_matches s
      /\ ds_bi_buf s' = ds_bi_buf s /\ ds_bi_valid s' = ds_bi_valid s)
  /\ (cs_input (ds_strm s') = cs_input (ds_strm s) /\ cs_out_rev (ds_strm s') = cs_out_rev (ds_strm s)
      /\ cs_avail_out (ds_strm s') = cs_avail_out (ds_strm s) /\ cs_total_out (ds_strm s') = cs_total_out (ds_strm s)
      /\ cs_msg (ds_strm s') = cs_msg (ds_strm s) /\ cs_data_type (ds_strm s') = cs_data_type (ds_strm s)).
Proof.
  intros s s' E. unfold fw_rest in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.


Lemma dwf_wk : forall s, dwf s -> 0 <= ds_w_bits s /\ ds_w_size s = 2 ^ ds_w_bits s.
Proof. intros s D. pose proof (df_wbits _ D). split; [lia | exact (df_wsize _ D)]. Qed.

Definition adler_ok (s : deflate_state) : Prop := 0 <= cs_adler (ds_strm s) < 2 ^ 64.

Lemma DX_FWX : forall s, dwf s -> DX s -> adler_ok s -> dmode s <> 0 -> FWX s.
Proof.
  intros s D X Ha Hm. constructor.
  - exact (dx_chain _ X Hm).
  - exact (dx_insh _ X).
  - exact (dx_ins _ X).
  - exact (dx_hw _ X).
  - exact Ha.
Qed.

Lemma DC_fill_window : forall c0 s, C0OK c0 -> DC c0 s -> dmode s <> 0 -> ds_status s <> FINISH_STATE ->
  ds_lookahead s < MIN_LOOKAHEAD ->
  let s' := fill_window s in
  DC c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ fw_rest s' = fw_rest s
  /\ ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s
  /\ ds_lookahead s <= ds_lookahead s' <= 2 * ds_w_size s
  /\ (ds_lookahead s' < MIN_LOOKAHEAD -> cs_avail_in (ds_strm s') = 0 /\ ds_strstart s' + ds_lookahead s' <= 2 * ds_w_size s - 2)
  /\ fw_wf (ds_w_size s) (ds_hash_size s) s'
  /\ ds_strstart s' <= 2 * ds_w_size s - MIN_LOOKAHEAD - 1
  /\ (1 <= ds_strstart s -> 1 <= ds_strstart s')
  /\ wrap32 (ds_strstart s' - ds_match_start s') = wrap32 (ds_strstart s - ds_match_start s).
Proof.
  intros c0 s HC0 HDC Hm Hst Hlook s'. subst s'. pose proof HDC as [[D X] V].
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh).
  assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
  pose proof (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
                (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)) as HW.
  pose proof (fill_window_facts (ds_w_size s) (ds_hash_size s) s HW Hlook) as (HW' & HC' & HK' & HL' & HA' & HX').
  pose proof (fill_window_FWX (ds_w_size s) (ds_hash_size s) (ds_w_bits s) (dwf_wk s D) s HW (DX_FWX s D X (sv_adler _ _ V) Hm) Hlook) as (FX' & G' & SL' & SS' & S1' & LL').
  pose proof (fw_rest_fill_window s) as R'.
  set (s' := fill_window s) in *.
  pose proof (fw_rest_fields s s' R') as (R1 & R2 & R3).
  destruct R1 as (Est & Epb & Epbs & Epo & Epd & Ewr & Egz & Egi & Eme & Elf & Ews & Ewb & Ewm & Ewsz & Ehs & Ehb & Ehm & Ehsh & Eml & Epm & Ema & Epl).
  destruct R2 as (Emc & Elz & Elv & Esy & Egm & Enm & Elfc & Eldl & Edfc & Eddl & Ebfc & Ebdl & Elmc & Edmc & Ebmc & Eblc & Ehp & Ehpl & Ehpm & Edep & Elbs & Esn & Ese & Eol & Esl & Emt & Ebb & Ebv).
  destruct R3 as (Ein & Eout & Eao & Eto & Emsg & Edt).
  pose proof (fwG_fields s s' G') as (EKV & Eext & Enin & _ & Ewms).
  pose proof HW' as W. destruct W.
  apply pair_equal_spec in EKV. destruct EKV as [EKV3 EB].
  assert (Eb1 : ds_window_blk s' = ds_window_blk s) by congruence.
  assert (Eb2 : ds_prev_blk s' = ds_prev_blk s) by congruence.
  assert (Eb3 : ds_head_blk s' = ds_head_blk s) by congruence.
  assert (Eb4 : ds_pending_buf_blk s' = ds_pending_buf_blk s) by congruence.
  assert (D' : dwf s').
  { destruct D; constructor; rewrite ?Est, ?Epb, ?Epbs, ?Epo, ?Epd, ?Ewr, ?Egz, ?Eme, ?Elf, ?Ews, ?Ewb, ?Ewm, ?Ewsz, ?Ehs, ?Ehb, ?Ehm, ?Ehsh,
      ?Elv, ?Esy, ?Elbs, ?Ese, ?Ebb, ?Ebv, ?Eb1, ?Eb2, ?Eb3, ?Eb4; try assumption.
    - unfold deflateStateCheck in *. rewrite Est. assumption.
    - unfold tree_lens in *. rewrite Elfc, Eldl, Edfc, Eddl, Ebfc, Ebdl, Eblc, Ehp, Edep. assumption.
    - clear - wf_ins wf_sl wf_look Sw. lia. }
  assert (X' : DX s').
  { pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
    pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Em' : dmode s' = dmode s) by (unfold dmode; rewrite Elv, Esy; reflexivity).
    assert (En' : nsym s' = nsym s) by (unfold nsym; rewrite Esn; reflexivity).
    destruct X; constructor; rewrite ?Em', ?En', ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Eml, ?Epl, ?Ema, ?Epm, ?Emt, ?Ewr, ?Est, ?Esn, ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv;
      try assumption.
    - exact (fx_insh _ FX').
    - exact (fx_ins _ FX').
    - exact (fx_hw _ FX').
    - intros Hm4. destruct (dx_slow Hm4) as (A1 & A2 & A3). split; [exact A1|]. split; [intros Hma; exact (S1' (A2 Hma))|].
      intros H3. destruct (A3 H3) as (A4 & A6 & A5). rewrite Ewms, Ews. split; [clear - A4 HL'; lia | split; [exact (S1' A6) | exact A5]].
    - intros Hm0. exfalso. exact (Hm Hm0).
    - intros Hf. exfalso. exact (Hst Hf).
    - intros j Hj. apply (sym_okb_same s s' j Epb Elbs). exact (Xsyms j Hj).
    - apply (freq_hist_same s s' Epb Elbs Esn Elfc Edfc Ebfc). exact Xhist.
    - rewrite Eext. assumption.
    - intros t i. destruct t; cbn [tree_fc]; rewrite ?Elfc, ?Edfc, ?Ebfc; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
    - intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
    - intros i. rewrite Edep. apply Xdepth.
    - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
    - intros _. exact (fx_chain _ FX'). }
  assert (V' : SV c0 s').
  { destruct HK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kout & Kao & Kto & Ksum).
    constructor; rewrite ?Ein, ?Eout, ?Eao, ?Eto, ?Edt.
    - exact (sv_input _ _ V).
    - assumption.
    - rewrite Enin. exact (sv_inlen _ _ V).
    - assumption.
    - exact (sv_out _ _ V).
    - exact (sv_aout _ _ V).
    - exact (sv_grow _ _ V).
    - exact (sv_outb _ _ V).
    - assumption.
    - exact (sv_tout _ _ V).
    - exact (fx_ad _ FX').
    - exact (sv_dt _ _ V).
    - rewrite <- Ein. assumption. }
  split; [exact (conj (conj D' X') V')|].
  split; [unfold KV; rewrite EB, Ews, Ehs, Elbs; reflexivity|].
  split; [apply OUTLE_out; exact Eout|].
  split; [exact R'|]. split; [exact Eext|]. split; [exact HL'|]. split; [| split; [exact HW' | split; [exact SS' | split; [exact S1' | exact Ewms]]]].
  intros Hl'. split; [exact (HX' Hl') | exact (SL' Hl')].
Qed.



Section Fast.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hfl : 0 <= flush <= 5.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition FTI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 3 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma FTI_facts : forall s, FTI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
    /\ ds_prev_length s = 2 /\ ds_match_length s < MIN_MATCH /\ ds_match_available s = 0
    /\ 0 <= nsym s <= ds_lit_bufsize s - 2 /\ ds_sym_next s = 3 * nsym s /\ ds_sym_end s = (ds_lit_bufsize s - 1) * 3
    /\ 0 <= ds_strstart s /\ 0 <= ds_lookahead s /\ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s
    /\ 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s.
  Proof.
    intros s (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (dx_fast _ X Hm) as [Hpl Hml]. pose proof (dx_notslow _ X ltac:(rewrite Hm; lia)) as Hma.
    pose proof (dx_nsym _ X). pose proof (dx_sn _ X). pose proof (df_symend _ D). pose proof (df_strstart _ D). pose proof (df_look _ D). pose proof (df_sl _ D).
    pose proof (dx_ext _ X ltac:(rewrite Hm; lia)) as He. rewrite Hma in He.
    repeat (split; [assumption|]). lia.
  Qed.

  Lemma fill_stage : forall s, FTI s ->
    let r := st_fill s flush in
    FTI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ 0 <= ds_lookahead s <= 2 * ds_w_size s
    /\ (ds_lookahead s < MIN_LOOKAHEAD -> fw_wf (ds_w_size s) (ds_hash_size s) s)
    /\ 0 <= ds_lookahead (fst r) <= 2 * ds_w_size s
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r)
                       /\ (ds_lookahead (fst r) < MIN_LOOKAHEAD -> ds_strstart (fst r) + ds_lookahead (fst r) <= 2 * ds_w_size s - 2))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ ds_strstart (fst r) + MIN_LOOKAHEAD <= 2 * ds_w_size s
    /\ snd r <> Some LCont.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold st_fill.
    destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst Hlt) as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS' & _).
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _) & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : FTI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      destruct ((ds_lookahead (fill_window s) <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)) eqn:E1.
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
        split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; injection Hbs as <-; reflexivity|]. split; [clear - SS'; lia | intros HH; discriminate HH].
      + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia | intros HH; discriminate HH].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [lia|]. split; [intros _; exact HW|].
          split; [lia|]. split; [exact Ews'|]. split; [intros _; split; [lia | intros Hl; exact (proj2 (HX' Hl))]|].
          split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - SS'; lia | intros HH; discriminate HH].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [lia|]. split; [intros; lia|].
      split; [lia|]. split; [reflexivity|].
      split; [intros _; split; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hge; lia | intros; lia]|].
      split; [intros HH; discriminate HH|]. split; [intros bs Hbs; discriminate Hbs|]. split; [clear - Hge Hsl; lia | intros HH; discriminate HH].
  Qed.


  Definition TF (s : deflate_state) :=
    ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
     (ds_insert s, ds_w_size s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_matches s, ds_high_water s, ds_window_size s),
     (ds_block_start s, ds_wrap s, ds_status s, ds_lit_bufsize s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s),
     (ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
     (ds_strm s, ds_pending s, ds_pending_out s, ds_bi_valid s, ds_bi_buf s, ds_last_flush s, ds_window s, KV s, ds_sym_end s),
     (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_heap s)).

  Lemma TF_fields : forall a b, TF b = TF a ->
    (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
     /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
    /\ (ds_insert b = ds_insert a /\ ds_w_size b = ds_w_size a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
        /\ ds_prev_match b = ds_prev_match a /\ ds_matches b = ds_matches a /\ ds_high_water b = ds_high_water a /\ ds_window_size b = ds_window_size a)
    /\ (ds_block_start b = ds_block_start a /\ ds_wrap b = ds_wrap a /\ ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a
        /\ ds_bl_tree_fc b = ds_bl_tree_fc a /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a)
    /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
        /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
    /\ (ds_strm b = ds_strm a /\ ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a
        /\ ds_bi_buf b = ds_bi_buf a /\ ds_last_flush b = ds_last_flush a /\ ds_window b = ds_window a /\ KV b = KV a /\ ds_sym_end b = ds_sym_end a)
    /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
        /\ ds_method b = ds_method a /\ ds_heap b = ds_heap a).
  Proof.
    intros a b E. unfold TF in E.
    repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
    repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
    repeat split; assumption.
  Qed.

  Definition HREL (s1 s2 : deflate_state) : Prop :=
    TF s2 = TF s1 /\ ds_strstart s2 = ds_strstart s1 /\ ds_match_length s2 = ds_match_length s1 /\ ds_lookahead s2 = ds_lookahead s1
    /\ ds_sym_next s2 = ds_sym_next s1 /\ ds_match_start s2 = ds_match_start s1 /\ ds_pending_buf s2 = ds_pending_buf s1
    /\ ds_dyn_ltree_fc s2 = ds_dyn_ltree_fc s1 /\ ds_dyn_dtree_fc s2 = ds_dyn_dtree_fc s1
    /\ arr_len (ds_head s2) = arr_len (ds_head s1) /\ arr_len (ds_prev s2) = arr_len (ds_prev s1)
    /\ (forall i, 0 <= i < ds_hash_size s1 -> 0 <= arr_get (ds_head s2) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s1 -> 0 <= arr_get (ds_prev s2) i < 65536)
    /\ 0 <= ds_ins_h s2 < 65536
    /\ CHAIN s2 (ds_strstart s1) (ds_strstart s1).

  Lemma hash_stage : forall s1, FTI s1 -> 1 <= ds_lookahead s1 ->
    let r := st_hash s1 in
    HREL s1 (fst r)
    /\ (lm_cond (fst r) (snd r) = true ->
          Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited (fst r) (snd r))
          /\ 1 <= snd r <= ds_strstart s1 - 1 /\ ds_strstart s1 - snd r <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1).
  Proof.
    intros s1 HF Hl1 r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (dx_chain _ X ltac:(rewrite Hm; lia)) as HC. pose proof (dx_insh _ X) as Hih.
    unfold st_hash.
    destruct (Z.leb_spec MIN_MATCH (ds_lookahead s1)) as [Big|Small].
    - pose proof (insert_string_facts s1 (ds_strstart s1)) as IF. cbv zeta in IF.
      destruct IF as (Ehh & Eih & Ehd & Epv & Estrm & Ewin & Elook & Estr & Ebs & Eml & Esn & Elfc & Edfc & Epd & Epb & Ebv & Ebb & Eins & Epl & Ems & Hh).
      specialize (Hh ltac:(rewrite (df_hmask _ D); lia)). rewrite (df_hmask _ D) in Hh.
      destruct (CHAIN_insert_string s1 (ds_strstart s1) (ds_strstart s1 - 1) (ds_strstart s1 - 1) (ds_w_bits s1) HC
                  (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                  ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(lia)) as [HC2 Hhh].
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1)) with (ds_strstart s1) in HC2 by lia.
      replace (Z.max (ds_strstart s1 - 1) (ds_strstart s1 - 1)) with (ds_strstart s1 - 1) in HC2 by lia.
      set (s2 := fst (insert_string s1 (ds_strstart s1))) in *. set (hh := snd (insert_string s1 (ds_strstart s1))) in *.
      split.
      + unfold HREL. rewrite Ehd, Epv, !arr_len_set.
        split; [subst s2; rewrite insert_string_fst; reflexivity|].
        split; [exact Estr|]. split; [exact Eml|]. split; [exact Elook|]. split; [exact Esn|]. split; [exact Ems|]. split; [exact Epb|].
        split; [exact Elfc|]. split; [exact Edfc|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply (df_hb _ D); exact Hi]|].
        split; [intros i Hi; rewrite arr_get_set; destruct (_ && _); [apply (df_hb _ D); lia | apply (df_pb _ D); exact Hi]|].
        split; [rewrite Eih; lia|].
        eapply CHAIN_mono; [| | exact HC2]; lia.
      + intros Hlm. unfold lm_cond in Hlm. apply andb_prop in Hlm as [Hnz Hdist].
        assert (Hhh0 : hh <> 0) by (intros E0; rewrite E0 in Hnz; discriminate Hnz).
        assert (Hhh1 : 1 <= hh <= ds_strstart s1 - 1) by (destruct Hhh as [Z0|B]; [exfalso; exact (Hhh0 Z0) | exact B]).
        rewrite Estr in Hdist. apply Z.leb_le in Hdist. rewrite wrap32_id in Hdist by lia.
        split; [| split; [lia | split; [change (ds_w_size s2) with (ds_w_size s1) in Hdist; lia | exact Big]]].
        pose proof (lm_visited_bound s1 (ds_strstart s1) (ds_w_bits s1) HC (df_wsize _ D) ltac:(pose proof (df_wbits _ D); lia) (df_wmask _ D) (df_pl _ D) (df_hl _ D)
                      ltac:(rewrite (df_hmask _ D); lia) (df_hmask _ D) ltac:(lia) ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia)) as LV.
        cbv zeta in LV. fold s2 hh in LV. specialize (LV Hhh0 Estr). rewrite Estr in LV. exact LV.
    - cbn [fst snd]. split.
      + unfold HREL. repeat (split; [reflexivity|]).
        split; [intros i Hi; apply (df_hb _ D); exact Hi|].
        split; [intros i Hi; apply (df_pb _ D); exact Hi|].
        split; [exact Hih|]. eapply CHAIN_mono; [| | exact HC]; lia.
      + intros Hlm. exfalso. unfold lm_cond in Hlm. cbn in Hlm. discriminate Hlm.
  Qed.

  Lemma lm_curs_limit : forall f s cur ch bl nice limit se1 se,
    Forall (fun c => c = cur \/ limit < c) (lm_curs f s cur ch bl nice limit se1 se).
  Proof.
    induction f as [|f IH]; intros s cur ch bl nice limit se1 se; cbn [lm_curs].
    - constructor; [left; reflexivity | constructor].
    - constructor; [left; reflexivity|].
      destruct (longest_match_body s cur ch bl nice limit se1 se) as [[[[[[s' b'] se1'] se'] cur'] ch'] cont] eqn:E.
      destruct cont; [|constructor].
      destruct (lmb_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ E) as (_ & Hlt & _).
      eapply Forall_impl; [| apply IH]. intros c [-> | H]; right; [exact Hlt | exact H].
  Qed.

  Definition MREL (s1 s2 s3 : deflate_state) : Prop :=
    TF s3 = TF s2 /\ ds_strstart s3 = ds_strstart s2 /\ ds_lookahead s3 = ds_lookahead s2
    /\ ds_sym_next s3 = ds_sym_next s2 /\ ds_pending_buf s3 = ds_pending_buf s2
    /\ ds_dyn_ltree_fc s3 = ds_dyn_ltree_fc s2 /\ ds_dyn_dtree_fc s3 = ds_dyn_dtree_fc s2
    /\ ds_head s3 = ds_head s2 /\ ds_prev s3 = ds_prev s2 /\ ds_ins_h s3 = ds_ins_h s2
    /\ 0 <= ds_match_length s3 <= MAX_MATCH /\ 0 <= ds_match_start s3 < 2 ^ 32
    /\ (MIN_MATCH <= ds_match_length s3 ->
          ds_match_length s3 <= ds_lookahead s1 /\ 1 <= ds_strstart s1 - ds_match_start s3 <= ds_w_size s1 - MIN_LOOKAHEAD).

  Lemma match_stage : forall s1 s2 hh, FTI s1 -> 1 <= ds_lookahead s1 -> HREL s1 s2 ->
    (lm_cond s2 hh = true ->
       Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited s2 hh)
       /\ 1 <= hh <= ds_strstart s1 - 1 /\ ds_strstart s1 - hh <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1) ->
    MREL s1 s2 (st_match s2 hh).
  Proof.
    intros s1 s2 hh HF Hl1 HR Hlm.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr & Eml & Elook & Esn & Ems & Epb & Elfc & Edfc & Lh & Lp & Bh & Bp & Bih & HC2).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & _ & _) & (_ & Ews & Epl & _) & _).
    unfold st_match. destruct (lm_cond s2 hh) eqn:Elm.
    - destruct (Hlm eq_refl) as (LV & Hh1 & Hhd & Big).
      destruct (longest_match_facts s2 hh ltac:(rewrite Estr; lia) ltac:(rewrite Epl, Hpl; unfold MAX_MATCH; lia) ltac:(rewrite Elook; lia))
        as (ms & Efst & Hml3 & Hle & Hup & Hms).
      destruct (longest_match s2 hh) as [s3' ml]. cbn [fst snd] in *. subst s3'.
      assert (Hm : forall m, In m (lm_visited s2 hh) -> 1 <= ds_strstart s1 - m <= ds_w_size s1 - MIN_LOOKAHEAD).
      { intros m Hin. rewrite Forall_forall in LV. pose proof (LV m Hin) as Bm.
        unfold lm_visited in Hin. cbv zeta in Hin.
        match type of Hin with In m (lm_curs ?f ?s ?cur ?ch ?bl ?nice ?limit ?se1 ?se) =>
          pose proof (lm_curs_limit f s cur ch bl nice limit se1 se) as LL end.
        rewrite Forall_forall in LL. specialize (LL m Hin). cbv beta in LL.
        rewrite Estr, Ews in LL. unfold NIL in LL.
        destruct LL as [-> | LL]; [lia|].
        destruct (Z.ltb_spec (ds_w_size s1 - MIN_LOOKAHEAD) (ds_strstart s1)); unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
      unfold MREL. destruct ms as [m|]; cbv beta iota; dsred.
      + repeat (split; [reflexivity|]).
        split; [exact Hml3|].
        split. { destruct Hms as [HH | (m' & Em & Hin)]; [discriminate HH|]. injection Em as ->. rewrite Forall_forall in LV. pose proof (LV m' Hin). lia. }
        intros H3. unfold MIN_MATCH in H3. split; [rewrite Elook in Hle; exact Hle|].
        destruct (Hup ltac:(rewrite Epl, Hpl; lia)) as (m' & Em & Hin). injection Em as ->. exact (Hm m' Hin).
      + repeat (split; [reflexivity|]).
        split; [exact Hml3|].
        split; [rewrite Ems; exact (df_ms _ D)|].
        intros H3. unfold MIN_MATCH in H3. exfalso. destruct (Hup ltac:(rewrite Epl, Hpl; lia)) as (m' & Em & _). discriminate Em.
    - unfold MREL. repeat (split; [reflexivity|]).
      split; [rewrite Eml; pose proof (dx_ml _ X); lia|].
      split; [rewrite Ems; exact (df_ms _ D)|].
      intros H3. exfalso. rewrite Eml in H3. unfold MIN_MATCH in *. lia.
  Qed.

  Definition IREL (s s' : deflate_state) : Prop :=
    TF s' = TF s /\ ds_strstart s' = ds_strstart s + ds_match_length s /\ ds_match_length s' = 0 /\ ds_lookahead s' = ds_lookahead s
    /\ ds_sym_next s' = ds_sym_next s /\ ds_match_start s' = ds_match_start s /\ ds_pending_buf s' = ds_pending_buf s
    /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
    /\ arr_len (ds_head s') = arr_len (ds_head s) /\ arr_len (ds_prev s') = arr_len (ds_prev s)
    /\ (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s') i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s') i < 65536)
    /\ 0 <= ds_ins_h s' < 65536
    /\ CHAIN s' (ds_strstart s + ds_match_length s) (ds_strstart s + ds_match_length s).

  Lemma fast_insert_facts : forall n s k,
    ds_w_size s = 2 ^ k -> 0 <= k -> ds_w_mask s = ds_w_size s - 1 -> arr_len (ds_prev s) = ds_w_size s ->
    arr_len (ds_head s) = ds_hash_size s -> 0 <= ds_hash_mask s -> ds_hash_mask s = ds_hash_size s - 1 -> ds_hash_size s <= 65536 ->
    (forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head s) i < 65536) ->
    (forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev s) i < 65536) ->
    0 <= ds_ins_h s < 65536 ->
    1 <= ds_match_length s <= Z.of_nat n -> 0 <= ds_strstart s -> ds_strstart s + ds_match_length s < 2 ^ 16 ->
    CHAIN s (ds_strstart s) (ds_strstart s) ->
    IREL s (deflate_fast_insert n s).
  Proof.
    induction n as [|n IH]; intros s k Ews Hk Ewm Lp Lh Hm0 Ehm Hhs Bh Bp Bih Hml Hstr Hbnd HC; [lia|].
    rewrite deflate_fast_insert_step. cbv zeta. rewrite insl_eq.
    set (t := set_strstart s (ds_strstart s + 1)).
    pose proof (insert_string_facts t (ds_strstart s + 1)) as IF. cbv zeta in IF.
    destruct IF as (Ehh & Eih & Ehd & Epv & Estrm & Ewin & Elook & Estr & Ebs & Eml & Esn & Elfc & Edfc & Epd & Epb & Ebv & Ebb & Eins & Epl & Ems & Hh).
    specialize (Hh ltac:(subst t; dsred; lia)).
    assert (Hh2 : 0 <= update_hash t (ds_ins_h t) (arr_get (ds_window t) (ds_strstart s + 1 + (MIN_MATCH - 1))) <= ds_hash_size s - 1)
      by (revert Hh; subst t; dsred; rewrite Ehm; intros Hh; exact Hh).
    destruct (CHAIN_insert_string t (ds_strstart s + 1) (ds_strstart s) (ds_strstart s) k
                ltac:(apply (CHAIN_same s); subst t; dsred; try reflexivity; exact HC)
                ltac:(subst t; dsred; exact Ews) Hk ltac:(subst t; dsred; exact Ewm) ltac:(subst t; dsred; exact Lp) ltac:(subst t; dsred; exact Lh)
                ltac:(subst t; dsred; exact Hm0) ltac:(subst t; dsred; exact Ehm) ltac:(lia)) as [HC1 _].
    replace (Z.max (ds_strstart s) (ds_strstart s + 1)) with (ds_strstart s + 1) in HC1 by lia.
    replace (Z.max (ds_strstart s) (ds_strstart s)) with (ds_strstart s) in HC1 by lia.
    set (t1 := fst (insert_string t (ds_strstart s + 1))) in *.
    assert (Hh' : 0 <= ds_ins_h t1 < 65536) by (rewrite Eih; lia).
    assert (Bh1 : forall i, 0 <= i < ds_hash_size s -> 0 <= arr_get (ds_head t1) i < 65536).
    { intros i Hi. rewrite Ehd. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | subst t; dsred; apply Bh; exact Hi]. }
    assert (Bp1 : forall i, 0 <= i < ds_w_size s -> 0 <= arr_get (ds_prev t1) i < 65536).
    { intros i Hi. rewrite Epv. rewrite arr_get_set. destruct (_ && _); [revert Hh2; subst t; dsred; unfold update_hash; dsred; intros Hh2; apply Bh; lia | subst t; dsred; apply Bp; exact Hi]. }
    assert (Lh1 : arr_len (ds_head t1) = ds_hash_size s) by (rewrite Ehd, arr_len_set; subst t; dsred; exact Lh).
    assert (Lp1 : arr_len (ds_prev t1) = ds_w_size s) by (rewrite Epv, arr_len_set; subst t; dsred; exact Lp).
    assert (Tt1 : TF t1 = TF s /\ ds_strstart t1 = ds_strstart s + 1 /\ ds_match_length t1 = ds_match_length s /\ ds_lookahead t1 = ds_lookahead s
                  /\ ds_sym_next t1 = ds_sym_next s /\ ds_match_start t1 = ds_match_start s /\ ds_pending_buf t1 = ds_pending_buf s
                  /\ ds_dyn_ltree_fc t1 = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc t1 = ds_dyn_dtree_fc s
                  /\ ds_w_size t1 = ds_w_size s /\ ds_hash_size t1 = ds_hash_size s /\ ds_w_mask t1 = ds_w_mask s /\ ds_hash_mask t1 = ds_hash_mask s).
    { subst t1 t. rewrite insert_string_fst. dsred. repeat split; reflexivity. }
    destruct Tt1 as (Tt1 & St1 & Mt1 & Lt1 & Nt1 & MSt1 & Pt1 & LFt1 & DFt1 & Wt1 & Ht1 & WMt1 & HMt1).
    cbv zeta. dsred.
    destruct (Z.eqb_spec (ds_match_length s - 1) 0) as [Z0|Z0]; cbn [negb].
    -
      assert (Hml1 : ds_match_length s = 1) by lia.
      unfold IREL. dsred. rewrite Hml1.
      split; [exact Tt1|]. split; [exact St1|]. split; [lia|]. split; [exact Lt1|]. split; [exact Nt1|]. split; [exact MSt1|]. split; [exact Pt1|].
      split; [exact LFt1|]. split; [exact DFt1|].
      split; [rewrite Lh1; symmetry; exact Lh|]. split; [rewrite Lp1; symmetry; exact Lp|].
      split; [exact Bh1|]. split; [exact Bp1|]. split; [exact Hh'|].
      apply (CHAIN_same t1); dsred; try reflexivity. eapply CHAIN_mono; [| | exact HC1]; lia.
    - pose proof (IH (set_match_length t1 (ds_match_length s - 1)) k) as IH'. revert IH'. dsred. rewrite Wt1, WMt1, Ht1, HMt1, St1, Lh1, Lp1. intros IH'.
      specialize (IH' Ews Hk Ewm ltac:(reflexivity) ltac:(reflexivity) Hm0 Ehm Hhs Bh1 Bp1 Hh' ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(apply (CHAIN_same t1); dsred; try reflexivity; eapply CHAIN_mono; [| | exact HC1]; lia)).
      revert IH'. unfold IREL. dsred. rewrite Lh1, Lp1, Wt1, Ht1, St1, Lt1, Nt1, MSt1, Pt1, LFt1, DFt1.
      replace (ds_strstart s + 1 + (ds_match_length s - 1)) with (ds_strstart s + ds_match_length s) by lia.
      intros (T' & R'). split; [rewrite T'; revert Tt1; unfold TF; dsred; intros Tt1; exact Tt1|].
      rewrite Lh, Lp. exact R'.
  Qed.


  Definition TALLYF (s3 s4 : deflate_state) : Prop :=
    TF s4 = TF s3 /\ ds_strstart s4 = ds_strstart s3 /\ ds_lookahead s4 = ds_lookahead s3 /\ ds_match_length s4 = ds_match_length s3
    /\ ds_match_start s4 = ds_match_start s3 /\ ds_head s4 = ds_head s3 /\ ds_prev s4 = ds_prev s3 /\ ds_ins_h s4 = ds_ins_h s3
    /\ arr_len (ds_pending_buf s4) = arr_len (ds_pending_buf s3)
    /\ (forall i, 0 <= i < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s4) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s4) = arr_len (ds_dyn_ltree_fc s3) /\ arr_len (ds_dyn_dtree_fc s4) = arr_len (ds_dyn_dtree_fc s3)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s4) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s4) i < 65536)
    /\ BQ s4 /\ nsym s4 = nsym s3 + 1 /\ ds_sym_next s4 = ds_sym_next s3 + 3.

  Lemma tally_common : forall s3 r,
    (forall j, 0 <= j < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s3) j < 256) ->
    (forall i, 0 <= arr_get (ds_dyn_ltree_fc s3) i < 65536) -> (forall i, 0 <= arr_get (ds_dyn_dtree_fc s3) i < 65536) ->
    tally_keep s3 r -> ds_sym_next r = ds_sym_next s3 + 3 ->
    (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s3) j < 256) -> forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf r) j < 256) ->
    (exists k v, ds_dyn_ltree_fc r = arr_set (ds_dyn_ltree_fc s3) k (wrap16 v)) ->
    (ds_dyn_dtree_fc r = ds_dyn_dtree_fc s3 \/ exists k v, ds_dyn_dtree_fc r = arr_set (ds_dyn_dtree_fc s3) k (wrap16 v)) ->
    ds_bl_tree_fc r = ds_bl_tree_fc s3 -> ds_dyn_ltree_dl r = ds_dyn_ltree_dl s3 -> ds_dyn_dtree_dl r = ds_dyn_dtree_dl s3 -> ds_bl_tree_dl r = ds_bl_tree_dl s3 ->
    ds_depth r = ds_depth s3 -> ds_bl_count r = ds_bl_count s3 -> ds_opt_len r = ds_opt_len s3 -> ds_static_len r = ds_static_len s3 ->
    ds_hash_mask r = ds_hash_mask s3 -> ds_last_flush r = ds_last_flush s3 -> KV r = KV s3 ->
    (ds_w_bits r, ds_hash_bits r, ds_gzhead r, ds_method r, ds_heap r) = (ds_w_bits s3, ds_hash_bits s3, ds_gzhead s3, ds_method s3, ds_heap s3) ->
    BQ r -> nsym r = nsym s3 + 1 ->
    TALLYF s3 r.
  Proof.
    intros s3 r Bpb Bl Bd TK Esn Hpb (k1 & v1 & EL) ED Ebl Eldl Eddl Ebdl Edep Eblc Eol Esl Ehm Elf EKV Emisc HBQ EN.
    injection Emisc as Ewb Ehb Egz Eme Ehp.
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    unfold TALLYF. split.
    { unfold TF. rewrite Egm, Elz, Enm, Emc, Elv, Esy, Eins, Ews, Epl, Ema, Epm, Emt, Ehw, Ewsz, Ebs, Ewr, Est, Elbs, Ebl, Eldl, Eddl, Ebdl,
        Edep, Eblc, Eol, Esl, Ehs, Ewm, Ehm, Ehsh, Estrm, Epd, Epo, Ebv, Ebb, Elf, Ewin, EKV, Ese, Ewb, Ehb, Epbs, Egz, Eme, Ehp. reflexivity. }
    split; [exact Estr|]. split; [exact Elook|]. split; [exact Eml|]. split; [exact Ems|]. split; [exact Ehead|]. split; [exact Eprev|]. split; [exact Eih|].
    split; [exact Lpb|].
    split; [apply Hpb; exact Bpb|].
    split; [rewrite EL, arr_len_set; reflexivity|].
    split; [destruct ED as [-> | (k2 & v2 & ->)]; [| rewrite arr_len_set]; reflexivity|].
    split; [intros i; rewrite EL, arr_get_set; destruct (_ && _); [apply wrap16_range | apply Bl]|].
    split; [intros i; destruct ED as [-> | (k2 & v2 & ->)]; [apply Bd | rewrite arr_get_set; destruct (_ && _); [apply wrap16_range | apply Bd]]|].
    split; [exact HBQ|]. split; [exact EN | exact Esn].
  Qed.

  Lemma DX_BQ : forall s, DX s -> BQ s.
  Proof. intros s X. split; [exact (dx_sn _ X)|]. split; [pose proof (dx_nsym _ X); lia|]. split; [exact (dx_syms _ X) | exact (dx_hist _ X)]. Qed.

  Lemma tally_lit_stage : forall s1 s2 s3, FTI s1 -> HREL s1 s2 -> MREL s1 s2 s3 ->
    let r := tr_tally_lit s3 (arr_get (ds_window s3) (ds_strstart s3)) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF HR MR r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    destruct MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & _ & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & _ & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    pose proof (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3))) as (TK & Esn & Ebf & Edt & Ebt & Elt & Rl & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3).
    { apply (BQ_same s1); [rewrite Epb3, Epb2 | rewrite Elbs3, Elbs2 | rewrite Esn3, Esn2 | rewrite Elfc3, Elfc2 | rewrite Edfc3, Edfc2 | rewrite Ebl3, Ebl2 |]; try reflexivity.
      exact (DX_BQ s1 X). }
    assert (N3 : nsym s3 = nsym s1) by (unfold nsym; rewrite Esn3, Esn2; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    destruct (BQ_tally_lit s3 BQ3 ltac:(rewrite Elbs3, Elbs2, Esn3, Esn2, Epb3, Epb2, (df_bl _ D); lia) ltac:(rewrite Elbs3, Elbs2; lia)
                ltac:(rewrite N3; lia) ltac:(rewrite Elfc3, Elfc2; unfold L_CODES; lia) (arr_get (ds_window s3) (ds_strstart s3))) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    split; [| exact Ebf].
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    eapply tally_common.
    - rewrite Elbs3, Elbs2, Epb3, Epb2. exact (df_bb _ D).
    - rewrite Elfc3, Elfc2. exact (dx_tfc _ X DeflateState.TL).
    - rewrite Edfc3, Edfc2. exact (dx_tfc _ X DeflateState.TD).
    - exact (proj1 (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3)))).
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - left. exact Edt.
    - exact Ebt.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact Ehmk.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.


  Lemma tally_dist_stage : forall s1 s2 s3, FTI s1 -> HREL s1 s2 -> MREL s1 s2 s3 -> MIN_MATCH <= ds_match_length s3 ->
    let r := tr_tally_dist s3 (wrap32 (ds_strstart s3 - ds_match_start s3)) (ds_match_length s3 - MIN_MATCH) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF HR MR H3 r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    destruct MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & _ & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & _ & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    destruct (Hdist3 H3) as [Hmll Hd]. rewrite Estr3, Estr2.
    rewrite wrap32_id by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
    set (dist := ds_strstart s1 - ds_match_start s3). set (len := ds_match_length s3 - MIN_MATCH).
    pose proof (tally_dist_facts s3 dist len) as (TK & Esn & Ebf & Ebt & Rl & Rd & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3).
    { apply (BQ_same s1); [rewrite Epb3, Epb2 | rewrite Elbs3, Elbs2 | rewrite Esn3, Esn2 | rewrite Elfc3, Elfc2 | rewrite Edfc3, Edfc2 | rewrite Ebl3, Ebl2 |]; try reflexivity.
      exact (DX_BQ s1 X). }
    assert (N3 : nsym s3 = nsym s1) by (unfold nsym; rewrite Esn3, Esn2; reflexivity).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL.
    destruct (BQ_tally_dist s3 BQ3 ltac:(rewrite Elbs3, Elbs2, Esn3, Esn2, Epb3, Epb2, (df_bl _ D); lia) ltac:(rewrite Elbs3, Elbs2; lia)
                ltac:(rewrite N3; lia) ltac:(rewrite Elfc3, Elfc2; unfold L_CODES; lia) ltac:(rewrite Edfc3, Edfc2; unfold D_CODES; lia)
                dist len ltac:(subst dist; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia)) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    pose proof (tally_dist_fields s3 dist len) as (_ & _ & _ & Elt & Edt & _). cbv zeta in Elt, Edt.
    split; [| exact Ebf].
    destruct TK as (Estrm & Ewin & Eprev & Ehead & Elook & Estr & Ebs & Eml & Ems & Epl & Epm & Ema & Epd & Epo & Ebv & Ebb & Elbs & Epbs & Ese
                    & Ews & Ehs & Ewm & Ehmk & Ehsh & Eih & Eins & Ewsz & Elv & Esy & Elz & Egm & Enm & Emc & Est & Ewr & Ehw & Emt & Lpb).
    eapply tally_common.
    - rewrite Elbs3, Elbs2, Epb3, Epb2. exact (df_bb _ D).
    - rewrite Elfc3, Elfc2. exact (dx_tfc _ X DeflateState.TL).
    - rewrite Edfc3, Edfc2. exact (dx_tfc _ X DeflateState.TD).
    - exact (proj1 (tally_dist_facts s3 dist len)).
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - right. eexists. eexists. exact Edt.
    - exact Ebt.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact Ehmk.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Definition TREL (s3 s7 : deflate_state) (adv : Z) : Prop :=
    TF s7 = TF s3 /\ ds_strstart s7 = ds_strstart s3 + adv /\ ds_lookahead s7 = ds_lookahead s3 - adv
    /\ 0 <= ds_match_length s7 < MIN_MATCH /\ 0 <= ds_match_start s7 < 2 ^ 32
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s3)
    /\ (forall i, 0 <= i < ds_lit_bufsize s3 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s3) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s3)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s3 + 1 /\ ds_sym_next s7 = ds_sym_next s3 + 3
    /\ arr_len (ds_head s7) = arr_len (ds_head s3) /\ arr_len (ds_prev s7) = arr_len (ds_prev s3)
    /\ (forall i, 0 <= i < ds_hash_size s3 -> 0 <= arr_get (ds_head s7) i < 65536)
    /\ (forall i, 0 <= i < ds_w_size s3 -> 0 <= arr_get (ds_prev s7) i < 65536)
    /\ 0 <= ds_ins_h s7 < 65536
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1).

  Lemma tally_stage : forall s1 s2 s3, FTI s1 -> 1 <= ds_lookahead s1 -> HREL s1 s2 -> MREL s1 s2 s3 ->
    let r := st_tally s3 in
    (exists adv, TREL s3 (fst r) adv /\ 1 <= adv /\ adv <= ds_lookahead s1 /\ adv <= 258
                 /\ (adv = 1 \/ adv = ds_match_length s3 /\ MIN_MATCH <= adv))
    /\ snd r = (ds_sym_next s3 + 3 =? ds_sym_end s3).
  Proof.
    intros s1 s2 s3 HF Hl1 HR MR r. subst r.
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    pose proof (TF_fields _ _ T2) as ((_ & _ & _ & _ & Elv2 & Esy2) & (_ & Ews2 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs2 & Ebl2 & _) & (_ & _ & _ & _ & Ehs2 & Ewm2 & Ehm2 & _) & (Estrm2 & Epd2 & Epo2 & Ebv2 & _ & _ & _ & EKV2 & Ese2) & _).
    pose proof (TF_fields _ _ T3) as ((_ & _ & _ & _ & Elv3 & Esy3) & (_ & Ews3 & _ & _ & _ & _ & _ & _) & (_ & _ & _ & Elbs3 & Ebl3 & _) & (_ & _ & _ & _ & Ehs3 & Ewm3 & Ehm3 & _) & (Estrm3 & Epd3 & Epo3 & Ebv3 & _ & _ & _ & EKV3 & Ese3) & _).
    unfold st_tally.
    destruct (Z.leb_spec MIN_MATCH (ds_match_length s3)) as [H3|H3].
    -
      destruct (tally_dist_stage s1 s2 s3 HF HR MR H3) as [TY Ebf]. cbv zeta in TY, Ebf.
      unfold st_dist. destruct (tr_tally_dist s3 _ _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      split; [| exact Ebf].
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      pose proof (TF_fields _ _ T4) as (_ & (_ & Ews4 & _) & (_ & _ & _ & Elbs4 & _) & (_ & _ & _ & _ & Ehs4 & Ewm4 & Ehm4 & _) & _).
      destruct (Hdist3 H3) as [Hmll Hd].
      set (s5 := set_lookahead s4 (ds_lookahead s4 - ds_match_length s4)).
      exists (ds_match_length s3).
      split; [| unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia].
      assert (HC5 : CHAIN s5 (ds_strstart s1) (ds_strstart s1)).
      { apply (CHAIN_same s2); subst s5; dsred; rewrite ?Ehd4, ?Epv4, ?Ehd3, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity. exact HC2. }
      destruct (ins_cond s5) eqn:Eic.
      +
        unfold st_ins.
        set (t := set_match_length s5 (ds_match_length s5 - 1)).
        assert (Hmlt : ds_match_length t = ds_match_length s3 - 1) by (subst t s5; dsred; rewrite Eml4; reflexivity).
        pose proof (fast_insert_facts (Z.to_nat (ds_match_length t)) t (ds_w_bits s1)) as IF.
        assert (Ewst : ds_w_size t = ds_w_size s1) by (subst t s5; dsred; rewrite Ews4, Ews3, Ews2; reflexivity).
        assert (Ehst : ds_hash_size t = ds_hash_size s1) by (subst t s5; dsred; rewrite Ehs4, Ehs3, Ehs2; reflexivity).
        specialize (IF ltac:(rewrite Ewst; exact (df_wsize _ D)) ltac:(pose proof (df_wbits _ D); lia)
                       ltac:(subst t s5; dsred; rewrite Ewm4, Ewm3, Ewm2, Ews4, Ews3, Ews2; exact (df_wmask _ D))
                       ltac:(subst t s5; dsred; rewrite Epv4, Epv3, Ews4, Ews3, Ews2, Lp2; exact (df_pl _ D))
                       ltac:(subst t s5; dsred; rewrite Ehd4, Ehd3, Ehs4, Ehs3, Ehs2, Lh2; exact (df_hl _ D))
                       ltac:(subst t s5; dsred; rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D); lia)
                       ltac:(subst t s5; dsred; rewrite Ehm4, Ehm3, Ehm2, Ehs4, Ehs3, Ehs2; exact (df_hmask _ D))
                       ltac:(rewrite Ehst; lia)
                       ltac:(rewrite Ehst; subst t s5; dsred; rewrite Ehd4, Ehd3; exact Bh2)
                       ltac:(rewrite Ewst; subst t s5; dsred; rewrite Epv4, Epv3; exact Bp2)
                       ltac:(subst t s5; dsred; rewrite Eih4, Eih3; exact Bih2)
                       ltac:(rewrite Hmlt, Z2Nat.id by (unfold MIN_MATCH in H3; lia); unfold MIN_MATCH in H3; lia)
                       ltac:(subst t s5; dsred; rewrite Estr4, Estr3, Estr2; lia)
                       ltac:(subst t s5; dsred; rewrite Estr4, Estr3, Estr2, Eml4; unfold MIN_MATCH in H3; lia)
                       ltac:(apply (CHAIN_same s5); subst t s5; dsred; try reflexivity; rewrite Estr4, Estr3, Estr2; exact HC5)).
        set (u := deflate_fast_insert (Z.to_nat (ds_match_length t)) t) in *.
        destruct IF as (Tu & Estru & Emlu & Elooku & Esnu & Emsu & Epbu & Elfcu & Edfcu & Lhu & Lpu & Bhu & Bpu & Bihu & HCu).
        assert (Et : TF t = TF s3 /\ ds_strstart t = ds_strstart s3 /\ ds_lookahead t = ds_lookahead s3 - ds_match_length s3
                     /\ ds_match_start t = ds_match_start s3 /\ ds_pending_buf t = ds_pending_buf s4
                     /\ ds_dyn_ltree_fc t = ds_dyn_ltree_fc s4 /\ ds_dyn_dtree_fc t = ds_dyn_dtree_fc s4
                     /\ ds_head t = ds_head s3 /\ ds_prev t = ds_prev s3 /\ ds_sym_next t = ds_sym_next s4 /\ ds_lit_bufsize t = ds_lit_bufsize s4
                     /\ ds_bl_tree_fc t = ds_bl_tree_fc s4).
        { subst t s5. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4. repeat split; try reflexivity. rewrite <- T4. reflexivity. }
        destruct Et as (Tt & Estrt & Elookt & Emst & Epbt & Elfct & Edfct & Ehdt & Epvt & Esnt & Elbst & Eblt).
        unfold TREL. dsred.
        split; [rewrite <- Tt, <- Tu; reflexivity|].
        split; [rewrite Estru, Estrt, Hmlt; lia|].
        split; [rewrite Elooku, Elookt; reflexivity|].
        split; [unfold MIN_MATCH; lia|].
        split; [rewrite Emsu, Emst; exact Hms3|].
        split; [rewrite Epbu, Epbt; exact Lpb4|].
        split; [rewrite Epbu, Epbt; exact Bpb4|].
        split; [rewrite Elfcu, Elfct; exact Llt4|]. split; [rewrite Edfcu, Edfct; exact Ldt4|].
        split; [rewrite Elfcu, Elfct; exact Blt4|]. split; [rewrite Edfcu, Edfct; exact Bdt4|].
        split; [apply (BQ_same u); dsred; try reflexivity; apply (BQ_same s4); rewrite ?Epbu, ?Epbt, ?Esnu, ?Esnt, ?Elfcu, ?Elfct, ?Edfcu, ?Edfct; try reflexivity;
                [pose proof (TF_fields _ _ Tu) as (_ & _ & (_ & _ & _ & L1 & _) & _); rewrite L1, Elbst; reflexivity
                | pose proof (TF_fields _ _ Tu) as (_ & _ & (_ & _ & _ & _ & B1 & _) & _); rewrite B1, Eblt; reflexivity
                | exact BQ4]|].
        split; [unfold nsym; dsred; rewrite Esnu, Esnt; unfold nsym in N4; exact N4|].
        split; [rewrite Esnu, Esnt; exact Esn4|].
        split; [rewrite Lhu, Ehdt; reflexivity|]. split; [rewrite Lpu, Epvt; reflexivity|].
        split; [rewrite Ehs3, Ehs2, <- Ehst; exact Bhu|]. split; [rewrite Ews3, Ews2, <- Ewst; exact Bpu|].
        split; [exact Bihu|].
        apply (CHAIN_same u); dsred; try reflexivity.
        replace (ds_strstart u + 1 - 1) with (ds_strstart t + ds_match_length t) by lia. exact HCu.
      +
        unfold st_noins, TREL. subst s5. dsred.
        rewrite Estr4, Eml4, Elook4, Ems4, Ehd4, Epv4.
        split; [rewrite <- T4; reflexivity|].
        split; [reflexivity|]. split; [lia|]. split; [unfold MIN_MATCH; lia|]. split; [exact Hms3|].
        split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
        split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
        split; [unfold nsym in *; dsred; exact N4|]. split; [exact Esn4|].
        split; [rewrite Ehd3; reflexivity|]. split; [rewrite Epv3; reflexivity|].
        split; [rewrite Ehd3, Ehs3, Ehs2; exact Bh2|]. split; [rewrite Epv3, Ews3, Ews2; exact Bp2|].
        split.
        { match goal with |- 0 <= update_hash ?st ?h ?c < 65536 =>
            pose proof (update_hash_range st h c ltac:(dsred; rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D); lia)) as R end.
          revert R. dsred. rewrite Ehm4, Ehm3, Ehm2, (df_hmask _ D). intros R. lia. }
        apply (CHAIN_same s2); dsred; rewrite ?Ehd4, ?Ehd3, ?Epv4, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity.
        eapply CHAIN_mono; [| | exact HC2]; rewrite Estr3, Estr2; unfold MIN_MATCH in H3; lia.
    -
      destruct (tally_lit_stage s1 s2 s3 HF HR MR) as [TY Ebf]. cbv zeta in TY, Ebf.
      unfold st_lit. destruct (tr_tally_lit s3 _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      split; [| exact Ebf].
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      exists 1. split; [| lia].
      unfold TREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4.
      split; [rewrite <- T4; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hms3|].
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4|]. split; [exact Esn4|].
      split; [rewrite Ehd3; reflexivity|]. split; [rewrite Epv3; reflexivity|].
      split; [rewrite Ehd3, Ehs3, Ehs2; exact Bh2|]. split; [rewrite Epv3, Ews3, Ews2; exact Bp2|].
      split; [rewrite Eih3; exact Bih2|].
      pose proof (TF_fields _ _ T4) as (_ & (_ & Ews4 & _) & _ & (_ & _ & _ & _ & Ehs4 & Ewm4 & _) & _).
      apply (CHAIN_same s2); dsred; rewrite ?Ehd4, ?Ehd3, ?Epv4, ?Epv3, ?Ehs4, ?Ehs3, ?Ews4, ?Ews3, ?Ewm4, ?Ewm3; try reflexivity.
      replace (ds_strstart s3 + 1 - 1) with (ds_strstart s1) by lia. exact HC2.
  Qed.


  Lemma trip_end : forall s1 s2 s3 s7 adv,
    FTI s1 -> 1 <= ds_lookahead s1 ->
    (ds_lookahead s1 < MIN_LOOKAHEAD -> ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1 - 2) ->
    HREL s1 s2 -> MREL s1 s2 s3 -> TREL s3 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 3 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 < lz_meas s1 /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3 /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ TF s7 = TF s1
    /\ CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1) /\ 0 <= ds_ins_h s7 < 65536 /\ ds_match_length s7 < MIN_MATCH.
  Proof.
    intros s1 s2 s3 s7 adv HF Hl1 Hslack HR MR TR Hadv Hadv2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
    destruct TR as (T7 & Estr7 & Elook7 & Hml7 & Hms7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7 & Lh7 & Lp7 & Bh7 & Bp7 & Bih7 & HC7).
    pose proof (TF_fields _ _ T2) as (_ & (_ & Ews2 & _) & (_ & _ & _ & Elbs2 & _) & (_ & _ & _ & _ & Ehs2 & _) & _).
    pose proof (TF_fields _ _ T3) as (_ & (_ & Ews3 & _) & (_ & _ & _ & Elbs3 & _) & (_ & _ & _ & _ & Ehs3 & _) & _).
    assert (T71 : TF s7 = TF s1) by (rewrite T7, T3, T2; reflexivity).
    pose proof (TF_fields _ _ T71) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    rewrite Estr3, Estr2 in Estr7. rewrite Elook3, Elook2 in Elook7.
    assert (N71 : nsym s7 = nsym s1 + 1) by (rewrite N7; unfold nsym; rewrite Esn3, Esn2; reflexivity).
    assert (Esn71 : ds_sym_next s7 = ds_sym_next s1 + 3) by (rewrite Esn7, Esn3, Esn2; reflexivity).
    assert (Em7 : dmode s7 = 3) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    assert (D7 : dwf s7).
    { destruct D; constructor; rewrite ?Est, ?Ewr, ?Elbs, ?Ebl, ?Eldl, ?Eddl, ?Ebdl, ?Edep, ?Eblc, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Elf, ?Ewin,
        ?Ese, ?Ewb, ?Ehb, ?Epbs, ?Egz, ?Eme, ?Elv, ?Esy, ?Ews, ?Eins, ?Ewsz, ?Ehw, ?Estr7, ?Elook7; try assumption.
      all: try (pose proof (KV_fields _ _ EKV) as (_ & _ & _ & KB); congruence).
      - unfold deflateStateCheck in *. rewrite Est. assumption.
      - unfold tree_lens. rewrite Llt7, Ldt7, Elfc3, Edfc3, Elfc2, Edfc2, Ebl, Eldl, Eddl, Ebdl, Eblc, Ehp, Edep. repeat split; assumption.
      - clear - Hstr Hadv Hsl Sw Hlook. lia.
      - clear - Hadv df_ins. lia.
      - clear - Hadv. lia.
      - clear - Hsl. lia.
      - clear - Bih7. lia.
      - rewrite Ews3, Ews2 in Bp7. exact Bp7.
      - rewrite Ehs3, Ehs2 in Bh7. exact Bh7.
      - rewrite Elbs3, Elbs2 in Bpb7. exact Bpb7. }
    assert (V7 : SV c0 s7) by (apply (SV_strm c0 s1); [exact Estrm | exact V]).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    destruct BQ7 as (Q1 & Q2 & Q3 & Q4).
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (X7 : nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7).
    { intros Hn7. pose proof X as X'. destruct X'; constructor; rewrite ?Em7, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Epl, ?Ema, ?Epm, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est,
        ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Estr7, ?Elook7, ?N71; try assumption.
      - clear - Hml7. unfold MIN_MATCH, MAX_MATCH in *. lia.
      - pose proof (RefDeflSafeI1.dx_matches _ X) as HM. clear - HM. lia.
      - intros _. split; [exact Hpl | exact (proj2 Hml7)].
      - intros _. exact Hma.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - intros HH. exfalso. exact (Hst HH).
      - rewrite Q1, N71. reflexivity.
      - revert Hn7. rewrite N71, ?Elbs. clear - Hn. intros Hn7. lia.
      - rewrite <- N71. exact Q3.
      - intros _. rewrite Hma. clear - Hext Hadv Hadv2 Hn. lia.
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - intros _. rewrite <- Estr7. exact HC7. }
    assert (FE7 : fb_entry s7 0).
    { pose proof (df_pend _ D) as Pd. pose proof (df_bi _ D) as Bi. pose proof (dx_biv _ X) as Bv. pose proof (dx_pout0 _ X Hp) as Po.
      pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
      pose proof (c0_out _ HC0w) as O0. pose proof (c0_aout _ HC0w) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
      pose proof (zlen_nonneg (cs_out_rev (ds_strm s1))) as Zl. unfold zlen in Zl.
      pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
      assert (Bpb7' : forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256) by (rewrite <- Elbs2, <- Elbs3; exact Bpb7).
      constructor; rewrite ?Estrm, ?Elv, ?Esy, ?Ews, ?Ebs, ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Ebb, ?Ewin, ?Ese, ?Estr7, ?Elook7, ?N71, ?Lpb7, ?Epb3, ?Epb2, ?(df_bl _ D).
      all: try assumption.
      - lia.
      - clear - Hext Hadv Hadv2 Hn Sl. lia.
      - pose proof (df_strstart _ D). clear - Hext H Hn Sl. lia.
      - clear - Hstr Hadv Hsl Hlook. lia.
      - clear - Hadv Hlook Hsl Hstr. lia.
      - clear - Sw. lia.
      - exact (df_wl _ D).
      - exact (df_wb _ D).
      - unfold dmode in Hm. destruct (Z.eqb_spec (ds_level s1) 0); [discriminate Hm | clear - Lv n; lia].
      - reflexivity.
      - clear - Bv Bi. lia.
      - clear - Bi. lia.
      - rewrite To. apply wrap64_range'.
      - clear - Ao Ou A0 Zl. lia.
      - rewrite Q1, N71. reflexivity.
      - clear - Hn. lia.
      - rewrite <- N71. exact Q3.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - exact (df_tl _ D7).
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - eexists; first [exact (df_lbs _ D7) | exact (df_lbs _ D)]. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear - Hadv; lia|]. split; [rewrite Elook7; clear - Hadv Hlook Hsl Hstr; lia|].
    split; [exact N71|]. split; [exact Esn71|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|].
    split.
    { pose proof X as X'. destruct X'; constructor; rewrite ?Em7, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eins, ?Ews, ?Epl, ?Ema, ?Epm, ?Emt, ?Ehw, ?Ewsz, ?Ebs, ?Ewr, ?Est,
        ?Elbs, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Estr7, ?Elook7, ?N71; try assumption.
      - clear - Hml7. unfold MIN_MATCH, MAX_MATCH in *. lia.
      - intros _. split; [exact Hpl | exact (proj2 Hml7)].
      - intros _. exact Hma.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - intros HH. exfalso. exact (Hst HH).
      - rewrite Edep. exact Xdepth.
      - intros i Hi. rewrite Eblc. apply Xblc. exact Hi.
      - intros _. rewrite <- Estr7. eapply CHAIN_mono; [| | exact HC7]; clear; lia. }
    split; [exact T71|]. split; [exact HC7|]. split; [exact Bih7 | exact (proj2 Hml7)].
  Qed.


  Lemma cfg_ranges : forall s, dwf s -> DX s -> dmode s <> 0 ->
    1 <= ds_level s <= 9
    /\ 4 <= ds_good_match s <= 32 /\ 4 <= ds_max_lazy_match s <= 258 /\ 8 <= ds_nice_match s <= 258 /\ 4 <= ds_max_chain_length s <= 4096.
  Proof.
    intros s D X Hm. pose proof (df_level _ D) as Lv. pose proof (dx_cfg _ X) as C.
    assert (Hl : ds_level s <> 0) by (intros E0; apply Hm; unfold dmode; rewrite E0; reflexivity).
    assert (Hc : ds_level s = 1 \/ ds_level s = 2 \/ ds_level s = 3 \/ ds_level s = 4 \/ ds_level s = 5 \/ ds_level s = 6 \/ ds_level s = 7 \/ ds_level s = 8 \/ ds_level s = 9) by lia.
    destruct Hc as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E in C |- *; cbn in C; injection C as -> -> -> ->; lia.
  Qed.

  Lemma trip_inv_intro : forall s, dwf s ->
    0 <= ds_ins_h s < 65536 -> 0 <= ds_match_length s <= 258 -> 0 <= ds_max_lazy_match s < 2 ^ 31 ->
    0 <= ds_sym_next s -> ds_sym_next s + 3 <= 3 * ds_lit_bufsize s ->
    (forall i, 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) -> (forall i, 0 <= arr_get (ds_dyn_dtree_fc s) i < 65536) ->
    trip_inv s.
  Proof.
    intros s D Hih Hml Hlz Hsn1 Hsn2 Hl Hd. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (df_hbits _ D) as Hb. pose proof (df_hshift _ D) as Hsh.
    constructor.
    - exact (proj1 (df_strstart _ D)).
    - exact (df_sl _ D).
    - exact (df_look _ D).
    - clear - Hih. lia.
    - exact (df_hmask _ D).
    - exact (df_wmask _ D).
    - rewrite Hsh. unfold MIN_MATCH. clear - Hb. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    - exact Hml.
    - exact (df_ms _ D).
    - exact Hlz.
    - clear - Hsn1 Hsn2. lia.
    - rewrite (df_symend _ D). clear - Sl. lia.
    - exact (df_wb _ D).
    - exact (df_hb _ D).
    - exact (df_pb _ D).
    - intros i _. apply Hl.
    - intros i _. apply Hd.
  Qed.

  Lemma trip_inv_transfer : forall a b, trip_inv a -> TF b = TF a ->
    ds_strstart b = ds_strstart a -> ds_lookahead b = ds_lookahead a -> ds_sym_next b = ds_sym_next a ->
    0 <= ds_ins_h b < 65536 -> 0 <= ds_match_length b <= 258 -> 0 <= ds_match_start b < 2 ^ 32 ->
    (forall i, 0 <= i < ds_hash_size a -> 0 <= arr_get (ds_head b) i < 65536) ->
    (forall i, 0 <= i < ds_w_size a -> 0 <= arr_get (ds_prev b) i < 65536) ->
    ds_dyn_ltree_fc b = ds_dyn_ltree_fc a -> ds_dyn_dtree_fc b = ds_dyn_dtree_fc a ->
    trip_inv b.
  Proof.
    intros a b T E Estr Elook Esn Hih Hml Hms Hh Hp El Ed.
    pose proof (TF_fields _ _ E) as ((_ & Elz & _) & (_ & Ews & _) & (_ & _ & _ & Elbs & _) & (_ & _ & _ & _ & Ehs & Ewm & Ehm & Ehsh) & (_ & _ & _ & _ & _ & _ & Ewin & _ & Ese) & _).
    destruct T; constructor; rewrite ?Estr, ?Elook, ?Esn, ?Elz, ?Ews, ?Elbs, ?Ehs, ?Ewm, ?Ehm, ?Ehsh, ?Ewin, ?Ese, ?El, ?Ed; try assumption.
    clear - Hih. lia.
  Qed.

  Lemma lm_stage_ok : forall s1 s2 hh, FTI s1 -> 1 <= ds_lookahead s1 -> ds_strstart s1 + MIN_LOOKAHEAD <= 2 * ds_w_size s1 ->
    HREL s1 s2 ->
    (lm_cond s2 hh = true ->
       Forall (fun c => 0 <= c < ds_strstart s1) (lm_visited s2 hh)
       /\ 1 <= hh <= ds_strstart s1 - 1 /\ ds_strstart s1 - hh <= ds_w_size s1 - MIN_LOOKAHEAD /\ MIN_MATCH <= ds_lookahead s1) ->
    lm_cond s2 hh = true -> lm_ok s2 hh.
  Proof.
    intros s1 s2 hh HF Hl1 Hss HR Hlm Hc. destruct (Hlm Hc) as (LV & Hh1 & Hhd & Big). clear Hlm.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
    pose proof (TF_fields _ _ T2) as ((Egm & _ & Enm & Emc & _) & (_ & Ews & Epl & _) & _ & (_ & _ & _ & _ & _ & Ewm & _) & (_ & _ & _ & _ & _ & _ & Ewin & _) & _).
    pose proof (cfg_ranges s1 D X ltac:(rewrite Hm; lia)) as (_ & Gg & _ & Gn & Gc).
    pose proof (df_strstart _ D) as Rstr.
    destruct (longest_match_facts s2 hh ltac:(rewrite Estr2; lia) ltac:(rewrite Epl, Hpl; unfold MAX_MATCH; lia) ltac:(rewrite Elook2; lia)) as (ms & _ & Rml & _).
    unfold lm_ok. rewrite Ews, Estr2, Ewm, Epl, Hpl, Enm, Elook2, Egm, Emc, Ewin.
    split; [exact (df_wb _ D)|]. split; [exact Bp2|]. split; [lia|].
    split; [unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss; lia|]. split; [exact (df_wmask _ D)|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [destruct (_ <=? 2); [rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_lower_bound; lia | lia]|].
    split; [lia|]. split; [exact LV|]. unfold MAX_MATCH in Rml. exact Rml.
  Qed.

  Definition RET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  Lemma fast_step : forall s, FTI s ->
    trip_ok (ds_w_size s0) (ds_hash_size s0) s flush
    /\ match snd (st_body s flush) with
       | LCont => FTI (fst (st_body s flush)) /\ lz_meas (fst (st_body s flush)) < lz_meas s
       | LBreak => FTI (fst (st_body s flush)) /\ ds_lookahead (fst (st_body s flush)) = 0
       | LRet bs => RET (fst (st_body s flush)) bs
       end.
  Proof.
    intros s HF. rewrite st_body_eq2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (KV_fields _ _ HK) as (Ews0 & Ehs0 & Elbs0 & _).
    pose proof (fill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hl0 & Hfw & Hl1r & Ews1 & Hnone & Hbrk & Hret & Hss1 & Hnc).
    set (s1 := fst (st_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (FTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hpl1 & Hml1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    rewrite <- Ews0, <- Ehs0.
    destruct (snd (st_fill s flush)) as [o|] eqn:Eo.
    -
      split.
      { split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - destruct (Hnone eq_refl) as [Hl1 Hslack].
      pose proof (hash_stage s1 HF1 Hl1) as HS. cbv zeta in HS. destruct HS as [HR Hlm].
      set (s2 := fst (st_hash s1)) in *. set (hh := snd (st_hash s1)) in *.
      pose proof (match_stage s1 s2 hh HF1 Hl1 HR Hlm) as MR.
      set (s3 := st_match s2 hh) in *.
      pose proof (tally_stage s1 s2 s3 HF1 Hl1 HR MR) as TS. cbv zeta in TS. destruct TS as [(adv & TR & Hadv1 & Hadv2 & Hadv3 & Hadv4) Ebf].
      set (s7 := fst (st_tally s3)) in *. set (bf := snd (st_tally s3)) in *.
      rewrite <- Ews1 in Hslack.
      pose proof (trip_end s1 s2 s3 s7 adv HF1 Hl1 Hslack HR MR TR (conj Hadv1 Hadv2) Hadv3) as TE.
      destruct TE as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Esn7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & T71 & HC7 & Hih7 & Hml7).
      pose proof HR as (T2 & Estr2 & Eml2 & Elook2 & Esn2 & Ems2 & Epb2 & Elfc2 & Edfc2 & Lh2 & Lp2 & Bh2 & Bp2 & Bih2 & HC2).
      pose proof MR as (T3 & Estr3 & Elook3 & Esn3 & Epb3 & Elfc3 & Edfc3 & Ehd3 & Epv3 & Eih3 & Hml3 & Hms3 & Hdist3).
      assert (T31 : TF s3 = TF s1) by (rewrite T3; exact T2).
      pose proof (TF_fields _ _ T31) as ((_ & Elz3 & _) & (_ & Ews3 & _) & _).
      pose proof (cfg_ranges s1 D1 X1 ltac:(rewrite Hm1; lia)) as (_ & _ & Glz & _).
      pose proof (dx_tfc _ X1) as Xtfc1.
      assert (TI1 : trip_inv s1).
      { apply (trip_inv_intro s1 D1 (dx_insh _ X1) ltac:(pose proof (dx_ml _ X1) as R; unfold MAX_MATCH in R; exact R) ltac:(clear - Glz; lia)
                 ltac:(clear - Hsn1 Hn1; lia) ltac:(clear - Hsn1 Hn1; lia)); intros i; [apply (Xtfc1 TL i) | apply (Xtfc1 TD i)]. }
      assert (TI3 : trip_inv s3).
      { apply (trip_inv_transfer s1 s3 TI1 T31); rewrite ?Estr3, ?Estr2, ?Elook3, ?Elook2, ?Esn3, ?Esn2, ?Eih3, ?Ehd3, ?Epv3, ?Elfc3, ?Elfc2, ?Edfc3, ?Edfc2; try reflexivity.
        - exact Bih2.
        - unfold MAX_MATCH in Hml3. exact Hml3.
        - exact Hms3.
        - exact Bh2.
        - exact Bp2. }
      assert (FOK : bf = true -> flush_ok s7 0).
      { intros _. exact (proj1 (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Hm7; lia))))). }
      split.
      { split; [exact Hl0|]. split; [exact Hfw|]. split; [exact Hl1r|]. intros _.
        change (trip_inv s1 /\ 1 <= ds_lookahead s1 <= 2 * ds_w_size s /\ (lm_cond s2 hh = true -> lm_ok s2 hh)
                /\ (trip_inv s3 /\ 1 <= ds_lookahead s3 <= 2 * ds_w_size s /\ (MIN_MATCH <= ds_match_length s3 -> dist_ok s3)
                    /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s /\ (bf = true -> flush_ok s7 0))).
        split; [exact TI1|]. split; [split; [exact Hl1 | exact (proj2 Hl1r)]|].
        split; [exact (lm_stage_ok s1 s2 hh HF1 Hl1 ltac:(rewrite <- Ews1 in Hss1; exact Hss1) HR Hlm)|].
        split; [exact TI3|]. split; [rewrite Elook3, Elook2; split; [exact Hl1 | exact (proj2 Hl1r)]|].
        split.
        { intros H3. destruct (Hdist3 H3) as [Hmll Hd]. unfold dist_ok, OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast3.tdist_D. rewrite Elook3, Elook2, Estr3, Estr2, Ews3.
          split; [exact Hmll|]. split; [| clear - Hss1 Hml3 Ews1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia].
          rewrite Z.mod_small; clear - Hd Sw1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia. }
        split; [rewrite <- Ews1; exact Hl7 | exact FOK]. }
      unfold st_rest. fold s2 hh s3. fold s7 bf.
      unfold st_bflush. destruct bf.
      +
        rewrite flush_block_eq'.
        pose proof (flush_block_only_facts c0 s7 0 HFB HC0w D7 V7 XX7 FE7 Hst7 ltac:(rewrite Hm7; lia) (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Hm7; lia)))) as FB. cbv zeta in FB.
        destruct FB as (_ & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
        set (s' := flush_block_only s7 0) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [Z.eqb negb fst snd].
        * split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [exact (OUTLE_trans _ _ _ Ho7 Ho')|]. reflexivity.
        * pose proof (PF_fields _ _ EPF) as (_ & _ & (Est' & _) & _).
          split.
          -- split; [exact DC'|]. split; [rewrite HK'; exact HK7|]. split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)]|].
             split; [rewrite (dmode_PF _ _ EPF); exact Hm7|]. split; [rewrite Est'; exact Hst7|]. exact (OUTLE_trans _ _ _ Ho7 Ho').
          -- unfold lz_meas. rewrite Elook', Eain. unfold lz_meas in Hmeas7, Emeas. rewrite <- Emeas. exact Hmeas7.
      +
        cbn [fst snd].
        assert (Hn7 : nsym s7 <= ds_lit_bufsize s7 - 2).
        { symmetry in Ebf. apply Z.eqb_neq in Ebf. rewrite Esn3, Esn2 in Ebf.
          pose proof (TF_fields _ _ T31) as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Ese3) & _). rewrite Ese3, (df_symend _ D1) in Ebf.
          rewrite Elbs7, N7. clear - Ebf Hsn1 Hn1. lia. }
        split.
        -- split; [split; [split; [exact D7 | exact (X7 Hn7)] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
           split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
        -- rewrite <- Emeas. exact Hmeas7.
  Qed.

  Lemma fast_loop : forall fuel s, FTI s -> lz_meas s < Z.of_nat fuel ->
    loop_ok (ds_w_size s0) (ds_hash_size s0) fuel s flush
    /\ match snd (deflate_fast_loop fuel s flush) with
       | None => FTI (fst (deflate_fast_loop fuel s flush)) /\ ds_lookahead (fst (deflate_fast_loop fuel s flush)) = 0
       | Some bs => RET (fst (deflate_fast_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (FTI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite loop_ok_S, loop_step. destruct (fast_step s HI) as [HT HC].
    destruct (snd (st_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (st_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  Lemma DD_set_insert : forall s v, dwf s -> DX s -> 0 <= v <= ds_strstart s -> v <= ds_w_size s ->
    dwf (set_insert s v) /\ DX (set_insert s v).
  Proof.
    intros s v D X Hv1 Hv2. split.
    - destruct D; constructor; try (dsred; assumption).
    - pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
      pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (dx_chain _ X) as Xchain.
      assert (En : nsym (set_insert s v) = nsym s) by reflexivity.
      assert (Em : dmode (set_insert s v) = dmode s) by reflexivity.
      destruct X; constructor; rewrite ?En, ?Em; try (dsred; assumption).
  Qed.

  Lemma fast_tail : forall s, FTI s -> ds_lookahead s = 0 ->
    tail_ok (ds_w_size s0) s flush
    /\ BFPOST c0 s0 flush (deflate_tail (tail_st s) flush).
  Proof.
    intros s HF Hl0.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (FTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hpl & Hml & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (KV_fields _ _ HK) as (Ews0 & _).
    set (st := tail_st s).
    assert (Efs : forall A (g : deflate_state -> A), (forall x v, g (set_insert x v) = g x) -> g st = g s) by (intros A g Hg; subst st; unfold tail_st; apply Hg).
    assert (Eins : 0 <= ds_insert st <= ds_strstart s /\ ds_insert st <= MIN_MATCH - 1).
    { subst st. unfold tail_st. dsred. destruct (Z.ltb_spec (ds_strstart s) (MIN_MATCH - 1)); unfold MIN_MATCH in *; lia. }
    destruct (DD_set_insert s (ds_insert st) D X ltac:(clear - Eins; lia) ltac:(clear - Eins Sw; unfold MIN_MATCH in Eins; lia)) as [Dst Xst].
    assert (Est : set_insert s (ds_insert st) = st) by (subst st; unfold tail_st; destruct s; reflexivity).
    rewrite Est in Dst, Xst.
    assert (Estrm : ds_strm st = ds_strm s) by (apply Efs; reflexivity).
    assert (Vst : SV c0 st) by (apply (SV_strm c0 s st Estrm V)).
    assert (DCst : DC c0 st) by (exact (conj (conj Dst Xst) Vst)).
    assert (Hpst : ds_pending st = 0) by (rewrite (Efs _ ds_pending) by reflexivity; exact Hp).
    assert (Hmst : dmode st = 3) by (rewrite (Efs _ dmode) by reflexivity; exact Hm).
    assert (Hstst : ds_status st <> FINISH_STATE) by (rewrite (Efs _ ds_status) by reflexivity; exact Hst).
    assert (HKst : KV st = KV s0) by (rewrite (Efs _ KV) by reflexivity; exact HK).
    assert (Hlst : ds_lookahead st = 0) by (rewrite (Efs _ ds_lookahead) by reflexivity; exact Hl0).
    assert (Esn : ds_sym_next st = ds_sym_next s) by (apply Efs; reflexivity).
    assert (Host : OUTLE s0 st) by (apply (OUTLE_trans _ s); [exact Ho | apply OUTLE_strm; exact Estrm]).
    assert (Hmast : ds_match_available st = 0) by (rewrite (Efs _ ds_match_available) by reflexivity; exact Hma).
    assert (FB : forall last, 0 <= last <= 1 ->
      let s' := flush_block_only st last in
      flush_ok st last /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ ds_lookahead s' = 0 /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
      /\ ds_match_available s' = 0).
    { intros last Hlast.
      pose proof (flush_block_only_facts c0 st last HFB HC0w Dst Vst (DX_DXX _ Xst) (DC_fb_entry c0 st last HC0w DCst Hpst ltac:(rewrite Hmst; lia) Hlast)
                    Hstst ltac:(rewrite Hmst; lia) (DX_BND st Xst)) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & EPF & _ & Elook' & _ & _ & _ & _ & Hpa & _).
      pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & _).
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [rewrite HK'; exact HKst|]. split; [exact (OUTLE_trans _ _ _ Host Ho')|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split.
    -
      split; [clear - Hstr Hlook Hsl Ews0; lia|]. split; [clear - Hsn Hn Sl; lia|].
      split; [intros _; exact (proj1 (FB 1 ltac:(lia))) | intros _ _; exact (proj1 (FB 0 ltac:(lia)))].
    -
      unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
      + rewrite flush_block_eq'. destruct (FB 1 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
        set (s' := flush_block_only st 1) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros HH; discriminate HH.
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros _. destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)].
      + destruct (Z.eqb_spec (ds_sym_next st) 0) as [N0|N0]; cbn [negb].
        * unfold BFPOST; cbn [fst snd].
          split; [exact DCst|]. split; [exact HKst|]. split; [exact Host|]. split; [intros _; split; [exact Hpst | split; [exact F4 | exact Hmast]]|].
          split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
        * rewrite flush_block_eq'. destruct (FB 0 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
          set (s' := flush_block_only st 0) in *. clearbody s'.
          destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
             split; [intros _; split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)] | split; [exact F4 | exact Hma']]|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
  Qed.

End Fast.


Theorem fast_bf_spec : FB_CALL -> BF_SPEC 3 fast_safe deflate_fast.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : FTI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (fast_loop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (Hao : 0 <= cs_avail_out (ds_strm s) < 2 ^ 32).
  { pose proof (sv_out _ _ V) as Ou. pose proof (sv_aout _ _ V) as Ao. pose proof (c0_out _ (c0'_ok _ HC0)) as O0. pose proof (c0_aout _ (c0'_ok _ HC0)) as A0.
    rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou. pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl. lia. }
  split.
  - unfold fast_safe. split; [exact (dwf_DWF s D Hao)|]. split; [exact HL|].
    destruct (snd (deflate_fast_loop (lz_fuel s) s flush)); [exact I|].
    destruct HR as [HF' Hl']. exact (proj1 (fast_tail c0 s flush HC0 HFB _ HF' Hl')).
  - unfold deflate_fast.
    destruct (deflate_fast_loop (lz_fuel s) s flush) as [s' r] eqn:E. cbn [fst snd] in HR.
    destruct r as [bs|].
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + destruct HR as [HF' Hl']. exact (proj2 (fast_tail c0 s flush HC0 HFB _ HF' Hl')).
Qed.
