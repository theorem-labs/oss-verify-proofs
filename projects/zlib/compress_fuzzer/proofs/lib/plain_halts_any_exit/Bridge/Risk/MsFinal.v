(** * Bridge.Risk.MsFinal — risk item (b), match_start live range: the
    statements [RiskIface] publishes, proved (group R).

    [RiskIface] closes its (b) lemmas by [exact] of the [_r] theorems here
    (the definitions are [MsDefs]'s, shared). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Chunk Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require Import MsKit MsFill MsDefs MsTrip MsTripS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Theorem ms_lm_live_r : forall g l cur,
  ms_prev_ok g l -> dg_w_mask g = dg_w_size g - 1 -> 1 <= dg_w_size g ->
  NIL < cur < ls_strstart l -> ls_strstart l - cur <= dg_max_dist g ->
  let r := longest_match g l cur in
  ls_prevlen l < fst r -> 1 <= ls_strstart l - snd r <= dg_max_dist g.
Proof. intros g l cur Hp Hwm Hws Hc Hd. exact (lm_live g l cur Hwm Hws Hp Hc Hd). Qed.

Lemma fill_slow_fast : forall s, msi s ->
  (ms_fast_inv s -> ms_fast_inv (ds_fill s)) /\ (ms_slow_inv s -> ms_slow_inv (ds_fill s)).
Proof.
  intros s Hm. destruct (fill_msi s Hm) as (_ & (A1 & A2 & A3 & A4 & A5) & EC).
  unfold ms_fast_inv, ms_slow_inv. rewrite EC, A2, A3. split; [exact (fun H => H)|].
  intros [S1 S2]. split; [destruct S1; [left | right]; lia | intros H; specialize (S2 H); lia].
Qed.

Theorem ms_fill_r : forall s,
  ms_inv s -> ms_inv (ds_fill s)
  /\ (ms_fast_inv s -> ms_fast_inv (ds_fill s))
  /\ (ms_slow_inv s -> ms_slow_inv (ds_fill s)).
Proof.
  intros s H. apply ms_inv_msi in H. destruct (fill_msi s H) as (H' & _ & _).
  split; [apply ms_inv_msi; exact H' | exact (fill_slow_fast s H)].
Qed.

Theorem ms_fast_emit_r : forall p0,
  ms_inv p0 -> ms_fast_inv p0 -> 1 <= ls_lookahead (d_ls p0) ->
  MIN_MATCH <= ls_matchlen (df_l1 p0) ->
  1 <= ls_strstart (df_l1 p0) - ls_matchstart (df_l1 p0) <= dg_max_dist (d_cfg p0).
Proof.
  intros p0 H [Fm Fp] Hl Hd. apply ms_inv_msi in H.
  destruct (df_l1_facts p0 H) as (_ & S1 & _ & _ & _ & _ & D1). unfold MIN_MATCH in *.
  rewrite S1. destruct D1 as [[E _]|[_ E]]; [lia | apply E; lia].
Qed.

Theorem ms_slow_emit_r : forall p0,
  ms_inv p0 -> ms_slow_inv p0 -> 1 <= ls_lookahead (d_ls p0) ->
  MIN_MATCH <= ls_prevlen (ds_l2 p0) -> ls_matchlen (ds_l2 p0) <= ls_prevlen (ds_l2 p0) ->
  1 <= ls_strstart (ds_l2 p0) - 1 - ls_prevmatch (ds_l2 p0) <= dg_max_dist (d_cfg p0).
Proof.
  intros p0 H [_ S2] Hl Hd _. apply ms_inv_msi in H.
  destruct (ds_l2_facts p0 H) as (_ & S1 & _ & _ & _ & PL & PM & _). rewrite S1, PM. rewrite PL in Hd.
  specialize (S2 Hd). lia.
Qed.

(** The step: fill, then (unless the fill stops the loop) one body. *)
Lemma step_cases : forall (body : DSt -> DsStep) flush s,
  step_state (if (ds_need s) && (ds_need (ds_fill s)) && (Z.eqb flush Z_NO_FLUSH)
              then DsRet NeedMore (ds_fill s)
              else if (ds_need s) && (Z.eqb (ls_lookahead (d_ls (ds_fill s))) 0)
              then DsBreak (ds_fill s)
              else body (ds_fill s))
  = ds_fill s
  \/ (step_state (if (ds_need s) && (ds_need (ds_fill s)) && (Z.eqb flush Z_NO_FLUSH)
                  then DsRet NeedMore (ds_fill s)
                  else if (ds_need s) && (Z.eqb (ls_lookahead (d_ls (ds_fill s))) 0)
                  then DsBreak (ds_fill s)
                  else body (ds_fill s))
      = step_state (body (ds_fill s))
      /\ (ds_need s = false \/ ls_lookahead (d_ls (ds_fill s)) <> 0)).
Proof.
  intros body flush s. destruct (_ && _ && _); [left; reflexivity|].
  destruct (ds_need s) eqn:EN; cbn [andb].
  - destruct (Z.eqb_spec (ls_lookahead (d_ls (ds_fill s))) 0); [left; reflexivity | right; split; [reflexivity | right; assumption]].
  - right. split; [reflexivity | left; reflexivity].
Qed.

Lemma body_lookahead : forall s, msi s ->
  (ds_need s = false \/ ls_lookahead (d_ls (ds_fill s)) <> 0) -> 1 <= ls_lookahead (d_ls (ds_fill s)).
Proof.
  intros s H C. destruct (fill_msi s H) as ((_ & (_ & _ & Hl & _)) & (A1 & _) & _).
  destruct C as [C|C]; [|lia].
  unfold ds_need in C. apply Z.ltb_ge in C. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in C. lia.
Qed.

Theorem ms_df_step_r : forall flush s,
  ms_inv s -> ms_fast_inv s ->
  ms_inv (step_state (df_step flush s)) /\ ms_fast_inv (step_state (df_step flush s)).
Proof.
  intros flush s H F. apply ms_inv_msi in H.
  destruct (fill_msi s H) as (H1 & _ & _). destruct (fill_slow_fast s H) as [FF _]. specialize (FF F).
  unfold df_step.
  destruct (step_cases (df_body flush) flush s) as [E|[E C]]; rewrite E.
  - split; [apply ms_inv_msi; exact H1 | exact FF].
  - destruct (df_body_msi flush (ds_fill s) H1 FF (body_lookahead s H C)) as [A B].
    split; [apply ms_inv_msi; exact A | exact B].
Qed.

Theorem ms_ds_step_r : forall flush s,
  ms_inv s -> ms_slow_inv s ->
  ms_inv (step_state (ds_step flush s)) /\ ms_slow_inv (step_state (ds_step flush s)).
Proof.
  intros flush s H F. apply ms_inv_msi in H.
  destruct (fill_msi s H) as (H1 & _ & _). destruct (fill_slow_fast s H) as [_ FS]. specialize (FS F).
  unfold ds_step.
  destruct (step_cases (ds_body flush) flush s) as [E|[E C]]; rewrite E.
  - split; [apply ms_inv_msi; exact H1 | exact FS].
  - destruct (ds_body_msi flush (ds_fill s) H1 FS (body_lookahead s H C)) as [A B].
    split; [apply ms_inv_msi; exact A | exact B].
Qed.

Theorem ms_init_r : forall level t0 z,
  defl_new level 8 15 8 0 = Some t0 ->
  let t := setD_strm z t0 in
  ms_inv t /\ ms_fast_inv t /\ ms_slow_inv t.
Proof.
  intros level t0 z H t. subst t. unfold defl_new, defl_init2 in H.
  destruct (defl_wrap 15) as [[wrap wb]|] eqn:EW; [| discriminate H].
  vm_compute in EW. injection EW as <- <-. cbn [Z.eqb] in H.
  destruct (defl_args_ok _ _ _ _ _ _); [| discriminate H].
  injection H as <-.
  unfold ms_fast_inv, ms_slow_inv, deflate_reset, lm_init, clear_hash. cbv zeta.
  cbn [d_cfg d_ls setD_strm ls_matchlen ls_prevlen ls_lookahead ls_strstart ls_matchstart
       setL_insh setL_matchavail setL_prevlen setL_matchlen setL_insert setL_lookahead setL_blockstart setL_strstart
       setL_head setL_windowsize].
  unfold MIN_MATCH, MIN_LOOKAHEAD, MAX_MATCH.
  split; [| split; [split; lia | split; [left; lia | intros HH; exfalso; lia]]].
  constructor; cbn; try change (Z.shiftl 1 15) with 32768; try change (Z.shiftl 1 (8 + 7)) with 32768; try lia.
  split.
  - intros i Hi. cbn. repeat (match goal with |- context [if ?c then _ else _] => destruct c end);
      unfold NIL, zzero, zconst in *; lia.
  - intros i Hi. cbn. repeat (match goal with |- context [if ?c then _ else _] => destruct c end);
      unfold NIL, zzero, zconst in *; lia.
Qed.
