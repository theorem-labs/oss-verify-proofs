(* an earlier development run PROPOSED CURE (2026-09-03) over tree GtInfTotal.v : StepPres's entry lemmas gain the premise
   `LeafPosT (t_codes (s_tab s)) ->` (after amb_ok) for the ReachCore row rc_leafpos; each apply site gains ONE bullet.
   Proof-only; no statement changes.  Owner routes; q4 never writes another lane. *)
(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtInfTotal — [inflate_model] answers
      at ReachSt entry states (Q7 decode lane, zlib-rt, 2026-08-19)

    [InflateThy.inflate_model_total] is Section-conditional on
    [Hstep : forall q, q_pos q -> step_ok c q] — universal over ALL
    positive states, which nothing can discharge (step_ok is a theorem
    only AT reachable states: [StepReach.step_ok_reach]).  This file is
    the ReachSt-THREADED twin: the same rank induction, with
    [step_ok_reach] supplying progress and [step_pres] carrying the
    invariant across [InfCont] trips.

    The conclusion deliberately exposes the EXIT JOINT rather than just
    [Some r]: the state [q0] that took the exiting step satisfies
    [ReachSt], and the step equation ([inf_step c q0 = InfLeave q1] /
    [= InfRet ..]) plus the packaging equation are handed to the
    consumer.  The cross-call re-entry lap (an earlier development run; G1 leave
    invariant, G2 writeback transfer) plugs its per-arm knowledge into
    exactly these two equations; the decode pump (Q7 legs 3-4) consumes
    the composite.  Nothing here claims anything about the LEAVE state
    [q1] — that is G1, not this file.  [InfRet]'s return code is NOT
    judged here either (no arm census in this file); the re-entry lap
    owes [r_ret <> Z_OK] on that side.

    One residual, Section-quantified as in StepReach/StepPres:
    [DynTblOk] (under inhabitation by a sibling lane). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The exit joint: who took the exiting step, and how the result was
    packaged. *)
Definition ExitJoint (c : InfCtx) (r : InfRes) : Prop :=
  (exists q0 q1, ReachSt q0 /\ inf_step c q0 = InfLeave q1
                 /\ inf_leave c q1 = (r_q r, r_ret r))
  \/ (exists q0, ReachSt q0 /\ inf_step c q0 = InfRet (r_q r) (r_ret r)).

Section InfTotalReach.

Variable Hdyn : DynTblOk.

(** The rank induction of [InflateThy.inf_loop_reaches_exit], with the
    invariant threaded.  Match-conclusion (R10): the [InfCont] /
    [InfDead] / [InfFuel] arms are the impossible ones. *)
Lemma inf_loop_reach :
  forall c n q, ReachSt q -> (inf_rank2 q <= n)%nat ->
    exists r, inf_loop (S n) c q = Some r
      /\ match r with
         | InfLeave q1  => exists q0, ReachSt q0 /\ inf_step c q0 = InfLeave q1
         | InfRet q1 rr => exists q0, ReachSt q0 /\ inf_step c q0 = InfRet q1 rr
         | _ => False
         end.
Proof.
  intros c.
  induction n as [|n IH]; intros q HR Hr;
    rewrite inf_loop_S;
    pose proof (step_ok_reach Hdyn c q HR) as HS; unfold step_ok in HS;
    pose proof (step_pres Hdyn c q HR) as HP;
    destruct (inf_step c q) as [q'|q'|q' r0|m0|] eqn:E.
  - destruct HS as [Hp' Hlt]. lia.
  - exists (InfLeave q'). split; [reflexivity|].
    exists q. split; [exact HR | exact E].
  - exists (InfRet q' r0). split; [reflexivity|].
    exists q. split; [exact HR | exact E].
  - contradiction.
  - contradiction.
  - destruct HS as [Hp' Hlt]. cbv beta iota in HP.
    apply IH; [exact HP | lia].
  - exists (InfLeave q'). split; [reflexivity|].
    exists q. split; [exact HR | exact E].
  - exists (InfRet q' r0). split; [reflexivity|].
    exists q. split; [exact HR | exact E].
  - contradiction.
  - contradiction.
Qed.

(** The twin.  Premises: the three NULL booleans are the caller's own
    constants ([zr_inf_call] / [Codec.inf_call] pass [false]); [q_pos]
    and the fuel domination come out of [ReachSt] itself ([rc_pos]),
    so no avail/bits sign premises are needed. *)
Theorem inflate_model_total_reach :
  forall a,
    g_state_null a = false -> g_out_null a = false -> g_in_null a = false ->
    ReachSt (inf_st0 a) ->
    exists r, inflate_model a = Some r /\ ExitJoint (inf_ctx a) r.
Proof.
  intros a Hn1 Hn2 Hn3 HR.
  unfold inflate_model.
  rewrite Hn1, Hn2, Hn3. cbv beta iota.
  pose proof HR as (HC & _).
  pose proof (rc_pos _ HC) as Hp0.
  set (n := Z.to_nat (33 * (8 * br_have (q_br (inf_st0 a))
                            + br_bits (q_br (inf_st0 a))
                            + o_left (q_ob (inf_st0 a)) + 1))).
  assert (Hfuel : Inflate.inf_fuel (inf_st0 a) = S n) by reflexivity.
  assert (Hle : (inf_rank2 (inf_st0 a) <= n)%nat).
  { pose proof (inf_fuel_dominates_rank2 (inf_st0 a) (q_pos_bud _ Hp0)) as HD.
    rewrite Hfuel in HD. lia. }
  destruct (inf_loop_reach (inf_ctx a) n (inf_st0 a) HR Hle) as [r [Heq HJ]].
  rewrite Hfuel, Heq.
  destruct r as [q1|q1|q1 r0|m0|]; try contradiction.
  - destruct (inf_leave (inf_ctx a) q1) as [q2 rr] eqn:EL.
    eexists. split; [reflexivity|].
    left. destruct HJ as [q0 [HR0 E0]].
    exists q0, q1. split; [exact HR0|]. split; [exact E0|].
    cbn [r_q r_ret]. exact EL.
  - eexists. split; [reflexivity|].
    right. destruct HJ as [q0 [HR0 E0]].
    exists q0. split; [exact HR0|]. cbn [r_q r_ret]. exact E0.
Qed.

End InfTotalReach.

(** ** Establishment at the decode driver's exact init

    [zr_decode] / [Codec.inf_call]-shaped callers start from
    [inflateInit2 z_fresh state_fresh wb].  [state_fresh] is all-zeros,
    so every garbage-field premise of [StepPres.reach_init2] is a
    computation; what survives is the per-call buffer contract. *)
Lemma reach_entry_fresh :
  forall z s wb (a : InfArgs),
    inflateInit2 z_fresh state_fresh wb = Some (z, s) ->
    g_st a = s ->
    (forall j, 0 <= g_inbuf a j < 256) ->
    0 <= g_avail_in a <= 4294967290 ->
    0 <= g_avail_out a <= 4294967295 ->
    (forall j, 0 <= g_outbuf a j < 256) ->
    ReachSt (inf_st0 a).
Proof.
  intros z s wb a HI Hg Hbytes Hain Haout Houtb.
  apply (reach_init2 z_fresh state_fresh wb z s a HI Hg Hbytes Hain Haout).
  - intros j. cbv [state_fresh s_win w_win zzero zconst]. lia.
  - cbv [state_fresh s_cur u_length]. lia.
  - unfold lens_ok. intros i.
    cbv [state_fresh s_bld b_lens zzero zconst]. lia.
  - cbv [state_fresh s_bld b_have]. lia.
  - cbv [state_fresh s_bld b_nlen]. lia.
  - cbv [state_fresh s_bld b_ndist]. lia.
  - intros i.
    cbv [state_fresh s_tab t_codes tnone c_op c_bits c_val].
    repeat split; try lia;
      try (intros H; exfalso; apply H; reflexivity).
  - (* W9 rc_leafpos (an earlier development run, proposed proof-only cure): the fresh codes array is [tnone] *)
    exact ItGTblLeafPos.leafpos_tnone.
  - exact Houtb.
Qed.

(** [zlist] of a byte list is byte-valued at EVERY index (out-of-range
    reads the 0 default) — the byte premise of [reach_entry_fresh] in
    the shape [zr_inf_call]'s [g_inbuf := zlist inb] wants it. *)
Lemma zlist_bytes :
  forall l, Forall (fun b => 0 <= b < 256) l ->
    forall j, 0 <= zlist l j < 256.
Proof.
  intros l Hl j. unfold zlist.
  destruct (Nat.lt_ge_cases (Z.to_nat j) (length l)) as [Hlt|Hge].
  - rewrite Forall_forall in Hl. apply Hl, nth_In, Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

(** Control (semantic receipt): the premises are inhabitable at BOTH
    decode windowBits values, at the exact entry record [zr_inf_call]
    builds (mirrored field-for-field; two input bytes, the decode
    pump's 4096-byte window).  A statement whose premises could not be
    supplied here would be dead on arrival at the face. *)
Example reach_entry_fresh_control_raw :
  exists z s, inflateInit2 z_fresh state_fresh (-15) = Some (z, s)
    /\ ReachSt (inf_st0 {| g_st := s; g_state_null := false; g_z := z;
                           g_inbuf := zlist [3; 0]; g_next_in := 0;
                           g_avail_in := zlen [3; 0]; g_in_null := false;
                           g_outbuf := zzero; g_next_out := 0;
                           g_avail_out := 4096; g_out_null := false;
                           g_flush := Z_NO_FLUSH; g_walloc := true;
                           g_wfresh := zzero |}).
Proof.
  destruct (inflateInit2 z_fresh state_fresh (-15)) as [[z s]|] eqn:EI;
    [| exfalso; vm_compute in EI; discriminate].
  exists z, s. split; [reflexivity|].
  apply (reach_entry_fresh z s (-15)).
  - exact EI.
  - reflexivity.
  - apply zlist_bytes. repeat constructor; lia.
  - cbn [g_avail_in].
    assert (zlen [3; 0] = 2) as -> by (vm_compute; reflexivity). lia.
  - cbn [g_avail_out]. lia.
  - intros j. cbn [g_outbuf]. cbv [zzero zconst]. lia.
Qed.

Example reach_entry_fresh_control_auto :
  exists z s, inflateInit2 z_fresh state_fresh 47 = Some (z, s)
    /\ ReachSt (inf_st0 {| g_st := s; g_state_null := false; g_z := z;
                           g_inbuf := zlist [31; 139]; g_next_in := 0;
                           g_avail_in := zlen [31; 139]; g_in_null := false;
                           g_outbuf := zzero; g_next_out := 0;
                           g_avail_out := 4096; g_out_null := false;
                           g_flush := Z_NO_FLUSH; g_walloc := true;
                           g_wfresh := zzero |}).
Proof.
  destruct (inflateInit2 z_fresh state_fresh 47) as [[z s]|] eqn:EI;
    [| exfalso; vm_compute in EI; discriminate].
  exists z, s. split; [reflexivity|].
  apply (reach_entry_fresh z s 47).
  - exact EI.
  - reflexivity.
  - apply zlist_bytes. repeat constructor; lia.
  - cbn [g_avail_in].
    assert (zlen [31; 139] = 2) as -> by (vm_compute; reflexivity). lia.
  - cbn [g_avail_out]. lia.
  - intros j. cbn [g_outbuf]. cbv [zzero zconst]. lia.
Qed.
