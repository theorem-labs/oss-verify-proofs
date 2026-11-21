(** * LkNb — K1: [ZrNbStarveShort_STMT] discharged (q7-decode leavekill
    fork, 2026-08-22, OFF-TREE SCRATCH — PROVISIONAL).

    Statement: the ratified Gap7LeaveKill.v (md5
    , byte-verbatim copy in this bed).

    Proof: the NBLeave twin of [ZReproQ6A.inf_nb_go_ok]'s induction,
    with the fuel-sufficiency invariant [n <= 8*fuel + br_bits] carried
    so the fuel-exhaustion corner is dead (the O case's guard would
    have answered NBOk).  The only NBLeave production site is then a
    failed PULLBYTE, which certifies [br_have = 0] at a preserved
    stream; [br_stream_length] turns the guard's [br_bits < n] into
    the statement's length bound.

    PA-EXPORT: k1_nb_starve_short. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The starve walk: under the fuel invariant, a leave certifies an
    empty byte counter, a preserved stream, and a bit count still under
    the demand.  [n <= 32] keeps [br_wf_pullbyte]'s 31-bit ceiling. *)
Lemma lk_nb_go_leave : forall f n b b',
  br_wf b -> 0 <= n <= 32 ->
  n <= 8 * Z.of_nat f + br_bits b ->
  inf_nb_go f n b = NBLeave b' ->
  br_wf b' /\ br_stream b' = br_stream b /\ br_have b' = 0
  /\ br_bits b' < n.
Proof.
  induction f as [|f IH]; intros n b b' Hwf Hn Hfuel H;
    cbn [inf_nb_go] in H.
  - destruct (Z.ltb_spec (br_bits b) n) as [Hlt|]; [|discriminate].
    cbn [Z.of_nat] in Hfuel. lia.
  - destruct (Z.ltb_spec (br_bits b) n) as [Hlt|]; [|discriminate].
    destruct (br_pullbyte b) as [b1|] eqn:EP.
    + assert (Hwf1 : br_wf b1)
        by (apply (br_wf_pullbyte b b1); [exact Hwf | lia | exact EP]).
      destruct (br_pullbyte_step b b1 EP) as (Hh1 & _ & Hb1 & _).
      destruct (IH n b1 b' Hwf1 Hn ltac:(lia) H) as (W & S & Hv & Hb).
      split; [exact W|].
      split; [rewrite S; exact (br_stream_pullbyte b b1 Hwf EP)|].
      split; [exact Hv | exact Hb].
    + injection H as <-.
      apply br_pullbyte_none in EP.
      repeat split; try assumption; try reflexivity; try apply Hwf.
Qed.

Theorem k1_nb_starve_short : ZrNbStarveShort_STMT.
Proof.
  unfold ZrNbStarveShort_STMT.
  intros n b b' Hwf Hn H.
  unfold inf_nb in H.
  pose proof Hwf as (Hbits & _ & _ & _).
  destruct (lk_nb_go_leave (Z.to_nat n) n b b' Hwf Hn
              ltac:(rewrite Z2Nat.id by lia; lia) H)
    as (Hwf' & HS & Hh0 & Hblt).
  pose proof (br_stream_length b' Hwf') as HL.
  split.
  { rewrite <- HS. lia. }
  split; [exact HS | exact Hh0].
Qed.

Set Printing Width 2000.
Print Assumptions k1_nb_starve_short.
