(* the zlib 1.4 twin of Q6AsmSupport, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from Q6AsmSupport), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * Q6AsmSupport — walk-independent plumbing for the face assemblies.

    OWNER: q6-fixedtbl lane (zlib z-repro campaign, 2026-08-20; TL
    assembly-pre-draft assignment).  Everything here is independent of
    the body walk's statement: loop composition and uniqueness, the
    initial reader's byte/stream/wf facts, and the FINISH-flush leave
    lemma (the L0C [zr_leave_done] generalized past its [q_out = o_left]
    premise — at [M_DONE]+[Z_FINISH]+[wsize 0] the window-update guard is
    false REGARDLESS of [wrote]: [m_val M_DONE < m_val M_BAD] holds but
    [< m_val M_CHECK] fails and the flush disjunct dies, so raw/gzip
    tails that never fold [q_out] still leave clean).

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Q6AsmSupport.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Loop plumbing beyond L0C's: composition and uniqueness.
   ========================================================================== *)

Lemma zr_iterloop_compose14 : forall k c q q' n s,
  inf_iter14 k c q = Some q' ->
  inf_loop14 n c q' = Some s ->
  inf_loop14 (k + n) c q = Some s.
Proof.
  induction k as [|k IH]; intros c q q' n s HI HL.
  - cbn [inf_iter14] in HI. injection HI as <-. exact HL.
  - cbn [inf_iter14] in HI. cbn [Nat.add inf_loop14].
    destruct (inf_step14 c q) as [q1| | | |] eqn:E; try discriminate.
    exact (IH c q1 q' n s HI HL).
Qed.

Lemma zr_loop_uniq14 : forall n m c q s s',
  inf_loop14 n c q = Some s ->
  inf_loop14 m c q = Some s' ->
  s = s'.
Proof.
  induction n as [|n IH]; intros m c q s s' H H'; [discriminate|].
  destruct m as [|m]; [discriminate|].
  cbn [inf_loop14] in H, H'.
  destruct (inf_step14 c q) as [q1| | | |] eqn:E;
    try (congruence).
  exact (IH m c q1 s s' H H').
Qed.

(* ==========================================================================
   2.  The initial reader: bytes, stream, well-formedness.
   ========================================================================== *)


(** [br_bytes] of a reader positioned [zlen pre] into [pre ++ rest] is
    [rest] — covers raw (pre = []) and gzip (pre = the 10-byte header). *)

(** At [bits = 0] the stream view is exactly the remaining bytes' bits,
    whatever junk sits in [hold] ([zwrite 0 _ = []]). *)

(** Initial-reader well-formedness from the face's byte premise. *)

(* ==========================================================================
   3.  The FINISH-flush leave: [zr_leave_done] without [q_out = o_left].
   ========================================================================== *)


(** The absorber's half: a non-STREAM_END ret survives the leave — every
    exit path returns MEM/BUF or the state's own ret. *)


(* ==========================================================================
   4.  Amendment #10 entry discharges: reader alignment + input budget at
       the fresh reader (all three face assemblies enter at bits = 0).
   ========================================================================== *)

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(** Reader alignment is vacuous at [bits = 0] (empty byte range) — the
    entry discharge for all three face assemblies. *)

(** The compositional input budget at the fresh reader: [bits = 0]
    collapses it to the face's [zlen] premise. *)

