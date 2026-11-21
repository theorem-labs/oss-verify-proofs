(** * EnoughFitsPhi — the Phi law of the use-loop accounting [chain_codes].

    Moved verbatim out of EnoughFitsB10.v (section 1) so that the
    memo-soundness files (EnoughFitsB11, EnoughFitsB12) no longer import
    EnoughFitsB10 and, through it, the enough.c oracle cells: the
    range-split proofs of those cells (EnoughSplit.v) are built on
    EnoughFitsB11/B12.  EnoughFitsB10 re-exports this file, so every name
    keeps resolving where it did. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The Phi law: fst - rem advances by EXACTLY one per code.
   ========================================================================== *)

Lemma chain_phi : forall k s m r,
  fst (chain_codes k s m r) - snd (chain_codes k s m r)
  = m - r + Z.of_nat k.
Proof.
  induction k as [|k IH]; intros s m r.
  - cbn [chain_codes fst snd]. clear; lia.
  - cbn [chain_codes].
    unfold chain_code.
    destruct (Z.eqb_spec r 0) as [->|Hne].
    + rewrite IH. clear; lia.
    + rewrite IH. clear; lia.
Qed.

Lemma chain_codes_rem_ub : forall k s m r,
  r <= s - 1 -> snd (chain_codes k s m r) <= s - 1.
Proof.
  induction k as [|k IH]; intros s m r Hr.
  - cbn [chain_codes snd]. exact Hr.
  - cbn [chain_codes].
    unfold chain_code.
    destruct (Z.eqb_spec r 0) as [->|Hne].
    + apply IH. clear; lia.
    + apply IH. clear -Hr; lia.
Qed.
