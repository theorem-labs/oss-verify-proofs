(* the zlib 1.4 twin of ZReproQ6I, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from ZReproQ6I), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * ZReproQ6I — iterate/loop toolkit and mode dispatchers.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-20).  Extracted
    from the body-walk file so the LEN-chain shares it: composition of
    [inf_iter]/[inf_loop], first-step aliasing (two states whose next
    step is THE SAME step value share every iterate/loop of positive
    index — the fallthrough-call idiom), and the one-line [inf_step]
    dispatch reductions per mode.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6I.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.







(** The dispatch reductions. *)
Lemma zr_step_at_type14 : forall c q,
  zr_cflush_ok c ->
  h_mode (s_hdr (q_st q)) = M_TYPE ->
  inf_step14 c q = inf_TYPEDO c q.
Proof.
  intros c q Hok Hm.
  unfold inf_step14, q_mode. rewrite Hm.
  unfold inf_TYPE.
  now rewrite (zr_eqb_nB c Hok), (zr_eqb_nT c Hok).
Qed.

Lemma zr_step_at_stored14 : forall c q,
  h_mode (s_hdr (q_st q)) = M_STORED ->
  inf_step14 c q = inf_STORED c q.
Proof.
  intros c q Hm. unfold inf_step14, q_mode. now rewrite Hm.
Qed.

Lemma zr_step_at_copy14 : forall c q,
  h_mode (s_hdr (q_st q)) = M_COPY ->
  inf_step14 c q = inf_COPY q.
Proof.
  intros c q Hm. unfold inf_step14, q_mode. now rewrite Hm.
Qed.





