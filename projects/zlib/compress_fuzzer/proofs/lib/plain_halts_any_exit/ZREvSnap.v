(** * ZREvSnap — the canonical per-event snapshot record.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20).  Converged
    spelling (g6-bound consumer, crc-capstone design, this lane
    producer): the walk exports [Forall (EvSnapOk g) evs] on every
    event list.  Sits between SwEv (FlushEv) and the walk lemmas. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwTally SwEv ZRTreeFacts ZRTreeState.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Definition EvSnapOk (g : DeflGeom) (ev : FlushEv) : Prop :=
  ZRTreeInv (d_ts (fe_s ev))
  /\ ts_optlen (d_ts (fe_s ev)) = 0
  /\ ts_statlen (d_ts (fe_s ev)) = 0
  /\ (fe_last ev = 0 -> ts_symnext (d_ts (fe_s ev)) = dg_sym_end g)
  /\ Forall FarOkTok (fe_toks ev)
  /\ (ls_blockstart (d_ls (fe_s ev)) < 0 ->
      dg_max_dist g < fe_end ev - fe_start ev).
