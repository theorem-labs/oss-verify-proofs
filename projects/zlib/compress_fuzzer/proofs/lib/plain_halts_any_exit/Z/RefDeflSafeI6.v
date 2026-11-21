(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayCoreL.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI5b.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflate_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma FB_CALL_ok : FB_CALL.
Proof. exact (FB_CALL_intro overlay_core_proof). Qed.

Theorem dreach_DD : forall s, dreach s -> DD s.
Proof.
  intros s Hr.
  induction Hr as [zc level method wb memlevel strategy chs s zr HML5 H | s zc flush s' zr Hr IH Hzc Hfl E | s zc dict s' zr Hr IH Hz Hb Hl E].
  - exact (dinit_DD zc level method wb memlevel strategy HML5 chs s zr H).
  - pose proof (deflate_m_DD _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok)
                  s zc flush IH Hzc Hfl) as D.
    rewrite E in D. exact D.
  - pose proof (setdict_DD s zc dict IH Hz Hb Hl) as D. rewrite E in D. exact D.
Qed.

