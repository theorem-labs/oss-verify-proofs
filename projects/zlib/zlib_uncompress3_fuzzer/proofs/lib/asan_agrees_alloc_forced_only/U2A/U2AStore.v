(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac farr_store_extra m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : f16arr ?segs m ?A2 ?k ?f |- _ =>
      first [ apply (f16arr_frame segs m A2 k f a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f32arr ?segs m ?A2 ?k ?f |- _ =>
      first [ apply (f32arr_frame segs m A2 k f a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : f8arr ?segs m ?A2 ?k ?f |- _ =>
      first [ apply (f8arr_frame segs m A2 k f a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac farr_call_extra segs W m m' MU WM :=
  repeat match goal with
  | H : f16arr segs m ?A2 ?k ?f |- _ =>
      first [ apply (f16arr_transport segs W m m' A2 k f) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat split; try exact I; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : f32arr segs m ?A2 ?k ?f |- _ =>
      first [ apply (f32arr_transport segs W m m' A2 k f) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat split; try exact I; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : f8arr segs m ?A2 ?k ?f |- _ =>
      first [ apply (f8arr_transport segs W m m' A2 k f) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat split; try exact I; lia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  end.
