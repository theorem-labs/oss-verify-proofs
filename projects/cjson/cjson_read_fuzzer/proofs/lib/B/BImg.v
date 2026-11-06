(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics State.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Export AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SegTask.
Lemma bsegs_task : forall x, find_segment bsegs x 1 <> None -> (x < TASK_SIZE)%Z.
Proof. apply (segs_task_of_tops bsegs 0x5ff000); [reflexivity| unfold TASK_SIZE; lia]. Qed.
