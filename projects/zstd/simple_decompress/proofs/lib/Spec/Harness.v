(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require FseNCount ZdHarness.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition PRODUCER_SIZE : Z := 16.
(* [comment removed for export] *)
Definition DCTX_SIZE : Z := 95992.
(* [comment removed for export] *)
Definition BUFF_MAX : Z := 10 * 2^26.

(* [comment removed for export] *)
Definition buff_size (payload : list Z) : Z := ZdHarness.sd_buf_size payload.

Lemma buff_size_range : forall payload, zlength payload <= 2^26 -> 0 <= buff_size payload <= BUFF_MAX.
Proof. intros payload H. unfold buff_size, BUFF_MAX. apply ZdHarness.sd_buf_size_range. exact H. Qed.

Section Harness.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).      (* [comment removed for export] *)
Variable raw_free : ptr -> M St unit.              (* [comment removed for export] *)
Variable new_handler : M St Empty_set.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fuzz_malloc (size : Z) : M St (option ptr) :=
  if 0 <? size then
    r <- raw_malloc size ;;
    match r with
    | Some p => mret (Some p)
    | None => e <- new_handler ;; match (e : Empty_set) with end
    end
  else mret None.

(* [comment removed for export] *)
Definition free_opt (p : option ptr) : M St unit :=
  match p with Some q => raw_free q | None => mret tt end.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z :=
  producer <- fuzz_malloc PRODUCER_SIZE ;;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  dctx <- fuzz_malloc DCTX_SIZE ;;                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rbuf <- fuzz_malloc (buff_size data) ;;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  free_opt rbuf ;;;                                  (* [comment removed for export] *)
  free_opt producer ;;;                              (* [comment removed for export] *)
  free_opt dctx ;;;                                  (* [comment removed for export] *)
  mret 0.

End Harness.
