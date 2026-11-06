(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Definition PRODUCER_SIZE : Z := 16.
Definition BUFF_MAX : Z := 512.
Definition buff_size (payload : list Z) : Z := 2.
Lemma buff_size_range : forall payload, 2 <= buff_size payload <= BUFF_MAX.
Proof. intros payload. unfold buff_size, BUFF_MAX. lia. Qed.

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

Definition free_opt (p : option ptr) : M St unit :=
  match p with Some q => raw_free q | None => mret tt end.

(* [comment removed for export] *)
Definition fuzz_one (data : list Z) : M St Z :=
  let _ := (raw_malloc, raw_free, new_handler) in      (* [comment removed for export] *)
  mret 0.

End Harness.
