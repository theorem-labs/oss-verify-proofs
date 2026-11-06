(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require FseNCount FseHarness.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.
Definition PRODUCER_SIZE : Z := 16.
Definition BUFF_MAX : Z := 512.
Definition buff_size (payload : list Z) : Z := FseHarness.fse_bsz payload.
Lemma buff_size_range : forall payload, 2 <= buff_size payload <= BUFF_MAX.
Proof. intros payload. unfold buff_size, BUFF_MAX. apply FseHarness.fse_bsz_range. Qed.
Section Harness.
Context {St ptr : Type}.
Variable raw_malloc : Z -> M St (option ptr).
Variable raw_free : ptr -> M St unit.
Variable new_handler : M St Empty_set.
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
Definition fuzz_one (data : list Z) : M St Z :=
producer <- fuzz_malloc PRODUCER_SIZE ;;
buff <- fuzz_malloc (buff_size data) ;;
free_opt buff ;;;
free_opt producer ;;;
mret 0.
End Harness.
