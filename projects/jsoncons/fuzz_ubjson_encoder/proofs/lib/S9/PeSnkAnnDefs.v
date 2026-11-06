(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5DefsA L5CoreAS9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmSpecs PmSpecsA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESKAND.
Section Specs.
Variable segs : list Segment.

Definition bhdr (M : word -> option byte) (v b n c : Z) : Prop :=
  L5.defined M v 24 /\ L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
  /\ 0 <= n <= c /\ 1 <= c /\ 4096 <= b /\ b mod 16 = 0 /\ L5.defined M b c.

Definition bat (M : word -> option byte) (v b n c : Z) : Prop :=
  L5.defined M v 24 /\ PMSPA.accA M v 24 /\ L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + n) /\ L5.u64_at segs M (v + 16) (b + c)
  /\ 0 <= n <= c /\ 1 <= c /\ 4096 <= b /\ b mod 16 = 0 /\ L5.defined M b c /\ PMSPA.accA M b n /\ PMSPA.annA M b n c.
End Specs.
End PESKAND.
