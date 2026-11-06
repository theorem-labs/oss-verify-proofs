(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg MallocDefs ImgParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module MN.

Section WithSegs.
  Context {fx : FPState}.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable MTB : mtab.

  (* [comment removed for export] *)
  Definition kz (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z := kreadZ segs k b off n.

  (* [comment removed for export] *)
End WithSegs.
End MN.
