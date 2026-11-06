(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Monad MSafe STree Malloc MallocCtrl Prog KInv KLink Path.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Fixpoint refuse_run {R} (t : stree ev Z R) (b : Z) : option R :=
  match t with
  | SRet r => Some r
  | SVis e k =>
      match e with
      | EMmap _ _ _ _ => refuse_run (k (neg_errno ENOMEM)) b
      | EMprotect _ _ _ => refuse_run (k (neg_errno ENOMEM)) b
      | EBrk req => if req =? 0 then None else refuse_run (k b) b
      | _ => None
      end
  end.

Definition refuses (s : PState) (n : Z) : Prop :=
  exists cs', refuse_run (cmalloc (ps_m s) n) (ps_brk s) = Some (cs', None).

End AC_1.
