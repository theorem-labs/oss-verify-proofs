(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import ITree Nodes NodesMM Decode.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Monad MSafe STree Malloc MallocCtrl Prog KInv KLink Path MFail.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Fixpoint refrun {R} (t : stree ev Z R) (pb cur : Z) : option R :=
  match t with
  | SRet r => Some r
  | SVis e k =>
      match e with
      | EMmap _ _ _ _ => refrun (k (neg_errno ENOMEM)) pb cur
      | EMprotect _ _ _ => refrun (k (neg_errno ENOMEM)) pb cur
      | EBrk req => if req =? 0 then refrun (k cur) cur cur else refrun (k pb) pb cur
      | _ => None
      end
  end.

Definition kbrk (mo : Model) : Z := bv_unsigned (vm_brk (m_vmmaps mo)).

Fixpoint nomunmap {R} (t : stree ev Z R) (pb cur : Z) : Prop :=
  match t with
  | SRet r => True
  | SVis e k =>
      match e with
      | EMmap _ _ _ _ => nomunmap (k (neg_errno ENOMEM)) pb cur
      | EMprotect _ _ _ => nomunmap (k (neg_errno ENOMEM)) pb cur
      | EBrk req => if req =? 0 then nomunmap (k cur) cur cur else nomunmap (k pb) pb cur
      | EMunmap _ _ => False
      | EPeek _ _ _ => False
      | EUndef _ => True
      end
  end.

Definition refuses_small (cs : mstate) (n : Z) : Prop :=
  forall pb cur cs' p, refrun (cmalloc cs n) pb cur = Some (cs', Some p) -> False.

End AC_1.
