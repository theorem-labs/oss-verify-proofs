(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StepFast.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Set Default Proof Mode "Classic".

Definition far_pair_b (segs : list Segment) (pc : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Auipc rd _, _) =>
          if Z.eqb (bv_unsigned rd) 0 then false else
          match fetch_word segs (Z_to_bv 64 (pc + 4)) with
          | Some w2 =>
              if is_ecall w2 then false else
              match decode_any w2 with
              | Some (Jalr _ rs1 _, _) => Z.eqb (bv_unsigned rs1) (bv_unsigned rd)
              | _ => false
              end
          | None => false
          end
      | _ => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Ltac far_fuse := constr:(true).

(* [comment removed for export] *)
Ltac step1 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac zstep1 := ltac2:(sf_core true).

Ltac far_pair_here :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let f := far_fuse in
      lazymatch f with
      | true => let b := eval vm_compute in (far_pair_b segs pc) in b
      | _ => constr:(false)
      end
  | _ => constr:(false)
  end.

Ltac step ::=
  let b := far_pair_here in
  lazymatch b with
  | true => step1; step1
  | _ => step1
  end.

Ltac zstep ::=
  let b := far_pair_here in
  lazymatch b with
  | true => zstep1; zstep1
  | _ => zstep1
  end.
