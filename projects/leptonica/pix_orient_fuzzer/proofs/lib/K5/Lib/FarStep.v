(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Exec Step Frame StepFast.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

(* [comment removed for export] *)
Definition far_link_reg (r : Z) : bool :=
  (Z.eqb r 1) || (Z.eqb r 5) || (Z.eqb r 6) || (Z.eqb r 7) || (Z.eqb r 31).

Definition far_link (segs : list Segment) (pc : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w1 =>
      match decode_any w1 with
      | Some (Auipc rd _, 4%Z) =>
          if far_link_reg (bv_unsigned rd) then
            match fetch_word segs (Z_to_bv 64 (pc + 4)) with
            | Some w2 =>
                match decode_any w2 with
                | Some (Jalr rd2 rs1 _, 4%Z) =>
                    (Z.eqb (bv_unsigned rs1) (bv_unsigned rd)) && ((Z.eqb (bv_unsigned rd2) (bv_unsigned rd)) || (Z.eqb (bv_unsigned rd2) 0))
                | _ => false
                end
            | None => false
            end
          else false
      | _ => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Ltac far_second tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => tac
  | |- _ => idtac
  end.

Ltac far_detect segs pc :=
  let b := eval vm_compute in (far_link segs pc) in b.

(* [comment removed for export] *)
Ltac step_core segs R F pc fc rv m ro ::=
  let b := far_detect segs pc in
  lazymatch b with
  | true => ltac2:(sf_core false); far_second ltac:(idtac; ltac2:(sf_core false))
  | false => ltac2:(sf_core false)
  end.

Ltac zstep ::=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := far_detect segs pc in
      lazymatch b with
      | true => ltac2:(sf_core true); far_second ltac:(idtac; ltac2:(sf_core true))
      | false => ltac2:(sf_core true)
      end
  | |- _ => ltac2:(sf_core true)
  end.

(* [comment removed for export] *)
Ltac far_here :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => let b := far_detect segs pc in idtac "far_link" pc "=" b
  end.
