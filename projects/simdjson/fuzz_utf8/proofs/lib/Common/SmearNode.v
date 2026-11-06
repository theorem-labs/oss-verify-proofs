(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module SMR.

Definition SMEAR_ID : nat := 113.
(* [comment removed for export] *)
Definition SMEAR_SHIFTS : list Z := [1; 2; 4; 8; 16; 32].
Definition V47 : Z := 2 ^ 47 - 1.

Section Node.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Definition smear_level (fk : list kentry) (s : expr) (k : Z) : expr :=
    mkAluK fk ALU_OR s (mkAluK fk ALU_SRL s (ELit k)).
  Definition rebuild (fk : list kentry) (x : expr) : expr :=
    fold_left (smear_level fk) SMEAR_SHIFTS x.

  Definition reg_arg (args : list expr) : nat :=
    match args with
    | [_; ELit r] => if (Z.leb 0 r && Z.ltb r 32)%bool then Z.to_nat r else 10%nat
    | _ => 10%nat
    end.

  Definition xn (args : list expr) (cs : acs) : option acs :=
    match args with
    | x :: _ =>
        let r := reg_arg args in
        let e := reg cs r in
        let fk := facts_of (kn cs) in
        if expr_eqb e (rebuild fk x) then
          match erange (kn cs) x with
          | Some (lo, hi) =>
              if (Z.leb (2 ^ 46) lo && Z.leb hi (2 ^ 47 - 1))%bool
              then Some (set_kn cs (KRange e V47 V47 :: kn cs))
              else None
          | None => None
          end
        else None
    | [] => None
    end.
End Node.

End SMR.
