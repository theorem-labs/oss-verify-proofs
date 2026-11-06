(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXUb.
Import ListNotations. Import KXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac kx_keep_small H :=
  repeat match goal with
  | X : ?T |- _ =>
      lazymatch X with H => fail | _ => idtac end;
      lazymatch type of T with Prop => idtac | _ => fail end;
      first [ lazymatch T with context [edenot] => clear X end
            | lazymatch T with context [ev] => clear X end
            | lazymatch T with context [mem_denot] => clear X end
            | tryif kx_is_arith T then fail else clear X ]
  end.

(* [comment removed for export] *)
Ltac kx_ub_decide_lia H :=
  repeat match type of H with
         | context [Z.ltb ?a ?b] =>
             first [ replace (Z.ltb a b) with true in H by (symmetry; apply Z.ltb_lt; clear H; lia)
                   | replace (Z.ltb a b) with false in H by (symmetry; apply Z.ltb_ge; clear H; lia) ]
         | context [Z.eqb ?a ?b] =>
             first [ replace (Z.eqb a b) with false in H by (symmetry; apply Z.eqb_neq; clear H; lia)
                   | replace (Z.eqb a b) with true in H by (symmetry; apply Z.eqb_eq; clear H; lia) ]
         end;
  cbn [Z.b2z negb Z.lxor Pos.lxor] in H.

Ltac kx_ub_fast H :=
  kx_sltu_in H; kx_ub_norm H; exfalso; kx_keep_small H; kx_ub_decide_lia H;
  first [ apply H; reflexivity | discriminate H | lia | congruence ].

(* [comment removed for export] *)
Ltac kx_trap_fast :=
  first [ match goal with H : ?T |- _ => lazymatch T with context [ALU_SLTU] => idtac end;
                                       lazymatch type of T with Prop => idtac end; solve [kx_ub_fast H] end
        | kx_trap ].
