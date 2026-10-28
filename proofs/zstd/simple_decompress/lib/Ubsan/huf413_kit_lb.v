(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.BothW Require Import AZ_hufkit42e.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Lemma h413_lbw_or_sll : forall (x y : word), bv_unsigned y <= 8 ->
  LBW 8 (alu64 ALU_SLL (alu64 ALU_OR x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hy. change (LBW 8) with (LBW (0 + 8)). apply lbw_sll; [apply lbw_or1 | | lia].
  pose proof (bv_unsigned_in_range 64 y) as R. rewrite Z.mod_small; [exact Hy|]. lia.
Qed.

Lemma h413_lbw_add_sll : forall (x y : word), EVENW x -> bv_unsigned y <= 8 ->
  LBW 8 (alu64 ALU_SLL (alu64 ALU_ADD x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hx Hy. change (LBW 8) with (LBW (0 + 8)). apply lbw_sll; [apply lbw_add1; exact Hx | | lia].
  pose proof (bv_unsigned_in_range 64 y) as R. rewrite Z.mod_small; [exact Hy|]. lia.
Qed.

Ltac h413_even :=
  lazymatch goal with
  | |- EVENW (edenot ?E (EAlu ALU_ADD ?a ?b)) =>
      change (EVENW (alu64 ALU_ADD (edenot E a) (edenot E b))); apply evenw_add; h413_even
  | |- EVENW (edenot ?E (EMd M_MUL (ELit ?c) ?b)) =>
      change (EVENW (mul_div M_MUL (Z_to_bv 64 c) (edenot E b))); apply evenw_mul_l; [lia | reflexivity]
  | |- EVENW (edenot ?E (EAlu ALU_AND ?a (ELit (-2)))) =>
      change (EVENW (alu64 ALU_AND (edenot E a) (Z_to_bv 64 (-2)))); apply evenw_and_m2
  | |- ?G => fail 1 "h413_even: unexpected term" G
  end.

Ltac h413_amt :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?a) <= 8 =>
      apply Z.leb_le;
      first
        [ match goal with H : bv_unsigned (ev E ?j) = 0 |- _ =>
            refine (kx_enum_ok E a j 0 1%nat (fun v => v <=? 8) _ _ _);
            [ vm_compute; reflexivity | vm_compute; reflexivity | lia ] end
        | match goal with H : bv_unsigned (ev E ?j) <> 0 |- _ =>
            refine (kx_enum_ok E a j 1 255%nat (fun v => v <=? 8) _ _ _);
            [ vm_compute; reflexivity | vm_compute; reflexivity
            | assert (bv_unsigned (ev E j) <= 255) by (first [lia | kx_lia]); lia ] end ]
  end.

Ltac h413_keep :=
  match goal with
  | AC : rw_cells _ _ _ ?cs |- _ =>
      lazymatch cs with
      | context [C8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_OR ?x (ELit 1)) ?a))] =>
          let KB := fresh "KB" in
          assert (KB : kx_keep (LBW 8 (edenot E (EAlu ALU_SLL (EAlu ALU_OR x (ELit 1)) a))))
            by (unfold kx_keep;
                change (LBW 8 (alu64 ALU_SLL (alu64 ALU_OR (edenot E x) (Z_to_bv 64 1)) (edenot E a)));
                apply h413_lbw_or_sll; h413_amt)
      | context [C8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?x (ELit 1)) ?a))] =>
          let KB := fresh "KB" in
          assert (KB : kx_keep (LBW 8 (edenot E (EAlu ALU_SLL (EAlu ALU_ADD x (ELit 1)) a))))
            by (unfold kx_keep;
                change (LBW 8 (alu64 ALU_SLL (alu64 ALU_ADD (edenot E x) (Z_to_bv 64 1)) (edenot E a)));
                apply h413_lbw_add_sll; [h413_even | h413_amt])
      end
  end.

Ltac h413_mod512 :=
  apply lb_to_mod512;
  lazymatch goal with |- LB 8 (bv_unsigned ?w) => lazymatch goal with KB : LBW 8 w |- _ => exact KB end end.
