(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AZ_huf_iface AZ_huf_lbkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fik_even :=
  lazymatch goal with
  | |- EVENW (edenot ?E (EAlu ALU_ADD ?a ?b)) =>
      change (EVENW (alu64 ALU_ADD (edenot E a) (edenot E b))); apply evenw_add; fik_even
  | |- EVENW (edenot ?E (EMd M_MUL (ELit ?c) ?b)) =>
      change (EVENW (mul_div M_MUL (Z_to_bv 64 c) (edenot E b))); apply evenw_mul_l; [lia | reflexivity]
  | |- EVENW (edenot ?E (EAlu ALU_AND ?a (ELit (-2)))) =>
      change (EVENW (alu64 ALU_AND (edenot E a) (Z_to_bv 64 (-2)))); apply evenw_and_m2
  | |- ?G => fail 1 "fik_even: unexpected term" G
  end.

(* [comment removed for export] *)
Ltac fik_lb_reload :=
  lazymatch goal with
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?x (ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_ADD (edenot E x) (Z_to_bv 64 1)) (edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload2;
      [ fik_even
      | lazymatch c with
        | EAlu ALU_AND ?v (ELit 7) => change (edenot E c) with (alu64 ALU_AND (edenot E v) (Z_to_bv 64 7)); apply land7_mod64
        | _ => cbn [edenot]; rewrite ?u_and64; rewrite ?(u_small 7) by lia; Z.div_mod_to_equations; lia
        end ]
  | |- LBW ?p (edenot ?E (EAlu ALU_SLL (EAlu ALU_OR ?x (ELit 1)) ?c)) =>
      change (LBW p (alu64 ALU_SLL (alu64 ALU_OR (edenot E x) (Z_to_bv 64 1)) (edenot E c)));
      apply (lbw_mono 7 p); [|lia]; apply lbw_reload;
      lazymatch c with
      | EAlu ALU_AND ?v (ELit 7) => change (edenot E c) with (alu64 ALU_AND (edenot E v) (Z_to_bv 64 7)); apply land7_mod64
      | _ => cbn [edenot]; rewrite ?u_and64; rewrite ?(u_small 7) by lia; Z.div_mod_to_equations; lia
      end
  | |- ?G => fail 1 "fik_lb_reload: unexpected term" G
  end.

(* [comment removed for export] *)
Ltac fik_lbw_reload_cell X W :=
  set (W := X) in *;
  let L := fresh "HLBN" in
  assert (L : LBW 8 W) by (subst W; fik_lb_reload);
  clearbody W.
