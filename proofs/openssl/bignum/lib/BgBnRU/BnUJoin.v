(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image SysStep Frame.
Import ListNotations.

(* [comment removed for export] *)
Ltac regs_of k :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let R' := eval cbv beta delta [mkR] in R in
    lazymatch R' with
    | TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) => k x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    end
  end.

(* [comment removed for export] *)
Ltac fold_regs :=
  regs_of ltac:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =>
    lazymatch goal with |- evt ?segs ?POST (MS _ ?F ?pc ?fc ?rv ?m ?rom) =>
      change (evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) end).

(* [comment removed for export] *)
Ltac forget_temps :=
  regs_of ltac:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =>
    lazymatch goal with |- evt ?segs ?POST (MS _ ?F ?pc ?fc ?rv ?m ?rom) =>
      refine ((_ : forall y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word, evt segs POST (MS (mkR x1 x2 x3 x4 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F pc fc rv m rom)) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)
    end).

(* [comment removed for export] *)
Ltac setreg_at r v' tac :=
  regs_of ltac:(fun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =>
    lazymatch goal with |- evt ?segs ?POST (MS _ ?F ?pc ?fc ?rv ?m ?rom) =>
      lazymatch r with
      | 1%Z => let H := fresh "Ereg" in assert (H : x1 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR y x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 2%Z => let H := fresh "Ereg" in assert (H : x2 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 y x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 3%Z => let H := fresh "Ereg" in assert (H : x3 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 y x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 4%Z => let H := fresh "Ereg" in assert (H : x4 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 y x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 5%Z => let H := fresh "Ereg" in assert (H : x5 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 y x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 6%Z => let H := fresh "Ereg" in assert (H : x6 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 y x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 7%Z => let H := fresh "Ereg" in assert (H : x7 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 y x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 8%Z => let H := fresh "Ereg" in assert (H : x8 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 y x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 9%Z => let H := fresh "Ereg" in assert (H : x9 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 y x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 10%Z => let H := fresh "Ereg" in assert (H : x10 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 11%Z => let H := fresh "Ereg" in assert (H : x11 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 12%Z => let H := fresh "Ereg" in assert (H : x12 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 13%Z => let H := fresh "Ereg" in assert (H : x13 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 14%Z => let H := fresh "Ereg" in assert (H : x14 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 y x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 15%Z => let H := fresh "Ereg" in assert (H : x15 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 y x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 16%Z => let H := fresh "Ereg" in assert (H : x16 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 17%Z => let H := fresh "Ereg" in assert (H : x17 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 y x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 18%Z => let H := fresh "Ereg" in assert (H : x18 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 y x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 19%Z => let H := fresh "Ereg" in assert (H : x19 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 y x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 20%Z => let H := fresh "Ereg" in assert (H : x20 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 y x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 21%Z => let H := fresh "Ereg" in assert (H : x21 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 y x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 22%Z => let H := fresh "Ereg" in assert (H : x22 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 y x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 23%Z => let H := fresh "Ereg" in assert (H : x23 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 y x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 24%Z => let H := fresh "Ereg" in assert (H : x24 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 y x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 25%Z => let H := fresh "Ereg" in assert (H : x25 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 y x26 x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 26%Z => let H := fresh "Ereg" in assert (H : x26 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 y x27 x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 27%Z => let H := fresh "Ereg" in assert (H : x27 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 y x28 x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 28%Z => let H := fresh "Ereg" in assert (H : x28 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y x29 x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 29%Z => let H := fresh "Ereg" in assert (H : x29 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 y x30 x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 30%Z => let H := fresh "Ereg" in assert (H : x30 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 y x31) F pc fc rv m rom)) _ H); clear H; cbv beta
      | 31%Z => let H := fresh "Ereg" in assert (H : x31 = v') by tac;
                refine (eq_ind_r (fun y : word => evt segs POST (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 y) F pc fc rv m rom)) _ H); clear H; cbv beta
      end
    end).
