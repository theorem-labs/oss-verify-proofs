(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition FUEL : list nat := [1900; 1100; 100; 100; 49900; 62400; 175600; 300; 800; 600; 600; 4400; 2400; 1000; 700; 3100; 1400; 100; 200; 1500; 3300; 500; 800; 2600]%nat.
Definition ECALLS : list Z := [0xc5e74; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c38; 0x73c44; 0x73c38; 0xc766c; 0xc7690; 0xcad04; 0xcad04; 0x73c38; 0x73c38; 0x73c38; 0x8fabc].
Definition plan_k (k : nat) : plan :=
  let f := List.nth k FUEL 1000%nat in
  let e := List.nth k ECALLS 0 in
  match k with
  | 12%nat => PJoin f [] 0x63b48 (PJoin f [] e PFin []) []
  | 15%nat => PJoin 0 [] 0x73c38 PFin [(0x73c48, PRun 3100 [0xd49dc] [(0xd49dc, PLoopW 200 [0x6b910] [(0x6b910, PRun 3100 [] [])])])]
  | _ => PJoin f [] e PFin []
  end.
Definition LIM : Z := 549755813888.
Inductive cstep : Type := SSeg (p : plan) | SNode (nk : nodek) | SOp (op : templop).
Definition mk (l : list cstep) (k : chain) : chain :=
  fold_right (fun s acc => match s with SSeg p => CSeg 20 p acc | SNode n => CNode n acc | SOp o => COp o acc end) k l.
Definition STEPS1 : list cstep := [
  SSeg (PJoin 2000 [] 0xc5e74 PFin []); SNode NTid;
  SSeg (PJoin 1100 [] 0xc5f10 PFin []); SOp (TForget (lconst 0x639880));
  SSeg (PJoin 1100 [] 0x73c38 PFin []);
  SNode (NNorep 0x7fff7000 0x10000000 GL false [(5%nat, 0x5c00); (6%nat, 0xc00); (7%nat, 0x4a); (8%nat, 0x10d20); (9%nat, 0x600); (10%nat, 0x200); (11%nat, 0x80200); (12%nat, 0x280); (13%nat, 0x2002); (14%nat, 0x4666); (15%nat, 0x31); (16%nat, 0x4e4); (17%nat, 0x1); (18%nat, 0x98)] true 0x10000 0x63c000);
  SSeg (plan_k 2); SNode (NNorep 0x8fff7000 0x20000000000 GN true [] false 0x10007fff8000 0x10007fff8000);
  SSeg (plan_k 3); SNode (NNorepB 0x2008fff7000 0xdfff0001000 GL
       (laddc (ladd (lscale 4096 (lvar 1)) (lscale 512 (lvar 2))) (0x7fff8000 + 512 - 0x100000))
       (laddc (lsub (lscale 512 (lvar 14)) (ladd (lscale 4096 (lvar 1)) (lscale 512 (lvar 2)))) (0x100000 - 512)) 0x300000 true);
  SSeg (plan_k 4); SNode (NNull 0x10000 GE true true false);
  SSeg (plan_k 5); SNode (NNull 0x38e000 GE true true false);
  SSeg (plan_k 6); SNode (NNull 0x2000011000 GN false false true);
  SSeg (plan_k 7); SNode (NFixNew 0x1000 0);
  SSeg (plan_k 8); SNode (NNull 0x800000 GN false false true);
  SSeg (plan_k 9); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 10); SNode (NNull 0x10000 GE true true false);
  SSeg (plan_k 11); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 12); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 13); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 14); SOp TDropA0; SNode (NUnmap 0);
  SSeg (plan_k 15); SNode (NNull 0xb09000 GE true true false);
  SSeg (plan_k 16); SNode NBrkQ;
  SSeg (plan_k 17) ].
Definition STEPS_OK : list cstep := [
  SOp (TSepG 0 12);
  SSeg (plan_k 18); SNode (NFixKeep 0x1000 true 0 GE);
  SSeg (plan_k 19); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 20); SNode (NNull 0x100000 GE true true false);
  SSeg (plan_k 21); SNode (NNull 0x800000 GL true true false);
  SSeg (plan_k 22); SNode (NNull 0x1000 GE true true false);
  SSeg (plan_k 23) ].
Definition STEPS_FAIL : list cstep := [
  SSeg (PJoin 3000 [] 0xcad04 PFin []); SNode (NNull 0x2000 GN false false true);
  SSeg (PJoin 3000 [] 0xcad5c PFin []); SOp (TAllowA0 0x1000); SNode (NMprot 0x1000 0);
  SSeg (PJoin 3000 [] 0xcad04 PFin []); SNode (NNull 0x1000 GE true true false);
  SSeg (PJoin 3300 [] 0x73c38 PFin []); SNode (NNull 0x100000 GE true true false);
  SSeg (PJoin 1000 [] 0x73c38 PFin []); SNode (NNull 0x800000 GL true true false);
  SSeg (PJoin 1000 [] 0x73c38 PFin []); SNode (NNull 0x1000 GE true true false);
  SSeg (PJoin 2600 [] 0x8fabc PFin []) ].
Definition CH1 : chain := mk STEPS1 (CGrow 0x2000 0x1000 0x1000 (mk STEPS_OK CEnd) (mk STEPS_FAIL CEnd)).
(* [comment removed for export] *)
