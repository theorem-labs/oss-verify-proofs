(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Abbreviation in_foot_b b k w F0L :=
(existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L).
Abbreviation in_kn_b K kn0 := (existsb (APC.kentry_eqb K) kn0).
Abbreviation live_b spoff b k SPV := ((negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool).
Abbreviation cells_of_b sF spoff live in_foot in_kn0 :=
(List.filter (fun K => match K with
| KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
| KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
| KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
| KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
| KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
| _ => false end)%bool (s_know sF)).
Abbreviation spoff_of_b sF SPV := (match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end).
Abbreviation mkps_b st F0L cells_of spoff_of := (SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st))).
Abbreviation ps_b pc regs_out F0L cells := (SR.PS pc (map (fun i => (i, nth i regs_out (ELit 0))) (seq 1 31)) F0L cells).
Abbreviation v0_b k := (EAlu Instr.ALU_ADD (EVar 0) (ELit k)).
