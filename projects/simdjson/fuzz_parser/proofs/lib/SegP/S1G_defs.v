(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP Require Import S1P_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition gBUF : ST.gatom := ST.GA 1 [vBUF; vLEN].
Definition gTAB : ST.gatom := ST.GA 2 [vSP].
Definition gM (j d er : expr) : ST.gatom := ST.GA 3 [vA1; j; d; er].
Definition gS (i k d er : expr) : ST.gatom := ST.GA 4 [vA1; i; k; d; er].
Definition gPR (i k d er : expr) : ST.gatom := ST.GA 5 [vA1; i; k; d; er].
Definition gX (rc n : expr) : ST.gatom := ST.GA 6 [vA1; rc; n; vTHIS].

(* [comment removed for export] *)
Definition vI := V 32.
Definition kn_I : list kentry := [KWord (SA (add vA1 vD) 0) 4 vI].

Definition G0 : ST.tmpl := ST.TMG (ST.t_pc T0) (ST.t_regs T0) (ST.t_know T0) (ST.t_ns T0) (ST.t_meas T0) (ST.t_rank T0) [gBUF].
Definition GO : ST.tmpl := ST.TMG (ST.t_pc TO) (ST.t_regs TO) (ST.t_know TO) (ST.t_ns TO) (ST.t_meas TO) (ST.t_rank TO)
                             [gBUF; gTAB; gM vJ vD (V 23)].
Definition GW : ST.tmpl := ST.TMG (ST.t_pc TW) (ST.t_regs TW) (ST.t_know TW) (ST.t_ns TW) (ST.t_meas TW) (ST.t_rank TW)
                             [gBUF; gTAB; gM vJ vD (V 23)].
Definition GS_ : ST.tmpl := ST.TMG (ST.t_pc TS) (ST.t_regs TS) (kn_I ++ ST.t_know TS) 33%nat (ST.t_meas TS) (ST.t_rank TS)
                              [gBUF; gTAB; gS vI vJ vD (V 23)].
Definition GSI : ST.tmpl := ST.TMG (ST.t_pc TSI) (ST.t_regs TSI) (kn_I ++ ST.t_know TSI) 33%nat (ST.t_meas TSI) (ST.t_rank TSI)
                              [gBUF; gTAB; gS vI vJ vD (V 23)].
Definition GP_ : ST.tmpl := ST.TMG (ST.t_pc TP) (ST.t_regs TP) (kn_I ++ ST.t_know TP) 33%nat (ST.t_meas TP) (ST.t_rank TP)
                              [gBUF; gTAB; gPR vI vJ vD (V 23)].
(* [comment removed for export] *)
Definition GX_ : ST.tmpl := ST.TMG (ST.t_pc TX) (ST.t_regs TX) (KWord (SA vTHIS 8) 4 (V 36) :: ST.t_know TX) 37%nat (ST.t_meas TX) (ST.t_rank TX)
                              [gBUF; gX (V 21) (V 36)].

Definition S1G : SP.prog := SP.PG 21 [G0; GO; GW; GS_; GSI; GP_] [GX_] [(vSP, -416, ELit 416); (vTHIS, 8, ELit 4); (vTHIS, 24, ELit 4); (vTHIS, 72, ELit 16); (vA1, 0, idxlen)].
