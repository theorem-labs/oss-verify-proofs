(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_setshadow R_prim_defs R_poison.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Definition PCP : mem -> Prop := ps_cells.

Lemma PCP_framed : PC_framed PCP.
Proof. unfold PC_framed, PCP. intros m m' W PS MU WM HD. exact (ps_cells_framed m m' W PS MU WM HD). Qed.

Lemma PCP_stmt : poison_stmt PCP.
Proof.
  unfold poison_stmt. intros until shj. intros Ha Hn Hn0 HH Hend SH PS ST HLOH HLO HSP MI.
  assert (HA : ps_args_ok a n) by (unfold ps_args_ok, kHighMemEnd; split; [split; [exact Ha| split; [exact Hn| exact Hn0]]| right; lia]).
  pose proof (ps_shad_range a n HA) as (SR1 & SR2 & SR3 & SR4).
  eapply evt_mono; [eapply (poison_small_spec ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6 F fc m a n 250 lo shj); try eassumption; lia |].
  intros ms' PO. unfold poison_small_post in PO. destruct_exs PO. destruct PO as (E & MU & WM & MI' & RW & ST').
  subst ms'. unfold poison_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact RW|]. split; [exact ST'|].
  apply (PCP_framed m _ _ PS MU WM). unfold kHighShadowEnd in *. destruct ST as [HL0 _].
  cbn [disjoint_from]. unfold img_hull_lo, img_hull_hi. lia.
Qed.
