(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit
  Sj_stage1_defs Sj_stage2_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_parse : Z := 0xe2cdc.

Lemma pa_walk1 : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 32 -> 0x6ca000 <= lo -> usp < 2^63 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j : list byte),
      ms = entry_st (Z_to_bv 64 0xe2cfc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 a3 a0 a0 a1 a2 (Z_to_bv 64 0) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A1_ENTRY m1
      /\ munch [(usp - 32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -32)
      /\ rw_cells asegs m1 (usp + -32) [CB 8 j; C8 s1; C8 s0; C8 ra])
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_parse m).
Proof.
  intros until m. intros ST LO GLO SPH MI.
  unfold entry_st, e_parse, A1_ENTRY in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma pa_walk2 : forall (usp lo : Z) (j : list byte) (gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c : word)
    F fc (m : mem),
  stk asegs m lo (usp + -32) -> lo <= usp - 32 -> 0x6ca000 <= lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -32) [CB 8 j; C8 s1c; C8 s0c; C8 rac] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c s1x s0x a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc S2A_ENTRY m1
      /\ munch [(usp - 32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
    (MS (mkR (Z_to_bv 64 0xe2cfc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe2cfc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH FR MI.
  unfold entry_st, S2A_ENTRY in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_true.
  zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Lemma pa_walk3 : forall (usp lo code : Z) (j : list byte) (gp tp t0 t1 t2 s0x s1x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c : word)
    F fc (m : mem),
  stk asegs m lo (usp + -32) -> lo <= usp - 32 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < code < 2^64 ->
  rw_cells asegs m (usp + -32) [CB 8 j; C8 s1c; C8 s0c; C8 rac] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 code) m1 ms /\ ms_fcsr ms = fc
      /\ munch [(usp - 32, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
    (MS (mkR (Z_to_bv 64 0xe2cfc) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 s0x s1x (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xe2cfc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH CD FR MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

