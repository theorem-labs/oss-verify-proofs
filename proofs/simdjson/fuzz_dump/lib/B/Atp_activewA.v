(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Atp_fzwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_getact : Z := 0xb307c.
Definition SJ_ACTIVE : Z := 0x6a9840.
Definition SJ_SINGLETON : Z := 0x6a98e0.

Definition one8 : byte := Z_to_bv 8 1.

Definition lib0 (m : mem) : Prop :=
  rw_cells bsegs m 0x6a9840 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x6a9860 [C1 z8; C1 z8]
  /\ rw_cells bsegs m 0x6a98e0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x6a9940 [C1 z8; C1 z8].

Definition lib1 (m : mem) : Prop :=
  rw_cells bsegs m 0x6a9840 [C8 (Z_to_bv 64 0x6a98e0)] /\ rw_cells bsegs m 0x6a9860 [C1 one8; C1 one8]
  /\ rw_cells bsegs m 0x6a98e0 [C8 (Z_to_bv 64 0x1689b0); C8 (Z_to_bv 64 0x28240); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x28440); C8 (Z_to_bv 64 31); C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x6a9940 [C1 one8; C1 one8].
Definition sj_lib (m : mem) : Prop := lib0 m \/ lib1 m.

Definition ga_W (usp : Z) : list ivl := [(usp - 32, usp); (0x6a9840, 0x6a9848); (0x6a9860, 0x6a9862); (0x6a98e0, 0x6a990c); (0x6a9940, 0x6a9942)].

Definition ga_post (ra : word) (usp : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m', ret_st ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x6a9840) m' ms /\ ms_fcsr ms = fc
    /\ munch (ga_W usp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ lib1 m'.

Lemma ga_walk_init : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> lib1 m -> mem_inv bsegs m ->
  evt bsegs (ga_post ra usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_getact m).
Proof.
  intros until m. intros ST LO GLO SPH (L1 & L2 & L3 & L4) MI.
  unfold entry_st, e_getact, ga_post, ga_W, one8 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (0x6a9840, 0x6a9848); (0x6a9860, 0x6a9862); (0x6a98e0, 0x6a990c); (0x6a9940, 0x6a9942)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_false.
  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep. zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. exact (conj L1 (conj L2 (conj L3 L4))).
Qed.

Lemma ga_walk_fresh : forall (usp lo : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6cd000 <= lo -> usp < 2^63 -> lib0 m -> mem_inv bsegs m ->
  evt bsegs (ga_post ra usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_getact m).
Proof.
  intros until m. intros ST LO GLO SPH (L1 & L2 & L3 & L4) MI.
  unfold entry_st, e_getact, ga_post, ga_W, one8 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp); (0x6a9840, 0x6a9848); (0x6a9860, 0x6a9862); (0x6a98e0, 0x6a990c); (0x6a9940, 0x6a9942)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.

  zstep. zstep. zstep. zstep. zstep. zstep. if_true.

  zstep. zstep. zstep.
  zstep. zstep. zstep. if_true. zstep. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.

  zstep. zstep. if_false.
  zstep. zstep. zstep.
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR0; [| reflexivity].
  cbn [mk_CB_cells app] in FR0.
  lstep. zstep. zstep. zstep. zstep. if_true.
  zstep. zstep. zstep.
  zstep. zstep. zstep. if_true. zstep. zstep. zstep. if_false. zstep. zstep. if_false. zstep. ls. zstep. zstep. zstep.
  zstep. zstep. if_false.

  do 10 zstep. lstep. lstep. lstep. lstep. zstep. zstep. lstep. ls.

  zstep. zstep.
  release_frame FR0 ST (usp + -16).
  zstep.
  zstep. zstep. ls. ls. zstep.

  zstep. zstep. lstep. zstep. zstep. zstep.
  zstep. zstep. ls. ls. zstep.
  zstep.
  zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep. zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. exact (conj L1 (conj L2 (conj L3 L4))).
Qed.
