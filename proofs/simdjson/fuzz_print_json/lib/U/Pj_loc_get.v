(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_steps Pj_loc_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_loc_defs.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition locale_dtor_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs).

Lemma locale_dtor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (P : Z),
  rw_cells usegs m P [C8 (Z_to_bv 64 0xed828)] -> (0 <= P < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (locale_dtor_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6618) fc None m (seg_rom usegs)).
Proof.
  intros until P. intros LOC RP MI.
  do 4 lstep.
  if_true.
  lstep.
  apply evt_done. unfold locale_dtor_post. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Definition locale_copy_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (D : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 0xed828)].

Lemma locale_copy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S : Z) (j : list byte),
  rw_cells usegs m S [C8 (Z_to_bv 64 0xed828)] -> rw_cells usegs m D [CB 8 j] ->
  (0 <= S < 2^63)%Z -> (0 <= D < 2^63)%Z -> (S + 8 <= D \/ D + 8 <= S)%Z -> mem_inv usegs m ->
  evt usegs (locale_copy_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc D m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa65f4) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros SRC DST RS RD SEP MI.
  pose proof (munch_refl [(D, D + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 5 lstep.
  if_true.
  lstep.
  unfold locale_copy_post. sys_finish.
Qed.

Lemma LOCB_transport : forall W m m', LOCB m -> munch W m m' -> wmono usegs m m' -> disjoint_from W 0xed228 3760 -> LOCB m'.
Proof.
  intros W m m' (j1 & j2 & j3 & j4 & j5 & j6 & H) MU WM D. exists j1, j2, j3, j4, j5, j6.
  apply (rw_cells_transport usegs W m m' _ _ H MU WM). rewrite locb_cells_size. exact D.
Qed.

Definition use_facet_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xed748) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ LOCB m'.

Lemma use_facet_ctype_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo P : Z),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 48)%Z -> (0x110000 <= lo)%Z ->
  LOCB m -> rw_cells usegs m P [C8 (Z_to_bv 64 0xed828)] -> (bv_unsigned sp <= P < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (use_facet_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 0xed4e0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6e80) fc None m (seg_rom usegs)).
Proof.
  intros until P. intros ST LO LOLO LB LOC RP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct LB as (j1 & j2 & j3 & j4 & j5 & j6 & LB). unfold locb_cells in LB.
  carve_frame 48%nat ST.
  do 11 lstep.
  if_true.
  lstep.
  replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3) by (vm_compute; reflexivity).
  do 6 lstep.
  if_false.
  do 4 lstep.
  if_false.
  do 5 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold use_facet_post. sys_finish.
  exists j1, j2, j3, j4, j5, j6. assumption.
Qed.

Definition locale_ctor_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo D K : Z) (W : list (Z * Z)) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch ((bv_unsigned sp - K, bv_unsigned sp) :: (D, D + 8) :: W)%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' D [C8 (Z_to_bv 64 0xed828)]
    /\ LOCB m'.

Lemma locale_ctor_specB : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32)%Z -> (0x110000 <= lo)%Z ->
  LOCB m -> rw_cells usegs m D [CB 8 j] -> (bv_unsigned sp <= D < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (locale_ctor_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D 32 [] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6540) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros ST LO LOLO LB DST RD MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (D, D + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct LB as (j1 & j2 & j3 & j4 & j5 & j6 & LB). unfold locb_cells in LB.
  carve_frame 32%nat ST.
  do 11 lstep.
  if_false.
  do 4 lstep.
  if_true.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold locale_ctor_post. sys_finish.
  exists j1, j2, j3, j4, j5, j6. assumption.
Qed.
