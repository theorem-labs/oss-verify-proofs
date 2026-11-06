(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Stdio_iface.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb ?x ?x) then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv beta iota delta [negb]
  end.
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition F_STDIO_EXIT : Z := 0xbef64.
Definition RSTDIN_USED : Z := 0xd7988.
Definition RSTDOUT_USED : Z := 0xd7a78.
Definition RSTDERR_USED : Z := 0xd7898.
Definition ROFL_LOCK : Z := 0x10a560.
Definition RLIBC_HEAD : Z := 0x10a028.

Definition clean_file_cells (j0 : list byte) (rp : Z) (j1 : list byte) (wp : Z) (j2 : list byte) (j3 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 rp); C8 (Z_to_bv 64 rp); CB 16 j1; C8 (Z_to_bv 64 wp); CB 8 j2; C8 (Z_to_bv 64 wp); CB 76 j3; C4 (Z_to_bv 64 0xffffffff)].

Definition stdio_exit_idle_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp).

Lemma stdio_exit_idle_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo Sin Sout Serr : Z)
    (i0 i1 i2 i3 o0 o1 o2 o3 e0 e1 e2 e3 : list byte) (irp iwp orp owp erp ewp : Z) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 32) -> (GLOBALS_TOP <= lo) ->
  rw_cells psegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells psegs m ROFL_LOCK [C4 z64; C4 z64; C8 z64] ->
  rw_cells psegs m RSTDIN_USED [C8 (Z_to_bv 64 Sin)] -> rw_cells psegs m Sin (clean_file_cells i0 irp i1 iwp i2 i3) -> (0 < Sin) -> (Sin + 148 <= GLOBALS_TOP) ->
  rw_cells psegs m RSTDOUT_USED [C8 (Z_to_bv 64 Sout)] -> rw_cells psegs m Sout (clean_file_cells o0 orp o1 owp o2 o3) -> (0 < Sout) -> (Sout + 148 <= GLOBALS_TOP) ->
  rw_cells psegs m RSTDERR_USED [C8 (Z_to_bv 64 Serr)] -> rw_cells psegs m Serr (clean_file_cells e0 erp e1 ewp e2 e3) -> (0 < Serr) -> (Serr + 148 <= GLOBALS_TOP) ->
  (0 <= irp < 2^64) -> (0 <= iwp < 2^64) -> (0 <= orp < 2^64) -> (0 <= owp < 2^64) -> (0 <= erp < 2^64) -> (0 <= ewp < 2^64) ->
  mem_inv psegs m ->
  evt psegs (stdio_exit_idle_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_STDIO_EXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST LO GLO LIBC OFL SIU SIN Sin0 SinH SOU SOUT Sout0 SoutH SEU SERR Serr0 SerrH B1 B2 B3 B4 B5 B6 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_STDIO_EXIT, RSTDIN_USED, RSTDOUT_USED, RSTDERR_USED, ROFL_LOCK, RLIBC_HEAD, GLOBALS_TOP, clean_file_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  carve_frame 16%nat ST.
  do 3 lstep.
  lstep.
  carve_frame 16%nat ST.
  do 5 lstep.

  steps_to 0xcb220%Z. lstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). lstep. if_true. lstep.

  lstep. lstep. lstep. lstep.
  release_frame FR0 ST (bv_unsigned sp + -16).
  lstep.

  lstep. lstep. if_false.

  lstep. lstep. lstep. if_cases Hs; zify_cond Hs. 1:{ exfalso. clear - Hs Sin0 SinH. try rewrite unsigned_lit in Hs by lia. lia. }
  lstep. lstep. if_lit.
  lstep. lstep. lstep. if_refl.
  lstep. lstep. lstep. if_refl.

  lstep. lstep. lstep. if_cases Ho; zify_cond Ho. 1:{ exfalso. clear - Ho Sout0 SoutH. try rewrite unsigned_lit in Ho by lia. lia. }
  lstep. lstep. if_lit.
  lstep. lstep. lstep. if_refl.
  lstep. lstep. lstep. if_refl.

  lstep. lstep. lstep. if_cases He; zify_cond He. 1:{ exfalso. clear - He Serr0 SerrH. try rewrite unsigned_lit in He by lia. lia. }
  lstep. lstep. if_lit.
  lstep. lstep. lstep. if_refl.
  lstep. lstep. lstep. if_refl.

  lstep. lstep. lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  apply evt_done. unfold stdio_exit_idle_post. sys_finish.
Qed.
