(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RATEXIT : Z := 0x3509b8.       (* [comment removed for export] *)
Definition RATEXIT_A0 : Z := 0x350ad8.    (* [comment removed for export] *)
Definition RATEXIT_CALL : Z := 0x2b06a4.  (* [comment removed for export] *)
Definition RAEF_INCB : Z := 0x32ddf4.     (* [comment removed for export] *)
Definition RAEF_GUARD : Z := 0xe1a2c.     (* [comment removed for export] *)
Definition RATEXIT_FN : Z := 0x2b05e0.    (* [comment removed for export] *)
Definition RFUNCS_ON_EXIT : Z := 0x2b0514.
Definition RLIBC_HEAD : Z := 0x350bf8.    (* [comment removed for export] *)
Definition RCXA_FINALIZE : Z := 0x2b05dc. (* [comment removed for export] *)
Definition RDSO : Z := 0x31d4a8.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ax_cells (fin slot head next f0 : Z) : list cell :=
  [C1 (Z_to_bv 8 fin); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 (repeat (Z_to_bv 8 0) 4);
   C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

(* [comment removed for export] *)
Definition AXSTAT (k : bool) (m : word -> option byte) : Prop :=
  rw_cells usegs m RAEF_INCB [C1 (Z_to_bv 8 0)]
  /\ (if k then rw_cells usegs m RATEXIT (ax_cells 0 1 (RATEXIT + 24) 0 RATEXIT_CALL) /\ rw_cells usegs m RATEXIT_A0 [C8 (Z_to_bv 64 RAEF_GUARD)]
      else rw_cells usegs m RATEXIT (ax_cells 0 0 0 0 0) /\ rw_cells usegs m RATEXIT_A0 [C8 (Z_to_bv 64 0)]).

(* [comment removed for export] *)
Definition axstat_addr (a : Z) : Prop :=
  (RAEF_INCB <= a < RAEF_INCB + 1)%Z \/ (RATEXIT <= a < RATEXIT + 40)%Z \/ (RATEXIT_A0 <= a < RATEXIT_A0 + 8)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atexit_guard_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATEXIT, RATEXIT + 40); (RATEXIT_A0, RATEXIT_A0 + 8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ AXSTAT true m'.

Lemma atexit_guard_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
  AXSTAT false m ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 RAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x353000 <= lo)%Z ->
  evt usegs (atexit_guard_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATEXIT_FN) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH [INCB [AX AX0]] MI -> LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RLIBC_HEAD, RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RATEXIT_FN, ax_cells in *. cbn [Z.add] in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x3509b8, 0x3509b8 + 40); (0x350ad8, 0x350ad8 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x2b0630%Z.   (* [comment removed for export] *)
  replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  steps_to 0x2b06a0%Z.
  release_frame FR ST (bv_unsigned sp). astep.
  apply evt_done. unfold atexit_guard_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unfold AXSTAT, RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RATEXIT_CALL, ax_cells. cbn [Z.add].
  split; [hyp_by_addr|]. split; hyp_by_addr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (RATEXIT, RATEXIT + 40)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Lemma funcs_on_exit_spec : forall (k : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m RLIBC_HEAD [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
  AXSTAT k m ->
  mem_inv usegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x353000 <= lo)%Z ->
  evt usegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFUNCS_ON_EXIT) fc None m (seg_rom usegs)).
Proof.
  intros until tm1. intros ST LCH [INCB AX2] MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold RLIBC_HEAD, RATEXIT, RATEXIT_A0, RAEF_INCB, RAEF_GUARD, RFUNCS_ON_EXIT, RATEXIT_CALL, ax_cells in *. cbn [Z.add] in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x3509b8, 0x3509b8 + 40)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  destruct k; destruct AX2 as [AX AX0].
  - (* [comment removed for export] *)
    steps_to 0x2b054c%Z.   (* [comment removed for export] *)
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    steps_to 0x2b05a0%Z.   (* [comment removed for export] *)
    replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    steps_to 0x2b05d8%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep. astep. astep.
    apply evt_done. unfold funcs_on_exit_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  - (* [comment removed for export] *)
    steps_to 0x2b05d8%Z.
    release_frame FR ST (bv_unsigned sp). astep. astep. astep. astep.
    apply evt_done. unfold funcs_on_exit_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.
