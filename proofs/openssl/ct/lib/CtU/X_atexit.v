(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image SysStep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ctusegs := ImageCt.ctusegs.

(* [comment removed for export] *)
Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

(* [comment removed for export] *)
Definition RATEXIT : Z := 0x353278.        (* [comment removed for export] *)
Definition RATEXIT_A0 : Z := 0x353398.     (* [comment removed for export] *)
Definition RATEXIT_BUILTIN : Z := 0x353290.
Definition R_ATEXIT : Z := 0x2b2e2c.       (* [comment removed for export] *)
Definition R_FUNCS_ON_EXIT : Z := 0x2b2d60.
Definition R_ATEXIT_CALL : Z := 0x2b2ef0.  (* [comment removed for export] *)
Definition R_AEF_GUARD : Z := 0xe2454.     (* [comment removed for export] *)
Definition RAEF_INCB : Z := 0x3306b4.      (* [comment removed for export] *)

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) : list cell :=
  [C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x353278, 0x353290)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma funcs_on_exit_R_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk ctusegs m lo (bv_unsigned sp) ->
  rw_cells ctusegs m 0x353278 (atexit_cells fin p1 p2 1 0x353290 0 0x2b2ef0) ->
  rw_cells ctusegs m 0x353398 [C8 (Z_to_bv 64 0xe2454)] ->
  rw_cells ctusegs m 0x3534b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells ctusegs m 0x3306b4 [C1 (Z_to_bv 8 0)] ->
  mem_inv ctusegs m ->
  lo <= bv_unsigned sp - 48 -> 0x355000 <= lo ->
  evt ctusegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b2d60) fc None m (seg_rom ctusegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC INCB MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x353278, 0x353290)] m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x2b2ddc%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0x2b2e24%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0x2be8ac%Z. xstep.
  unfold funcs_on_exit_post. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma funcs_on_exit_E_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (slot next f0 : Z) (cdt thr sec : byte) (tm1 : word),
  stk ctusegs m lo (bv_unsigned sp) ->
  rw_cells ctusegs m 0x353278 (atexit_cells fin p1 p2 slot 0 next f0) ->
  rw_cells ctusegs m 0x3534b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv ctusegs m ->
  lo <= bv_unsigned sp - 48 -> 0x355000 <= lo ->
  evt ctusegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b2d60) fc None m (seg_rom ctusegs)).
Proof.
  intros until tm1. intros ST ATX LIBC MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x353278, 0x353290)] m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x2b2e24%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0x2be8ac%Z. xstep.
  unfold funcs_on_exit_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (fin : byte) (p1 p2 : list byte) (next : Z) (func : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x353278, 0x3532a0); (0x353398, 0x3533a0)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' 0x353278 (atexit_cells fin p1 p2 1 0x353290 next 0x2b2ef0)
    /\ rw_cells ctusegs m' 0x353398 [C8 func].

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (next f0 : Z) (av : word) (cdt thr sec : byte) (tm1 : word),
  stk ctusegs m lo (bv_unsigned sp) ->
  rw_cells ctusegs m 0x353278 (atexit_cells (Z_to_bv 8 0) p1 p2 0 0 next f0) ->
  rw_cells ctusegs m 0x353398 [C8 av] ->
  rw_cells ctusegs m 0x3534b8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv ctusegs m ->
  lo <= bv_unsigned sp - 48 -> 0x355000 <= lo ->
  evt ctusegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (Z_to_bv 8 0) p1 p2 next a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b2e2c) fc None m (seg_rom ctusegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x353278, 0x3532a0); (0x353398, 0x3533a0)] m) as MU.
  pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x2b2ee8%Z.
  xstep.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold atexit_post, atexit_cells. sys_finish.
Qed.
