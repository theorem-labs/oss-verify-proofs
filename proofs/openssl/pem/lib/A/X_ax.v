(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AX_LATCH : Z := 0xb9f190.   (* [comment removed for export] *)
Definition AX_INCB  : Z := 0xb9f194.   (* [comment removed for export] *)
Definition AX_CALL  : Z := 0x51b00c.   (* [comment removed for export] *)
Definition AX_GUARD : Z := 0x1f2fc4.   (* [comment removed for export] *)
Definition AX_COVD  : Z := 0x1e258c.   (* [comment removed for export] *)
Definition ax_slot (k : bool) : Z := if k then 2 else 1.

(* [comment removed for export] *)
Definition ax_cells (k : bool) (fin : byte) (p1 p2 : list byte) : list cell :=
  [C1 (if k then fin else Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (ax_slot k)); CB 4 p2;
   C8 (Z_to_bv 64 0xbc3f58); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 AX_CALL); C8 (Z_to_bv 64 (if k then AX_CALL else 0))].
(* [comment removed for export] *)
Definition ax_acells (k : bool) : list cell :=
  [C8 (Z_to_bv 64 AX_COVD); C8 (Z_to_bv 64 (if k then AX_GUARD else 0))].
(* [comment removed for export] *)
Definition AXA (k : bool) (fin : byte) (p1 p2 : list byte) (m : word -> option byte) : Prop :=
  rw_cells asegs m 0xbc3f40 (ax_cells k fin p1 p2) /\ rw_cells asegs m 0xbc4060 (ax_acells k).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xbc3f40, 0xbc3f70); (0xbc4060, 0xbc4070)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xbc3f40 (ax_cells true (Z_to_bv 8 0) p1 p2)
    /\ rw_cells asegs m' 0xbc4060 (ax_acells true).

Lemma atexit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0xbc3f40 (ax_cells false (Z_to_bv 8 0) p1 p2) ->
  rw_cells asegs m 0xbc4060 (ax_acells false) ->
  rw_cells asegs m 0xbc4180 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbc6000 <= lo ->
  evt asegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AX_GUARD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x51af48) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC MI LO LOLO.
  unfold ax_cells, ax_acells, ax_slot, AX_CALL, AX_GUARD, AX_COVD in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xbc3f40, 0xbc3f70); (0xbc4060, 0xbc4070)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  xsteps_to 0x51b004%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep. xstep.
  unfold atexit_post, ax_cells, ax_acells, ax_slot, AX_CALL, AX_GUARD, AX_COVD. sys_finish.
Qed.
