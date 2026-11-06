(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac SysStep. 
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.
Ltac xstep := lstep; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) (f1 : word) : list cell :=
  [C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0); C8 f1].

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (f1 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctbsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xbfc280, 0xbfc298)] m m' /\ wmono ctbsegs m m' /\ mem_inv ctbsegs m'
    /\ stk ctbsegs m' lo (bv_unsigned sp)
    /\ rw_cells ctbsegs m' 0xbfc280 (atexit_cells (Z_to_bv 8 1) p1 p2 32 0 0 0x55895c f1).

(* [comment removed for export] *)
Lemma funcs_on_exit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 f1 a1v : word),
  stk ctbsegs m lo (bv_unsigned sp) ->
  rw_cells ctbsegs m 0xbfc280 (atexit_cells fin p1 p2 1 0xbfc298 0 0x55895c f1) ->
  rw_cells ctbsegs m 0xbfc3a0 [C8 (Z_to_bv 64 0x1de5cc); C8 a1v] ->
  rw_cells ctbsegs m 0xbfc4c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells ctbsegs m 0x736d20 [C1 (Z_to_bv 8 0)] ->
  mem_inv ctbsegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbfe000 <= lo ->
  evt ctbsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 f1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5587cc) fc None m (seg_rom ctbsegs)).
Proof.
  intros until a1v. intros ST ATX ATA LIBC COV MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xbfc280, 0xbfc298)] m) as MU.
  pose proof (wmono_refl ctbsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x558848%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0x558890%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0x564e88%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

(* [comment removed for export] *)
Lemma funcs_on_exit_spec2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk ctbsegs m lo (bv_unsigned sp) ->
  rw_cells ctbsegs m 0xbfc280 (atexit_cells fin p1 p2 2 0xbfc298 0 0x55895c (Z_to_bv 64 0x55895c)) ->
  rw_cells ctbsegs m 0xbfc3a0 [C8 (Z_to_bv 64 0x1de5cc); C8 (Z_to_bv 64 0x1ef004)] ->
  rw_cells ctbsegs m 0xbfc4c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells ctbsegs m 0x736d20 [C1 (Z_to_bv 8 0)] ->
  rw_cells ctbsegs m 0xbd74d4 [C1 (Z_to_bv 8 0)] ->
  mem_inv ctbsegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbfe000 <= lo ->
  evt ctbsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 (Z_to_bv 64 0x55895c) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5587cc) fc None m (seg_rom ctbsegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV ICB MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xbfc280, 0xbfc298)] m) as MU.
  pose proof (wmono_refl ctbsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x558848%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0x558848%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0x558890%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0x564e88%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

(* [comment removed for export] *)
Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (fin : byte) (p1 p2 : list byte) (func : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctbsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0xbfc288, 0xbfc28c); (0xbfc2a8, 0xbfc2b0); (0xbfc3a8, 0xbfc3b0)] m m'
    /\ wmono ctbsegs m m' /\ mem_inv ctbsegs m'
    /\ stk ctbsegs m' lo (bv_unsigned sp)
    /\ rw_cells ctbsegs m' 0xbfc280 (atexit_cells fin p1 p2 2 0xbfc298 0 0x55895c (Z_to_bv 64 0x55895c))
    /\ rw_cells ctbsegs m' 0xbfc3a0 [C8 (Z_to_bv 64 0x1de5cc); C8 func].

Lemma atexit_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 f1 a1v : word),
  stk ctbsegs m lo (bv_unsigned sp) ->
  rw_cells ctbsegs m 0xbfc280 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0xbfc298 0 0x55895c f1) ->
  rw_cells ctbsegs m 0xbfc3a0 [C8 (Z_to_bv 64 0x1de5cc); C8 a1v] ->
  rw_cells ctbsegs m 0xbfc4c0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv ctbsegs m ->
  lo <= bv_unsigned sp - 48 -> 0xbfe000 <= lo ->
  evt ctbsegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (Z_to_bv 8 0) p1 p2 a0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x558898) fc None m (seg_rom ctbsegs)).
Proof.
  intros until a1v. intros ST ATX ATA LIBC MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0xbfc288, 0xbfc28c); (0xbfc2a8, 0xbfc2b0); (0xbfc3a8, 0xbfc3b0)] m) as MU.
  pose proof (wmono_refl ctbsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0x558958%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep.
  unfold atexit_post, atexit_cells. sys_finish.
Qed.
