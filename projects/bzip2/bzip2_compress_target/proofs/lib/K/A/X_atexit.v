(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__.
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

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) : list cell :=
  [C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

Definition ph_slot (ph : bool) : Z := if ph then 2 else 1.

Definition atexit_ph1 (m : word -> option byte) : Prop :=
  rw_cells bsegs m 0x629550 [C8 (Z_to_bv 64 0xbc6d8)] /\ rw_cells bsegs m 0x629650 [C8 (Z_to_bv 64 0x8128c)]
  /\ rw_cells bsegs m 0x608b94 [C1 (Z_to_bv 8 0)].

Definition atexit_ph (ph : bool) (m : word -> option byte) : Prop := if ph then atexit_ph1 m else True.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x629528, 0x629540)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x629528 (atexit_cells (Z_to_bv 8 1) p1 p2 32 0 0 0xbc6d8).

Lemma funcs_on_exit_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x629528 (atexit_cells fin p1 p2 1 0x629540 0 0xbc6d8) ->
  rw_cells bsegs m 0x629648 [C8 (Z_to_bv 64 0x708c4)] ->
  rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x1683e0 [C1 (Z_to_bv 8 0)] ->
  mem_inv bsegs m ->
  lo <= bv_unsigned sp - 48 -> 0x62b000 <= lo ->
  evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbc548) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x629528, 0x629540)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xbc5c4%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0xbc60c%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0xc6cc4%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x629528 (atexit_cells fin p1 p2 2 0x629540 0 0xbc6d8) ->
  rw_cells bsegs m 0x629648 [C8 (Z_to_bv 64 0x708c4)] ->
  rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x1683e0 [C1 (Z_to_bv 8 0)] ->
  atexit_ph1 m ->
  mem_inv bsegs m ->
  lo <= bv_unsigned sp - 48 -> 0x62b000 <= lo ->
  evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbc548) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV (F1 & A1 & FLAG) MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x629528, 0x629540)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xbc5c4%Z.
  xstep. xsteps_to 0xbc5c4%Z.
  xstep. xsteps_to 0xbc60c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep. xsteps_to 0xc6cc4%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x629528 (atexit_cells fin p1 p2 (ph_slot ph) 0x629540 0 0xbc6d8) ->
  rw_cells bsegs m 0x629648 [C8 (Z_to_bv 64 0x708c4)] ->
  rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m 0x1683e0 [C1 (Z_to_bv 8 0)] ->
  atexit_ph ph m ->
  mem_inv bsegs m ->
  lo <= bv_unsigned sp - 48 -> 0x62b000 <= lo ->
  evt bsegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbc548) fc None m (seg_rom bsegs)).
Proof.
  intros [|]; cbn [ph_slot atexit_ph]; intros.
  - eapply funcs_on_exit_spec1; eassumption.
  - eapply funcs_on_exit_spec0; eassumption.
Qed.


Definition TR_LATCH : Z := 0x608b90.

Definition reg_pre (m : word -> option byte) : Prop :=
  exists (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
    rw_cells bsegs m 0x629528 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x629540 0 0xbc6d8)
    /\ rw_cells bsegs m 0x629550 [C8 j1] /\ rw_cells bsegs m 0x629650 [C8 j2]
    /\ rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 0)].

Definition reg_post (m : word -> option byte) : Prop :=
  exists (p1 p2 : list byte),
    rw_cells bsegs m 0x629528 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x629540 0 0xbc6d8)
    /\ rw_cells bsegs m 0x629550 [C8 (Z_to_bv 64 0xbc6d8)] /\ rw_cells bsegs m 0x629650 [C8 (Z_to_bv 64 0x8128c)]
    /\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 1)].

Definition REG_CELLS : list (Z * Z) := [(0x608b90, 0x608b91); (0x629528, 0x629540); (0x629550, 0x629558); (0x629650, 0x629658)].

Lemma in_REG_CELLS : forall x, in_ranges REG_CELLS x <->
  (0x608b90 <= x < 0x608b91 \/ 0x629528 <= x < 0x629540 \/ 0x629550 <= x < 0x629558 \/ 0x629650 <= x < 0x629658).
Proof.
  intros x. unfold REG_CELLS, in_ranges. split.
  - intros (lo & hi & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
  - intros [H|[H|[H|H]]]; [exists 0x608b90, 0x608b91| exists 0x629528, 0x629540| exists 0x629550, 0x629558| exists 0x629650, 0x629658];
      (split; [cbn; tauto| exact H]).
Qed.

Definition atexit_reg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo func : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x629528, 0x629540); (0x629550, 0x629558); (0x629650, 0x629658)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x629528 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x629540 0 0xbc6d8)
    /\ rw_cells bsegs m' 0x629550 [C8 (Z_to_bv 64 0xbc6d8)] /\ rw_cells bsegs m' 0x629650 [C8 (Z_to_bv 64 func)].

Lemma atexit_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
  a0 = Z_to_bv 64 func -> 0 <= func < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x629528 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x629540 0 0xbc6d8) ->
  rw_cells bsegs m 0x629550 [C8 j1] -> rw_cells bsegs m 0x629650 [C8 j2] ->
  rw_cells bsegs m 0x629768 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv bsegs m ->
  lo <= bv_unsigned sp - 48 -> 0x62b000 <= lo ->
  evt bsegs (atexit_reg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbc614) fc None m (seg_rom bsegs)).
Proof.
  intros until j2. intros -> HF ST ATX F1 A1 LIBC MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x629528, 0x629540); (0x629550, 0x629558); (0x629650, 0x629658)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xbc6bc%Z.
  xstep. xstep. xstep. xstep. xstep.
  release_frame FR ST (bv_unsigned sp).
  xstep. xstep.
  unfold atexit_reg_post, atexit_cells. sys_finish.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface.
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

Definition atexit_cells (fin : byte) (p1 p2 : list byte) (slot head next f0 : Z) : list cell :=
  [C1 fin; CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 next); C8 (Z_to_bv 64 f0)].

Definition ph_slot (ph : bool) : Z := if ph then 2 else 1.

Definition atexit_ph1 (m : word -> option byte) : Prop :=
  rw_cells asegs m 0x61c150 [C8 (Z_to_bv 64 0xaf2f8)] /\ rw_cells asegs m 0x61c250 [C8 (Z_to_bv 64 0x81840)]
  /\ rw_cells asegs m 0x5fb794 [C1 (Z_to_bv 8 0)].

Definition atexit_ph (ph : bool) (m : word -> option byte) : Prop := if ph then atexit_ph1 m else True.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x61c128, 0x61c140)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x61c128 (atexit_cells (Z_to_bv 8 1) p1 p2 32 0 0 0xaf2f8).

Lemma funcs_on_exit_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x61c128 (atexit_cells fin p1 p2 1 0x61c140 0 0xaf2f8) ->
  rw_cells asegs m 0x61c248 [C8 (Z_to_bv 64 0x70e78)] ->
  rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x15afe0 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x61e000 <= lo ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf168) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x61c128, 0x61c140)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xaf1e4%Z.
  (* [comment removed for export] *)
  xstep. xsteps_to 0xaf22c%Z.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  xstep. xsteps_to 0xb98e4%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x61c128 (atexit_cells fin p1 p2 2 0x61c140 0 0xaf2f8) ->
  rw_cells asegs m 0x61c248 [C8 (Z_to_bv 64 0x70e78)] ->
  rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x15afe0 [C1 (Z_to_bv 8 0)] ->
  atexit_ph1 m ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x61e000 <= lo ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf168) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA LIBC COV (F1 & A1 & FLAG) MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x61c128, 0x61c140)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xaf1e4%Z.
  xstep. xsteps_to 0xaf1e4%Z.
  xstep. xsteps_to 0xaf22c%Z.
  release_frame FR ST (bv_unsigned sp).
  xstep. xsteps_to 0xb98e4%Z. xstep.
  unfold funcs_on_exit_post, atexit_cells. sys_finish.
Qed.

Lemma funcs_on_exit_spec : forall (ph : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (fin : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x61c128 (atexit_cells fin p1 p2 (ph_slot ph) 0x61c140 0 0xaf2f8) ->
  rw_cells asegs m 0x61c248 [C8 (Z_to_bv 64 0x70e78)] ->
  rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells asegs m 0x15afe0 [C1 (Z_to_bv 8 0)] ->
  atexit_ph ph m ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x61e000 <= lo ->
  evt asegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf168) fc None m (seg_rom asegs)).
Proof.
  intros [|]; cbn [ph_slot atexit_ph]; intros.
  - eapply funcs_on_exit_spec1; eassumption.
  - eapply funcs_on_exit_spec0; eassumption.
Qed.


Definition TR_LATCH : Z := 0x5fb790.

Definition reg_pre (m : word -> option byte) : Prop :=
  exists (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
    rw_cells asegs m 0x61c128 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x61c140 0 0xaf2f8)
    /\ rw_cells asegs m 0x61c150 [C8 j1] /\ rw_cells asegs m 0x61c250 [C8 j2]
    /\ rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 0)].

Definition reg_post (m : word -> option byte) : Prop :=
  exists (p1 p2 : list byte),
    rw_cells asegs m 0x61c128 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x61c140 0 0xaf2f8)
    /\ rw_cells asegs m 0x61c150 [C8 (Z_to_bv 64 0xaf2f8)] /\ rw_cells asegs m 0x61c250 [C8 (Z_to_bv 64 0x81840)]
    /\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 1)].

Definition REG_CELLS : list (Z * Z) := [(0x5fb790, 0x5fb791); (0x61c128, 0x61c140); (0x61c150, 0x61c158); (0x61c250, 0x61c258)].

Lemma in_REG_CELLS : forall x, in_ranges REG_CELLS x <->
  (0x5fb790 <= x < 0x5fb791 \/ 0x61c128 <= x < 0x61c140 \/ 0x61c150 <= x < 0x61c158 \/ 0x61c250 <= x < 0x61c258).
Proof.
  intros x. unfold REG_CELLS, in_ranges. split.
  - intros (lo & hi & Hin & Hx). cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
  - intros [H|[H|[H|H]]]; [exists 0x5fb790, 0x5fb791| exists 0x61c128, 0x61c140| exists 0x61c150, 0x61c158| exists 0x61c250, 0x61c258];
      (split; [cbn; tauto| exact H]).
Qed.

Definition atexit_reg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo func : Z) (p1 p2 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x61c128, 0x61c140); (0x61c150, 0x61c158); (0x61c250, 0x61c258)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x61c128 (atexit_cells (Z_to_bv 8 0) p1 p2 2 0x61c140 0 0xaf2f8)
    /\ rw_cells asegs m' 0x61c150 [C8 (Z_to_bv 64 0xaf2f8)] /\ rw_cells asegs m' 0x61c250 [C8 (Z_to_bv 64 func)].

Lemma atexit_reg_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo func : Z) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word),
  a0 = Z_to_bv 64 func -> 0 <= func < 2^64 ->
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x61c128 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x61c140 0 0xaf2f8) ->
  rw_cells asegs m 0x61c150 [C8 j1] -> rw_cells asegs m 0x61c250 [C8 j2] ->
  rw_cells asegs m 0x61c368 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv asegs m ->
  lo <= bv_unsigned sp - 48 -> 0x61e000 <= lo ->
  evt asegs (atexit_reg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo func p1 p2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xaf234) fc None m (seg_rom asegs)).
Proof.
  intros until j2. intros -> HF ST ATX F1 A1 LIBC MI LO LOLO.
  unfold atexit_cells in ATX.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x61c128, 0x61c140); (0x61c150, 0x61c158); (0x61c250, 0x61c258)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  xsteps_to 0xaf2dc%Z.
  xstep. xstep. xstep. xstep. xstep.
  release_frame FR ST (bv_unsigned sp).
  xstep. xstep.
  unfold atexit_reg_post, atexit_cells. sys_finish.
Qed.
