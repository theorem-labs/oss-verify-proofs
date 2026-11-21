(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import StrFun STRW_tac Startup_kit Amo_tac DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PATEXIT : Z := 0x18f88.
Definition PFUNCS_ON_EXIT : Z := 0x18ebc.
Definition PATX_CALL : Z := 0x1904c.
Definition PAEF_GUARD : Z := 0x14cf4.
Definition PAEF_INCB : Z := 0x32e64.
Definition PATX : Z := 0x92fa0.
Definition PATX_N : Z := 544.
Definition PLOCK_FN : Z := 0x20774.
Definition PUNLOCK_FN : Z := 0x209fc.
Definition PLIBC : Z := 0x931e8.

Definition atx_cells0 (m : mem) : Prop :=
  rw_cells psegs m PATX [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells psegs m (PATX + 288) [C8 (Z_to_bv 64 0)].

Definition atx_cellsA (m : mem) : Prop :=
  rw_cells psegs m PATX [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 (PATX + 24)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 PATX_CALL)]
  /\ rw_cells psegs m (PATX + 288) [C8 (Z_to_bv 64 PAEF_GUARD)].

Definition atx_cellsR (m : mem) : Prop := atx_cellsA m /\ rw_cells psegs m PAEF_INCB [C1 (Z_to_bv 8 0)].

Definition atx_addr (a : Z) : Prop := (PATX <= a < PATX + PATX_N) \/ (PAEF_INCB <= a < PAEF_INCB + 1).

Definition atx_addrA (a : Z) : Prop := PATX <= a < PATX + PATX_N.
Lemma atx_cellsA_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, atx_addrA a -> P a) -> atx_cellsA m -> atx_cellsA m'.
Proof.
  intros P m m' AG HP H. unfold atx_cellsA, atx_addrA, PATX, PATX_N in *. destruct H as [A B]. split.
  - eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact B| intros a Ha; apply HP; cbn in Ha; lia].
Qed.
Lemma atx_cells0_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cells0 m -> atx_cells0 m'.
Proof.
  intros P m m' AG HP H. unfold atx_cells0, atx_addr, PATX, PATX_N, PAEF_INCB in *. destruct H as [A B]. split.
  - eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact B| intros a Ha; apply HP; cbn in Ha; lia].
Qed.
Lemma atx_cellsR_agree : forall (P : Z -> Prop) m m', magree psegs P m m' -> (forall a, atx_addr a -> P a) -> atx_cellsR m -> atx_cellsR m'.
Proof.
  intros P m m' AG HP H. unfold atx_cellsR, atx_cellsA, atx_addr, PATX, PATX_N, PAEF_INCB in *. destruct H as [[A B] C]. split; [split|].
  - eapply rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact B| intros a Ha; apply HP; cbn in Ha; lia].
  - eapply rw_cells_magree; [exact AG| exact C| intros a Ha; apply HP; cbn in Ha; lia].
Qed.
Lemma atx_cells0_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, atx_addr a -> outside W a) -> atx_cells0 m -> atx_cells0 m'.
Proof. intros W m m' MU WM HW. apply (atx_cells0_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma atx_cellsR_munch : forall W m m', munch W m m' -> wmono psegs m m' -> (forall a, atx_addr a -> outside W a) -> atx_cellsR m -> atx_cellsR m'.
Proof. intros W m m' MU WM HW. apply (atx_cellsR_agree _ _ _ (magree_of_munch _ _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Ltac atx_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells psegs m A cs);
  [ apply (InitMem.rw_cells_recast psegs m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 psegs m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; unfold atx_addr, PATX, PATX_N, PAEF_INCB; left; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
Lemma atx_cells0_init : forall m : mem, (forall a : word, atx_addr (bv_unsigned a) -> m a = None) -> atx_cells0 m.
Proof.
  intros m NONE. unfold atx_cells0, PATX.
  atx_chunk0 NONE m 0x92fa0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                            C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H1.
  atx_chunk0 NONE m (0x92fa0 + 288) [C8 (Z_to_bv 64 0)] H2.
  split; [exact H1| exact H2].
Qed.

Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PATX, PATX + PATX_N)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ atx_cellsA m'.

Lemma atexit_guard_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  atx_cells0 m ->
  rw_cells psegs m PLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv psegs m ->
  a0 = Z_to_bv 64 PAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x94000 <= lo)%Z ->
  evt psegs (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PATEXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST [AX AXA] LCH MI -> LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold PATX, PATX_N, PLIBC, PAEF_GUARD, PATEXIT in *. change (602016 + 288) with 602304 in AXA.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x92fa0, 0x92fa0 + 544)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  lstep. carve_frame 48%nat ST. do 5 lstep.
  do 6 lstep.
  astep. astep. astep. astep.
  astep. astep. astep.
  astep. astep. astep. astep.
  astep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.
  do 9 astep.
  astep. astep. astep. astep. astep.
  astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
  unfold atexit_post, atx_cellsA. sys_finish.
Qed.

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PATX, PATX + PATX_N)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp).

Lemma funcs_on_exit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) ->
  (atx_cells0 m \/ atx_cellsR m) ->
  rw_cells psegs m PLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv psegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x94000 <= lo)%Z ->
  evt psegs (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFUNCS_ON_EXIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST AX LCH MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold atx_cells0, atx_cellsR, atx_cellsA, PATX, PATX_N, PLIBC, PFUNCS_ON_EXIT, PAEF_INCB, PATX_CALL, PAEF_GUARD in *.
  change (602016 + 288) with 602304 in AX. change (602016 + 24) with 602040 in AX.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x92fa0, 0x92fa0 + 544)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  destruct AX as [[AX AXA]|[[AX AXA] CB0]].
  -
    lstep. carve_frame 48%nat ST. do 5 lstep.
    do 5 lstep. astep. astep. astep. astep.
    astep. astep.
    astep. astep. astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
    astep. astep. astep.
    unfold funcs_on_exit_post. sys_finish.
  -
    lstep. carve_frame 48%nat ST. do 5 lstep.
    do 5 lstep. astep. astep. astep. astep.
    astep. astep. astep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). astep.
    astep. astep. astep.
    astep. astep. astep. astep. astep.
    astep. astep. astep. astep. astep.
    astep. astep. astep. astep. astep. astep. astep.
    astep. astep. astep. astep. astep.
    astep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.
    astep. astep. astep.
    astep. astep. astep. astep. astep. astep.
    astep. astep. astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
    astep. astep. astep.
    unfold funcs_on_exit_post. sys_finish.
Qed.
End CANSEC1.
