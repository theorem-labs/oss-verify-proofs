(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition atexit_cells (fin : byte) (p1 p2 p3 : byte) (slot : Z) (pad : word) (head : Z) : list cell :=
  [C1 fin; C1 p1; C1 p2; C1 p3; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); C4 pad;
   C8 (Z_to_bv 64 head); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x91cbc)].

Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 p3 : byte) (pad : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x600b60, 0x600b78)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x600b60 (atexit_cells (Z_to_bv 8 1) p1 p2 p3 32 pad 0).

Lemma funcs_on_exit_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (fin p1 p2 p3 : byte) (pad : word) (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop),
    (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x603000 <= lo -> lo <= bv_unsigned sp - 48 ->
    mem_inv asegs m ->
    rw_cells asegs m 0x600b60 (atexit_cells fin p1 p2 p3 1 pad 0x600b78) ->
    rw_cells asegs m 0x600c80 [C8 (Z_to_bv 64 0x71504)] ->                      (* [comment removed for export] *)
    rw_cells asegs m 0x13fa20 [C1 (Z_to_bv 8 0)] ->                             (* [comment removed for export] *)
    rw_cells asegs m 0x600da0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evtA asegs P (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo p1 p2 p3 pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x91b2c) fc None m (seg_rom asegs)).
Proof.
  intros until P; intros PSTK PIMG ST LOC LO MI ATX ARG COV LIBC RA.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x600b60, 0x600b78)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold atexit_cells in ATX.
  carve_frame 48%nat ST.
  do 6 stepA. stepA. zstepA. zstepA. zstepA.
  (* [comment removed for export] *)
  stepA. stepA. stepA. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). stepA. if_true. stepA.
  (* [comment removed for export] *)
  stepA. stepA. if_false. zstepA.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
  stepA. zstepA. change (bv_swrap 32 (1 + -1)) with 0. stepA. stepA. if_false.
  stepA. zstepA. zstepA. stepA. stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA. stepA. zstepA. stepA. if_false. stepA.
  (* [comment removed for export] *)
  zstepA. stepA. stepA. stepA. stepA. stepA. stepA. if_true. stepA.
  (* [comment removed for export] *)
  zstepA. stepA. stepA. stepA. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). stepA. if_true. stepA.
  (* [comment removed for export] *)
  zstepA. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
  zstepA. change (bv_swrap 32 (0 + -1)) with (-1). stepA. stepA. if_false.
  stepA. stepA. stepA. zstepA. stepA. stepA. stepA. if_true.
  (* [comment removed for export] *)
  zstepA. stepA. zstepA. do 5 stepA. stepA.
  release_frame FR ST (bv_unsigned sp).
  stepA. zstepA. stepA. if_false. stepA.
  lazymatch goal with H : rw_cells asegs _ 6294368 _ |- _ =>
    replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in H by (apply bv_eq; vm_compute; reflexivity);
    change (bv_swrap 32 (0 + -1)) with (-1) in H end.
  apply evtA_done. unfold funcs_on_exit_post, atexit_cells. do 16 eexists.
  split; [reflexivity|]. repeat (split; [assumption|]).
  lazymatch goal with H : rw_cells asegs _ 6294368 _ |- rw_cells _ _ _ ?cs => let ty := type of H in idtac ty; idtac cs; exact H end.
Qed.
End RC__1.
