(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsAtomics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition DEPOT_LOCK : Z := 0x1e1910.

Definition lock_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' P [C4 (wz (v + 2^31))] /\ a0 = wz v /\ stk asegs m' lo (bv_unsigned sp).

Theorem lock_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P v lo : Z),
  a0 = wz P -> P mod 4 = 0 -> 0 <= v < 2^31 -> 0 <= P -> P + 4 <= lo ->
  rw_cells asegs m P [C4 (wz v)] ->
  stk asegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
  mem_inv asegs m ->
  evt asegs (lock_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P v lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DEPOT_LOCK) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> AL VB P0 PLO C ST LO MI. unfold wz, DEPOT_LOCK.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  do 10 step.
  (* [comment removed for export] *)
  zstep. rewrite sx32_wz by lia.
  step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  astep. rewrite ?sx32_wz by lia.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso; lia. }
  (* [comment removed for export] *)
  astep.
  (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso; revert K3; rewrite ?unsigned_lit by lia; lia. }
  step. if_cases K4; zify_cond K4. 2:{ exfalso; lia. }
  do 5 step. release_frame FR ST (bv_unsigned sp). step. step.
  rewrite unsigned_lit in C by lia. apply lock_cell in C; [|lia].
  finish. all: try reflexivity.
Qed.
