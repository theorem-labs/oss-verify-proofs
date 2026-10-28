(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition cond_cells : list cell := [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition cond_init_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (junk : list byte) (canary : word),
    rw_cells usegs m (bv_unsigned a0) [CB 48 junk] -> a1 = Z_to_bv 64 0 ->
    ssp_cells m canary ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
    (bv_unsigned a0 + 48 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (got_ssp + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 48 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 48 <= ssp_guard) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 48)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
                 /\ rw_cells usegs m' (bv_unsigned a0) cond_cells)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2bc488) fc None m (seg_rom usegs)).

Theorem cond_init_null_proof : cond_init_null_stmt.
Proof.
  unfold cond_init_null_stmt. intros until canary. intros MC -> [GOT GU] ST LO S1 S4 S5 S6 S7 MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Ap := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  unfold got_ssp, ssp_guard in *.
  carve_frame 64%nat ST.
  do 6 step.
  apply (rw_cells_split_CB usegs _ _ [] 48 _ [C8 canary; C8 ra] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (rw_cells_split_CB usegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in MC; [| reflexivity]. cbn [mk_CB_cells app] in MC.
  do 6 ths.
  do 12 ths.
  ths. th_if_lit.
  do 3 ths. rewrite (proj2 (Fs.bv_eqb_eq canary canary) eq_refl). cbv beta iota delta [negb].
  do 4 ths.
  release_frame FR ST (bv_unsigned sp).
  lazymatch goal with MI' : mem_inv usegs ?mm |- _ => assert (SSP : ssp_cells mm canary) by (split; assumption) end.
  unfold cond_cells. finish.
Qed.
