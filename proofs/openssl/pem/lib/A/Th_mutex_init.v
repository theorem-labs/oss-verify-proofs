(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mutex_init_attr_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (junk : list byte) (canary : word),
    rw_cells asegs m (bv_unsigned a0) [CB 40 junk] ->
    rw_cells asegs m (bv_unsigned a1) [C4 (Z_to_bv 64 0)] -> bv_unsigned a1 <> 0 ->      (* [comment removed for export] *)
    ssp_cells m canary ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
    (bv_unsigned a0 + 40 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a1 + 4 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a1) ->
    (bv_unsigned a0 + 40 <= bv_unsigned a1 \/ bv_unsigned a1 + 4 <= bv_unsigned a0) ->
    (got_ssp + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 40 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 40 <= ssp_guard) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
                 /\ rw_cells asegs m' (bv_unsigned a1) [C4 (Z_to_bv 64 0)]
                 /\ rw_cells asegs m' (bv_unsigned a0) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x529888) fc None m (seg_rom asegs)).

Theorem mutex_init_attr_proof : mutex_init_attr_stmt.
Proof.
  unfold mutex_init_attr_stmt. intros until canary. intros MC AT NZ [GOT GU] ST LO S1 S2 S3 S4 S5 S6 S7 MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (rw_cells_bound _ _ _ _ AT) as AB. cbn [cells_size csize Nat.add] in AB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  set (Ap := bv_unsigned a0) in *. set (Bp := bv_unsigned a1) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a1 with (Z_to_bv 64 Bp) by (unfold Bp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  unfold got_ssp, ssp_guard in *.
  carve_frame 64%nat ST.
  do 6 step.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [C8 canary; C8 ra] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (rw_cells_split_CB asegs _ _ [] 40 _ [] [8; 8; 8; 8; 8]%nat) in MC; [| reflexivity]. cbn [mk_CB_cells app] in MC.
  do 5 ths.
  do 10 ths.
  assert (NZb : bv_eqb (Z_to_bv 64 Bp) (Z_to_bv 64 0) = false).
  { destruct (bv_eqb (Z_to_bv 64 Bp) (Z_to_bv 64 0)) eqn:Eb; [|reflexivity]. apply Fs.bv_eqb_eq in Eb.
    apply (f_equal bv_unsigned) in Eb. rewrite !unsigned_lit in Eb by lia. contradiction. }
  ths. rewrite NZb. cbv iota.
  apply (th_cells_congr asegs m1 Ap _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in MC;
    [| reflexivity | reflexivity | cbn; tauto].
  do 2 ths.
  do 3 ths. rewrite (proj2 (Fs.bv_eqb_eq canary canary) eq_refl). cbv beta iota delta [negb].
  do 4 ths.
  release_frame FR ST (bv_unsigned sp).
  apply (th_cells_congr asegs m0 Ap _ (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) in MC; [| reflexivity | reflexivity | cbn; tauto].
  assert (SSP : ssp_cells m0 canary) by (split; assumption).
  finish.
Qed.

(* [comment removed for export] *)
Definition mutex_init_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (junk : list byte) (canary : word),
    rw_cells asegs m (bv_unsigned a0) [CB 40 junk] -> a1 = Z_to_bv 64 0 ->
    ssp_cells m canary ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
    (bv_unsigned a0 + 40 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (got_ssp + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 40 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 40 <= ssp_guard) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
                 /\ rw_cells asegs m' (bv_unsigned a0) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x529888) fc None m (seg_rom asegs)).

Theorem mutex_init_null_proof : mutex_init_null_stmt.
Proof.
  unfold mutex_init_null_stmt. intros until canary. intros MC -> [GOT GU] ST LO S1 S4 S5 S6 S7 MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 40)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  set (Ap := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  unfold got_ssp, ssp_guard in *.
  carve_frame 64%nat ST.
  do 6 step.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [C8 canary; C8 ra] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  apply (rw_cells_split_CB asegs _ _ [] 40 _ [] [8; 8; 8; 8; 8]%nat) in MC; [| reflexivity]. cbn [mk_CB_cells app] in MC.
  do 5 ths.
  do 10 ths.
  ths. th_if_lit.
  do 3 ths. rewrite (proj2 (Fs.bv_eqb_eq canary canary) eq_refl). cbv beta iota delta [negb].
  do 4 ths.
  release_frame FR ST (bv_unsigned sp).
  lazymatch goal with MI' : mem_inv asegs ?mm |- _ =>
    assert (SSP : ssp_cells mm canary) by (split; assumption);
    apply (th_cells_congr asegs mm Ap _ (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) in MC; [| reflexivity | reflexivity | cbn; tauto] end.
  finish.
Qed.
