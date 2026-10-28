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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma key_scale : forall k, 0 <= k < 128 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 k) ≪ 32)) ≫ 29) = Z_to_bv 64 (8 * k).
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (k * 2 ^ 32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  f_equal. change (2 ^ 32) with (2 ^ 29 * 8). rewrite Z.mul_assoc, (Z.mul_comm k), <- Z.mul_assoc, Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Definition getspecific_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (T k : Z) (v : word),
    a0 = Z_to_bv 64 k -> 0 <= k < 128 ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp ->
    ro_cells asegs m (T + 8 * k) [C8 v] -> 0 <= T ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists a1' : word,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x529438) fc None m (seg_rom asegs)).

Theorem getspecific_proof : getspecific_stmt.
Proof.
  unfold getspecific_stmt. intros until v. intros -> HK TS TP VC T0 MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  do 4 step. rewrite (key_scale k HK).
  step. set (Pk := T + 8 * k) in *. clearbody Pk.
  do 2 step.
  apply evt_done. eexists. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition setspecific_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (T k : Z) (old : word) (u : byte),
    a0 = Z_to_bv 64 k -> 0 <= k < 128 ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 150 <= bv_unsigned tp ->
    rw_cells asegs m (T + 8 * k) [C8 old] -> 0 <= T ->
    rw_cells asegs m (bv_unsigned tp + -150) [C1 u] ->
    (T + 8 * k + 8 <= bv_unsigned tp + -150 \/ bv_unsigned tp + -149 <= T + 8 * k) ->
    (T + 8 * k + 8 <= bv_unsigned tp + -88 \/ bv_unsigned tp + -80 <= T + 8 * k) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a2' a3' : word) (u' : byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ ro_cells asegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)]
                 /\ rw_cells asegs m' (T + 8 * k) [C8 a1]
                 /\ rw_cells asegs m' (bv_unsigned tp + -150) [C1 u'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x52a584) fc None m (seg_rom asegs)).

Theorem setspecific_proof : setspecific_stmt.
Proof.
  unfold setspecific_stmt. intros until u. intros -> HK TS TP VC T0 UC S1 S2 MI.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 4 step. rewrite (key_scale k HK).
  step. set (Pk := T + 8 * k) in *. clearbody Pk.
  do 2 step.
  destruct (bv_eqb old a1) eqn:EQ; cbv iota.
  - (* [comment removed for export] *) apply Fs.bv_eqb_eq in EQ. subst a1.
    do 2 step. apply evt_done. do 2 eexists. exists u, m.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact TS|]. split; [exact VC | exact UC].
  - do 4 ths. th_sb. do 2 ths.
    apply evt_done. do 2 eexists.
    lazymatch goal with UC' : rw_cells asegs ?mm (bv_unsigned tp + -150) [C1 ?uu] |- _ => exists uu, mm end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact TS|]. split; [exact VC | exact UC].
Qed.
