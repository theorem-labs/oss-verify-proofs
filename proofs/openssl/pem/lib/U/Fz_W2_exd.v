(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_key Th_mutex Th_once. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_local Fz_T_once Fz_T_lock Fz_iface Fz_M_free Fz_I3_base Fz_I3_fxi.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition DC_IP12 : Z := 0x32df38.
Definition NEWEX_STACK : Z := 304.
Definition FREEEX_STACK : Z := 384.

(* [comment removed for export] *)
Definition hboxed (P : Prop) : Prop := P.
Ltac hbox H := lazymatch type of H with ?P => change P with (hboxed P) in H end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma munch_restore : forall A n W (m m' : mem) bs,
  munch ((A, A + n) :: W) m m' -> bytes_at usegs m A bs -> bytes_at usegs m' A bs -> Z.of_nat (length bs) = n ->
  (A + n <= 0x10000 \/ 0x353000 <= A) -> munch W m m'.
Proof.
  intros A n W m m' bs MU B1 B2 LEN RNG x OUT.
  pose proof (bv_unsigned_in_range 64 x) as RX. unfold bv_modulus in RX. cbn in RX.
  destruct (Z_lt_dec (bv_unsigned x) A) as [L|GE]; [apply MU; cbn [outside]; split; [lia| exact OUT]|].
  destruct (Z_lt_dec (bv_unsigned x) (A + n)) as [L2|GE2]; [| apply MU; cbn [outside]; split; [lia| exact OUT]].
  destruct B1 as (A0 & AN & H1). destruct B2 as (_ & _ & H2).
  set (i := Z.to_nat (bv_unsigned x - A)).
  assert (Hi : (i < length bs)%nat) by lia.
  specialize (H1 i Hi). specialize (H2 i Hi).
  assert (EX : wa (A + Z.of_nat i) = x) by (unfold wa; replace (A + Z.of_nat i) with (bv_unsigned x) by lia; apply Z_to_bv_bv_unsigned).
  rewrite EX in H1, H2. rewrite (ref_mrd_overlay m x) in H1 by lia. rewrite (ref_mrd_overlay m' x) in H2 by lia.
  destruct (nth_error bs i) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; lia]. congruence.
Qed.

(* [comment removed for export] *)
Definition T_defctx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd : Z),
    ro_cells usegs m DC_S [C1 (Z_to_bv 8 1)] ->
    ro_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * kd) [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * kd + 8 <= lo \/ bv_unsigned sp <= T + 8 * kd) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 DC_CTX) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe485c) fc None m (seg_rom usegs)).

Theorem T_defctx_proof : T_defctx_stmt.
Proof.
  unfold T_defctx_stmt. intros until kd.
  intros INI KC HK O1 R1 O2 R2 TS TP T0 SLOTC ST GLO LO S1 S2 MI.
  unfold DC_S, DC_CTX, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * kd) in *.
  change (3333808 + 4) with 3333812 in *. change (3333808 + 8) with 3333816 in *. change (3333808 + 12) with 3333820 in *.
  change (3333808 + 16) with 3333824 in *. change (3333808 + 20) with 3333828 in *.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 10 ths. ths.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. ths. th_if_lit.
  ths. ths. th_if_lit.
  ths. ths. ths. ths.
  tcall (T_run_once_done_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  ths. ths. ths. th_if_lit.
  ths. ths. th_if_lit.
  ths. ths.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd (Z_to_bv 64 0)).
  all: try first [eassumption | lia].
  cbv beta delta [mkR].
  (* [comment removed for export] *)
  ths. ths. ths. ths. th_if_lit.
  ths.
  do 4 ths.
  th_release FR (bv_unsigned sp).
  ths.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_exg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd : Z),
    ro_cells usegs m DC_S [C1 (Z_to_bv 8 1)] ->
    ro_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * kd) [C8 z64] ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 64 ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * kd + 8 <= lo \/ bv_unsigned sp <= T + 8 * kd) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t1' a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 DC_GLOBAL_LOCK) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe4b1c) fc None m (seg_rom usegs)).

Theorem T_exg_proof : T_exg_stmt.
Proof.
  unfold T_exg_stmt. intros until kd.
  intros INI KC HK O1 R1 O2 R2 TS TP T0 SLOTC ST GLO LO S1 S2 MI.
  unfold DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * kd) in *.
  ths. th_if_lit.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths. ths.
  pose proof T_defctx_proof as X. unfold T_defctx_stmt, DC_S, DC_CTX, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  do 2 ths. th_release FR (bv_unsigned sp). ths.
  ths. th_if_lit. ths. ths. th_if_lit. ths. ths.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_gal_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo LK : Z),
    ro_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> 0 < LK -> LK mod 4 = 0 ->
    rw_cells usegs m LK (mutex_cells z64 z64) ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 ->
    LK + 40 <= lo ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DC_IP12) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' LK (mutex_cells z64 (Z_to_bv 64 16)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DC_GLOBAL_LOCK) (Z_to_bv 64 12) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe5000) fc None m (seg_rom usegs)).

Theorem T_gal_proof : T_gal_stmt.
Proof.
  unfold T_gal_stmt. intros until LK.
  intros GL LK0 LKAL MC ST GLO LO SEP MI.
  unfold DC_IP12, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ MC) as LKB. cbn [cells_size mutex_cells csize Nat.add] in LKB.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold mutex_cells in MC.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 9 ths. th_if_lit.
  ths. ths. ths. th_if_lit.
  ths. ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. th_if_lit.
  ths.
  pose proof T_read_lock_proof as X. unfold T_lock_stmt, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit.
  ths. ths. ths. ths. th_if_lit.
  ths. ths.
  do 5 ths. th_release FR (bv_unsigned sp). ths.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_sknum_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe6e50) fc None m (seg_rom usegs)).
Theorem T_sknum_null_proof : T_sknum_null_stmt.
Proof.
  unfold T_sknum_null_stmt. intros until lo. intros ST GLO LO MI. unfold GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths. ths. th_if_lit. ths.
  do 2 ths. th_release FR (bv_unsigned sp). ths. ths.
  finish.
Qed.

Definition T_skfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe637c) fc None m (seg_rom usegs)).
Theorem T_skfree_null_proof : T_skfree_null_stmt.
Proof.
  unfold T_skfree_null_stmt. intros until lo. intros ST GLO LO MI. unfold GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 6 ths. ths. th_if_lit.
  do 4 ths. th_release FR (bv_unsigned sp). ths. ths.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_newex_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd LK AD : Z) (c0 c1 : word),
    a0 = Z_to_bv 64 12 -> a2 = Z_to_bv 64 AD ->
    ro_cells usegs m DC_S [C1 (Z_to_bv 8 1)] ->
    ro_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * kd) [C8 z64] ->
    ro_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> 0 < LK -> LK mod 4 = 0 -> (LK + 40 <= 0x10000 \/ 0x353000 <= LK) ->
    rw_cells usegs m LK (mutex_cells z64 z64) ->
    ro_cells usegs m DC_IP12 [C8 z64] ->
    rw_cells usegs m AD [C8 c0; C8 c1] -> 0 < AD ->
    AD mod 8 = 0 ->
    lx_statics m ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - NEWEX_STACK ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * kd + 8 <= lo \/ bv_unsigned sp <= T + 8 * kd) ->
    LK + 40 <= lo -> AD + 16 <= lo -> (AD + 16 <= LK \/ LK + 40 <= AD) -> (AD + 16 <= 0x10000 \/ 0x353000 <= AD) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - NEWEX_STACK, bv_unsigned sp); (AD, AD + 16)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' AD [C8 z64; C8 z64] /\ rw_cells usegs m' LK (mutex_cells z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe564c) fc None m (seg_rom usegs)).

Theorem T_newex_proof : T_newex_stmt.
Proof.
  unfold T_newex_stmt. intros until c1.
  intros -> -> INI KC HK O1 R1 O2 R2 TS TP T0 SLOTC GL LK0 LKAL LKIMG MC IP ADC AD0 ALAD LXS ST GLO LO S1 S2 SEPL SEPA SEPAL ADIMG MI.
  unfold NEWEX_STACK, DC_IP12, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (AD, AD + 16); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * kd) in *.
  change (3333808 + 4) with 3333812 in *. change (3333808 + 8) with 3333816 in *. change (3333808 + 12) with 3333820 in *.
  change (3333808 + 16) with 3333824 in *. change (3333808 + 20) with 3333828 in *.
  unfold mutex_cells in MC. pose proof (proj2 (proj1 MC)) as MCB0. cbn [cells_bytes cbytes app] in MCB0. hbox MCB0.
  (* [comment removed for export] *)
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths. do 4 ths. do 2 ths. th_release FR (bv_unsigned sp). ths. ths.
  (* [comment removed for export] *)
  th_frame 192%nat [88; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 ths.
  do 4 ths. ths.

  pose proof T_exg_proof as X. unfold T_exg_stmt, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  ths. ths. ths. ths.
  pose proof T_gal_proof as X. unfold T_gal_stmt, DC_IP12, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo LK).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit.
  ths. ubs_if. ths. ths. ths. ubs_if.
  ths. ths. ths. ths. th_if_lit.
  ths. ths.
  pose proof T_sknum_null_proof as X. unfold T_sknum_null_stmt, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. ths. th_if_lit.
  ths. ths. ths. th_if_lit. ths. ths.
  pose proof T_unlock_proof as X. unfold T_unlock_stmt, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit. ths. th_if_lit.
  ths. ths.
  ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  ths. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with MUh : munch _ m mc, WMh : wmono usegs m mc |- _ =>
      assert (LXSc : lx_statics mc)
        by (eapply Drv_kit.lx_statics_agree; [exact (Drv_kit.agree_on_of_munch _ _ _ MUh WMh)| | exact LXS];
            intros a Ha; cbv beta; cbn [outside]; unfold Drv_kit.lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; clear - Ha GLO LO RSP ADIMG LKIMG AD0 LK0; lia) end end.
  pose proof crypto_free_null as X. unfold GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [reflexivity | eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. ths.
  do 14 ths. th_release FR (bv_unsigned sp). ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    lazymatch goal with MUh : munch _ m mf, MCf : rw_cells usegs mf LK _ |- _ =>
      assert (MUr : munch [(LK, LK + 40); (bv_unsigned sp - 304, bv_unsigned sp); (AD, AD + 16)] m mf)
        by (eapply munch_weaken; [| exact MUh]; unfold sub_fp; cbn [outside]; clear; intros; lia);
      unfold hboxed in MCB0;
      pose proof (munch_restore LK 40 _ m mf _ MUr MCB0) as MUf;
      cbn [cells_bytes cbytes app] in MUf; specialize (MUf (proj2 (proj1 MCf)) eq_refl LKIMG);
      clear MUh MUr
    end end.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_freeex_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T kd LK AD : Z),
    a0 = Z_to_bv 64 12 -> a2 = Z_to_bv 64 AD ->
    ro_cells usegs m DC_S [C1 (Z_to_bv 8 1)] ->
    ro_cells usegs m (DC_S + 4) [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
    ro_cells usegs m (DC_S + 8) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 12) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (DC_S + 16) [C4 (Z_to_bv 64 2)] -> ro_cells usegs m (DC_S + 20) [C4 (Z_to_bv 64 1)] ->
    ro_cells usegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> 0 <= T ->
    ro_cells usegs m (T + 8 * kd) [C8 z64] ->
    ro_cells usegs m DC_GLOBAL_LOCK [C8 (Z_to_bv 64 LK)] -> 0 < LK -> LK mod 4 = 0 -> (LK + 40 <= 0x10000 \/ 0x353000 <= LK) ->
    rw_cells usegs m LK (mutex_cells z64 z64) ->
    ro_cells usegs m DC_IP12 [C8 z64] ->
    rw_cells usegs m AD [C8 z64; C8 z64] -> 0 < AD ->
    AD mod 8 = 0 ->
    lx_statics m ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - FREEEX_STACK ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (T + 8 * kd + 8 <= lo \/ bv_unsigned sp <= T + 8 * kd) ->
    LK + 40 <= lo -> AD + 16 <= lo -> (AD + 16 <= LK \/ LK + 40 <= AD) -> (AD + 16 <= 0x10000 \/ 0x353000 <= AD) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - FREEEX_STACK, bv_unsigned sp); (AD, AD + 16)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' AD [C8 z64; C8 z64] /\ rw_cells usegs m' LK (mutex_cells z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe5a38) fc None m (seg_rom usegs)).

Theorem T_freeex_proof : T_freeex_stmt.
Proof.
  unfold T_freeex_stmt. intros until AD.
  intros -> -> INI KC HK O1 R1 O2 R2 TS TP T0 SLOTC GL LK0 LKAL LKIMG MC IP ADC AD0 ALAD LXS ST GLO LO S1 S2 SEPL SEPA SEPAL ADIMG MI.
  unfold FREEEX_STACK, DC_IP12, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 384, bv_unsigned sp); (AD, AD + 16); (LK + 4, LK + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Pk := T + 8 * kd) in *.
  change (3333808 + 4) with 3333812 in *. change (3333808 + 8) with 3333816 in *. change (3333808 + 12) with 3333820 in *.
  change (3333808 + 16) with 3333824 in *. change (3333808 + 20) with 3333828 in *.
  unfold mutex_cells in MC. pose proof (proj2 (proj1 MC)) as MCB0. cbn [cells_bytes cbytes app] in MCB0. hbox MCB0.
  th_frame 272%nat [168; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 16 ths. ths. first [ubs_if | th_if_lit].
  ths. ths. ths. ths. ubs_if. ths. ths.
  pose proof T_exg_proof as X. unfold T_exg_stmt, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit.
  ths. ths. ths. ths.
  pose proof T_gal_proof as X. unfold T_gal_stmt, DC_IP12, DC_GLOBAL_LOCK, DC_S, DC_CTX, GLOBALS_TOP, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo LK).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit.
  ths. ths. ths. first [ubs_if | th_if_lit]. ths. ths.
  pose proof T_sknum_null_proof as X. unfold T_sknum_null_stmt, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. ths. th_if_lit. ths. ths. ths. th_if_lit. ths. ths.
  pose proof T_unlock_proof as X. unfold T_unlock_stmt, mutex_cells in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. th_if_lit. ths. ths. if_cases KS0; zify_cond KS0. { exfalso. rewrite ?unsigned_lit in KS0 by lia. lia. }
  ths. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with MUh : munch _ m mc, WMh : wmono usegs m mc |- _ =>
      assert (LXSc : lx_statics mc)
        by (eapply Drv_kit.lx_statics_agree; [exact (Drv_kit.agree_on_of_munch _ _ _ MUh WMh)| | exact LXS];
            intros a Ha; cbv beta; cbn [outside]; unfold Drv_kit.lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; clear - Ha GLO LO RSP ADIMG LKIMG AD0 LK0; lia) end end.
  pose proof crypto_free_null as X. unfold GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [reflexivity | eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. ths.
  pose proof T_skfree_null_proof as X. unfold T_skfree_null_stmt, GLOBALS_TOP in X.
  tcall (X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  all: try first [eassumption | lia].
  clear X. cbv beta delta [mkR].
  ths. ths.
  do 14 ths. th_release FR (bv_unsigned sp). ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    lazymatch goal with MUh : munch _ m mf, MCf : rw_cells usegs mf LK _ |- _ =>
      assert (MUr : munch [(LK, LK + 40); (bv_unsigned sp - 384, bv_unsigned sp); (AD, AD + 16)] m mf)
        by (eapply munch_weaken; [| exact MUh]; unfold sub_fp; cbn [outside]; clear; intros; lia);
      unfold hboxed in MCB0;
      pose proof (munch_restore LK 40 _ m mf _ MUr MCB0) as MUf;
      cbn [cells_bytes cbytes app] in MUf; specialize (MUf (proj2 (proj1 MCf)) eq_refl LKIMG);
      clear MUh MUr
    end end.
  finish.
Qed.
End WithCeiling0.
