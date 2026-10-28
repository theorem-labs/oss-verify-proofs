(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_once.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RUN_ONCE_RET : Z := 0x1f6120.

Definition T_run_once_done_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    ro_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 2)] ->
    stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ ro_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 2)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6108) fc None m (seg_rom asegs)).

Theorem T_run_once_done_proof : T_run_once_done_stmt.
Proof.
  unfold T_run_once_done_stmt. intros until lo. intros CC ST LO0 LO SEP MI.
  pose proof (ro_cells_bound _ _ _ _ CC) as CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  eapply evt_cut; [eapply once_done_proof; eassumption|].
  intros ms' (a2' & a3' & ->). cbv delta [mkR]. th_ret_lit.
  do 5 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_run_once_enter_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo INIT : Z) (oldcb canary : word),
    rw_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] -> bv_unsigned a0 mod 4 = 0 ->
    a1 = Z_to_bv 64 INIT -> 0 <= INIT < 2 ^ 64 -> INIT mod 2 = 0 ->
    ssp_cells m canary ->
    rw_cells asegs m (bv_unsigned tp + -96) [C8 oldcb] -> 96 <= bv_unsigned tp ->
    stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 128 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned tp + -88 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -96) ->
    (bv_unsigned a0 + 4 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= bv_unsigned a0) ->
    (got_ssp + 8 <= lo \/ bv_unsigned sp <= got_ssp) -> (ssp_guard + 8 <= lo \/ bv_unsigned sp <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= ssp_guard) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a0' a1' a2' a3' : word) (junk : list byte) (m' : mem),
                 ms' = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 a0 (Z_to_bv 64 INIT) a0' a1' a2' a3' a4 a5 a6 a7
                               (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc (Z_to_bv 64 INIT)) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp + -128) /\ ssp_cells m' canary
                 /\ rw_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 1)]
                 /\ rw_cells asegs m' (bv_unsigned tp + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -128))]
                 /\ rw_cells asegs m' (bv_unsigned sp + -128) (once_full_cells (bv_unsigned a0) oldcb canary s6 s5 s4 s3 s2 s1 sp)
                 /\ rw_cells asegs m' (bv_unsigned sp + -32) [Cells.CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
                 /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6108) fc None m (seg_rom asegs)).

Theorem T_run_once_enter_proof : T_run_once_enter_stmt.
Proof.
  unfold T_run_once_enter_stmt. intros until canary. intros CC AL EA1 HI HI2 [GOT GU] CB TP ST LO0 LO S1 S2 S3 S4 S5 S6 S7 S8 S9 MI.
  pose proof (rw_cells_bound _ _ _ _ CC) as CBD. cbn [cells_size csize Nat.add] in CBD.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold got_ssp, ssp_guard in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  pose proof once_enter_proof as OE. unfold once_enter_stmt in OE.
  specialize (OE (Z_to_bv 64 0x1f6120) (Z_to_bv 64 (bv_unsigned sp + -16))).
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in OE by lia.
  unfold ssp_cells, got_ssp, ssp_guard in OE.
  call (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo INIT oldcb canary).
  1-21: first [eassumption | reflexivity | lia | split; eassumption].
  clear OE.
  replace (bv_unsigned sp + -16 + -112) with (bv_unsigned sp + -128) in * by lia.
  replace (bv_unsigned sp + -16 + -16) with (bv_unsigned sp + -32) in * by lia.
  apply evt_done. exists x, x0, x1, x2, x3, x4.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [exact PC0|].
  split; [exact PC1|]. split; [exact PC2|]. split; [exact PC3|]. split; [exact POST | exact FR].
Qed.

(* [comment removed for export] *)
Definition T_run_once_leave_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SP0 Cp : Z) (cbv oldcb canary rao s0o s1o s2o s3o s4o s5o s6o : word) (junk : list byte),
    rw_cells asegs m Cp [C4 (Z_to_bv 64 1)] -> Cp mod 4 = 0 ->
    ssp_cells m canary ->
    rw_cells asegs m (bv_unsigned tp + -96) [C8 cbv] -> 96 <= bv_unsigned tp ->
    rw_cells asegs m (SP0 + -128) (once_full_cells Cp oldcb canary s6o s5o s4o s3o s2o s1o (Z_to_bv 64 SP0)) ->
    rw_cells asegs m (SP0 + -32) [Cells.CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)] ->
    rw_cells asegs m (SP0 + -16) [C8 s0o; C8 rao] ->
    stk asegs m lo (SP0 + -128) -> 0 <= lo -> lo <= SP0 - 160 -> SP0 < 2 ^ 64 ->
    (Cp + 4 <= lo \/ SP0 <= Cp) ->
    (bv_unsigned tp + -88 <= lo \/ SP0 <= bv_unsigned tp + -96) ->
    (Cp + 4 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= Cp) ->
    (got_ssp + 8 <= lo \/ SP0 <= got_ssp) -> (ssp_guard + 8 <= lo \/ SP0 <= ssp_guard) ->
    (got_ssp + 8 <= Cp \/ Cp + 4 <= got_ssp) -> (ssp_guard + 8 <= Cp \/ Cp + 4 <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= ssp_guard) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR rao (Z_to_bv 64 SP0) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc rao) fc None m' (seg_rom asegs)
                 /\ munch [(SP0 - 160, SP0); (Cp, Cp + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo SP0 /\ ssp_cells m' canary
                 /\ rw_cells asegs m' Cp [C4 (Z_to_bv 64 2)]
                 /\ rw_cells asegs m' (bv_unsigned tp + -96) [C8 oldcb])
        (MS (mkR ra (Z_to_bv 64 (SP0 + -128)) gp tp t0 t1 t2 (Z_to_bv 64 Cp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom asegs)).

Theorem T_run_once_leave_proof : T_run_once_leave_stmt.
Proof.
  unfold T_run_once_leave_stmt. intros until junk. intros CC AL SSP CB TP FR0 FR1 FR ST LO0 LO SPH S1 S2 S3 S4 S5 S6 S7 S8 S9 MI.
  pose proof (rw_cells_bound _ _ _ _ CC) as CBD. cbn [cells_size csize Nat.add] in CBD.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(SP0 - 160, SP0); (Cp, Cp + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  replace (SP0 + -128) with (SP0 + -16 + -112) in * by lia.
  replace (SP0 + -32) with (SP0 + -16 + -16) in * by lia.
  pose proof (once_leave_proof ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (SP0 + -16) Cp
                cbv oldcb canary (Z_to_bv 64 RUN_ONCE_RET) (Z_to_bv 64 SP0) s1o s2o s3o s4o s5o s6o junk) as OL.
  unfold RUN_ONCE_RET in *.
  call OL.
  1-21: first [eassumption | lia].
  clear OL. cbv delta [mkR].
  do 5 ths.
  th_release FR SP0.
  finish.
Qed.
