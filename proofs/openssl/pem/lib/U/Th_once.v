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

(* [comment removed for export] *)
Definition once_done_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ro_cells usegs m (bv_unsigned a0) [C4 (Z_to_bv 64 2)] -> mem_inv usegs m ->
    evt usegs (fun ms' => exists a2' a3' : word,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2bea4c) fc None m (seg_rom usegs)).

Theorem once_done_proof : once_done_stmt.
Proof.
  unfold once_done_stmt. intros until m. intros CC MI.
  pose proof (ro_cells_bound _ _ _ _ CC) as CB. cbn [cells_size csize Nat.add] in CB.
  set (Cp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Cp) by (unfold Cp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  do 3 step. th_if_lit.
  do 3 step.
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ONCE_UNDO : Z := 0x2be9ec.
Definition ONCE_RET_FULL : Z := 0x2bea70.
Definition ONCE_RET_INIT : Z := 0x2be94c.
Definition once_full_cells (ctl : Z) (oldcb canary s6 s5 s4 s3 s2 s1 s0 : word) : list cell :=
  [C8 (Z_to_bv 64 ONCE_UNDO); C8 (Z_to_bv 64 ctl); C8 oldcb; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 ONCE_RET_FULL)].

Definition once_enter_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo INIT : Z) (oldcb canary : word),
    rw_cells usegs m (bv_unsigned a0) [C4 (Z_to_bv 64 0)] -> bv_unsigned a0 mod 4 = 0 ->
    a1 = Z_to_bv 64 INIT -> 0 <= INIT < 2 ^ 64 -> INIT mod 2 = 0 ->
    ssp_cells m canary ->
    rw_cells usegs m (bv_unsigned tp + -96) [C8 oldcb] -> 96 <= bv_unsigned tp ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    (bv_unsigned a0 + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned tp + -88 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned tp + -96) ->
    (bv_unsigned a0 + 4 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= bv_unsigned a0) ->
    (got_ssp + 8 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= ssp_guard) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a0' a1' a2' a3' : word) (junk : list byte) (m' : mem),
                 (* [comment removed for export] *)
                 ms' = MS (mkR (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 a0 (Z_to_bv 64 INIT) a0' a1' a2' a3' a4 a5 a6 a7
                               (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc (Z_to_bv 64 INIT)) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp + -112) /\ ssp_cells m' canary
                 /\ rw_cells usegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 1)]
                 /\ rw_cells usegs m' (bv_unsigned tp + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -112))]
                 /\ rw_cells usegs m' (bv_unsigned sp + -112) (once_full_cells (bv_unsigned a0) oldcb canary s6 s5 s4 s3 s2 s1 s0)
                 /\ rw_cells usegs m' (bv_unsigned sp + -16) [Cells.CB 8 junk; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2bea4c) fc None m (seg_rom usegs)).

Theorem once_enter_proof : once_enter_stmt.
Proof.
  unfold once_enter_stmt. intros until canary. intros CC AL -> HI0 HI2 [GOT GU] CB TP ST LO0 LO S1 S2 S3 S4 S5 S6 S7 S8 S9 MI.
  pose proof (rw_cells_bound _ _ _ _ CC) as CBD. cbn [cells_size csize Nat.add] in CBD.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  set (Cp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Cp) by (unfold Cp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (AMO : amo_aligned AW (Z_to_bv 64 Cp) = true) by (apply th_amo_aligned; [lia | exact AL]).
  unfold got_ssp, ssp_guard in *.
  do 3 step. th_if_lit.
  carve_frame 16%nat ST.
  do 3 ths.
  carve_frame 96%nat ST.
  do 9 ths.
  do 9 ths.
  do 2 ths.
  apply (rw_cells_split_CB usegs _ _ [] 24 _ _ [8; 8; 8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  th_amo_step AMO. ths. th_if_lit.
  th_amo_step AMO. ths. th_if_lit.
  ths. ths. th_if_lit. ths. th_if_lit. ths. th_if_lit.
  do 5 ths.
  do 3 ths.
  do 5 ths.
  ths.
  apply evt_done. do 5 eexists.
  lazymatch goal with MI' : mem_inv usegs ?mm |- _ => exists mm; assert (SSP : ssp_cells mm canary) by (split; assumption) end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact SSP|].
  split; [exact CC|]. split; [exact CB|]. split; [exact FR0 | exact FR].
Qed.

(* [comment removed for export] *)
Definition once_leave_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SP0 Cp : Z) (cbv oldcb canary rao s0o s1o s2o s3o s4o s5o s6o : word) (junk : list byte),
    rw_cells usegs m Cp [C4 (Z_to_bv 64 1)] -> Cp mod 4 = 0 ->
    ssp_cells m canary ->
    rw_cells usegs m (bv_unsigned tp + -96) [C8 cbv] -> 96 <= bv_unsigned tp ->
    rw_cells usegs m (SP0 + -112) (once_full_cells Cp oldcb canary s6o s5o s4o s3o s2o s1o s0o) ->
    rw_cells usegs m (SP0 + -16) [Cells.CB 8 junk; C8 rao] ->
    stk usegs m lo (SP0 + -112) -> 0 <= lo -> lo <= SP0 - 144 -> SP0 < 2 ^ 64 ->
    (Cp + 4 <= SP0 - 144 \/ SP0 <= Cp) ->
    (bv_unsigned tp + -88 <= SP0 - 144 \/ SP0 <= bv_unsigned tp + -96) ->
    (Cp + 4 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= Cp) ->
    (got_ssp + 8 <= SP0 - 144 \/ SP0 <= got_ssp) -> (ssp_guard + 8 <= SP0 - 144 \/ SP0 <= ssp_guard) ->
    (got_ssp + 8 <= Cp \/ Cp + 4 <= got_ssp) -> (ssp_guard + 8 <= Cp \/ Cp + 4 <= ssp_guard) ->
    (got_ssp + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= got_ssp) -> (ssp_guard + 8 <= bv_unsigned tp + -96 \/ bv_unsigned tp + -88 <= ssp_guard) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR rao (Z_to_bv 64 SP0) gp tp t0 t1 t2 s0o s1o (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc rao) fc None m' (seg_rom usegs)
                 /\ munch [(SP0 - 144, SP0); (Cp, Cp + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo SP0 /\ ssp_cells m' canary
                 /\ rw_cells usegs m' Cp [C4 (Z_to_bv 64 2)]
                 /\ rw_cells usegs m' (bv_unsigned tp + -96) [C8 oldcb])
        (MS (mkR ra (Z_to_bv 64 (SP0 + -112)) gp tp t0 t1 t2 (Z_to_bv 64 Cp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ONCE_RET_INIT) fc None m (seg_rom usegs)).

Theorem once_leave_proof : once_leave_stmt.
Proof.
  unfold once_leave_stmt. intros until junk. intros CC AL [GOT GU] CB TP FR0 FR ST LO0 LO SPH S1 S2 S3 S4 S5 S6 S7 S8 S9 MI.
  pose proof (rw_cells_bound _ _ _ _ CC) as CBD. cbn [cells_size csize Nat.add] in CBD.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (munch_refl [(SP0 - 144, SP0); (Cp, Cp + 4); (bv_unsigned tp + -96, bv_unsigned tp + -88)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  assert (AMO : amo_aligned AW (Z_to_bv 64 Cp) = true) by (apply th_amo_aligned; [lia | exact AL]).
  unfold got_ssp, ssp_guard, ONCE_RET_INIT, once_full_cells, ONCE_UNDO, ONCE_RET_FULL in *.
  do 3 ths.
  carve_frame 32%nat ST.
  do 7 ths.
  do 4 ths.
  ths. th_if_lit.
  do 5 ths.
  release_frame FR1 ST (SP0 + -112).
  do 2 ths.
  th_amo_step AMO. ths. th_if_lit.
  th_amo_step AMO. ths. th_if_lit.
  ths. ths. th_if_lit.
  ths. ths. th_if_lit.
  do 3 ths. rewrite (proj2 (Fs.bv_eqb_eq canary canary) eq_refl). cbv beta iota delta [negb].
  do 11 ths.
  do 4 ths.
  release_frame FR0 ST (SP0 + -16).
  release_frame FR ST SP0.
  apply evt_done. do 3 eexists.
  lazymatch goal with MI' : mem_inv usegs ?mm |- _ => exists mm; assert (SSP : ssp_cells mm canary) by (split; assumption) end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact SSP|].
  split; [exact CC | exact CB].
Qed.
