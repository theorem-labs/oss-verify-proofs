(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Th_tsd Th_key Th_once Fz_T_once Fz_T_local.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).        (* [comment removed for export] *)
Notation MK_ONCE := (0xb9f500)%Z (only parsing).     (* [comment removed for export] *)
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation MK_INIT := (0xb9f540)%Z (only parsing).
Notation MK_CLEAN := (0x1f69dc)%Z (only parsing).    (* [comment removed for export] *)
Notation E_INIT_MASTER_KEY := (0x1f67c0)%Z (only parsing).

(* [comment removed for export] *)
Definition key_create_main_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w : word),
    rw_cells asegs m (bv_unsigned a0) [C4 kold] ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)] -> 88 <= bv_unsigned tp ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 96 ->
    (bv_unsigned a0 + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + 4 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned a0) ->
    KEY_LOCK + 12 <= bv_unsigned sp - 96 ->
    (bv_unsigned tp + -80 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 z64 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (if bv_eqb a1 z64 then Z_to_bv 64 NODTOR else a1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5295a4) fc None m (seg_rom asegs)).

Theorem key_create_main_proof : key_create_main_stmt.
Proof.
  unfold key_create_main_stmt. intros until w. intros KC TC TP NK HNK KL KJ PROBE CASE ST LO0 LO S1 S2 S3 S4 MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  set (KP := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 KP) by (unfold KP; rewrite Z_to_bv_bv_unsigned; reflexivity).
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 ths. do 3 ths.
  do 4 ths. th_if_lit. ths.
  destruct (bv_eqb a1 (Z_to_bv 64 0)) eqn:EA; cbv beta iota delta [negb].
  + do 2 ths. kc_call (Z_to_bv 64 5412472) lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
  + kc_call a1 lo sp KP nk j sh ra s0 s1 s2 s3 s4 kold w.
Qed.

(* [comment removed for export] *)
Definition init_local_main_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w : word),
    tp = Z_to_bv 64 TP_A ->
    rw_cells asegs m (bv_unsigned a0) [C4 kold] -> bv_unsigned a0 + 4 <= KEYS ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (if bv_eqb a1 z64 then Z_to_bv 64 NODTOR else a1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6134) fc None m (seg_rom asegs)).

Theorem init_local_main_proof : init_local_main_stmt.
Proof.
  unfold init_local_main_stmt. intros until w. intros -> KC KLO TC NK HNK KL KJ PROBE CASE ST LO0 LO HTOP MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  pose proof key_create_main_proof as KCP. unfold key_create_main_stmt in KCP.
  specialize (KCP (Z_to_bv 64 0x1f614c) (Z_to_bv 64 (bv_unsigned sp + -16))).
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in KCP by lia.
  call (KCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w).
  1-17: first [eassumption | rewrite unsigned_lit by lia; lia | lia].
  cbv delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_init_master_key_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w : word) (ib : byte),
    tp = Z_to_bv 64 TP_A ->
    rw_cells asegs m MK_INIT [C1 ib] ->
    rw_cells asegs m MK_KEY [C4 kold] ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 0xb9f7e8) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (MK_INIT, MK_INIT + 1); (MK_KEY, MK_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
                 /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 E_INIT_MASTER_KEY) fc None m (seg_rom asegs)).

Theorem T_init_master_key_proof : T_init_master_key_stmt.
Proof.
  unfold T_init_master_key_stmt. intros until ib. intros -> IC KC TC NK HNK KL KJ PROBE CASE ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (MK_INIT, MK_INIT + 1); (MK_KEY, MK_KEY + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 zstep.
  tcall (init_local_main_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w);
    [first [eassumption | reflexivity | rewrite unsigned_lit by lia; lia | lia] .. |].
  cbv delta [mkR].
  zstep. th_if_lit.
  do 2 zstep. zstep. fix_lit_store.
  do 2 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  change (if bv_eqb (Z_to_bv 64 MK_CLEAN) (Z_to_bv 64 0) then Z_to_bv 64 NODTOR else Z_to_bv 64 MK_CLEAN) with (Z_to_bv 64 MK_CLEAN) in *.
  finish.
Qed.

(* [comment removed for export] *)
Definition T_get_local_ex_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo id nk j sb : Z) (sh kold w oldcb canary : word) (ib : byte),
    tp = Z_to_bv 64 TP_A -> a0 = Z_to_bv 64 id -> 0 <= id <= 8 -> a1 = Z_to_bv 64 1 ->
    rw_cells asegs m MK_ONCE [C4 z64] ->
    rw_cells asegs m MK_INIT [C1 ib] ->
    rw_cells asegs m MK_KEY [C4 kold] ->
    ro_cells asegs m (MK_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ssp_cells m canary ->
    rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
    ro_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    ro_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 304 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 z64 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                           (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
                 /\ rw_cells asegs m' MK_ONCE [C4 (Z_to_bv 64 2)]
                 /\ rw_cells asegs m' MK_INIT [C1 (Z_to_bv 8 1)]
                 /\ rw_cells asegs m' MK_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 MK_CLEAN)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f66e4) fc None m (seg_rom asegs)).

Theorem T_get_local_ex_first_proof : T_get_local_ex_first_stmt.
Proof.
  unfold T_get_local_ex_first_stmt, g_shadow_memory_dynamic_address, SHB. intros until ib.
  intros -> -> HID -> OC IC KC KSB HSB UT SHC [GOT GU] CB TC NK HNK KL KJ PROBE CASE SLOT ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp); (MK_ONCE, MK_ONCE + 4); (MK_KEY, MK_KEY + 4); (MK_INIT, MK_INIT + 1);
                           (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  unfold got_ssp, ssp_guard in *.
  set (Pj := TSD_MAIN + 8 * j) in *.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  do 7 zstep. do 3 zstep.
  do 2 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep.
  pose proof T_run_once_enter_proof as OE. unfold T_run_once_enter_stmt, ssp_cells, got_ssp, ssp_guard in OE.
  tcall (OE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo E_INIT_MASTER_KEY oldcb canary).
  1-21: first [eassumption | reflexivity | lia | split; eassumption].
  clear OE. cbv beta delta [mkR]. try th_ret_lit.
  destruct PC0 as [GOT' GU']. clear GOT GU. unfold once_full_cells in PC3.
  tcall (T_init_master_key_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w ib);
    [first [eassumption | reflexivity | lia] .. |].
  cbv beta delta [mkR]. unfold ONCE_RET_INIT. th_ret_lit.
  pose proof (T_run_once_leave_proof) as OL. unfold T_run_once_leave_stmt, ssp_cells, got_ssp, ssp_guard, ONCE_RET_INIT in OL.
  tcall (OL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (bv_unsigned sp + -48) MK_ONCE (Z_to_bv 64 (bv_unsigned sp + -48 + -128)) oldcb canary
              (Z_to_bv 64 0x1f6740) sp (Z_to_bv 64 0) (Z_to_bv 64 id) (Z_to_bv 64 2147450880) s4 s5 s6 x3).
  1-22: first [eassumption | reflexivity | lia | split; eassumption].
  clear OL. cbv beta delta [mkR].
  do 2 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let K := fresh "K8" in destruct c eqn:K; [ zify_cond K; exfalso; lia | ] end.
  zstep. th_if_lit.
  do 2 zstep. zstep.
  lazymatch goal with K : rw_cells _ _ MK_KEY [C4 (Z_to_bv 64 j)] |- _ => pose proof (proj1 K) as KRO end.
  tcall (T_get_local_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD_MAIN j sb (Z_to_bv 64 0));
    [first [eassumption | reflexivity | lia | exact (ut_munch _ m _ UT MU HWU)] .. |].
  cbv beta delta [mkR].
  zstep. th_if_lit.
  zstep. do 5 zstep.
  th_release FR (bv_unsigned sp).
  do 2 zstep.
  finish. split; [exact GOT' | exact GU'].
Qed.
