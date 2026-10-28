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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Th_tsd Th_key Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).


(* [comment removed for export] *)
Ltac t_chk4 AL SBV :=
  destruct SBV as [-> | ->];
  [ zstep; th_if_lit
  | zstep; th_if_lit; zstep;
    lazymatch goal with
    | |- context [Z.land ?x 7] => replace (Z.land x 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; exact (eq_sym AL))
    end;
    zstep; zstep; th_if_lit ].

(* [comment removed for export] *)
Definition T_get_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k sb : Z) (v : word),
    ro_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->                (* [comment removed for export] *)
    ro_cells asegs m (bv_unsigned a0 / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> bv_unsigned tp <= lo ->
    ro_cells asegs m (T + 8 * k) [C8 v] -> 0 <= T -> T + 8 * k + 8 <= lo ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t1' a1' a2' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 v a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6160) fc None m (seg_rom asegs)).

Theorem T_get_local_proof : T_get_local_stmt.
Proof.
  unfold T_get_local_stmt, g_shadow_memory_dynamic_address, SHB. intros until v. intros KC HK AL NZ ALO SBC SBV UT SHC TS TP TPLO VC T0 VLO ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (div8_facts (bv_unsigned a0)) as D8.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  set (Pk := T + 8 * k) in *.
  carve_frame 16%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.                                                                             (* [comment removed for export] *)
  do 3 zstep.
  zstep. rewrite (shr3_div (bv_unsigned a0)) by lia.
  do 2 zstep.
  t_chk4 AL SBV.
  all: zstep; rewrite (t_sx32_small k) by lia; do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep.
  all: (eapply evt_mono; [eapply (getspecific_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T k v); first [reflexivity | eassumption | lia] |]).
  all: intros ms' [a1' ->]; do 3 eexists; exists m1.
  all: (split; [cbv delta [mkR]; reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI | exact ST]).
Qed.

(* [comment removed for export] *)
Definition T_set_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T k sb : Z) (old : word) (u : byte),
    ro_cells asegs m (bv_unsigned a0) [C4 (Z_to_bv 64 k)] -> 0 <= k < 128 ->
    bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->                (* [comment removed for export] *)
    ro_cells asegs m (bv_unsigned a0 / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 150 <= bv_unsigned tp -> bv_unsigned tp <= lo ->
    rw_cells asegs m (T + 8 * k) [C8 old] -> 0 <= T -> T + 8 * k + 8 <= lo ->
    rw_cells asegs m (bv_unsigned tp + -150) [C1 u] ->
    (T + 8 * k + 8 <= bv_unsigned tp + -150 \/ bv_unsigned tp + -149 <= T + 8 * k) ->
    (T + 8 * k + 8 <= bv_unsigned tp + -88 \/ bv_unsigned tp + -80 <= T + 8 * k) ->
    (T + 8 * k + 8 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= T + 8 * k) ->
    (bv_unsigned tp + -149 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= bv_unsigned tp + -150) ->
    IMG_UT_HI <= T -> IMG_UT_HI + 150 <= bv_unsigned tp ->          (* [comment removed for export] *)
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a2' a3' : word) (u' : byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ ro_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 k)]
                 /\ ro_cells asegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)]
                 /\ rw_cells asegs m' (T + 8 * k) [C8 a1]
                 /\ rw_cells asegs m' (bv_unsigned tp + -150) [C1 u'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f61b4) fc None m (seg_rom asegs)).

Theorem T_set_local_proof : T_set_local_stmt.
Proof.
  unfold T_set_local_stmt, g_shadow_memory_dynamic_address, SHB. intros until u. intros KC HK AL NZ ALO SBC SBV UT SHC TS TP TPLO VC T0 VLO UC S1 S2 S3 S4 TRO TPRO ST LO0 LO HTOP MI.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  pose proof (div8_facts (bv_unsigned a0)) as D8.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (T + 8 * k, T + 8 * k + 8); (bv_unsigned tp + -150, bv_unsigned tp + -149)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  set (Pk := T + 8 * k) in *.
  carve_frame 16%nat ST.
  do 4 zstep.                                                                             (* [comment removed for export] *)
  do 3 zstep.
  zstep. rewrite (shr3_div (bv_unsigned a0)) by lia.
  do 2 zstep.
  t_chk4 AL SBV.
  all: zstep; rewrite (t_sx32_small k) by lia; zstep.
  all: call (setspecific_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T k old u); [ first [reflexivity | eassumption | lia] .. | ].
  all: cbv delta [mkR]; do 5 zstep; th_release FR (bv_unsigned sp); finish; eassumption.
Qed.

(* [comment removed for export] *)
Definition T_init_local_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo nk j : Z) (sh kold w tsd : word),
    rw_cells asegs m (bv_unsigned a0) [C4 kold] ->
    rw_cells asegs m (bv_unsigned tp + -88) [C8 tsd] -> 88 <= bv_unsigned tp -> (tsd = z64 \/ tsd = Z_to_bv 64 TSD_MAIN) ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] ->
    ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
    stk asegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    (bv_unsigned a0 + 4 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a0 + 4 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned a0) ->
    KEY_LOCK + 12 <= lo ->
    (bv_unsigned tp + -80 <= lo \/ bv_unsigned sp <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= bv_unsigned a0 \/ bv_unsigned a0 + 4 <= bv_unsigned tp + -88) ->
    (bv_unsigned tp + -80 <= KEYS \/ KEY_LOCK + 12 <= bv_unsigned tp + -88) ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' (bv_unsigned a0) [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' (bv_unsigned tp + -88) [C8 (Z_to_bv 64 TSD_MAIN)]
                 /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
                 /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh]
                 /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (if bv_eqb a1 z64 then Z_to_bv 64 NODTOR else a1)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6134) fc None m (seg_rom asegs)).

Theorem T_init_local_proof : T_init_local_stmt.
Proof.
  unfold T_init_local_stmt. intros until tsd. intros KC TC TP TV NK HNK KL KJ PROBE CASE ST LO0 LO S1 S2 S3 S4 S5 S6 MI.
  pose proof (rw_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 tp) as RTP. unfold bv_modulus in RTP. cbn in RTP.
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | apply Z.mod_pos_bound; lia]).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 4); (NEXT_KEY, NEXT_KEY + 12);
                           (KEYS + 8 * j, KEYS + 8 * j + 8); (bv_unsigned tp + -88, bv_unsigned tp + -80)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  pose proof key_create_proof as KCP. unfold key_create_stmt in KCP.
  specialize (KCP (Z_to_bv 64 0x1f614c) (Z_to_bv 64 (bv_unsigned sp + -16))).
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in KCP by lia.
  call (KCP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo nk j sh kold w tsd).
  1-20: first [eassumption | lia].
  cbv delta [mkR].
  do 5 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.
