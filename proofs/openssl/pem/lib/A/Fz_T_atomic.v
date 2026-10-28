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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition T_atomic_load_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (v old : word),
    ro_cells asegs m (bv_unsigned a0) [C8 v] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 ->
    rw_cells asegs m (bv_unsigned a1) [C8 old] -> acc asegs m (bv_unsigned a1) 8 -> bv_unsigned a1 mod 8 = 0 ->
    (bv_unsigned a0 + 8 <= bv_unsigned a1 \/ bv_unsigned a1 + 8 <= bv_unsigned a0) ->
    (bv_unsigned a1 + 8 <= IMG_UT_LO \/ IMG_UT_HI <= bv_unsigned a1) ->
    (bv_unsigned a1 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned a1) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    bv_unsigned a0 + 8 <= lo -> bv_unsigned a1 + 8 <= lo ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a2' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2' v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ ro_cells asegs m' (bv_unsigned a0) [C8 v]
                 /\ rw_cells asegs m' (bv_unsigned a1) [C8 v])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6378) fc None m (seg_rom asegs)).

Theorem T_atomic_load_proof : T_atomic_load_stmt.
Proof.
  unfold T_atomic_load_stmt, g_shadow_memory_dynamic_address, SHB. intros until old. intros VC VA VAL RC RA RAL SEP RUT RSH UT SHC ST LO0 LO HTOP S1 S2 MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (rw_cells_bound _ _ _ _ RC) as RB. cbn [cells_size csize Nat.add] in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Vp := bv_unsigned a0) in *. set (Rp := bv_unsigned a1) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a1 with (Z_to_bv 64 Rp) by (unfold Rp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  th_frame 16%nat [8; 8]%nat ST.
  do 10 zstep.
  zstep. th_if_lit.
  do 5 zstep.
  zstep. th_if_lit.
  do 6 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

Lemma t_amo_aligned8 : forall a : Z, 0 <= a < 2 ^ 64 -> a mod 8 = 0 -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Lemma t_amo_or : forall v a : word, amo_val AMO_OR v a = Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a)).
Proof.
  intros v a. unfold amo_val. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 (bv_or v a)) as R. rewrite bv_or_unsigned in *.
  symmetry. apply bv_wrap_small. exact R.
Qed.

(* [comment removed for export] *)
Definition T_atomic_or_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (v old : word),
    rw_cells asegs m (bv_unsigned a0) [C8 v] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 ->
    rw_cells asegs m (bv_unsigned a2) [C8 old] -> acc asegs m (bv_unsigned a2) 8 -> bv_unsigned a2 mod 8 = 0 -> bv_unsigned a2 <> 0 ->      (* [comment removed for export] *)
    (bv_unsigned a0 + 8 <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= bv_unsigned a0) ->
    (bv_unsigned a0 + 8 <= IMG_UT_LO \/ IMG_UT_HI <= bv_unsigned a0) -> (bv_unsigned a0 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned a0) ->
    (bv_unsigned a2 + 8 <= IMG_UT_LO \/ IMG_UT_HI <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= bv_unsigned a2) ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    bv_unsigned a0 + 8 <= lo -> bv_unsigned a2 + 8 <= lo ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (nv a3' a4' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) nv a2 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 8); (bv_unsigned a2, bv_unsigned a2 + 8)] m m'
                 /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ nv = Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a1))
                 /\ rw_cells asegs m' (bv_unsigned a0) [C8 nv]
                 /\ rw_cells asegs m' (bv_unsigned a2) [C8 nv])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f6310) fc None m (seg_rom asegs)).

Theorem T_atomic_or_proof : T_atomic_or_stmt.
Proof.
  unfold T_atomic_or_stmt, g_shadow_memory_dynamic_address, SHB. intros until old. intros VC VA AL RC RA RAL NZ SEP VUT VSH RUT RSH UT SHC ST LO0 LO HTOP S1 S2 MI.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (rw_cells_bound _ _ _ _ RC) as RB. cbn [cells_size csize Nat.add] in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 8); (bv_unsigned a2, bv_unsigned a2 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Vp := bv_unsigned a0) in *. set (Rp := bv_unsigned a2) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a2 with (Z_to_bv 64 Rp) by (unfold Rp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (AMO : amo_aligned AD (Z_to_bv 64 Vp) = true) by (apply t_amo_aligned8; [lia | exact AL]).
  th_frame 16%nat [8; 8]%nat ST.
  do 10 zstep.
  zstep. th_if_lit.
  th_amo_step AMO. rewrite t_amo_or in VC.
  do 3 zstep.
  zstep. th_if_lit.
  do 7 zstep.
  th_release FR (bv_unsigned sp).
  apply evt_done. exists (Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a1))). do 2 eexists. exists m1.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity|]. split; [exact VC | exact RC].
Qed.
