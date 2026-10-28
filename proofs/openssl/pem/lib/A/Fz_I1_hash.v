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

Definition e_err_hash : Z := 0x1ffc90.
Definition e_err_cmp : Z := 0x1ffd14.
Definition e_err_hash_thunk : Z := 0x1ffd80.
Definition e_err_comp_thunk : Z := 0x1ffda0.

(* [comment removed for export] *)
Definition err_hash_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e : word),
    ro_cells asegs m (bv_unsigned a0) [C8 e] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (h a1' a2' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 h a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_err_hash) fc None m (seg_rom asegs)).

Theorem err_hash_proof : err_hash_stmt.
Proof.
  unfold err_hash_stmt, g_shadow_memory_dynamic_address, SHB, e_err_hash. intros until e. intros VC VA VAL VNZ VLO UT SHC ST LO0 LO HTOP MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Vp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.                                                                               (* [comment removed for export] *)
  do 6 zstep.
  zstep. th_if_lit. do 3 zstep.
  (* [comment removed for export] *)
  if_cases Hb; [zstep | do 2 zstep].
  all: do 13 zstep; th_release FR (bv_unsigned sp); zstep; zstep; finish.
Qed.

(* [comment removed for export] *)
Definition err_cmp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e1 e2 : word),
    ro_cells asegs m (bv_unsigned a0) [C8 e1] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->
    ro_cells asegs m (bv_unsigned a1) [C8 e2] -> acc asegs m (bv_unsigned a1) 8 -> bv_unsigned a1 mod 8 = 0 -> bv_unsigned a1 <> 0 -> bv_unsigned a1 + 8 <= lo ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (v a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_err_cmp) fc None m (seg_rom asegs)).

Theorem err_cmp_proof : err_cmp_stmt.
Proof.
  unfold err_cmp_stmt, g_shadow_memory_dynamic_address, SHB, e_err_cmp. intros until e2. intros VC VA VAL VNZ VLO WC WA WAL WNZ WLO UT SHC ST LO0 LO HTOP MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (ro_cells_bound _ _ _ _ WC) as WB. cbn [cells_size csize Nat.add] in WB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Vp := bv_unsigned a0) in *. set (Wp := bv_unsigned a1) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a1 with (Z_to_bv 64 Wp) by (unfold Wp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.                                                                                (* [comment removed for export] *)
  do 6 zstep.
  zstep. th_if_lit. do 3 zstep.
  zstep. th_if_lit.
  do 8 zstep. th_release FR (bv_unsigned sp). zstep. finish.
Qed.

(* [comment removed for export] *)
Definition err_hash_thunk_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e : word),
    a1 = Z_to_bv 64 e_err_hash ->
    ro_cells asegs m (bv_unsigned a0) [C8 e] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (h a1' a2' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 h a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_err_hash_thunk) fc None m (seg_rom asegs)).

Theorem err_hash_thunk_proof : err_hash_thunk_stmt.
Proof.
  unfold err_hash_thunk_stmt, g_shadow_memory_dynamic_address, SHB, e_err_hash_thunk. intros until e. intros -> VC VA VAL VNZ VLO UT SHC ST LO0 LO HTOP MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 7 zstep. th_release FR (bv_unsigned sp). zstep.
  rewrite (ret_pc_even e_err_hash) by (unfold e_err_hash; first [lia | reflexivity]). unfold e_err_hash.
  call err_hash_proof; [exact VC| exact (acc_munch_sh _ m _ _ _ VA MU HWS ltac:(lia) ltac:(lia))| exact VAL| exact VNZ| exact VLO| exact (ut_munch _ m _ UT MU HWU)
                      | exact SHC| exact ST| lia| lia| lia| assumption|].
  finish.
Qed.

(* [comment removed for export] *)
Definition err_comp_thunk_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (e1 e2 : word),
    a2 = Z_to_bv 64 e_err_cmp ->
    ro_cells asegs m (bv_unsigned a0) [C8 e1] -> acc asegs m (bv_unsigned a0) 8 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 <> 0 -> bv_unsigned a0 + 8 <= lo ->
    ro_cells asegs m (bv_unsigned a1) [C8 e2] -> acc asegs m (bv_unsigned a1) 8 -> bv_unsigned a1 mod 8 = 0 -> bv_unsigned a1 <> 0 -> bv_unsigned a1 + 8 <= lo ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (v a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_err_comp_thunk) fc None m (seg_rom asegs)).

Theorem err_comp_thunk_proof : err_comp_thunk_stmt.
Proof.
  unfold err_comp_thunk_stmt, g_shadow_memory_dynamic_address, SHB, e_err_comp_thunk. intros until e2.
  intros -> VC VA VAL VNZ VLO WC WA WAL WNZ WLO UT SHC ST LO0 LO HTOP MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (ro_cells_bound _ _ _ _ WC) as WB. cbn [cells_size csize Nat.add] in WB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 7 zstep. th_release FR (bv_unsigned sp). zstep.
  rewrite (ret_pc_even e_err_cmp) by (unfold e_err_cmp; first [lia | reflexivity]). unfold e_err_cmp.
  call err_cmp_proof; [exact VC| exact (acc_munch_sh _ m _ _ _ VA MU HWS ltac:(lia) ltac:(lia))| exact VAL| exact VNZ| exact VLO
                     | exact WC| exact (acc_munch_sh _ m _ _ _ WA MU HWS ltac:(lia) ltac:(lia))| exact WAL| exact WNZ| exact WLO
                     | exact (ut_munch _ m _ UT MU HWU)| exact SHC| exact ST| lia| lia| lia| assumption|].
  finish.
Qed.
