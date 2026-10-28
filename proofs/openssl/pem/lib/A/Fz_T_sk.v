(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_G_CRYPTO_calloc Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Definition e_sk_reserve : Z := 0x1fa5e0.
Definition e_sk_insert : Z := 0x1faa5c.
Definition e_sk_push : Z := 0x1fb7f4.
Definition SITE_skr_calloc : Z := 0x1fa6e0.
Definition SITE_ski_reserve : Z := 0x1fab44.
Definition SK_FILE : Z := 0x495a0.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition sk_cells (num pad data sorted nalloc comp cmpt freet copyt : word) : list cell :=
  [C4 num; C4 pad; C8 data; C4 sorted; C4 nalloc; C8 comp; C8 cmpt; C8 freet; C8 copyt].

(* [comment removed for export] *)
Lemma skr_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad srt nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 194) a4 a5 a6 a7
                    (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_calloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -80) /\ rw_cells asegs m' A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_reserve) fc None m (seg_rom asegs)).
Proof.
  intros until copyt. intros AHI AAL ALO HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sk_reserve, sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_skr_calloc, SK_FILE, e_CRYPTO_calloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 11 zstep.
  do 3 zstep.                                               (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.
  do 3 zstep.                                               (* [comment removed for export] *)
  repeat match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
  zstep. zstep. th_if_lit.                                  (* [comment removed for export] *)
  zstep.                                                    (* [comment removed for export] *)
  zstep. zstep. th_if_lit. zstep.                           (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 6 zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma skr_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D : Z) (pad srt nalloc comp cmpt freet copyt : word) (j : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> rw_cells asegs m A (sk_cells z64 pad z64 srt nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  0x10007fff8000 <= D -> D + 32 <= lo ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -80) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A + 8, A + 16); (A + 20, A + 24)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells z64 pad (Z_to_bv 64 D) srt (Z_to_bv 64 4) comp cmpt freet copyt))
    (MS (mkR (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_skr_calloc) fc None m (seg_rom asegs)).
Proof.
  intros until s7v. intros AHI AAL ALO HC ACC DHI DLO UT SHC FR ST LO0 LO HTOP MI. unfold sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_skr_calloc, SK_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(A + 8, A + 16); (A + 20, A + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-80) EU1.
  zstep. zstep. th_if_lit.
  zstep.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 3 zstep. zstep. zstep. th_if_lit.
  zstep. fix_lit_store. zstep.
  zstep. do 9 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ski_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 1) z64 a3 a4 a5 a6 a7
                    z64 s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_reserve) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -112) /\ rw_cells asegs m' A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val z64 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_insert) fc None m (seg_rom asegs)).
Proof.
  intros until copyt. intros AHI AAL ALO HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sk_insert, e_sk_reserve, sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_ski_reserve in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  zstep.                                                    (* [comment removed for export] *)
  do 2 zstep. do 3 zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. do 2 zstep. zstep. th_if_lit.
  do 3 zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma ski_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A D : Z) (pad comp cmpt freet copyt : word) (j : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo -> rw_cells asegs m A (sk_cells z64 pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt) -> acc asegs m A 56 ->
  0x10007fff8000 <= D -> D mod 8 = 0 -> D + 32 <= lo -> rw_cells asegs m D [C8 z64; CB 24 (zeros 24)] -> acc asegs m D 32 -> (A + 56 <= D \/ D + 32 <= A) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j; C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -112) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' a3' a4' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(A, A + 4); (D, D + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' A (sk_cells (Z_to_bv 64 1) pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
       /\ rw_cells asegs m' D [C8 val; CB 24 (zeros 24)])
    (MS (mkR (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
            z64 s3 val s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ski_reserve) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros AHI AAL ALO HC ACC DHI DAL DLO DC ACCD DISJ UT SHC FR ST LO0 LO HTOP MI. unfold sk_cells, g_shadow_memory_dynamic_address, SHB, SITE_ski_reserve in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 val) as RV. unfold bv_modulus in RV. cbn in RV.
  pose proof (munch_refl [(A, A + 4); (D, D + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-112) EU1.
  zstep. th_if_lit.                                                   (* [comment removed for export] *)
  zstep. zstep. th_if_lit.                                            (* [comment removed for export] *)
  do 3 zstep. zstep. zstep. th_if_lit.                                (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small 0) by lia. zstep.                     (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.                                       (* [comment removed for export] *)
  zstep. zstep.                                                       (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.                                       (* [comment removed for export] *)
  zstep. zstep. zstep.                                                (* [comment removed for export] *)
  zstep. zstep. th_if_lit.                                            (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small 0) by lia.                            (* [comment removed for export] *)
  do 4 zstep. fix_lit_store. do 2 zstep. zstep. th_if_lit.            (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small 1) by lia. zstep. th_if_lit.          (* [comment removed for export] *)
  zstep. th_if_lit. zstep. zstep. th_if_lit.                          (* [comment removed for export] *)
  zstep. rewrite (t_sx32_small 1) by lia.                            (* [comment removed for export] *)
  do 13 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma skp_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 val : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo A : Z) (pad nalloc comp cmpt freet copyt : word),
  0x10007fff8000 <= A -> A mod 8 = 0 -> A + 56 <= lo ->
  rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) -> acc asegs m A 56 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a4' : word) (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val z64 (Z_to_bv 64 (Z.shiftr A 3)) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_sk_insert) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) val a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_sk_push) fc None m (seg_rom asegs)).
Proof.
  intros until copyt. intros AHI AAL ALO HC ACC UT SHC ST LO0 LO HTOP MI. unfold e_sk_push, e_sk_insert, sk_cells, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 3 zstep. do 2 zstep. zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small 0) by lia.
  do 2 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

Section CSk.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.

Definition SKR_SITES : list (Z * Z) := [(SITE_skr_calloc, e_sk_reserve); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition SKR_CALLS : list (Z * Z) := [(SITE_skr_calloc, e_CRYPTO_calloc); (SITE_skr_calloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition SKI_SITES : list (Z * Z) := (SITE_ski_reserve, e_sk_insert) :: SKR_SITES.
Definition SKI_CALLS : list (Z * Z) := (SITE_ski_reserve, e_sk_reserve) :: SKR_CALLS.

(* [comment removed for export] *)
Definition sk_first_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z) (canary : word) (A : Z)
    (num pad comp cmpt freet copyt w : word) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (D : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (A, A + 56)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' A (sk_cells num pad (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) comp cmpt freet copyt)
           /\ rw_cells asegs m' D [C8 w; CB 24 (zeros 24)]) c
       /\ rt_live RT Σ' = (D, 32) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < D /\ D mod 16 = 0 /\ D + 32 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Definition sk_reserve_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x170 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_sk_reserve (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SKR_SITES SKR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_reserve m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A z64 pad comp cmpt freet copyt z64).

Theorem sk_reserve_first_cps : sk_reserve_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary A pad nalloc comp cmpt freet copyt
    FDO MST -> -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE INSA SAAL HC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 368 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 80) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m A 56 ART0 INSA) as (SA0 & SALO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 ART0 INSA)) as ACC0.
  (* [comment removed for export] *)
  pose proof (skr_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo A pad (Z_to_bv 64 1) nalloc comp cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC ACC0 UT SHC ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & HC1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_reserve e_CRYPTO_calloc SITE_skr_calloc m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (C_CALLOC Σ PMc (Z_to_bv 64 SITE_skr_calloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 194) a4 a5 a6 a7
           (Z_to_bv 64 (A + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 (Z.shiftr (A + 8) 3 + SHB)) (Z_to_bv 64 SHB) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary
           FDO MST eq_refl ltac:(rewrite !unsigned_lit by lia; lia) ltac:(vm_compute; reflexivity) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 5. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_skr_calloc) by (unfold SITE_skr_calloc; lia). exact CTX1. }
  { exact UWC1. }
  { rewrite (unsigned_lit SITE_skr_calloc) by (unfold SITE_skr_calloc; lia). apply (proj2 CGH). cbn [SKR_CALLS In]. tauto. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SKR_SITES SKR_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { rewrite !unsigned_lit by lia. change (mcost (4 * 8)) with 0. exact Hcr. } { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PU & CG1).
  rewrite !unsigned_lit in LV1, CR1, PU, Hc2 by lia. change (4 * 8) with 32 in *. change (mcost 32) with 0 in CR1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & WRB & ACCB & ZB) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_skr_calloc) in Hc2' by (unfold SITE_skr_calloc; lia). change (Z.to_nat 32) with 32%nat in ZB.
  assert (INB : In (D, 32) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INSA1 : In (A, 56) (rt_live RT Σ1)) by (rewrite LV1; right; exact INSA).
  pose proof (af_live_range RT AF Σ1 m2 D 32 ART2 INB) as (_ & PLO & _). rewrite SP1 in PLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 D 32 ART2 INB ltac:(lia)) as PHI.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold G_ALLOW_CUST. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx NUM LOW HSTK. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (HC2 : rw_cells asegs m2 A (sk_cells (Z_to_bv 64 0) pad (Z_to_bv 64 0) (Z_to_bv 64 1) nalloc comp cmpt freet copyt)).
  { apply (rw_cells_agree asegs m1 m2 _ _ HC1); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add sk_cells] in Hx.
    apply PRES2; [apply (acl_live _ _ _ A 56); [exact INSA | lia]|]. unfold G_ALLOW_CUST. cbn [outside]. clear - Hx SAHI. lia. }
  assert (PC2 : rw_cells asegs m2 D [C8 (Z_to_bv 64 0); CB 24 (zeros 24)]) by (split; [split; [cbn; repeat split; reflexivity | exact ZB] | exact WRB]).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 A 56 ART2 INSA1)) as ACC2.
  (* [comment removed for export] *)
  pose proof (skr_w1 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s4 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo A D pad (Z_to_bv 64 1) nalloc comp cmpt freet copyt j ra s0 s1 s2 s3 s4 s5 s6 s7
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC2 ACC2 PHI ltac:(clear - PLO LOW; lia) UT2 SHC2 FR2 ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (e1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HC3) & Hc3'). clear Hc3.
  fold usp in ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx; apply (acl_live _ _ _ A 56); [exact INSA1 | clear - Hin; lia| exact INSA1 | clear - Hin; lia]. }
  assert (PC3 : rw_cells asegs m3 D [C8 (Z_to_bv 64 0); CB 24 (zeros 24)]).
  { apply (rw_cells_agree asegs m2 m3 _ _ PC2); [| exact WM3]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply MU3. cbn [outside].
    pose proof (af_live_disj RT AF Σ1 m2 D 32 A 56 [] (rt_live RT Σ) ART2 LV1 INSA) as DJ. clear - Hx DJ. repeat split; try exact I; lia. }
  assert (CRQ : rt_credit RT Σ1 = rt_credit RT Σ) by (rewrite CR1; lia).
  apply Hk. exists Σ1, D.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CRQ (conj P0 (conj P16 (conj PU CG1)))))))].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, u1, u2, e1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros x Hx Ho. pose proof (newchunk_apart RT AF Σ Σ1 m2 D 32 usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx) as NB.
    pose proof (aclient_split RT AF Σ m usp (bv_unsigned x) ART0 Hx) as SPL. cbn [outside] in Ho. destruct Ho as (O1 & O2 & _).
    rewrite (MU3 x ltac:(unfold usp1 in *; cbn [outside]; clear - NB O2 SPL NUM; repeat split; try exact I; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; exact (conj O1 I))). apply PR1; [exact Hx | exact I]. }
  split; [apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia|].
  exact (conj HC3 PC3).
Qed.

(* [comment removed for export] *)
Definition sk_insert_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  a0 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x1f0 <= bv_unsigned sp ->      (* [comment removed for export] *)
  cg_ctx (rt_cg RT Σ) e_sk_insert (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) SKI_SITES SKI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_insert m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A (Z_to_bv 64 1) pad comp cmpt freet copyt a1).


Theorem sk_insert_first_cps : sk_insert_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary A pad nalloc comp cmpt freet copyt
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE INSA SAAL HC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 496 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -112).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 112) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m A 56 ART0 INSA) as (SA0 & SALO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 ART0 INSA)) as ACC0.
  (* [comment removed for export] *)
  pose proof (ski_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m lo A pad nalloc comp cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC ACC0 UT SHC ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & HC1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 112 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 112 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_sk_insert e_sk_reserve SITE_ski_reserve m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  (* [comment removed for export] *)
  apply (sk_reserve_first_cps Σ PMc (Z_to_bv 64 SITE_ski_reserve) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 A) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7
           (Z_to_bv 64 0) s3 a1 s5 s6 (Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary A pad nalloc comp cmpt freet copyt
           FDO MST eq_refl eq_refl eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 7. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_ski_reserve) by (unfold SITE_ski_reserve; lia). exact CTX1. }
  { exact UWC1. }
  { split; intros x Hx; [apply (proj1 CGH) | apply (proj2 CGH)]; cbn [SKI_SITES SKI_CALLS SKR_SITES SKR_CALLS In] in Hx |- *; clear - Hx; tauto. }
  { exact Hlen. } { exact Hcr. } { exact CLE1. } { exact INSA. } { exact SAAL. } { exact HC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & D & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & HC2 & PC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ski_reserve) in Hc2' by (unfold SITE_ski_reserve; lia).
  assert (INB : In (D, 32) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INSA1 : In (A, 56) (rt_live RT Σ1)) by (rewrite LV1; right; exact INSA).
  pose proof (af_live_range RT AF Σ1 m2 D 32 ART2 INB) as (_ & PLO & _). rewrite SP1 in PLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 D 32 ART2 INB ltac:(lia)) as PHI.
  pose proof (af_live_disj RT AF Σ1 m2 D 32 A 56 [] (rt_live RT Σ) ART2 LV1 INSA) as DISJ.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold G_ALLOW_CUST. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx NUM LOW HSTK SAHI SALO. repeat split; try exact I; lia. }
  cl_keep FR1 AG2 WM2 FR2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 A 56 ART2 INSA1)) as ACC2.
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 D 32 ART2 INB)) as ACCD.
  (* [comment removed for export] *)
  pose proof (ski_w1 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s3 s5 s6 s9 s10 s11 u3 u4 u5 u6 a1 F2 fc2 m2 lo A D pad comp cmpt freet copyt j ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC2 ACC2 PHI ltac:(clear - P16; Z.div_mod_to_equations; lia) ltac:(clear - PLO LOW; lia) PC2 ACCD ltac:(clear - DISJ; lia)
                UT2 SHC2 FR2 ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (e1 & e2 & e3 & e4 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HC3 & PC3) & Hc3'). clear Hc3.
  fold usp in ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. repeat split; try exact I.
    - intros Hin; apply Hx. apply (acl_live _ _ _ A 56); [exact INSA1 | clear - Hin; lia].
    - intros Hin; apply Hx. apply (acl_live _ _ _ D 32); [exact INB | clear - Hin; lia]. }
  assert (CRQ : rt_credit RT Σ1 = rt_credit RT Σ) by (rewrite CR1; lia).
  apply Hk. exists Σ1, D.
  split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CRQ (conj P0 (conj P16 (conj PU CG1)))))))].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, u1, u2, e1, e2, e3, e4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) | exact ST3]]]|].
  split.
  { intros x Hx Ho. pose proof (newchunk_apart RT AF Σ Σ1 m2 D 32 usp _ ART2 LV1 FRS1 SP1 ltac:(lia) ltac:(lia) Hx) as NB.
    cbn [outside] in Ho. destruct Ho as (O1 & O2 & _).
    rewrite (MU3 x ltac:(cbn [outside]; clear - NB O2; repeat split; try exact I; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(cbn [outside]; exact (conj O1 (conj O2 I)))). apply PR1; [exact Hx | exact I]. }
  split; [apply (cl_env_seg _ m2 m3 _ canary CLE2 MU3); cl_fp_lia|].
  exact (conj HC3 PC3).
Qed.

(* [comment removed for export] *)
Definition sk_push_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (A : Z) (pad nalloc comp cmpt freet copyt : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  a0 = Z_to_bv 64 A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x1f0 <= bv_unsigned sp ->      (* [comment removed for export] *)
  cg_ctx (rt_cg RT Σ) e_sk_push (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> In (bv_unsigned ra, e_sk_insert) (cg_call (rt_cg RT Σ)) ->
  cg_has (rt_cg RT Σ) SKI_SITES SKI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  In (A, 56) (rt_live RT Σ) -> A mod 8 = 0 -> rw_cells asegs m A (sk_cells z64 pad z64 (Z_to_bv 64 1) nalloc comp cmpt freet copyt) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_sk_push m)))
    (sk_first_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo canary A (Z_to_bv 64 1) pad comp cmpt freet copyt a1).

Theorem sk_push_first_cps : sk_push_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary A pad nalloc comp cmpt freet copyt
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC TCALL CGH Hlen Hcr CLE INSA SAAL HC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 496 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 16) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m A 56 ART0 INSA) as (SA0 & SALO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m A 56 ART0 INSA ltac:(lia)) as SAHI.
  pose proof (proj2 (af_acc_live RT AF Σ m A 56 ART0 INSA)) as ACC0.
  (* [comment removed for export] *)
  pose proof (skp_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 F fc m lo A pad nalloc comp cmpt freet copyt
                SAHI SAAL ltac:(clear - SALO LOW; lia) HC ACC0 UT SHC ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a3x & m1 & -> & MU1 & WM1 & MI1 & ST1 & HC1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG01) as UWCm1.
  (* [comment removed for export] *)
  apply (sk_insert_first_cps Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr A 3)) a3x a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo outer lb canary A pad nalloc comp cmpt freet copyt FDO MST eq_refl eq_refl eq_refl ART1 MI1).
  { unfold call_ok. fold usp. split; [exact ST1|]. split; [exact LOW|]. split; [exact LOR|]. split; [exact SPT | exact SPA]. }
  { exact HSTK. }
  { destruct CTX as [_ LK]. split; [exact TCALL | exact LK]. }
  { exact UWCm1. }
  { exact CGH. } { exact Hlen. } { exact Hcr. } { exact CLE1. } { exact INSA. } { exact SAAL. } { exact HC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & D & Hc2 & REST).
  apply Hk. exists Σ1, D. split; [| exact REST].
  apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms2 (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & HC2 & PC2). exists m2.
  split; [exact RS2|].
  split; [split; [exact ART2|]; split; [exact MI2|]; split; [exact (wmono_trans asegs _ _ _ WM1 WM2) | exact ST2]|].
  split.
  { intros a Ha Ho. pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (PRES2 a Ha Ho). apply MU1. cbn [outside]. split; [lia | exact I]. }
  split; [exact CLE2|]. exact (conj HC2 PC2).
Qed.
End CSk.
