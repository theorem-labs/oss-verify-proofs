(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_I1_img Fz_I1_insw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition e_err_load_strings : Z := 0x1fd62c.
Definition e_T_write_lock : Z := 0x1f6054.
Definition e_T_unlock : Z := 0x1f6080.
Definition SITE_els_insert : Z := 0x1fd6a0.     (* [comment removed for export] *)
Definition ELS_LOCK_RET : Z := 0x1fd670.       (* [comment removed for export] *)
Definition ELS_EXIT : Z := 0x1fd6c0.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition G_ERR_LOCK : Z := 0xb9f7e0.
Definition G_ERR_HASH : Z := 0xb9f800.

(* [comment removed for export] *)
Definition els_w0_post (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (LK : Z) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 ELS_LOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp a0 (Z_to_bv 64 LK) (Z_to_bv 64 LK) a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_T_write_lock) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma els_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo LK : Z),
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> 0 <= LK < 2^64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (els_w0_post sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m LK)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_err_load_strings) fc None m (seg_rom asegs)).
Proof.
  intros until LK. intros LKC LKR UT SHC ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold e_err_load_strings. unfold G_ERR_LOCK in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 zstep.
  do 8 zstep.
  apply evt_done. unfold els_w0_post, ELS_LOCK_RET, e_T_write_lock, SHB. do 2 eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition els_w1_post (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (str lh e0 : Z) : machine_state -> Prop :=
  fun ms =>
    ms = (if e0 =? 0
          then MS (mkR (Z_to_bv 64 ELS_LOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 str) (Z_to_bv 64 e0) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ELS_EXIT) fc None m (seg_rom asegs)
          else MS (mkR (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 str) (Z_to_bv 64 lh) (Z_to_bv 64 str) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (str + 16)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 e_lh_insert) fc None m (seg_rom asegs)).

Lemma els_w1 : forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo str lh e0 : Z),
  ro_cells asegs m str [C8 (Z_to_bv 64 e0)] -> 0 <= e0 < 2^64 -> acc asegs m str 8 -> str mod 8 = 0 -> 0x10000 <= str -> str + 16 <= SEGTOP_A -> SEGTOP_A <= lo ->
  rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)] -> 0 <= lh < 2^64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (els_w1_post sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str lh e0)
      (MS (mkR (Z_to_bv 64 ELS_LOCK_RET) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 str) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ELS_LOCK_RET) fc None m (seg_rom asegs)).
Proof.
  intros until e0. intros EC ER ACC AL SLO SHI UTLO LHC LHR UT SHC ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address in SHC. unfold ELS_LOCK_RET, SHB in *. unfold G_ERR_HASH in LHC. unfold SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit.
  do 3 zstep. zstep. th_if_lit. zstep.
  zstep. if_cases Hb; zify_cond Hb.
  - apply evt_done. unfold els_w1_post, ELS_EXIT, ELS_LOCK_RET, SHB. rewrite (proj2 (Z.eqb_eq e0 0) Hb). cbv delta [mkR]. reflexivity.
  - do 4 zstep. zstep.
    apply evt_done. unfold els_w1_post, SITE_els_insert, e_lh_insert, SHB. rewrite (proj2 (Z.eqb_neq e0 0) Hb). cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition els_w2_post (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (cur lh e' : Z) : machine_state -> Prop :=
  fun ms =>
    ms = (if e' =? 0
          then MS (mkR (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (cur + 16)) (Z_to_bv 64 e') a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (cur + 32)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ELS_EXIT) fc None m (seg_rom asegs)
          else MS (mkR (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (cur + 16)) (Z_to_bv 64 lh) (Z_to_bv 64 (cur + 16)) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (cur + 32)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 e_lh_insert) fc None m (seg_rom asegs)).

Lemma els_w2 : forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo cur lh e' : Z),
  ro_cells asegs m (cur + 16) [C8 (Z_to_bv 64 e')] -> 0 <= e' < 2^64 -> acc asegs m (cur + 16) 8 -> (cur + 16) mod 8 = 0 -> 0x10000 <= cur -> cur + 32 <= SEGTOP_A -> SEGTOP_A <= lo ->
  rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)] -> 0 <= lh < 2^64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (els_w2_post sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cur lh e')
      (MS (mkR (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 cur) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (cur + 16)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_els_insert) fc None m (seg_rom asegs)).
Proof.
  intros until e'. intros EC ER ACC AL SLO SHI UTLO LHC LHR UT SHC ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address in SHC. unfold SITE_els_insert, SHB in *. unfold G_ERR_HASH in LHC. unfold SEGTOP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  zstep. if_cases Hb; zify_cond Hb.
  - do 2 zstep. zstep.
    apply evt_done. unfold els_w2_post, e_lh_insert. rewrite (proj2 (Z.eqb_neq e' 0) Hb). cbv delta [mkR]. reflexivity.
  - apply evt_done. unfold els_w2_post, ELS_EXIT. rewrite (proj2 (Z.eqb_eq e' 0) Hb). cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma els_w3 : forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo LK : Z) (rav s0v s1v s2v s3v s4v s5v : word) (j6 : list byte),
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> 0 <= LK < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j6; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 LK) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (Z_to_bv 64 e_T_unlock) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 0xb9f658) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ELS_EXIT) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros LKC LKR FR UT ST LO0 LO HTOP MI.
  unfold ELS_EXIT in *. unfold G_ERR_LOCK in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. do 7 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -64 + Z.of_nat 64) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep. apply evt_done. unfold e_T_unlock. split; [| exact FR']. cbv delta [mkR].
  replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite ?(Z_to_bv_bv_unsigned sp). reflexivity.
Qed.
