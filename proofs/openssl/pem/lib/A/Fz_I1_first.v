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
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_T_once Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_M_zalloc Fz_M_locknew Fz_W5_icb Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_set_thunks Fz_G_OPENSSL_LH_new Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition e_lh_daw_thunk : Z := 0x1ffdc0.
Definition e_lh_daaw_thunk : Z := 0x1ffde0.
Definition SITE_desi_icb : Z := 0x1fd5a0.       (* [comment removed for export] *)
Definition SITE_desi_ln : Z := 0x1fd5a8.        (* [comment removed for export] *)
Definition SITE_desi_lhn : Z := 0x1fd5c8.       (* [comment removed for export] *)
Definition SITE_desi_st : Z := 0x1fd5ec.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition desi_w0_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_desi_icb) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_init_crypto) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma desi_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (desi_w0_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_do_esi) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold e_do_esi.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 8 zstep.
  apply evt_done. unfold desi_w0_post, SITE_desi_icb, e_init_crypto, OPT_BASE_ONLY. do 2 eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma desi_w1 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_desi_ln) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_lock_new) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 SITE_desi_icb) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_desi_icb) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold SITE_desi_icb in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit. zstep.
  apply evt_done. unfold SITE_desi_ln, e_lock_new. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition desi_w2_post (sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (pk : Z) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_desi_lhn) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xb9f5a8) (Z_to_bv 64 e_err_hash) (Z_to_bv 64 e_err_cmp) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_LH_new) fc None m' (seg_rom asegs)
    /\ munch [(G_ERR_LOCK, G_ERR_LOCK + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' G_ERR_LOCK [C8 (Z_to_bv 64 pk)]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma desi_w2 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo pk : Z) (lk0 : word),
  rw_cells asegs m G_ERR_LOCK [C8 lk0] -> 0 < pk < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (desi_w2_post sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m pk)
      (MS (mkR (Z_to_bv 64 SITE_desi_ln) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pk) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_desi_ln) fc None m (seg_rom asegs)).
Proof.
  intros until lk0. intros LKC PK ST LO0 LO HTOP MI.
  unfold SITE_desi_ln in *. unfold G_ERR_LOCK in LKC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(G_ERR_LOCK, G_ERR_LOCK + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. unfold G_ERR_LOCK in MU.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. zstep.
  zstep. if_cases Hb; zify_cond Hb. { exfalso. rewrite ?unsigned_lit in Hb by lia. lia. }
  do 4 zstep. zstep.
  apply evt_done. unfold desi_w2_post, SITE_desi_lhn, e_OPENSSL_LH_new, e_err_hash, e_err_cmp, G_ERR_LOCK. eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma desi_w3 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_desi_st) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0
                                   (Z_to_bv 64 e_err_hash_thunk) (Z_to_bv 64 e_err_comp_thunk) (Z_to_bv 64 e_lh_daw_thunk) (Z_to_bv 64 e_lh_daaw_thunk) a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_OPENSSL_LH_set_thunks) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 SITE_desi_lhn) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_desi_lhn) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold SITE_desi_lhn in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  do 9 zstep.
  apply evt_done. unfold SITE_desi_st, e_OPENSSL_LH_set_thunks, e_err_hash_thunk, e_err_comp_thunk, e_lh_daw_thunk, e_lh_daaw_thunk. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lhst_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (j1 j2 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) (Z_to_bv 64 (p0 + 48)) (Z_to_bv 64 0) a3 a4 (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 0)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(p0 + 24, p0 + 56); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' p0 [CB 24 j1; C8 a1; C8 a2; C8 a3; C8 a4; CB 48 j2]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma lhst_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (j1 j2 : list byte)
    (x1 x2 x3 x4 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m p0 [CB 24 j1; C8 x1; C8 x2; C8 x3; C8 x4; CB 48 j2] -> acc asegs m p0 104 -> p0 mod 8 = 0 ->
  0x10007fff8000 <= p0 -> p0 + 104 <= 2 ^ 47 -> p0 + 104 <= lo ->
  mem_inv asegs m ->
  evt asegs (lhst_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0 j1 j2 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_OPENSSL_LH_set_thunks) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO LO0 HTOP UT SHC HB ACC PAL PHI PTOP PSTK MI.
  unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold e_OPENSSL_LH_set_thunks.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(p0 + 24, p0 + 56); (bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. ifF.
  do 7 zstep.
  zstep. ifF.
  zstep.
  do 4 zstep.
  zstep. ifF.
  zstep.
  do 4 zstep.
  zstep. ifF.
  zstep.
  do 4 zstep.
  zstep. ifF.
  zstep.
  cl_eu (bv_unsigned sp) (-16) EU1.
  do 2 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep.
  apply evt_done. unfold lhst_post, SHB. eexists.
  split; [cbv delta [mkR]; replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| exact FR'].
Qed.

(* [comment removed for export] *)
Definition desi_w4_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (lh : Z) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) (Z_to_bv 64 0xb9f610) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' G_ERR_HASH [C8 (Z_to_bv 64 lh)] /\ rw_cells asegs m' G_ERR_FLAG [C4 (Z_to_bv 64 1)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma desi_w4 : forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh : Z) (h0 f0 rav s0v s1v : word) (j8 : list byte),
  rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] -> 0 < lh < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j8; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (desi_w4_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0v s1v F fc lo m lh)
      (MS (mkR (Z_to_bv 64 SITE_desi_st) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xb9f5a8) (Z_to_bv 64 lh) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_desi_st) fc None m (seg_rom asegs)).
Proof.
  intros until j8. intros LHC FLC LH FR ST LO0 LO HTOP MI.
  unfold SITE_desi_st in *. unfold G_ERR_HASH in LHC. unfold G_ERR_FLAG in FLC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM. unfold G_ERR_HASH, G_ERR_FLAG in MU.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  zstep. zstep.
  zstep. if_cases Hb; zify_cond Hb. { exfalso. rewrite ?unsigned_lit in Hb by lia. lia. }
  zstep. zstep.
  zstep. zstep.
  do 3 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep.
  apply evt_done. unfold desi_w4_post, G_ERR_HASH, G_ERR_FLAG. eexists.
  split; [cbv delta [mkR]; replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|]. split; [eassumption| exact FR'].
Qed.

(* [comment removed for export] *)
Lemma cells_mid_congr : forall (m : mem) A pre mid mid' post, cells_bytes mid = cells_bytes mid' -> cells_size mid = cells_size mid' -> cells_wf mid' ->
  rw_cells asegs m A (pre ++ mid ++ post) -> rw_cells asegs m A (pre ++ mid' ++ post).
Proof.
  intros m A pre mid mid' post EB ES WF H. eapply th_cells_congr; [| | | exact H].
  - rewrite !cells_bytes_app, EB. reflexivity.
  - rewrite !cells_size_app, ES. reflexivity.
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app in W2. destruct W2 as [_ W3].
    apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [exact WF| exact W3].
Qed.
Local Ltac closed_bytes := vm_compute; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); reflexivity.
Lemma concat_repeat_nil' : forall {X} n, concat (repeat (@nil X) n) = [].
Proof. intros X n. induction n as [|n IH]; cbn; [reflexivity| exact IH]. Qed.

Section DoEsi.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ICB : init_crypto_base_stmt RT.
Hypothesis C_LN : crypto_lock_new_env_stmt RT.
Hypothesis C_LHN : OPENSSL_LH_new_stmt RT.

(* [comment removed for export] *)
Lemma newchunk_apart_gen : forall (Σ Σ1 : rts RT) (m1 : mem) l1 p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ Σ1 m1 l1 p n usp a ART1 LV FRS SP0 LU Hn Ha.
  assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (R0 & R1 & R2). rewrite SP0 in R1.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p2 & n2 & Hin & Hp).
    destruct (af_live_disj RT AF Σ1 m1 p n p2 n2 l1 (rt_live RT Σ) ART1 LV ltac:(apply in_or_app; right; exact Hin)); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (SL & _). destruct (SL p n INL); lia.
Qed.

Definition DESI_SITES : list (Z * Z) :=
  [(SITE_desi_ln, e_do_esi); (SITE_desi_lhn, e_do_esi); (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new);
   (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition DESI_CALLS : list (Z * Z) :=
  [(SITE_desi_ln, e_lock_new); (SITE_desi_lhn, e_OPENSSL_LH_new); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc);
   (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].
Definition LH_G0 : lh_geo := mkGeo 8 16 0 8 0.

(* [comment removed for export] *)
Definition do_esi_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary od lk0 h0 f0 : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x200 + 32 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_do_esi (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) DESI_SITES DESI_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> 2 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 od] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m G_ERR_LOCK [C8 lk0] -> rw_cells asegs m G_ERR_HASH [C8 h0] -> rw_cells asegs m G_ERR_FLAG [C4 f0] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_do_esi m)))
    (fun c => exists (Σ' : rts RT) (pk lh B : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
                [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (G_ERR_LOCK, G_ERR_LOCK + 8); (G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 od]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' G_ERR_LOCK [C8 (Z_to_bv 64 pk)] /\ rw_cells asegs m' G_ERR_HASH [C8 (Z_to_bv 64 lh)] /\ rw_cells asegs m' G_ERR_FLAG [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' pk (mutex_cells z64 z64)
           /\ lh_repE GOBJ m' [(lh, 104); (B, 128)] lh B LH_G0 (repeat [] 16)) c
       /\ rt_live RT Σ' = (B, 128) :: (lh, 104) :: (pk, 40) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP).

Theorem do_esi_cps : do_esi_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary od lk0 h0 f0
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV STP OD ONCE BRET LKC LHC FLC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 544 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-32) EU1.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in STP, OD, ONCE, BRET. unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC. unfold G_ERR_FLAG in FLC.
  (* [comment removed for export] *)
  pose proof (desi_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 32, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 32) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ABOVE1 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= SEGTOP_A -> rw_cells asegs m1 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m m1 _ _ H); [| exact WM1]. apply BELOW1. unfold SEGTOP_A in *. intros; lia. }
  pose proof (STAT1 _ _ STP ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as STP1. pose proof (STAT1 _ _ OD ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as OD1.
  pose proof (STAT1 _ _ ONCE ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as ONCE1. pose proof (STAT1 _ _ BRET ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as BRET1.
  pose proof (STAT1 _ _ LKC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as LKC1. pose proof (STAT1 _ _ LHC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as LHC1.
  pose proof (STAT1 _ _ FLC ltac:(lia) ltac:(cbn; unfold SEGTOP_A; lia)) as FLC1.
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_agree m m1 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in *.
    apply MU1. cbn [outside]. split; [lia| exact I]. }
  pose proof (uw_chain_agree outer m m1 sp s0 UWC ltac:(apply ABOVE1; cbv beta; unfold USTACK_TOP in *; intros; lia)) as UWC1.
  (* [comment removed for export] *)
  apply (C_ICB Σ PMc (Z_to_bv 64 SITE_desi_icb) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 OPT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact Hfr. }
  { lia. }
  { exact STP1. }
  { exact OD1. }
  { exact ONCE1. }
  { exact BRET1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM12 & ST2) & PRES2 & STP2 & OD2 & ONCE2 & BRET2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. fold usp in ST2, PRES2. rewrite (ret_pc_even SITE_desi_icb) in Hc2' by (unfold SITE_desi_icb; lia).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in STP2, OD2, ONCE2, BRET2.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp - 32) x) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ (HP _ Ha)); [intros e He; exact He| intros e He; exact He| lia]. }
  assert (STAT2 : forall a cs, rw_cells asegs m1 a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f848 -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m1 m2 _ _ H); [| exact WM12]. apply AG2. intros x Hx. right; left. apply client_static_intro. lia. }
  pose proof (STAT2 _ _ LKC1 ltac:(lia) ltac:(cbn; lia)) as LKC2. pose proof (STAT2 _ _ LHC1 ltac:(lia) ltac:(cbn; lia)) as LHC2. pose proof (STAT2 _ _ FLC1 ltac:(lia) ltac:(cbn; lia)) as FLC2.
  eassert (FR2 : rw_cells asegs m2 (usp + -32) _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM12]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. left. unfold USTACK_TOP in *. lia. }
  pose proof (cl_env_pres _ _ _ m1 m2 lb canary ENV1 PRES2) as ENV2.
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; left; lia)) as UWC2.
  (* [comment removed for export] *)
  pose proof (desi_w1 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo
                ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  rewrite <- CG2 in CTX, CGH.
  assert (FR16 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { change ([CB 8 j8; C8 s1; C8 s0; C8 ra]) with ([CB 8 j8; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
    pose proof (rw_cells_skip m2 _ _ _ FR2) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -32 + 16) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ2) e_do_esi e_lock_new SITE_desi_ln m2 m2 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH (SITE_desi_ln, e_do_esi) ltac:(left; reflexivity)) (proj2 CGH (SITE_desi_ln, e_lock_new) ltac:(left; reflexivity)) UWC2 ltac:(intros a _; reflexivity)
              FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  apply (C_LN Σ2 PMc (Z_to_bv 64 SITE_desi_ln) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 (Z_to_bv 64 1) e1 e2 e3 e4 e5 e6 e7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW2 SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_desi_ln) by (unfold SITE_desi_ln; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold DESI_SITES, DESI_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { rewrite FRS2. exact Hfr. }
  { rewrite LV2. lia. }
  { rewrite CR2. lia. }
  { exact ENV2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ4 & pk & Hc4 & LV4 & FRS4 & SP4 & CR4 & PK0 & PK16 & PKHI & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM24 & ST4) & PRES4 & ENV4 & MC4 & PKACC) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_desi_ln) in Hc4' by (unfold SITE_desi_ln; lia).
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp - 32) x /\ x <> G_ALLOW_CUST) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). rewrite <- LV2, <- FRS2 in X1. apply PRES4; [| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  assert (STAT4 : forall a cs, rw_cells asegs m2 a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f848 -> rw_cells asegs m4 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m2 m4 _ _ H); [| exact WM24]. apply AG4. intros x Hx. split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST; lia]. }
  pose proof (STAT4 _ _ LKC2 ltac:(lia) ltac:(cbn; lia)) as LKC4. pose proof (STAT4 _ _ LHC2 ltac:(lia) ltac:(cbn; lia)) as LHC4. pose proof (STAT4 _ _ FLC2 ltac:(lia) ltac:(cbn; lia)) as FLC4.
  assert (STATI4 : forall a cs, rw_cells asegs m2 a cs -> 0xb9f1c0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f3c0 -> rw_cells asegs m4 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m2 m4 _ _ H); [| exact WM24]. apply AG4. intros x Hx. split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST; lia]. }
  pose proof (STATI4 _ _ STP2 ltac:(unfold G_IC_STOPPED; lia) ltac:(cbn; unfold G_IC_STOPPED; lia)) as STP4. pose proof (STATI4 _ _ OD2 ltac:(unfold G_IC_OPTSDONE; lia) ltac:(cbn; unfold G_IC_OPTSDONE; lia)) as OD4.
  pose proof (STATI4 _ _ ONCE2 ltac:(unfold G_IC_BASE_ONCE; lia) ltac:(cbn; unfold G_IC_BASE_ONCE; lia)) as ONCE4. pose proof (STATI4 _ _ BRET2 ltac:(unfold G_IC_BASE_RET; lia) ltac:(cbn; unfold G_IC_BASE_RET; lia)) as BRET4.
  eassert (FR4 : rw_cells asegs m4 (usp + -32) _).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact WM24]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold G_ALLOW_CUST, STACK_WIN in *; lia]. }
  pose proof (uw_chain_agree outer m2 m4 sp s0 UWC2 ltac:(apply AG4; intros x Hx; split; [left; lia| unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia])) as UWC4.
  assert (PKR : 0 < pk < 2^64) by (unfold USTACK_TOP in PKHI; lia).
  (* [comment removed for export] *)
  pose proof (desi_w2 sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp s1 d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 lo pk lk0
                LKC4 PKR ST4 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ4 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & LKC5 & ST5) & Hc5'). clear Hc5.
  assert (MU5' : munch ([(G_ERR_LOCK, G_ERR_LOCK + 8)] ++ [(usp - 32 - 0, usp - 32)]) m4 m5) by (eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ4 m4 m5 (usp - 32) 0 [(G_ERR_LOCK, G_ERR_LOCK + 8)] ART4 ltac:(rewrite SP4; lia) ltac:(lia) MU5'
                ltac:(intros x Hx; apply client_static_intro; unfold G_ERR_LOCK in Hx; cbn [outside] in Hx; lia) WM5) as ART5.
  assert (OFF5 : forall P : Z -> Prop, (forall x, P x -> ~ (G_ERR_LOCK <= x < G_ERR_LOCK + 8)) -> agree_on P m4 m5) by (intros P HP a Ha; apply MU5; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (STAT5 : forall a cs, rw_cells asegs m4 a cs -> (a + Z.of_nat (cells_size cs) <= G_ERR_LOCK \/ G_ERR_LOCK + 8 <= a) -> rw_cells asegs m5 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m4 m5 _ _ H); [| exact WM5]. apply OFF5. intros; lia. }
  unfold G_ERR_LOCK in STAT5, OFF5.
  pose proof (STAT5 _ _ LHC4 ltac:(cbn; lia)) as LHC5. pose proof (STAT5 _ _ FLC4 ltac:(cbn; lia)) as FLC5.
  pose proof (STAT5 _ _ STP4 ltac:(cbn; lia)) as STP5. pose proof (STAT5 _ _ OD4 ltac:(cbn; lia)) as OD5. pose proof (STAT5 _ _ ONCE4 ltac:(cbn; lia)) as ONCE5. pose proof (STAT5 _ _ BRET4 ltac:(cbn; lia)) as BRET5.
  pose proof (STAT5 _ _ FR4 ltac:(cbn; unfold STACK_WIN in *; lia)) as FR5.
  pose proof (af_live_range RT AF Σ4 m4 pk 40 ART4 ltac:(rewrite LV4; left; reflexivity)) as (_ & PKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ4 m4 pk 40 ART4 ltac:(rewrite LV4; left; reflexivity) ltac:(lia)) as PKH.
  pose proof (STAT5 _ _ MC4 ltac:(cbn; lia)) as MC5.
  assert (ENV5 : cl_env m5 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m4 m5 _ canary ENV4 MU5); unfold G_ERR_LOCK; cl_fp_lia).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWC4 ltac:(apply OFF5; cbv beta; unfold USTACK_TOP, STACK_WIN in *; intros; lia)) as UWC5.
  (* [comment removed for export] *)
  rewrite <- CG4 in CTX, CGH.
  assert (FR16b : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { change ([CB 8 j8; C8 s1; C8 s0; C8 ra]) with ([CB 8 j8; C8 s1] ++ [C8 s0; C8 ra]) in FR5.
    pose proof (rw_cells_skip m5 _ _ _ FR5) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -32 + 16) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ4) e_do_esi e_OPENSSL_LH_new SITE_desi_lhn m5 m5 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH (SITE_desi_lhn, e_do_esi) ltac:(right; left; reflexivity)) (proj2 CGH (SITE_desi_lhn, e_OPENSSL_LH_new) ltac:(right; left; reflexivity)) UWC5 ltac:(intros a _; reflexivity)
              FR16b ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXd & UWCd).
  assert (LOW4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact LOW2).
  apply (C_LHN Σ4 PMc (Z_to_bv 64 SITE_desi_lhn) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 0xb9f5a8) (Z_to_bv 64 e_err_hash) (Z_to_bv 64 e_err_cmp) d2 d3 d4 d5 d6 d7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_desi_lhn) by (unfold SITE_desi_lhn; lia). exact CTXd. }
  { exact UWCd. }
  { clear - CGH. unfold DESI_SITES, DESI_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { rewrite LV4, LV2. cbn [length]. lia. }
  { rewrite CR4. unfold mcost. cbn. lia. }
  { exact ENV5. }
  { reflexivity. }
  { reflexivity. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ6 & lh & B & Hc6 & LV6 & FRS6 & SP6 & CR6 & LH0 & LH16 & LHHI & B0 & B16 & BHI & CG6).
  destruct (ASTA_unpack RT Σ6 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM56 & ST6) & PRES6 & ENV6 & WRL & ACCL & WRB & ACCB & SC6 & ZB6) & Hc6'). clear Hc6.
  destruct RS6 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. fold usp in ST6, PRES6. rewrite (ret_pc_even SITE_desi_lhn) in Hc6' by (unfold SITE_desi_lhn; lia).
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ4) (rt_frames RT Σ) (usp - 32) x /\ x <> G_ALLOW_CUST) -> agree_on P m5 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). rewrite <- FRS2, <- FRS4 in X1. apply PRES6; [| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  assert (STAT6 : forall a cs, rw_cells asegs m5 a cs -> 0xb9f7e0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f848 -> rw_cells asegs m6 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m5 m6 _ _ H); [| exact WM56]. apply AG6. intros x Hx. split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST; lia]. }
  pose proof (STAT6 _ _ LKC5 ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_LOCK; lia)) as LKC6. pose proof (STAT6 _ _ LHC5 ltac:(lia) ltac:(cbn; lia)) as LHC6. pose proof (STAT6 _ _ FLC5 ltac:(lia) ltac:(cbn; lia)) as FLC6.
  assert (STATI6 : forall a cs, rw_cells asegs m5 a cs -> 0xb9f1c0 <= a -> a + Z.of_nat (cells_size cs) <= 0xb9f3c0 -> rw_cells asegs m6 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m5 m6 _ _ H); [| exact WM56]. apply AG6. intros x Hx. split; [right; left; apply client_static_intro; lia| unfold G_ALLOW_CUST; lia]. }
  pose proof (STATI6 _ _ STP5 ltac:(lia) ltac:(cbn; lia)) as STP6. pose proof (STATI6 _ _ OD5 ltac:(lia) ltac:(cbn; lia)) as OD6.
  pose proof (STATI6 _ _ ONCE5 ltac:(lia) ltac:(cbn; lia)) as ONCE6. pose proof (STATI6 _ _ BRET5 ltac:(lia) ltac:(cbn; lia)) as BRET6.
  eassert (FR6 : rw_cells asegs m6 (usp + -32) _).
  { apply (rw_cells_agree asegs m5 m6 _ _ FR5); [| exact WM56]. apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold G_ALLOW_CUST, STACK_WIN in *; lia]. }
  assert (MC6 : rw_cells asegs m6 pk (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m5 m6 _ _ MC5); [| exact WM56]. apply AG6. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx.
    split; [right; right; left; exists pk, 40; split; [rewrite LV4; left; reflexivity| lia]| unfold G_ALLOW_CUST in *; lia]. }
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWC5 ltac:(apply AG6; intros x Hx; split; [left; lia| unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia])) as UWC6.
  pose proof (af_live_range RT AF Σ6 m6 lh 104 ART6 ltac:(rewrite LV6; right; left; reflexivity)) as (_ & LHLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ6 m6 lh 104 ART6 ltac:(rewrite LV6; right; left; reflexivity) ltac:(lia)) as LHH.
  pose proof (af_live_range RT AF Σ6 m6 B 128 ART6 ltac:(rewrite LV6; left; reflexivity)) as (_ & BLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ6 m6 B 128 ART6 ltac:(rewrite LV6; left; reflexivity) ltac:(lia)) as BH.
  rewrite SP6, SP4 in LHLO, BLO.
  destruct (af_client_consts RT AF Σ6 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  (* [comment removed for export] *)
  pose proof (cells_mid_congr m6 lh [] [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 e_err_cmp); C8 (Z_to_bv 64 e_err_hash); CB 32 (repeat (Z_to_bv 8 0) 32)]
                [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_err_cmp) ++ le8 (Z_to_bv 64 e_err_hash)); C8 z64; C8 z64; C8 z64; C8 z64]
                [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]
                ltac:(cbn [cells_bytes cbytes app]; rewrite <- !app_assoc; reflexivity) eq_refl ltac:(cbn; repeat split; reflexivity) SC6) as SC6'.
  cbn [app] in SC6'.
  pose proof (cells_mid_congr m6 lh [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_err_cmp) ++ le8 (Z_to_bv 64 e_err_hash)); C8 z64; C8 z64; C8 z64; C8 z64]
                [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]
                [CB 48 (le4 (Z_to_bv 64 8) ++ le4 (Z_to_bv 64 16) ++ repeat (Z_to_bv 8 0) 4 ++ le4 (Z_to_bv 64 8) ++ le8 (Z_to_bv 64 512) ++ le8 (Z_to_bv 64 256) ++ repeat (Z_to_bv 8 0) 16)] []
                ltac:(closed_bytes) eq_refl ltac:(cbn; repeat split; reflexivity) ltac:(rewrite app_nil_r; exact SC6')) as SC6''.
  rewrite app_nil_r in SC6''. cbn [app] in SC6''.
  (* [comment removed for export] *)
  pose proof (desi_w3 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 0xb9f5a8) (Z_to_bv 64 lh) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F6 fc6 m6 lo
                ST6 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI6) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ6 _ _ c7 Hc7) as (ms7 & -> & Hc7'). clear Hc7.
  (* [comment removed for export] *)
  epose proof (lhst_walk (Z_to_bv 64 SITE_desi_st) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 0xb9f5a8)
                (Z_to_bv 64 e_err_hash_thunk) (Z_to_bv 64 e_err_comp_thunk) (Z_to_bv 64 e_lh_daw_thunk) (Z_to_bv 64 e_lh_daaw_thunk) b5 b6 b7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 lh _ _ z64 z64 z64 z64 F6 fc6 m6 lo) as WT.
  rewrite EU1 in WT. specialize (WT ST6 ltac:(unfold RT_STACK in *; lia) LO0 ltac:(unfold USTACK_TOP in *; lia) UT6 SHC6 SC6'' ACCL ltac:(clear - LH16; Z.div_mod_to_equations; lia)
                                LHH ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) MI6).
  cl_lift WT Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ6 _ _ c8 Hc8) as (ms8 & (m8 & -> & MU8 & WM8 & MI8 & SC8 & ST8) & Hc8'). clear Hc8.
  rewrite EU1 in MU8, ST8.
  rewrite (ret_pc_even SITE_desi_st) in Hc8' by (unfold SITE_desi_st; lia).
  assert (ART8 : ART RT Σ6 m8).
  { apply (af_frame RT AF Σ6 m6 m8 (usp - 48) ART6 ltac:(rewrite SP6, SP4; lia)); [| exact WM8]. intros a Ha. apply MU8. cbn [outside].
    split; [intros X; apply Ha; right; right; left; exists lh, 104; split; [rewrite LV6; right; left; reflexivity| lia]|].
    split; [| exact I]. intros X. apply Ha. left. unfold USTACK_TOP in *. lia. }
  assert (OFF8 : forall P : Z -> Prop, (forall x, P x -> ~ (lh + 24 <= x < lh + 56) /\ ~ (usp - 48 <= x < usp - 32)) -> agree_on P m6 m8).
  { intros P HP a Ha. apply MU8. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  assert (STAT8 : forall a cs, rw_cells asegs m6 a cs -> a + Z.of_nat (cells_size cs) <= SEGTOP_A -> rw_cells asegs m8 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m6 m8 _ _ H); [| exact WM8]. apply OFF8. unfold SEGTOP_A, STACK_WIN in *. intros; lia. }
  unfold SEGTOP_A in STAT8.
  pose proof (STAT8 _ _ LKC6 ltac:(cbn; unfold G_ERR_LOCK; lia)) as LKC8. pose proof (STAT8 _ _ LHC6 ltac:(cbn; lia)) as LHC8. pose proof (STAT8 _ _ FLC6 ltac:(cbn; lia)) as FLC8.
  pose proof (STAT8 _ _ STP6 ltac:(cbn; lia)) as STP8. pose proof (STAT8 _ _ OD6 ltac:(cbn; lia)) as OD8. pose proof (STAT8 _ _ ONCE6 ltac:(cbn; lia)) as ONCE8. pose proof (STAT8 _ _ BRET6 ltac:(cbn; lia)) as BRET8.
  eassert (FR8 : rw_cells asegs m8 (usp + -32) _) by (apply (rw_cells_agree asegs m6 m8 _ _ FR6); [apply OFF8; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM8]).
  pose proof (live_apart RT AF Σ6 m6 (lh, 104) (pk, 40) ART6 ltac:(rewrite LV6; right; left; reflexivity) ltac:(rewrite LV6, LV4; right; right; left; reflexivity)
                ltac:(intros E; injection E; lia)) as APK. cbn [fst snd] in APK.
  pose proof (live_apart RT AF Σ6 m6 (lh, 104) (B, 128) ART6 ltac:(rewrite LV6; right; left; reflexivity) ltac:(rewrite LV6; left; reflexivity)
                ltac:(intros E; injection E; lia)) as ALB. cbn [fst snd] in ALB.
  assert (MC8 : rw_cells asegs m8 pk (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m6 m8 _ _ MC6); [apply OFF8; cbn [cells_size csize Nat.add mutex_cells]; unfold STACK_WIN in *; intros; lia| exact WM8]).
  assert (ZB8 : rw_cells asegs m8 B [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (rw_cells_agree asegs m6 m8 _ _ ZB6); [apply OFF8; cbn [cells_size csize Nat.add]; unfold STACK_WIN in *; intros; lia| exact WM8]).
  assert (ENV8 : cl_env m8 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m6 m8 _ canary ENV6 MU8); cl_fp_lia).
  assert (LHR : 0 < lh < 2^64) by (unfold USTACK_TOP in LHHI; lia).
  (* [comment removed for export] *)
  pose proof (desi_w4 sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 (lh + 48)) (Z_to_bv 64 0) (Z_to_bv 64 e_lh_daw_thunk) (Z_to_bv 64 e_lh_daaw_thunk) (Z_to_bv 64 0) (Z_to_bv 64 SHB) (Z_to_bv 64 0)
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F6 fc6 m8 lo lh _ _ ra s0 s1 j8 LHC8 FLC8 LHR FR8 ST8 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI8) as W4.
  cl_lift W4 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ6 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & LHC9 & FLC9 & ST9) & Hc9'). clear Hc9.
  assert (MU9' : munch ([(G_ERR_HASH, G_ERR_HASH + 8); (G_ERR_FLAG, G_ERR_FLAG + 4)] ++ [(usp - 0, usp)]) m8 m9) by (eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ6 m8 m9 usp 0 _ ART8 ltac:(rewrite SP6, SP4; lia) ltac:(lia) MU9'
                ltac:(intros x Hx; apply client_static_intro; unfold G_ERR_HASH, G_ERR_FLAG in Hx; cbn [outside] in Hx; lia) WM9) as ART9.
  assert (OFF9 : forall P : Z -> Prop, (forall x, P x -> ~ (G_ERR_HASH <= x < G_ERR_HASH + 8) /\ ~ (G_ERR_FLAG <= x < G_ERR_FLAG + 4)) -> agree_on P m8 m9).
  { intros P HP a Ha. apply MU9. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  unfold G_ERR_HASH, G_ERR_FLAG in OFF9.
  assert (STAT9 : forall a cs, rw_cells asegs m8 a cs -> (a + Z.of_nat (cells_size cs) <= 0xb9f800 \/ (0xb9f808 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f840) \/ 0xb9f844 <= a) ->
                   rw_cells asegs m9 a cs).
  { intros a cs H H1. apply (rw_cells_agree asegs m8 m9 _ _ H); [| exact WM9]. apply OFF9. intros; lia. }
  pose proof (STAT9 _ _ LKC8 ltac:(cbn; unfold G_ERR_LOCK; lia)) as LKC9.
  pose proof (STAT9 _ _ STP8 ltac:(cbn; lia)) as STP9. pose proof (STAT9 _ _ OD8 ltac:(cbn; lia)) as OD9. pose proof (STAT9 _ _ ONCE8 ltac:(cbn; lia)) as ONCE9. pose proof (STAT9 _ _ BRET8 ltac:(cbn; lia)) as BRET9.
  pose proof (STAT9 _ _ MC8 ltac:(cbn; lia)) as MC9. pose proof (STAT9 _ _ ZB8 ltac:(cbn; lia)) as ZB9. pose proof (STAT9 _ _ SC8 ltac:(cbn; lia)) as SC9.
  assert (ENV9 : cl_env m9 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m8 m9 _ canary ENV8 MU9); unfold G_ERR_HASH, G_ERR_FLAG; cl_fp_lia).
  (* [comment removed for export] *)
  apply Hk. exists Σ6, pk, lh, B.
  split.
  - apply (ASTA_conseq RT Σ6 PMc _ _ c9 Hc9'). intros ms9 <-. exists m9. fold usp in ST9.
    split; [exists u0, u1, u2, (Z_to_bv 64 0xb9f610), (Z_to_bv 64 0), (Z_to_bv 64 e_lh_daw_thunk), (Z_to_bv 64 e_lh_daaw_thunk), (Z_to_bv 64 0), (Z_to_bv 64 SHB), (Z_to_bv 64 0), u3, u4, u5, u6, F6, fc6; reflexivity|].
    split; [exact (conj ART9 (conj MI9 ST9))|].
    split. { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & _). unfold G_ALLOW_CUST in O1. unfold G_ERR_LOCK in O2. unfold G_ERR_HASH in O3. unfold G_ERR_FLAG in O4.
             pose proof (cl_split RT AF Σ m usp 544 _ ART0 ltac:(lia) ltac:(lia) Ha) as OFFa.
             assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -32) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
             assert (Ha4 : aclient (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -32) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha'); [rewrite LV4, LV2; intros e He; right; exact He| rewrite FRS4, FRS2; intros e He; exact He| lia]).
             pose proof (newchunk_apart_gen Σ4 Σ6 m6 [(B, 128)] lh 104 usp (bv_unsigned a) ART6 LV6 ltac:(rewrite FRS6; reflexivity) SP6 ltac:(rewrite SP4; lia) ltac:(lia)
                           ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV4, LV2; intros e He; right; exact He| rewrite FRS4, FRS2; intros e He; exact He| lia])) as NLH.
             rewrite (MU9 a ltac:(cbn [outside]; unfold G_ERR_HASH, G_ERR_FLAG; repeat split; try exact I; lia)).
             rewrite (MU8 a ltac:(cbn [outside]; unfold STACK_WIN in *; repeat split; try exact I; lia)).
             rewrite (PRES6 a Ha4 ltac:(cbn [outside]; unfold G_ALLOW_CUST; split; [lia| exact I])).
             rewrite (MU5 a ltac:(cbn [outside]; unfold G_ERR_LOCK; split; [lia| exact I])).
             rewrite (PRES4 a ltac:(rewrite LV2, FRS2; exact Ha') ltac:(cbn [outside]; unfold G_ALLOW_CUST; split; [lia| exact I])).
             rewrite (PRES2 a Ha'). apply MU1. cbn [outside]. destruct OFFa; split; try exact I; lia. }
    split; [exact ENV9|]. split; [exact STP9|]. split; [exact OD9|]. split; [exact ONCE9|]. split; [exact BRET9|].
    split; [exact LKC9|]. split; [exact LHC9|]. split; [exact FLC9|]. split; [exact MC9|].
    (* [comment removed for export] *)
    split; [| split; [apply Permutation_refl| constructor; [cbn; clear - LH16; Z.div_mod_to_equations; lia| constructor; [cbn; clear - B16; Z.div_mod_to_equations; lia| constructor]]]].
    unfold lh_rep, LH_G0. cbn [g_nn g_na g_p g_pmax g_items]. change (8 * 16) with 128.
    split; [unfold lh_geo_ok, LH_KMAX; cbn [g_nn g_na g_p g_pmax g_items]; lia|].
    split; [split; [left; reflexivity| reflexivity]|]. split; [unfold LH_CEIL; lia|].
    split. { exists (Z_to_bv 64 e_lh_daw_thunk), (Z_to_bv 64 e_lh_daaw_thunk), z64, z64. unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz. cbn [g_nn g_na g_p g_pmax g_items].
             apply (cells_mid_congr m9 lh [] [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_err_cmp) ++ le8 (Z_to_bv 64 e_err_hash))] [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 e_err_cmp); C8 (Z_to_bv 64 e_err_hash)]
                      [C8 (Z_to_bv 64 e_err_hash_thunk); C8 (Z_to_bv 64 e_err_comp_thunk); C8 (Z_to_bv 64 e_lh_daw_thunk); C8 (Z_to_bv 64 e_lh_daaw_thunk);
                       C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]);
               [cbn [cells_bytes cbytes app]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn; tauto|]. cbn [app].
             apply (cells_mid_congr m9 lh [CB 24 (le8 (Z_to_bv 64 B) ++ le8 (Z_to_bv 64 e_err_cmp) ++ le8 (Z_to_bv 64 e_err_hash)); C8 (Z_to_bv 64 e_err_hash_thunk); C8 (Z_to_bv 64 e_err_comp_thunk); C8 (Z_to_bv 64 e_lh_daw_thunk); C8 (Z_to_bv 64 e_lh_daaw_thunk)]
                      [CB 48 (le4 (Z_to_bv 64 8) ++ le4 (Z_to_bv 64 16) ++ repeat (Z_to_bv 8 0) 4 ++ le4 (Z_to_bv 64 8) ++ le8 (Z_to_bv 64 512) ++ le8 (Z_to_bv 64 256) ++ repeat (Z_to_bv 8 0) 16)]
                      [C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] []);
               [closed_bytes| reflexivity| cbn; tauto|]. rewrite app_nil_r. cbn [app]. exact SC9. }
    split; [split; [right; left; reflexivity| reflexivity]|]. split; [unfold LH_CEIL; lia|].
    split; [rewrite repeat_length; reflexivity|].
    split. { intros i Hi. rewrite nth_repeat. exists (B + 8 * i). split; [reflexivity|].
             pose proof (cells_zero asegs m9 B 16 (Z.to_nat i) ZB9 ltac:(lia)) as C0. rewrite Z2Nat.id in C0 by lia. unfold wz. exact C0. }
    split; [intros i _; apply nth_repeat|].
    rewrite concat_repeat_nil'. cbn [map].
    constructor; [intros [E|[]]; apply bp_inj in E; lia| constructor; [intros []| constructor]].
  - split; [rewrite LV6, LV4, LV2; reflexivity|]. split; [rewrite FRS6, FRS4; exact FRS2|]. split; [rewrite SP6, SP4; exact SP2|].
    split; [rewrite CR6, CR4, CR2; unfold mcost; cbn; lia|]. split; [rewrite CG6, CG4; exact CG2|]. split; [lia|]. split; [exact PK16| exact PKHI].
Qed.
End DoEsi.
