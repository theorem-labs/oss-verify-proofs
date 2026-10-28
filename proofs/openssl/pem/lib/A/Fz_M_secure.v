(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_free Fz_M_cleanse Fz_M_clear_free.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_CRYPTO_secure_malloc : Z := 0x2019a4.
Definition e_CRYPTO_secure_free : Z := 0x201f98.
Definition e_CRYPTO_secure_clear_free : Z := 0x202364.
Definition SITE_scf_cleanse : Z := 0x202420.       (* [comment removed for export] *)
Definition SEC_INIT : Z := 0xb9f860.                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_off (m : mem) : Prop := rw_cells asegs m SEC_INIT [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition sm_post (ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sm_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  lo <= bv_unsigned sp - 160 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  sec_off m -> mem_inv asegs m ->
  evt asegs (sm_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_secure_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros HLO HLOS SPH ST UT SEC MI.
  unfold e_CRYPTO_secure_malloc, sec_off, SEC_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 160, SP)]) by sh_fp_lia.
  th_frame 160%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 13 zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep.
  do 13 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sm_post, e_CRYPTO_malloc. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition e_CRYPTO_secure_allocated : Z := 0x202080.
Lemma sec_allocated_off_proof : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  sec_off m -> stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 -> img_untouched m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem),
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom asegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ sec_off m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 e_CRYPTO_secure_allocated) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros SEC ST HLOS HLO SPH UT MI. unfold e_CRYPTO_secure_allocated, sec_off, SEC_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 16, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 16, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 16, SP)]) by sh_fp_lia.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep. zstep. zstep. zstep. th_if_lit. zstep. zstep.
  do 2 zstep. th_release FR SP. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition sf_post (ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ a0' = a0
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma sf_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo p : Z),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  sec_off m -> 0 < p < 2^64 -> mem_inv asegs m ->
  evt asegs (sf_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_secure_free) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros HLO HLOS SPH ST UT SEC HP MI.
  unfold e_CRYPTO_secure_free, sec_off, SEC_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 5 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  do 3 zstep. zstep. th_if_lit.                                                                      (* [comment removed for export] *)
  zstep. do 5 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold sf_post, e_CRYPTO_free. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition scf_s0_post (sp gp tp t0 t1 t2 a1 a4 a5 a6 a7 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' a2 a3 : word) (p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_scf_cleanse) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 p) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                 a3 a2 s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_cleanse) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma scf_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo p : Z),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  sec_off m -> 0 < p < 2^64 -> mem_inv asegs m ->
  evt asegs (scf_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 a1 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' a2 a3 p lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_CRYPTO_secure_clear_free) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros HLO HLOS SPH ST UT SEC HP MI.
  unfold e_CRYPTO_secure_clear_free, sec_off, SEC_INIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 64, SP)]) by sh_fp_lia.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 5 zstep. zstep.
  zstep. if_cases Ka; zify_cond Ka; try (exfalso; rewrite ?unsigned_lit in Ka by lia; lia). try clear Ka.
  do 5 zstep. zstep. th_if_lit.                                                                      (* [comment removed for export] *)
  zstep. zstep.                                                                           (* [comment removed for export] *)
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold scf_s0_post, SITE_scf_cleanse, e_OPENSSL_cleanse. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR | assumption].
Qed.

(* [comment removed for export] *)
Definition scf_s1_post (ra0 sp gp tp t0 t1 t2 s0' s1' s2' s3' a2 a3 x3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 p) a2 a3 x3 a4 a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma scf_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' j4 x0 x1 x2 x3 x4 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo p : Z),
  lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -48) -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j4; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] -> 0 <= p < 2^64 -> mem_inv asegs m ->
  evt asegs (scf_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' s2' s3' a2 a3 x3 a4 a5 a6 a7 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 p) x0 x1 x2 x3 a4 a5 a6 a7 a3 a2 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_scf_cleanse) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros HLO HLOS SPH ST UT FR HP MI.
  unfold SITE_scf_cleanse in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  zstep. zstep. zstep.
  do 5 zstep. zstep. th_release FR SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold scf_s1_post, e_CRYPTO_free. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

Lemma sec_init_static : client_static SEC_INIT.
Proof.
  unfold SEC_INIT. split; [exists 0xb9f190, 0xbc57d0; split; [unfold CLIENT_STATIC; cbn [In]; tauto | lia]|].
  intros (lo & hi & Hin & H). unfold RT_STATIC in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E | Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma sec_off_agree : forall (m m' : mem), sec_off m -> (forall a : word, bv_unsigned a = SEC_INIT -> m' a = m a) -> sec_off m'.
Proof.
  intros m m' H AG. unfold sec_off in *. apply (rw_cells_agree_nw asegs m m' _ _ H). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
  apply AG. lia.
Qed.

Section CSec.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_FR : crypto_free_env_stmt RT.
Hypothesis C_CL : openssl_cleanse_env_stmt RT.

(* [comment removed for export] *)
Definition crypto_secure_malloc_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba3ef0 -> 1 <= n <= 0x8000000 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_secure_malloc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_CRYPTO_malloc) (cg_call (rt_cg RT Σ)) -> cg_has (rt_cg RT Σ) [(SITE_cm_malloc, e_CRYPTO_malloc)] [(SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_secure_malloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m' /\ wr_at asegs m' p n /\ acc asegs m' p n) c
       /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem crypto_secure_malloc_cps : crypto_secure_malloc_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo outer lb canary
    FDO MST -> -> Hn ART0 MI0 CALL HSTK CTX UWC TL CGH Hlen Hcr CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 160 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 160) by (clear - LOR; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (sm_walk ra sp gp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HLO1 HLOS SPH ST UT SEC MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 160 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_CM Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 n lo outer lb canary
           FDO MST eq_refl eq_refl Hn ART1 MI1 CO1 HSTK (conj TL (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) CGH Hlen Hcr CLE1).
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ' & p & Hc2 & REST). apply Hk. exists Σ', p. split; [| exact REST].
  eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & CLE2 & WR & ACC). exists m2.
  split; [exact RS|]. split; [exact (conj ART2 (conj MI2 (conj (wmono_trans asegs _ _ _ WM1 WM2) ST2)))|].
  assert (AG02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] (bv_unsigned x) -> m2 x = m x).
  { intros x Hx Ho. rewrite (PRES x Hx Ho). apply PR1; [exact Hx | exact I]. }
  split; [exact AG02|]. split; [exact CLE2|]. split; [| exact (conj WR ACC)].
  apply (sec_off_agree m m2 SEC). intros a Ha. apply AG02; [right; left; rewrite Ha; exact sec_init_static|].
  cbn [outside]. rewrite Ha. unfold SEC_INIT, G_ALLOW_CUST. split; [lia | exact I].
Qed.

(* [comment removed for export] *)
Definition sec_free_post (Σ : rts RT) PMc (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (lb : byte) (canary : word) (p : Z)
    : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m'
           /\ cl_env m' lb canary /\ sec_off m') c
       /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ.

(* [comment removed for export] *)
Definition crypto_secure_free_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xba3ef0 -> In (p, n) (rt_live RT Σ) -> 1 <= n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_secure_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_secure_free m)))
    (sec_free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary p).

Theorem crypto_secure_free_cps : crypto_secure_free_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo outer lb canary
    FDO MST -> -> Hin Hn1 ART0 MI0 CALL CTX UWC TL1 TL2 CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - LOR; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (P0 & PLO & _).
  pose proof (sf_walk ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p HLO1 HLOS SPH ST UT SEC
                ltac:(clear - P0 PLO SP0R Hn1; unfold USTACK_TOP, STACK_WIN in *; lia) MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a0' & m1 & -> & _ & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  assert (CO1 : call_ok RT Σ m1 sp lo) by exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))).
  apply (C_FR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 p n lo outer lb canary FDO MST eq_refl eq_refl Hin ART1 MI1 CO1 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m1 sp s0 UWC AG1) TL2 CLE1).
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ' & v & Hc2 & LV & FRS & SP0 & CR & CG).
  apply Hk. unfold sec_free_post. exists Σ', v. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR CG))))].
  eapply ASTA_conseq; [exact Hc2|]. cbv beta. intros ms (m2 & RS & RAF & PRES & CLE2). exists m2.
  split; [exact RS|]. split; [exact RAF|].
  assert (AG02 : forall x : word, aclient (rt_live RT Σ') (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m x).
  { intros x Hx. rewrite (PRES x Hx). apply PR1; [| exact I]. apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV; intros e He; exact (live_remove_sub _ _ _ He) | auto | clear; lia]. }
  split; [exact AG02|]. split; [exact CLE2|].
  apply (sec_off_agree m m2 SEC). intros a Ha. apply AG02. right; left. rewrite Ha. exact sec_init_static.
Qed.

(* [comment removed for export] *)
Definition crypto_secure_clear_free_env_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p n len lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 len -> tp = Z_to_bv 64 0xba3ef0 ->
  In (p, n) (rt_live RT Σ) -> 0 <= len <= n -> 1 <= n -> len < 2 ^ 40 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_CRYPTO_secure_clear_free (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  In (bv_unsigned ra, e_CRYPTO_free) (cg_call (rt_cg RT Σ)) -> In (bv_unsigned ra, e_free) (cg_call (rt_cg RT Σ)) ->
  cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_CRYPTO_secure_clear_free m)))
    (sec_free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m lb canary p).

Theorem crypto_secure_clear_free_cps : crypto_secure_clear_free_env_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n len lo outer lb canary
    FDO MST -> -> -> Hin Hlen Hn1 Hl40 ART0 MI0 CALL HSTK CTX UWC TL1 TL2 CLE SEC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (P0 & PLO & PIMG).
  (* [comment removed for export] *)
  pose proof (scf_s0_walk ra sp gp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p HLO1 HLOS SPH ST UT SEC
                ltac:(clear - P0 PLO SP0R Hn1; unfold USTACK_TOP, STACK_WIN in *; lia) MI0) as W0.
  fold usp in W0. fold usp1 in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (SEC1 : sec_off m1) by (apply (sec_off_agree m m1 SEC); intros a Ha; apply MU1; cbn [outside]; rewrite Ha; unfold SEC_INIT; split; [clear - HLO1 HLOS; lia | exact I]).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  assert (OFF : forall x, cl_cell x -> ~ (p <= x < p + len)).
  { intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)). unfold SEGTOP_A in *. lia. }
  (* [comment removed for export] *)
  apply (C_CL Σ PMc (Z_to_bv 64 SITE_scf_cleanse) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
           a3 a2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 p len lo lb canary FDO MST eq_refl eq_refl eq_refl
           ltac:(lia) ltac:(unfold USTACK_TOP, STACK_WIN in *; lia) ltac:(lia)
           (live_checked_dst RT AF Σ m1 _ p n p len ART1 Hin ltac:(lia) ltac:(lia) ltac:(lia)) OFF ART1 MI1 CO1 CLE1).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ZER2 & CLE2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_scf_cleanse) in Hc2' by (unfold SITE_scf_cleanse; lia).
  assert (AG12 : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m2 x = m1 x) by (intros x Hx; apply PRES2; [left; exact Hx | unfold usp1 in Hx; clear - Hx PLO LOW HLO1 Hlen; lia]).
  assert (FR2 : rw_cells asegs m2 usp1 [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add length] in Hx. apply AG12. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (SEC2 : sec_off m2).
  { apply (sec_off_agree m1 m2 SEC1). intros a Ha. apply PRES2; [right; left; rewrite Ha; exact sec_init_static | rewrite Ha; unfold SEC_INIT; clear - PIMG P0 Hlen; unfold SEGTOP_A in *; lia]. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (scf_s1_walk ra (Z_to_bv 64 SITE_scf_cleanse) sp gp u0 u1 u2 s0 s1 s2 s3 j (Z_to_bv 64 p) b1 b2 b3 s4 a2 a3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                F2 fc2 m2 lo p ltac:(clear - HLO1; lia) HLOS SPH ST2 UT2 FR2 ltac:(clear - P0 PLO SP0R Hn1; unfold USTACK_TOP, STACK_WIN in *; lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ST3) & Hc3'). clear Hc3. fold usp in ST3.
  assert (E3 : forall x : word, m3 x = m2 x) by (intros x; apply MU3; exact I).
  assert (ART3 : ART RT Σ m3) by (apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(unfold usp1; clear - NUM; lia)); [intros x _; apply E3 | exact WM3]).
  assert (CO3 : call_ok RT Σ m3 sp lo) by exact (conj ST3 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros a Ha. cbv beta in Ha. rewrite E3, (AG12 a ltac:(unfold usp1; clear - Ha; lia)). exact (AG1 a Ha). }
  pose proof (cl_env_agree m2 m3 lb canary CLE2 ltac:(intros a _; apply E3)) as CLE3.
  (* [comment removed for export] *)
  apply (C_FR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 s0 s1 (Z_to_bv 64 p) a2 a3 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m3 p n lo outer lb canary FDO MST eq_refl eq_refl Hin ART3 MI3 CO3 (conj TL1 (proj2 CTX)) (uw_chain_agree outer m m3 sp s0 UWC AG03) TL2 CLE3).
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ' & v & Hc4 & LV & FRS & SP0 & CR & CG).
  apply Hk. unfold sec_free_post. exists Σ', v. split; [| exact (conj LV (conj FRS (conj SP0 (conj CR CG))))].
  eapply ASTA_conseq; [exact Hc4|]. cbv beta. intros ms (m4 & RS & RAF & PRES & CLE4). exists m4.
  split; [exact RS|]. split; [exact RAF|].
  assert (AG04 : forall x : word, aclient (rt_live RT Σ') (rt_frames RT Σ) usp (bv_unsigned x) -> m4 x = m x).
  { intros a Ha. rewrite (PRES a Ha). rewrite E3.
    assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a))
      by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV; intros e He; exact (live_remove_sub _ _ _ He) | auto | lia]).
    rewrite LV in Ha. pose proof (removed_apart RT AF Σ m p n usp _ ART0 Hin ltac:(lia) Ha) as NP.
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha0); [auto | auto | unfold usp1; clear; lia]) ltac:(clear - NP Hlen; lia)).
    exact (PR1 a Ha0 I). }
  split; [exact AG04|]. split; [exact CLE4|].
  apply (sec_off_agree m m4 SEC). intros a Ha. apply AG04. right; left. rewrite Ha. exact sec_init_static.
Qed.
End CSec.
