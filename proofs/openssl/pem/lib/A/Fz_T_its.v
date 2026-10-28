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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_create_global_tevent_register_ossl Th_tsd Th_key Th_mutex Th_once Fz_T_once Fz_T_local Fz_T_lock Fz_T_sk Fz_T_mtl Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation zeros n := (repeat (Z_to_bv 8 0) n) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation DTOR_KEY := (0x5a9f20)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_ONCE := (0xb9f4a0)%Z (only parsing).      (* [comment removed for export] *)
Notation TEV_RET := (0xb9f4c0)%Z (only parsing).
Notation TEV_REG := (0xb9f4e0)%Z (only parsing).
Definition e_its : Z := 0x1f4838.
Definition SITE_its_mtl : Z := 0x1f4880.
Definition SITE_its_cm : Z := 0x1f489c.

(* [comment removed for export] *)
Lemma its_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_its_mtl) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) z64 a2 a3 a4 a5 a6 a7 a0 a1 a2 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_mtl) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_its) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros UT SHC ST LO0 LO HTOP MI. unfold e_its, e_mtl, g_shadow_memory_dynamic_address, SHB, SITE_its_mtl in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 9 zstep. do 8 zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption | assumption].
Qed.

(* [comment removed for export] *)
Lemma its_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo H : Z),
  0x10007fff8000 <= H -> H + 8 <= lo ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_its_cm) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 H) (Z_to_bv 64 32) (Z_to_bv 64 MTL_FILE) (Z_to_bv 64 423) a3 a4 a5 a6 a7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_CRYPTO_malloc) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_its_mtl) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_its_mtl) fc None m (seg_rom asegs)).
Proof.
  intros until H. intros HHI HLO ST LO0 LO HTOP MI. unfold SITE_its_mtl, SITE_its_cm, MTL_FILE, e_CRYPTO_malloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp []) by ut_fp_lia. assert (HWS : sh_fp []) by sh_fp_lia.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstep. do 4 zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma its_w2 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 index arg handfn : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo H N : Z) (nb : list byte) (j : list byte) (rav s0v s1v s2v s3v s4v s5v : word),
  0x10007fff8000 <= H -> H mod 8 = 0 -> H + 8 <= lo -> rw_cells asegs m H [C8 z64] -> acc asegs m H 8 ->
  0x10007fff8000 <= N -> N mod 8 = 0 -> N + 32 <= lo -> rw_cells asegs m N [CB 32 nb] -> acc asegs m N 32 -> (H + 8 <= N \/ N + 32 <= H) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' a2' : word) (m' : mem),
       ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs)
       /\ munch [(N, N + 32); (H, H + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (bv_unsigned sp)
       /\ rw_cells asegs m' N [C8 index; C8 arg; C8 handfn; C8 z64] /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)])
    (MS (mkR (Z_to_bv 64 SITE_its_cm) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 H) (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7
            index arg handfn (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_its_cm) fc None m (seg_rom asegs)).
Proof.
  intros until s5v. intros HHI HAL HLO HC ACCH NHI NAL NLO NC ACCN DISJ UT SHC FR ST LO0 LO HTOP MI. unfold SITE_its_cm, g_shadow_memory_dynamic_address, SHB in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(N, N + 32); (H, H + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  pose proof (rw_cells_bound _ _ _ _ NC) as NB. cbn [cells_size csize Nat.add] in NB.
  apply (rw_cells_split_CB asegs m N [] 32 nb [] [8; 8; 8; 8]%nat) in NC; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in NC.
  cl_eu (bv_unsigned sp) (-64) EU1.
  zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  do 3 zstep. zstep. zstep. th_if_lit. zstep.
  do 3 zstep. zstep. zstep. th_if_lit. zstep.
  do 2 zstep. zstep. zstep. th_if_lit.
  zstep.                                                      (* [comment removed for export] *)
  do 2 zstep. zstep. zstep. th_if_lit.
  do 3 zstep. zstep. zstep. th_if_lit.
  zstep. zstep. fix_lit_store. zstep. zstep.
  do 7 zstep. th_release FR (bv_unsigned sp). do 2 zstep.
  finish.
Qed.

Section CIts.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CALLOC : CRYPTO_calloc_stmt RT.
Hypothesis C_TEV : create_global_tevent_register_ossl_stmt RT.
Hypothesis GO_dtor : GOBJ DTOR_KEY 8.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].

Definition ITS_SITES : list (Z * Z) := [(SITE_its_mtl, e_its); (SITE_its_cm, e_its)] ++ MTL_SITES.
Definition ITS_CALLS : list (Z * Z) := [(SITE_its_mtl, e_mtl); (SITE_its_cm, e_CRYPTO_malloc)] ++ MTL_CALLS.

(* [comment removed for export] *)
Definition its_first_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k : Z) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x330 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_its (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) ITS_SITES ITS_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 6 <= LIVE_MAX -> 1 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 k); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] ->
  rw_cells asegs m TEV_ONCE [C4 z64] -> rw_cells asegs m TEV_RET [C4 r0] -> rw_cells asegs m TEV_REG [C8 g0] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_its m)))
    (fun c => exists (Σ' : rts RT) (N H G SK LK D : Z) (u' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (MTL_W k) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' TEV_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' TEV_REG [C8 (Z_to_bv 64 G)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells asegs m' N [C8 a0; C8 a1; C8 a2; C8 z64]
           /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
           /\ rw_cells asegs m' SK (sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (zeros 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ Forall (fun b => 0x10007fff8000 <= fst b /\ fst b mod 16 = 0 /\ fst b + snd b < USTACK_TOP) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)]).

Theorem its_first_cps : its_first_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary k u r0 g0 oldcb
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE DK4 HK SLOT UC ONC TRET TREG CBC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 816 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (HLO1 : lo <= usp - 64) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (its_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo UT SHC ST HLOS HLO1 SPH MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 64) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  pose proof (cl_env_seg _ m m1 lb canary CLE MU1 ltac:(cl_fp_lia)) as CLE1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0xbc6000 -> rw_cells asegs m1 a cs).
  { intros a cs X H1. apply (rw_cells_agree asegs m m1 _ _ X); [| exact WM1]. apply BELOW1. intros; lia. }
  pose proof (STAT1 _ _ DK4 ltac:(cbn; lia)) as DK4_1. pose proof (STAT1 _ _ SLOT ltac:(cbn; lia)) as SLOT1. pose proof (STAT1 _ _ UC ltac:(cbn; lia)) as UC1.
  pose proof (STAT1 _ _ ONC ltac:(cbn; lia)) as ONC1. pose proof (STAT1 _ _ TRET ltac:(cbn; lia)) as TRET1. pose proof (STAT1 _ _ TREG ltac:(cbn; lia)) as TREG1. pose proof (STAT1 _ _ CBC ltac:(cbn; lia)) as CBC1.
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_its e_mtl SITE_its_mtl m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG01) as UWCm1.
  (* [comment removed for export] *)
  apply (mtl_first_cps RT GOBJ AF AFP C_CZ C_CALLOC C_TEV GO_dtor TSD Σ PMc (Z_to_bv 64 SITE_its_mtl) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 (Z_to_bv 64 1) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
           a0 a1 a2 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary k u r0 g0 oldcb FDO MST eq_refl eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_its_mtl) by (unfold SITE_its_mtl; lia). exact CTX1. }
  { exact UWC1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. } { lia. } { exact Hcr. } { exact CLE1. } { exact DK4_1. } { exact HK. } { exact SLOT1. } { exact UC1. } { exact ONC1. } { exact TRET1. } { exact TREG1. } { exact CBC1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & H & G & SK & LK & D & u' & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1 & BLK1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & SLOT2 & UC2 & ONC2 & TRET2 & TREG2 & CBC2 & HC2 & GC2 & SKC2 & LKC2 & DC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_its_mtl) in Hc2' by (unfold SITE_its_mtl; lia).
  pose proof (proj1 (Forall_forall _ _) BLK1) as BLK1'.
  assert (INH : In (H, 8) (rt_live RT Σ1)) by (rewrite LV1; do 4 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 H 8 ART2 INH) as (_ & HLO & _). rewrite SP1 in HLO.
  pose proof (BLK1' (H, 8) ltac:(do 4 right; left; reflexivity)) as (HHI & H16 & HU). cbn [fst snd] in HHI, H16, HU.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 x /\ outside (MTL_W k) x) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). exact (PRES2 a X1 X2). }
  eassert (FR2 : rw_cells asegs m2 usp1 _).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia|].
    unfold MTL_W. cbn [outside]. unfold G_ALLOW_CUST, usp1, STACK_WIN, RT_STACK in *. repeat split; try exact I; lia. }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWCm1 ltac:(apply AG2; intros x Hx; cbv beta in Hx; split; [left; unfold usp1; lia | unfold MTL_W; cbn [outside]; unfold G_ALLOW_CUST, RT_STACK, USTACK_TOP in *; repeat split; try exact I; lia])) as UWCm2.
  (* [comment removed for export] *)
  pose proof (its_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 a0 a1 a2 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo H HHI ltac:(clear - HLO LOW; lia) ST2 HLOS HLO1 SPH MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  assert (FRR2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m2 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  rewrite <- CG1 in CGH, CTX.
  destruct (cl_chain_call (rt_cg RT Σ1) e_its e_CRYPTO_malloc SITE_its_cm m2 m2 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; left; reflexivity)) UWCm2 ltac:(intros a _; reflexivity) FRR2 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX2 & UWC2).
  (* [comment removed for export] *)
  apply (C_CM Σ1 PMc (Z_to_bv 64 SITE_its_cm) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 H) (Z_to_bv 64 32) (Z_to_bv 64 MTL_FILE) (Z_to_bv 64 423) b3 b4 b5 b6 b7
           a0 a1 a2 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 32 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl ltac:(lia) ART2 MI2).
  { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [rewrite SP1; exact LOW|]. split; [unfold usp1, RT_STACK in *; lia|]. split; [unfold usp1, USTACK_TOP in *; lia|].
    unfold usp1. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, RT_STACK in *. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_its_cm) by (unfold SITE_its_cm; lia). exact CTX2. }
  { exact UWC2. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { rewrite LV1. cbn [length app]. lia. } { rewrite CR1. change (mcost 32) with 0. lia. } { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & N & Hc4 & LV2 & FRS2 & SP2 & CR2 & N0 & N16 & NU & CG2). change (mcost 32) with 0 in CR2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & WRN & ACCN) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_its_cm) in Hc4' by (unfold SITE_its_cm; lia).
  assert (INN : In (N, 32) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (INH2 : In (H, 8) (rt_live RT Σ2)) by (rewrite LV2; right; exact INH).
  pose proof (af_live_range RT AF Σ2 m4 N 32 ART4 INN) as (_ & NLO & _). rewrite SP2, SP1 in NLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 N 32 ART4 INN ltac:(lia)) as NHI.
  pose proof (af_live_disj RT AF Σ2 m4 N 32 H 8 [] (rt_live RT Σ1) ART4 LV2 INH) as DJ_NH.
  destruct (wr_at_bytes m4 N 32 WRN ltac:(lia)) as (nb & NB & NBL).
  assert (NC4 : rw_cells asegs m4 N [CB 32 nb]) by (split; [split; [cbn; split; [lia | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact NB] | exact WRN]).
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ x <> G_ALLOW_CUST) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES4; [exact X1|]. unfold G_ALLOW_CUST in *. cbn [outside]. split; [lia | exact I]. }
  eassert (FR4 : rw_cells asegs m4 usp1 _).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold usp1, USTACK_TOP in *; lia | unfold G_ALLOW_CUST, usp1, STACK_WIN, RT_STACK in *; lia]. }
  assert (HC4 : rw_cells asegs m4 H [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m2 m4 _ _ HC2); [| exact WM4]. apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply (acl_live _ _ _ H 8); [exact INH | lia]|]. unfold G_ALLOW_CUST. lia. }
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ2 m4 H 8 ART4 INH2)) as ACCH4.
  (* [comment removed for export] *)
  pose proof (its_w2 sp gp (Z_to_bv 64 TP_A) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 a0 a1 a2 F4 fc4 m4 lo H N nb j ra s0 s1 s2 s3 s4 s5
                HHI ltac:(clear - H16; Z.div_mod_to_equations; lia) ltac:(clear - HLO LOW; lia) HC4 ACCH4 NHI ltac:(clear - N16; Z.div_mod_to_equations; lia) ltac:(clear - NLO LOW; lia) NC4 ACCN ltac:(clear - DJ_NH; lia)
                UT4 SHC4 FR4 ST4 HLOS HLO1 SPH MI4) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (e1 & e2 & m5 & -> & MU5 & WM5 & MI5 & ST5 & NC5 & HC5) & Hc5'). clear Hc5. fold usp in ST5.
  assert (ART5 : ART RT Σ2 m5).
  { apply (af_frame RT AF Σ2 m4 m5 usp1 ART4 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. repeat split; try exact I; intros Hin; apply Hx; [apply (acl_live _ _ _ N 32); [exact INN | lia] | apply (acl_live _ _ _ H 8); [exact INH2 | lia]]. }
  pose proof (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(cl_fp_lia)) as CLE5.
  assert (OFF5 : forall P : Z -> Prop, (forall x, P x -> ~ (N <= x < N + 32) /\ ~ (H <= x < H + 8)) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. destruct (HP _ Ha) as (X1 & X2). repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  apply Hk. exists Σ2, N, H, G, SK, LK, D, u'.
  split.
  2:{ split; [rewrite LV2, LV1; reflexivity|]. split; [rewrite FRS2; exact FRS1|]. split; [rewrite SP2; exact SP1|]. split; [rewrite CR2, CR1; lia|]. split; [rewrite CG2; exact CG1|].
      apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [assumption | lia] | exact BLK1]. }
  apply (ASTA_conseq RT Σ2 PMc _ _ c5 Hc5'). intros ms5 <-. exists m5.
  split; [exists v0, v1, v2, e1, e2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F4, fc4; reflexivity|].
  split; [split; [exact ART5|]; split; [exact MI5|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 WM5))) | exact ST5]|].
  assert (ACL1 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x).
  { intros x Hx. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV1; do 5 right; exact He | rewrite FRS1; intros e He; exact He | unfold usp1; lia]. }
  assert (NH : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (H <= x < H + 8)).
  { intros x Hx. exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] H 8 usp x ART2 LV1 ltac:(do 4 right; left; reflexivity) FRS1 SP1 ltac:(lia) ltac:(lia) Hx). }
  assert (NN : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (N <= x < N + 32)).
  { intros x Hx. apply (newchunk_apart RT AF Σ1 Σ2 m4 N 32 usp _ ART4 LV2 FRS2 SP2 ltac:(rewrite SP1; lia) ltac:(lia)).
    apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; rewrite LV1; do 5 right; exact He | rewrite FRS1; intros e He; exact He | lia]. }
  split.
  { intros a Ha Ho. pose proof (cl_split RT AF Σ m usp 64 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (MU5 a ltac:(cbn [outside]; pose proof (NH _ Ha); pose proof (NN _ Ha); repeat split; try exact I; lia)).
    assert (O1 : bv_unsigned a <> G_ALLOW_CUST) by (unfold MTL_W in Ho; cbn [outside] in Ho; lia).
    rewrite (PRES4 a (ACL1 _ Ha) ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He | intros e He; exact He | unfold usp1; lia]) Ho).
    apply PR1; [exact Ha | exact I]. }
  split; [exact CLE5|].
  assert (KEEP : forall a cs, rw_cells asegs m2 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x /\ x <> G_ALLOW_CUST /\ ~ (H <= x < H + 8)) ->
            rw_cells asegs m5 a cs).
  { intros a cs X HX. apply (rw_cells_agree asegs m2 m5 _ _ X); [| exact (wmono_trans asegs _ _ _ WM4 WM5)]. intros x Hx. cbv beta in Hx. destruct (HX _ Hx) as (X1 & X2 & X3).
    pose proof (newchunk_apart RT AF Σ1 Σ2 m4 N 32 usp1 _ ART4 LV2 FRS2 SP2 ltac:(rewrite SP1; unfold usp1; lia) ltac:(lia) X1) as X4.
    rewrite (OFF5 (fun y => y = bv_unsigned x) ltac:(intros y ->; split; [exact X4 | exact X3]) x eq_refl).
    exact (AG4 (fun y => y = bv_unsigned x) ltac:(intros y ->; exact (conj X1 X2)) x eq_refl). }
  assert (STC : forall a cs, rw_cells asegs m2 a cs ->
            (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98 /\ (a + Z.of_nat (cells_size cs) <= 0xb9f7c0 \/ 0xb9f7c1 <= a)) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) ->
            rw_cells asegs m5 a cs).
  { intros a cs X H1. apply (KEEP _ _ X). intros x Hx. split; [right; left; apply client_static_intro; lia|]. unfold G_ALLOW_CUST. clear - Hx H1 HHI. split; lia. }
  split; [exact (STC _ _ SLOT2 ltac:(cbn; lia))|]. split; [exact (STC _ _ UC2 ltac:(cbn; lia))|]. split; [exact (STC _ _ ONC2 ltac:(cbn; lia))|].
  split; [exact (STC _ _ TRET2 ltac:(cbn; lia))|]. split; [exact (STC _ _ TREG2 ltac:(cbn; lia))|]. split; [exact (STC _ _ CBC2 ltac:(cbn; lia))|].
  split; [exact HC5|]. split; [exact NC5|].
  assert (BLK : forall a cs p n, rw_cells asegs m2 a cs -> In (p, n) [(D, 32); (LK, 40); (SK, 56); (G, 16)] -> p <= a -> a + Z.of_nat (cells_size cs) <= p + n -> rw_cells asegs m5 a cs).
  { intros a cs p n X Hin H1 H2. assert (INP : In (p, n) (rt_live RT Σ1)) by (rewrite LV1; cbn [In app] in Hin |- *; tauto).
    pose proof (BLK1' (p, n) ltac:(cbn [In] in Hin |- *; tauto)) as (PHI & _ & _). cbn [fst] in PHI.
    pose proof (af_live_disj RT AF Σ1 m2 H 8 p n [(D, 32); (LK, 40); (SK, 56); (G, 16)] (rt_live RT Σ) ART2 LV1 ltac:(apply in_or_app; left; exact Hin)) as DJ.
    apply (KEEP _ _ X). intros x Hx. split; [apply (acl_live _ _ _ p n); [exact INP | lia]|]. unfold G_ALLOW_CUST. clear - Hx H1 H2 PHI DJ. split; lia. }
  split; [exact (BLK _ _ G 16 GC2 ltac:(do 3 right; left; reflexivity) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (BLK _ _ SK 56 SKC2 ltac:(do 2 right; left; reflexivity) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (BLK _ _ LK 40 LKC2 ltac:(right; left; reflexivity) ltac:(lia) ltac:(cbn; lia))|].
  exact (BLK _ _ D 32 DC2 ltac:(left; reflexivity) ltac:(lia) ltac:(cbn; lia)).
Qed.
End CIts.
