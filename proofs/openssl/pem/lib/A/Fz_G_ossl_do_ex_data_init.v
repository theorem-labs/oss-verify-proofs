(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_G_ossl_lib_ctx_get_ex_data_global Fz_M_malloc Fz_M_zalloc Th_mutex Fz_M_locknew Fz_env.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tslia ::= wp_tslia.
(* [comment removed for export] *)
Local Ltac wp_out Ho SPL unf := cbn [app outside]; unf;
  repeat (split; [ first [ wp_na
                         | (clear - Ho SPL; first [ tauto | lia ])
                         | match goal with H : wp_box (aclient _ _ _ _) |- _ => unfold wp_box in H; lia end
                         | (repeat match goal with H : wp_box _ |- _ => unfold wp_box in H end; lia) ] |]); exact I.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Definition e_ossl_do_ex_data_init : Z := 0x1f809c.
Definition SITE_ossl_do_ex_data_init_1 : Z := 0x1f80c4.     (* [comment removed for export] *)
Definition SITE_ossl_do_ex_data_init_2 : Z := 0x1f80d0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_do_ex_data_init_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2064580) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 12187008) (Z_to_bv 64 6736696) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2062880) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187016 [C8 g2]
    /\ ro_cells asegs m' 2148974257 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma ossl_do_ex_data_init_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xb9f588 [C8 g2] ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974257 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (ossl_do_ex_data_init_s0_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 12187008) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f809c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 G2 GACCbd1c40 GPALbd1c40 GSH80172389 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep.
  do 4 zstore.
  do 5 zstep.
  unfold ossl_do_ex_data_init_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_do_ex_data_init_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g2 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2064592) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 12187016) (Z_to_bv 64 12187016) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2055740) fc1 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187016 [C8 g2]
    /\ ro_cells asegs m' 2148974257 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma ossl_do_ex_data_init_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g2 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> lo <= (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187016 [C8 g2] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974257 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (ossl_do_ex_data_init_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g2 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 12187016) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x1f80c4) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G2 G1 UT GACCbd1c40 GPALbd1c40 GSH80172389 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  do 2 zstep.
  unfold ossl_do_ex_data_init_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_do_ex_data_init_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v2 : Z) (g2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_2 u1_2 u2_2 s0 s1 (Z_to_bv 64 (Z.b2z (0 <? v2))) (Z_to_bv 64 0) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (ret_pc ra) fc2 None m' (seg_rom asegs)
    /\ munch [(0xb9f588, 0xb9f590); (bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187016 [C8 (Z_to_bv 64 v2)]
    /\ ro_cells asegs m' 2148974257 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_do_ex_data_init_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v2 : Z) (g2 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> lo <= (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187016 [C8 g2] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974257 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (ossl_do_ex_data_init_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v2 g2 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 12187016) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x1f80d0) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G2 G1 Hv2 UT GACCbd1c40 GPALbd1c40 GSH80172389 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f588, 0xb9f590); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  do 7 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_do_ex_data_init_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_do_ex_data_init_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_bd1c40 : GOBJ 12187008 328.          (* [comment removed for export] *)
Hypothesis C_ossl_lib_ctx_get_ex_data_global : ossl_lib_ctx_get_ex_data_global_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.

Definition ossl_do_ex_data_init_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (g2 : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 12187008 -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x220 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_do_ex_data_init (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_do_ex_data_init_1, e_ossl_do_ex_data_init); (SITE_ossl_do_ex_data_init_2, e_ossl_do_ex_data_init); (SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_ossl_do_ex_data_init_1, e_ossl_lib_ctx_get_ex_data_global); (SITE_ossl_do_ex_data_init_2, e_lock_new); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m 0xb9f588 [C8 g2] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_do_ex_data_init m)))
    (fun c => exists (Σ' : rts RT) (q1 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.b2z (0 <? q1))) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (0xb9f588, 0xb9f590)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 40
           /\ acc asegs m' q1 40
           /\ rw_cells asegs m' 12187016 [C8 (Z_to_bv 64 q1)]
           /\ rw_cells asegs m' q1 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q1, 40) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 40 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_do_ex_data_init_cps : ossl_do_ex_data_init_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary g2
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV XS0.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 < usp - 32 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-32) EU1.
  assert (WHLO : lo <= usp - 32) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (afp_acc_global RT GOBJ AFP Σ m 12187008 328 12187008 328 ART0 GO_bd1c40 ltac:(lia) ltac:(lia)) as GACCbd1c40_1.
  assert (GSH80172389_1 : ro_cells asegs m 2148974257 [C1 (Z_to_bv 8 0)]) by exact (afp_gsh_byte RT GOBJ AFP Σ m 12187008 328 12187016 ART0 GO_bd1c40 ltac:(lia) ltac:(lia) ltac:(reflexivity)).
  (* [comment removed for export] *)
  pose proof (ossl_do_ex_data_init_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 F fc m lo
                ST WHLO WHIMG WHTOP UT SHC XS0 GACCbd1c40_1 ltac:(reflexivity) GSH80172389_1 MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & H1_2 & H1_3 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1', H1_0.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  (* [comment removed for export] *)
  apply (C_ossl_lib_ctx_get_ex_data_global Σ PMc (Z_to_bv 64 SITE_ossl_do_ex_data_init_1) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 12187008) (Z_to_bv 64 6736696) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & F1 & fc1 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_do_ex_data_init_1) in Hc2' by (unfold SITE_ossl_do_ex_data_init_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -32 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; exact (AGc2 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AGu2) as UWF2.
  cl_keep H1_0 AGc2 WM2 KF1.
  assert (KF2 : rw_cells asegs m2 12187016 [C8 g2]) by (apply (wg_keep_static _ _ _ _ m1 m2 _ _ H1_1 PRES2 WM2); intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply client_static_intro; lia | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (ENV2 : cl_env m2 lb canary).
  { assert (HFP : cl_fp []) by cl_fp_lia. apply (cl_env_agree m1 m2 _ _ ENV1). intros a Ha. apply PRES2; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (afp_acc_global RT GOBJ AFP Σ m2 12187008 328 12187008 328 ART2 GO_bd1c40 ltac:(lia) ltac:(lia)) as GACCbd1c40_3.
  assert (GSH80172389_3 : ro_cells asegs m2 2148974257 [C1 (Z_to_bv 8 0)]) by exact (afp_gsh_byte RT GOBJ AFP Σ m2 12187008 328 12187016 ART2 GO_bd1c40 ltac:(lia) ltac:(lia) ltac:(reflexivity)).
  (* [comment removed for export] *)
  pose proof (ossl_do_ex_data_init_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_do_ex_data_init_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g2 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 KF2 SHC2 UT2 GACCbd1c40_3 ltac:(reflexivity) GSH80172389_3 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & H3_2 & H3_3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_0.
  assert (ART3 : ART RT Σ m3).
  { apply (wg_seg_ART RT AF Σ m2 m3 usp 32 [] ART2 ltac:(lia) ltac:(lia) MU3); [|exact WM3].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_do_ex_data_init e_lock_new SITE_ossl_do_ex_data_init_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH (SITE_ossl_do_ex_data_init_2, e_ossl_do_ex_data_init) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_do_ex_data_init_2, e_lock_new) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -32 + Z.of_nat (cells_size [C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -32) [C8 s2; C8 s1] [C8 s0; C8 ra] H3_0))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_lock_new Σ PMc (Z_to_bv 64 SITE_ossl_do_ex_data_init_2) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp (Z_to_bv 64 12187016) (Z_to_bv 64 12187016) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_do_ex_data_init_2) by (unfold SITE_ossl_do_ex_data_init_2; lia). exact CTXc3. }
  { exact UWCc3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_MX & G2_ACC) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_do_ex_data_init_2) in Hc4' by (unfold SITE_ossl_do_ex_data_init_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -32 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  cl_keep H3_0 AGc4 WM4 KF5.
  assert (KF6 : rw_cells asegs m4 12187016 [C8 g2]) by (apply (wg_keep_static _ _ _ _ m3 m4 _ _ H3_1 PRES4 WM4); intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply client_static_intro; lia | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof SP4 as SPc4. pose proof CG4 as CGc4.
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (rewrite LV4; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 1) by lia. wp_box1 CR4.
  assert (Hfr4 : (length (rt_frames RT Σ2) < FRAMES_MAX)%nat) by (rewrite FRS4; exact Hfr).
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_do_ex_data_init (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v2_4 : In (v2, 40) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 40 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v2 : v2 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (afp_acc_global RT GOBJ AFP Σ2 m4 12187008 328 12187008 328 ART4 GO_bd1c40 ltac:(lia) ltac:(lia)) as GACCbd1c40_5.
  assert (GSH80172389_5 : ro_cells asegs m4 2148974257 [C1 (Z_to_bv 8 0)]) by exact (afp_gsh_byte RT GOBJ AFP Σ2 m4 12187008 328 12187016 ART4 GO_bd1c40 ltac:(lia) ltac:(lia) ltac:(reflexivity)).
  (* [comment removed for export] *)
  pose proof (ossl_do_ex_data_init_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_do_ex_data_init_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v2 g2 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF5 KF6 SHC4 PR64_v2 UT4 GACCbd1c40_5 ltac:(reflexivity) GSH80172389_5 MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  apply Hk. exists Σ2, v2.
  split; [| split; [rewrite LV4; reflexivity|]; split; [rewrite FRS4; reflexivity|]; split; [rewrite SP4; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; rewrite CG4; reflexivity].
  apply (ASTA_conseq RT Σ2 PMc _ _ c5 Hc5). intros ms5 (m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & H5_2 & ST5). fold usp in MU5, ST5.
  exists m5.
  split; [exists u0_2, u1_2, u2_2, (Z_to_bv 64 0), b2_2, b3_2, b4_2, b5_2, b6_2, b7_2, u3_2, u4_2, u5_2, u6_2, F2, fc2; reflexivity|].
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 32 [(0xb9f588, 0xb9f590)] ART4 ltac:(rewrite SPc4; lia) ltac:(lia) MU5); [|exact WM5].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [left; apply client_static_intro; lia | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART5|]; split; [exact MI5|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 WM5)))) | exact ST5]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV4; do 1 right; exact He | rewrite FRS4; intros e He; exact He | lia]).
    assert (NA_v2 : ~ (v2 <= bv_unsigned a < v2 + 40)) by exact (wg_newchunk_apart RT AF Σ Σ2 m4 [(v2, 40)] v2 40 usp _ ART4 LV4 ltac:(left; reflexivity) FRS4 SP4 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha).
    wp_box1 NA_v2.
    wp_box1 Ha1.
    pose proof (cl_split RT AF Σ m usp 32 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
    rewrite (MU5 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES4 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU3 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES2 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    reflexivity. }
  pose proof (af_acc_live RT AF Σ2 m5 v2 40 ART5 INP_v2_4) as (WRE_v2 & ACCE_v2).
  split; [exact (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(cl_fp_lia))|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  split; [exact H5_0|].
  apply (wg_keep_seg _ m4 m5 _ _ G2_MX MU5 WM5); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I.
Qed.
End ossl_do_ex_data_init_cps.
