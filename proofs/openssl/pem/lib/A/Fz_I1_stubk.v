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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_T_once Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw Fz_I1_load Fz_I1_errload Fz_I1_const Fz_I1_getitem Fz_I1_reason.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition stub_w0_spec (E CODE RET1 : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists m' : mem,
       ms = MS (mkR (Z_to_bv 64 RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 CODE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_reason) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\ stk asegs m' lo (bv_unsigned sp + -16))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 E) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition stub_w1_spec (RET1 RET2 T : Z) : Prop :=
  forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo v : Z),
  0 <= v < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = (if v =? 0
       then MS (mkR (Z_to_bv 64 RET2) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_err_const) fc None m (seg_rom asegs)
       else MS (mkR (Z_to_bv 64 RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 RET2) fc None m (seg_rom asegs)))
    (MS (mkR (Z_to_bv 64 RET1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RET1) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition stub_w2_spec (RET2 : Z) : Prop :=
  forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (rav s0v : word),
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 RET2) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Ltac stub_w0_tac sp m ST :=
  let RSP := fresh "RSP" in pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  let MU := fresh "MU" in let WM := fresh "WM" in
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU; pose proof (wmono_refl asegs m) as WM;
  let HWU := fresh "HWU" in let HWS := fresh "HWS" in
  assert (HWU : ut_fp [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by ut_fp_lia; assert (HWS : sh_fp [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by sh_fp_lia;
  th_frame 16%nat [8; 8]%nat ST;
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 2092916) _ _ _ _) => fail | |- _ => zstep end);
  apply evt_done; unfold e_reason; eexists;
  split; [cbv delta [mkR]; reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [eassumption| assumption].
Ltac stub_w1_tac sp m v :=
  let RSP := fresh "RSP" in pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  let MU := fresh "MU" in let WM := fresh "WM" in
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM;
  let HWU := fresh "HWU" in let HWS := fresh "HWS" in
  assert (HWU : ut_fp []) by ut_fp_lia; assert (HWS : sh_fp []) by sh_fp_lia;
  zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [ rewrite ?unsigned_lit in K by lia; rewrite (proj2 (Z.eqb_neq v 0) K); apply evt_done; cbv delta [mkR]; reflexivity
  | rewrite ?unsigned_lit in K by lia; rewrite (proj2 (Z.eqb_eq v 0) K); do 3 zstep; apply evt_done; unfold e_err_const; cbv delta [mkR]; reflexivity ].
Ltac stub_w2_tac sp m FR ST :=
  let RSP := fresh "RSP" in pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  let MU := fresh "MU" in let WM := fresh "WM" in
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM;
  let HWU := fresh "HWU" in let HWS := fresh "HWS" in
  assert (HWU : ut_fp []) by ut_fp_lia; assert (HWS : sh_fp []) by sh_fp_lia;
  let EU1 := fresh "EU1" in cl_eu (bv_unsigned sp) (-16) EU1;
  do 3 zstep;
  let FR' := fresh "FR'" in pose proof FR as FR'; eapply stk_release in FR'; [| exact ST| lia]; cbn [cells_size csize Nat.add] in FR';
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR' by lia;
  zstep; zstep; apply evt_done; split; [| exact FR']; cbv delta [mkR];
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; rewrite ?(Z_to_bv_bv_unsigned sp); reflexivity.

Section Stub.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ERS : ers_stmt RT GOBJ.
Hypothesis C_ELC : err_const_stmt RT GOBJ.
Variables E CODE T RET1 RET2 : Z.
Hypothesis CODER : 0 <= CODE < 2^64.
Hypothesis TR : 0 <= T < 2^64.
Hypothesis RET1R : 0 <= RET1 < 2^64.
Hypothesis RET1E : RET1 mod 2 = 0.
Hypothesis RET2R : 0 <= RET2 < 2^64.
Hypothesis RET2E : RET2 mod 2 = 0.
Hypothesis W0 : stub_w0_spec E CODE RET1.
Hypothesis W1 : stub_w1_spec RET1 RET2 T.
Hypothesis W2 : stub_w2_spec RET2.

Definition STUB_SITES : list (Z * Z) := [(RET2, E)] ++ ELC_SITES.
Definition STUB_CALLS : list (Z * Z) := [(RET2, e_err_const)] ++ ELC_CALLS.

(* [comment removed for export] *)
Definition stub_stmt (n : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    (LK n1 n2 : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 480 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) E (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) STUB_SITES STUB_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + n1 + n2 + n < LIVE_MAX -> 1 <= rt_credit RT Σ ->
  cl_env m lb canary -> err_statics m LK lh ->
  In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  els_table GOBJ ERR_TAB1 n1 -> els_table GOBJ ERR_TAB2 n2 -> els_table GOBJ T n -> 0 <= n1 -> 0 <= n2 -> 0 <= n -> g_items g + n1 + n2 + n < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc E m)))
    (fun c => exists (Σ' : rts RT) (L' : list (Z * Z)) (B' : Z) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m'
           /\ cl_env m' lb' canary /\ lh_repE GOBJ m' L' lh B' g' bks'
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ err_statics m' LK lh) c
       /\ Permutation (rt_live RT Σ') (L' ++ REST) /\ Z.of_nat (length L') <= Z.of_nat (length L) + n1 + n2 + n
       /\ g_items g <= g_items g' <= g_items g + n1 + n2 + n
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem stub_cps_gen : forall n, stub_stmt n.
Proof.
  intros n Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary L REST lh B g bks LK n1 n2
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV STC INLK AL4 MC REPE PERM RPOS TAB1 TAB2 TAB N1 N2 N0 ITEMS.
  intros TT c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 736 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-16) EU1.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 736).
  { intros a Ha. apply (cl_split RT AF Σ m usp 736 a ART0 ltac:(lia) ltac:(lia)). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros e He; exact He| lia]. }
  assert (STATR : forall a, G_ERR_LOCK <= a < G_ERR_FLAG + 4 -> aclient REST (rt_frames RT Σ) (usp - 16) a) by (intros a Ha; right; left; apply client_static_intro; unfold G_ERR_LOCK, G_ERR_FLAG in Ha; lia).
  (* [comment removed for export] *)
  assert (EXITK : forall (Σ1 : rts RT) (m1 : mem) (L1 : list (Z * Z)) (B1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z))) (lb1 : byte)
      (rax a0x b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (c1 : config),
    ART RT Σ1 m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -16) ->
    rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_cg RT Σ1 = rt_cg RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ1 ->
    rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    lh_repE GOBJ m1 L1 lh B1 g1 bks1 -> Permutation (rt_live RT Σ1) (L1 ++ REST) -> Z.of_nat (length L1) <= Z.of_nat (length L) + n1 + n2 + n -> g_items g <= g_items g1 <= g_items g + n1 + n2 + n ->
    cl_env m1 lb1 canary -> rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m1 ->
    rw_cells asegs m1 LK (mutex_cells z64 z64) -> err_statics m1 LK lh ->
    ASTA RT Σ1 PMc (eq (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1 a0x b1 b2 b3 b4 b5 b6 b7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F1 (Z_to_bv 64 RET2) fc1 None m1 (seg_rom asegs))) c1 ->
    realizes asegs c1 TT).
  { intros Σ1 m1 L1 B1 g1 bks1 lb1 rax a0x b1 b2 b3 b4 b5 b6 b7 u0 u1 u2 u3 u4 u5 u6 F1 fc1 c1 ART1 MI1 ST1 FRS1 SP1 CG1 CR1 FR1 REPE1 PERM1 LL1 IT1 ENV1 PRES1 MC1 STC1 Hc1.
    pose proof (W2 rax sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1 a0x b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 lo ra s0
                  FR1 ST1 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI1) as WX.
    cl_lift WX Hc1 c2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (-> & ST2) & Hc2'). clear Hc2.
    apply Hk. exists Σ1, L1, B1, g1, bks1, lb1.
    split; [| split; [exact PERM1| split; [exact LL1| split; [exact IT1| split; [exact FRS1| split; [exact SP1| split; [exact CR1| exact CG1]]]]]]].
    apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2'). intros ms2 <-. exists m1. fold usp in ST2.
    split; [exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F1, fc1; reflexivity|].
    split; [exact (conj ART1 (conj MI1 ST2))|]. split; [exact PRES1|]. split; [exact ENV1|]. split; [exact REPE1|]. exact (conj MC1 STC1). }
  (* [comment removed for export] *)
  pose proof (W0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as WA.
  cl_lift WA HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 16) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ABOVE1 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> G_ERR_LOCK <= a -> a + Z.of_nat (cells_size cs) <= G_ERR_FLAG + 4 -> rw_cells asegs m1 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m m1 _ _ H); [| exact WM1]. apply BELOW1. unfold G_ERR_LOCK, G_ERR_FLAG, SEGTOP_A in *. intros; lia. }
  assert (STC1 : err_statics m1 LK lh).
  { destruct STC as (X1 & X2 & X3 & X4). unfold G_ERR_ONCE, G_ERR_FLAG, G_ERR_LOCK, G_ERR_HASH in X1, X2, X3, X4.
    split; [| split; [| split]]; [apply (STAT1 _ _ X1)| apply (STAT1 _ _ X2)| apply (STAT1 _ _ X3)| apply (STAT1 _ _ X4)]; cbn [cells_size csize Nat.add]; unfold G_ERR_LOCK, G_ERR_FLAG; lia. }
  assert (MC1 : rw_cells asegs m1 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m m1 _ _ MC); [apply BELOW1; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM1]).
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_agree m m1 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in *.
    apply MU1. cbn [outside]. split; [lia| exact I]. }
  pose proof (uw_chain_agree outer m m1 sp s0 UWC ltac:(apply ABOVE1; cbv beta; unfold USTACK_TOP in *; intros; lia)) as UWC1.
  destruct REPE as (REP & PERML & ALN).
  assert (REPE1 : lh_repE GOBJ m1 L lh B g bks).
  { split; [| exact (conj PERML ALN)]. eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X].
    assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
    assert (INLHL : In (lh, 104) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
    assert (INBL : In (B, 8 * g_na g) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
    pose proof (af_live_range RT AF Σ m lh 104 ART0 (INL _ INLHL)) as (_ & R1 & _). pose proof (af_live_range RT AF Σ m B (8 * g_na g) ART0 (INL _ INBL)) as (_ & R2 & _).
    eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU1' WM1)|].
    intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside app]; (split; [| exact I]); [lia| lia|].
    destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R3 & _). unfold STACK_WIN, RT_STACK in *. lia. }
  pose proof (Permutation_length PERM) as PL0. rewrite length_app in PL0.
  (* [comment removed for export] *)
  apply (C_ERS Σ PMc (Z_to_bv 64 RET1) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 CODE) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo L REST lh B g bks LK CODE FDO MST eq_refl eq_refl CODER ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact Hfr. }
  { exact Hcr. }
  { exact STC1. }
  { exact INLK. }
  { exact AL4. }
  { exact MC1. }
  { exact REPE1. }
  { exact PERM. }
  { exact RPOS. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & v & Hc2 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & REPE2 & MC2 & STC2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. fold usp in ST2, PRES2. rewrite (ret_pc_even RET1 RET1R RET1E) in Hc2'.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 16) x /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES2; [| cbn [outside]; split; [lia| exact I]].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR2 : rw_cells asegs m2 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia| unfold STACK_WIN in *; lia]. }
  assert (ENV2 : cl_env m2 lb canary).
  { apply (cl_env_agree m1 m2 lb canary ENV1).
    exact (AG2 cl_cell ltac:(intros x Hx; split; [right; left; exact (cl_cell_static _ Hx)| pose proof (client_static_range _ (cl_cell_static _ Hx)); unfold SEGTOP_A in *; lia])). }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; lia|]; unfold USTACK_TOP, STACK_WIN in *; lia)) as UWC2.
  assert (PRES_2 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m2).
  { intros a Ha Ho. cbn [outside] in Ho. rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]) ltac:(cbn [outside]; split; [lia| exact I])).
    apply MU1. cbn [outside]. destruct (OFFS _ Ha); split; try exact I; lia. }
  pose proof (bv_unsigned_in_range 64 v) as VR. unfold bv_modulus in VR. cbn [Z.of_N] in VR. rewrite <- (Z_to_bv_bv_unsigned v) in Hc2'.
  (* [comment removed for export] *)
  pose proof (W1 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo (bv_unsigned v)
                VR ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as WB.
  cl_lift WB Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  destruct (bv_unsigned v =? 0) eqn:VZ; cycle 1.
  { (* [comment removed for export] *)
    eapply (EXITK Σ2 m2 L B g bks lb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 c3 ART2 MI2 ST2 FRS2 SP2 CG2 ltac:(lia) FR2 REPE2 ltac:(rewrite LV2; exact PERM) ltac:(lia) ltac:(lia)
              ENV2 PRES_2 MC2 STC2 Hc3'). }
  (* [comment removed for export] *)
  rewrite <- CG2 in CTX, CGH.
  destruct (cl_chain_call (rt_cg RT Σ2) E e_err_const RET2 m2 m2 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (RET2, E) ltac:(left; reflexivity)) (proj2 CGH (RET2, e_err_const) ltac:(left; reflexivity)) UWC2 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR2) ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  pose proof (Permutation_length PERM) as PL. rewrite length_app in PL.
  apply (C_ELC Σ2 PMc (Z_to_bv 64 RET2) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 (Z_to_bv 64 T) e1 e2 e3 e4 e5 e6 e7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo (bv_unsigned ra :: outer) lb canary L REST lh B g bks LK n1 n2 T n FDO MST eq_refl eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW2 SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit RET2) by exact RET2R. exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold STUB_SITES, STUB_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; apply in_or_app; right; exact Hx. }
  { rewrite LV2. lia. }
  { rewrite CR2. lia. }
  { exact ENV2. }
  { exact STC2. }
  { exact INLK. }
  { exact AL4. }
  { exact MC2. }
  { exact REPE2. }
  { rewrite LV2. exact PERM. }
  { exact RPOS. }
  { exact TAB1. }
  { exact TAB2. }
  { exact TAB. }
  { lia. }
  { lia. }
  { lia. }
  { lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ4 & L4 & B4 & g4 & bks4 & lb4 & Hc4 & PERM4 & LL4 & IT4 & FRS4 & SP4 & CR4 & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & ENV4 & REPE4 & MC4 & STC4) & Hc4'). clear Hc4.
  destruct RS4 as (x0 & x1 & x2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x4 & x5 & x6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even RET2 RET2R RET2E) in Hc4'.
  rewrite FRS2 in PRES4.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES4; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR4 : rw_cells asegs m4 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  assert (PRES_4 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m4).
  { intros a Ha Ho. cbn [outside] in Ho. rewrite (PRES4 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]) ltac:(cbn [outside]; repeat split; try exact I; lia)).
    exact (PRES_2 a Ha ltac:(cbn [outside]; exact Ho)). }
  eapply (EXITK Σ4 m4 L4 B4 g4 bks4 lb4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 c4 ART4 MI4 ST4 ltac:(rewrite FRS4; exact FRS2) ltac:(rewrite SP4; exact SP2) ltac:(rewrite CG4; exact CG2)
            ltac:(rewrite CR4, CR2; lia) FR4 REPE4 PERM4 ltac:(lia) ltac:(lia) ENV4 PRES_4 MC4 STC4 Hc4').
Qed.
End Stub.
