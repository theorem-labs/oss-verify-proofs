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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_T_once Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw Fz_I1_load.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).


Definition e_err_strings : Z := 0x1fd520.
Definition e_T_run_once : Z := 0x1f6108.
Definition e_do_esi : Z := 0x1fd580.
Definition OELS_ONCE_RET : Z := 0x1fd544.      (* [comment removed for export] *)
Definition SITE_oels_1 : Z := 0x1fd560.        (* [comment removed for export] *)
Definition SITE_oels_2 : Z := 0x1fd56c.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition G_ERR_ONCE : Z := 0xb9f820.
Definition G_ERR_FLAG : Z := 0xb9f840.
Definition ERR_TAB1 : Z := 0x52ec60.
Definition ERR_TAB2 : Z := 0x52efc0.

(* [comment removed for export] *)
Definition oels_w0_post (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 OELS_ONCE_RET) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 G_ERR_ONCE) (Z_to_bv 64 e_do_esi) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_T_run_once) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -16).

Lemma oels_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (oels_w0_post sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_err_strings) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold e_err_strings.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 9 zstep.
  apply evt_done. unfold oels_w0_post, OELS_ONCE_RET, e_T_run_once, G_ERR_ONCE, e_do_esi. eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma oels_w1 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  rw_cells asegs m G_ERR_FLAG [C4 (Z_to_bv 64 1)] ->
  img_untouched m ->
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_oels_1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ERR_TAB1) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_err_load_strings) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 OELS_ONCE_RET) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 OELS_ONCE_RET) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros FLC UT ST LO0 LO HTOP MI.
  unfold OELS_ONCE_RET in *. unfold G_ERR_FLAG in FLC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit.
  zstep. zstep. zstep. th_if_lit.
  do 3 zstep.
  apply evt_done. unfold SITE_oels_1, ERR_TAB1, e_err_load_strings. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma oels_w2 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_oels_2) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ERR_TAB2) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_err_load_strings) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 SITE_oels_1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_oels_1) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO0 LO HTOP MI.
  unfold SITE_oels_1 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  apply evt_done. unfold SITE_oels_2, ERR_TAB2, e_err_load_strings. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma oels_w3 : forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z) (rav s0v : word),
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rav) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_oels_2) fc None m (seg_rom asegs)).
Proof.
  intros until s0v. intros FR ST LO0 LO HTOP MI.
  unfold SITE_oels_2 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-16) EU1.
  zstep. do 2 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep. apply evt_done. split; [| exact FR']. cbv delta [mkR].
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. rewrite ?(Z_to_bv_bv_unsigned sp). reflexivity.
Qed.

Section ErrStrings.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ELS : err_load_strings_stmt RT GOBJ.

Definition OELS_SITES : list (Z * Z) := [(SITE_oels_1, e_err_strings); (SITE_oels_2, e_err_strings)] ++ ELS_SITES.
Definition OELS_CALLS : list (Z * Z) := [(SITE_oels_1, e_err_load_strings); (SITE_oels_2, e_err_load_strings)] ++ ELS_CALLS.

(* [comment removed for export] *)
Definition err_statics (m : mem) (LK lh : Z) : Prop :=
  rw_cells asegs m G_ERR_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m G_ERR_FLAG [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] /\ rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)].

(* [comment removed for export] *)
Definition err_strings_steady_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (LK n1 n2 : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 432 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_err_strings (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) OELS_SITES OELS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + n1 + n2 < LIVE_MAX -> 0 <= rt_credit RT Σ ->
  cl_env m lb canary -> err_statics m LK lh ->
  In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  els_table GOBJ ERR_TAB1 n1 -> els_table GOBJ ERR_TAB2 n2 -> 0 <= n1 -> 0 <= n2 -> g_items g + n1 + n2 < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_err_strings m)))
    (fun c => exists (Σ' : rts RT) (L' : list (Z * Z)) (B' : Z) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m'
           /\ cl_env m' lb' canary /\ lh_repE GOBJ m' L' lh B' g' bks'
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ err_statics m' LK lh) c
       /\ Permutation (rt_live RT Σ') (L' ++ REST) /\ Z.of_nat (length L') <= Z.of_nat (length L) + n1 + n2
       /\ g_items g <= g_items g' <= g_items g + n1 + n2
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_strings_steady_cps : err_strings_steady_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary L REST lh B g bks LK n1 n2
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV (ONC & FLC & LKC & LHC) INLK AL4 MC REPE PERM RPOS TAB1 TAB2 N1 N2 ITEMS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 432 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-16) EU1.
  unfold G_ERR_ONCE in ONC. unfold G_ERR_FLAG in FLC. unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 432).
  { intros a Ha. apply (cl_split RT AF Σ m usp 432 a ART0 ltac:(lia) ltac:(lia)). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros e He; exact He| lia]. }
  assert (STATR : forall a, G_ERR_LOCK <= a < G_ERR_FLAG + 4 -> aclient REST (rt_frames RT Σ) (usp - 16) a) by (intros a Ha; right; left; apply client_static_intro; unfold G_ERR_LOCK, G_ERR_FLAG in Ha; lia).
  (* [comment removed for export] *)
  pose proof (oels_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 16, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 16) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ABOVE1 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ONC1 : rw_cells asegs m1 G_ERR_ONCE [C4 (Z_to_bv 64 2)]) by (apply (rw_cells_agree asegs m m1 _ _ ONC); [apply BELOW1; cbn [cells_size csize Nat.add]; unfold G_ERR_ONCE, SEGTOP_A in *; intros; lia| exact WM1]).
  (* [comment removed for export] *)
  pose proof (T_run_once_done_proof (Z_to_bv 64 OELS_ONCE_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 G_ERR_ONCE) (Z_to_bv 64 e_do_esi) a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo) as WR.
  rewrite (unsigned_lit G_ERR_ONCE), EU1 in WR by (unfold G_ERR_ONCE; lia). unfold G_ERR_ONCE in WR.
  specialize (WR (proj1 ONC1) ST1 ltac:(lia) ltac:(unfold RT_STACK in *; lia) ltac:(left; lia) MI1).
  cl_lift WR Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a2' & a3' & m2 & -> & MU2 & WM2 & MI2 & ST2 & ONC2) & Hc2'). clear Hc2.
  rewrite (ret_pc_even OELS_ONCE_RET) in Hc2' by (unfold OELS_ONCE_RET; lia).
  assert (MU2' : munch ([] ++ [(usp - 32, usp)]) m m2).
  { apply (munch_trans _ m m1 m2); [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside app]; intros; lia. }
  pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
  pose proof (cl_seg_ART RT AF Σ m m2 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU2' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM02) as ART2.
  assert (BELOW2 : forall P : Z -> Prop, (forall x, P x -> x < usp - 32) -> agree_on P m m2) by (intros P HP a Ha; apply MU2'; cbn [outside app]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (ABOVE2 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m2) by (intros P HP a Ha; apply MU2'; cbn [outside app]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (OFF12 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 32 <= x < usp - 16)) -> agree_on P m1 m2) by (intros P HP a Ha; apply MU2; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  eassert (FR2 : rw_cells asegs m2 (usp + -16) _) by (apply (rw_cells_agree asegs m1 m2 _ _ FR1); [apply OFF12; cbn [cells_size csize Nat.add]; intros; lia| exact WM2]).
  assert (STAT2 : forall a cs, rw_cells asegs m a cs -> G_ERR_LOCK <= a -> a + Z.of_nat (cells_size cs) <= G_ERR_FLAG + 4 -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree asegs m m2 _ _ H); [| exact WM02]. apply BELOW2. unfold G_ERR_LOCK, G_ERR_FLAG, SEGTOP_A in *. intros; lia. }
  pose proof (STAT2 _ _ FLC ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_FLAG; lia)) as FLC2.
  pose proof (STAT2 _ _ LKC ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_FLAG; lia)) as LKC2.
  pose proof (STAT2 _ _ LHC ltac:(unfold G_ERR_LOCK; lia) ltac:(cbn; unfold G_ERR_FLAG; lia)) as LHC2.
  assert (ONC2' : rw_cells asegs m2 G_ERR_ONCE [C4 (Z_to_bv 64 2)]) by (split; [exact ONC2| exact (wr_at_transport asegs m m2 _ _ (proj2 ONC) WM02)]).
  assert (MC2 : rw_cells asegs m2 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m m2 _ _ MC); [apply BELOW2; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM02]).
  assert (ENV2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in *.
    apply MU2'. cbn [outside app]. split; [lia| exact I]. }
  pose proof (uw_chain_agree outer m m2 sp s0 UWC ltac:(apply ABOVE2; cbv beta; unfold USTACK_TOP in *; intros; lia)) as UWC2.
  destruct REPE as (REP & PERML & ALN).
  assert (REPE2 : lh_repE GOBJ m2 L lh B g bks).
  { split; [| exact (conj PERML ALN)]. eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X].
    assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
    assert (INLHL : In (lh, 104) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
    assert (INBL : In (B, 8 * g_na g) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
    pose proof (af_live_range RT AF Σ m lh 104 ART0 (INL _ INLHL)) as (_ & R1 & _). pose proof (af_live_range RT AF Σ m B (8 * g_na g) ART0 (INL _ INBL)) as (_ & R2 & _).
    eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU2' WM02)|].
    intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside app]; (split; [| exact I]); [lia| lia|].
    destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R3 & _). lia. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (oels_w1 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 e_do_esi) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo
                FLC2 UT2 ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  pose proof (Permutation_length PERM) as PL0. rewrite length_app in PL0.
  (* [comment removed for export] *)
  destruct (cl_chain_call (rt_cg RT Σ) e_err_strings e_err_load_strings SITE_oels_1 m2 m2 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (SITE_oels_1, e_err_strings) ltac:(left; reflexivity)) (proj2 CGH (SITE_oels_1, e_err_load_strings) ltac:(left; reflexivity)) UWC2 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR2) ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  apply (C_ELS Σ PMc (Z_to_bv 64 SITE_oels_1) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 ERR_TAB1) (Z_to_bv 64 e_do_esi) a2' a3' a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo (bv_unsigned ra :: outer) lb canary L REST lh B g bks LK ERR_TAB1 n1 FDO MST eq_refl eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_oels_1) by (unfold SITE_oels_1; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { lia. }
  { exact Hcr. }
  { exact ENV2. }
  { exact LKC2. }
  { exact LHC2. }
  { exact INLK. }
  { exact AL4. }
  { exact MC2. }
  { exact REPE2. }
  { exact PERM. }
  { exact RPOS. }
  { exact TAB1. }
  { lia. }
  { lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ4 & L4 & B4 & g4 & bks4 & lb4 & Hc4 & PERM4 & LL4 & IT4 & FRS4 & SP4 & CR4 & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & ENV4 & REPE4 & MC4 & LKC4 & LHC4) & Hc4'). clear Hc4.
  destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_oels_1) in Hc4' by (unfold SITE_oels_1; lia).
  pose proof (Permutation_length PERM4) as PL4. rewrite length_app in PL4.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES4; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR4 : rw_cells asegs m4 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (ONC4 : rw_cells asegs m4 G_ERR_ONCE _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ ONC2'). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_ONCE, G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_ONCE, G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (FLC4 : rw_cells asegs m4 G_ERR_FLAG _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FLC2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_FLAG, G_ALLOW_CUST, STACK_WIN in *. lia. }
  pose proof (uw_chain_agree outer m2 m4 sp s0 UWC2 ltac:(apply AG4; intros x Hx; split; [left; lia|]; unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia)) as UWC4.
  (* [comment removed for export] *)
  pose proof (oels_w2 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 (Z_to_bv 64 1) e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo
                ST4 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ4 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  (* [comment removed for export] *)
  rewrite <- CG4 in CTX, CGH.
  destruct (cl_chain_call (rt_cg RT Σ4) e_err_strings e_err_load_strings SITE_oels_2 m4 m4 ra s0 sp (Z_to_bv 64 (usp + -16)) outer CTX
              (proj1 CGH (SITE_oels_2, e_err_strings) ltac:(right; left; reflexivity)) (proj2 CGH (SITE_oels_2, e_err_load_strings) ltac:(right; left; reflexivity)) UWC4 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -16) by lia; exact FR4) ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXd & UWCd).
  assert (LOW4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact LOW).
  apply (C_ELS Σ4 PMc (Z_to_bv 64 SITE_oels_2) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp s1 (Z_to_bv 64 ERR_TAB2) e1 e2 e3 e4 e5 e6 e7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo (bv_unsigned ra :: outer) lb4 canary L4 REST lh B4 g4 bks4 LK ERR_TAB2 n2 FDO MST eq_refl eq_refl ART4 MI4).
  { fold usp in SPA. cl_call_ok EU1 ST4 LOW4 SPA 1. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_oels_2) by (unfold SITE_oels_2; lia). exact CTXd. }
  { exact UWCd. }
  { clear - CGH. unfold OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { lia. }
  { rewrite CR4. exact Hcr. }
  { exact ENV4. }
  { exact LKC4. }
  { exact LHC4. }
  { exact INLK. }
  { exact AL4. }
  { exact MC4. }
  { exact REPE4. }
  { exact PERM4. }
  { exact RPOS. }
  { exact TAB2. }
  { lia. }
  { lia. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ6 & L6 & B6 & g6 & bks6 & lb6 & Hc6 & PERM6 & LL6 & IT6 & FRS6 & SP6 & CR6 & CG6).
  destruct (ASTA_unpack RT Σ6 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & ST6) & PRES6 & ENV6 & REPE6 & MC6 & LKC6 & LHC6) & Hc6'). clear Hc6.
  destruct RS6 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. fold usp in ST6, PRES6. rewrite (ret_pc_even SITE_oels_2) in Hc6' by (unfold SITE_oels_2; lia).
  rewrite FRS4 in PRES6.
  assert (AG6 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 16) x /\ x <> G_ALLOW_CUST /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m4 m6).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES6; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR6 : rw_cells asegs m6 (usp + -16) _).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ FR4). apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (ONC6 : rw_cells asegs m6 G_ERR_ONCE _).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ ONC4). apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_ONCE, G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_ONCE, G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (FLC6 : rw_cells asegs m6 G_ERR_FLAG _).
  { apply (rw_cells_agree_nw asegs m4 m6 _ _ FLC4). apply AG6. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_FLAG, G_ALLOW_CUST, STACK_WIN in *. lia. }
  (* [comment removed for export] *)
  pose proof (oels_w3 (Z_to_bv 64 SITE_oels_2) sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp s1 (Z_to_bv 64 1) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F6 fc6 m6 lo ra s0
                FR6 ST6 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI6) as W3.
  cl_lift W3 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ6 _ _ c7 Hc7) as (ms7 & (-> & ST7) & Hc7'). clear Hc7.
  apply Hk. exists Σ6, L6, B6, g6, bks6, lb6.
  split.
  - apply (ASTA_conseq RT Σ6 PMc _ _ c7 Hc7'). intros ms7 <-. exists m6. fold usp in ST7.
    split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F6, fc6; reflexivity|].
    split; [exact (conj ART6 (conj MI6 ST7))|].
    split. { intros a Ha Ho. cbn [outside] in Ho.
             assert (Ha' : aclient REST (rt_frames RT Σ) (usp - 16) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
             rewrite (PRES6 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)). rewrite (PRES4 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)).
             apply MU2'. cbn [outside app]. destruct (OFFS _ Ha); split; try exact I; lia. }
    split; [exact ENV6|]. split; [exact REPE6|]. split; [exact MC6|].
    split; [exact ONC6|]. split; [exact FLC6|]. exact (conj LKC6 LHC6).
  - split; [exact PERM6|]. split; [lia|]. split; [lia|].
    split; [rewrite FRS6; exact FRS4|]. split; [rewrite SP6; exact SP4|]. split; [rewrite CR6; exact CR4| rewrite CG6; exact CG4].
Qed.
End ErrStrings.
