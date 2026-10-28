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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_T_once Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw Fz_I1_load Fz_I1_errload.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition e_err_const : Z := 0x1fd7f0.
Definition SITE_elc_1 : Z := 0x1fd80c.         (* [comment removed for export] *)
Definition SITE_elc_2 : Z := 0x1fd818.         (* [comment removed for export] *)

Definition elc_w0_post (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (str : Z) : machine_state -> Prop :=
  fun ms => exists (j8 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_elc_1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 str) (Z_to_bv 64 str) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_err_strings) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma elc_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo str : Z),
  0 <= str < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (elc_w0_post sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc lo m str)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 str) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_err_const) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros SR ST LO0 LO HTOP MI.
  unfold e_err_const.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  do 7 zstep.
  apply evt_done. unfold elc_w0_post, SITE_elc_1, e_err_strings. do 2 eexists.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma elc_w1 : forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo str : Z),
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 SITE_elc_2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 str) (Z_to_bv 64 str) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 e_err_load_strings) fc None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 SITE_elc_1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 str) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_elc_1) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST LO0 LO HTOP MI.
  unfold SITE_elc_1 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. th_if_lit. zstep. zstep.
  apply evt_done. unfold SITE_elc_2, e_err_load_strings. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma elc_w2 : forall (rax sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z) (rav s0v s1v : word) (j8 : list byte),
  rw_cells asegs m (bv_unsigned sp + -32) [CB 8 j8; C8 s1v; C8 s0v; C8 rav] ->
  stk asegs m lo (bv_unsigned sp + -32) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rav) fc None m (seg_rom asegs)
                       /\ stk asegs m lo (bv_unsigned sp))
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_elc_2) fc None m (seg_rom asegs)).
Proof.
  intros until j8. intros FR ST LO0 LO HTOP MI.
  unfold SITE_elc_2 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-32) EU1.
  zstep. do 3 zstep.
  pose proof FR as FR'. eapply stk_release in FR'; [| exact ST| lia]. cbn [cells_size csize Nat.add] in FR'.
  replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in FR' by lia.
  zstep. zstep. apply evt_done. split; [| exact FR']. cbv delta [mkR].
  replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. rewrite ?(Z_to_bv_bv_unsigned sp). reflexivity.
Qed.

Section ErrConst.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ELS : err_load_strings_stmt RT GOBJ.
Hypothesis C_OELS : err_strings_steady_stmt RT GOBJ.

Definition ELC_SITES : list (Z * Z) := [(SITE_elc_1, e_err_const); (SITE_elc_2, e_err_const)] ++ OELS_SITES.
Definition ELC_CALLS : list (Z * Z) := [(SITE_elc_1, e_err_strings); (SITE_elc_2, e_err_load_strings)] ++ OELS_CALLS.

(* [comment removed for export] *)
Definition err_const_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    (LK n1 n2 str n : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 str -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 464 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_err_const (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) ELC_SITES ELC_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + n1 + n2 + n < LIVE_MAX -> 0 <= rt_credit RT Σ ->
  cl_env m lb canary -> err_statics m LK lh ->
  In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  els_table GOBJ ERR_TAB1 n1 -> els_table GOBJ ERR_TAB2 n2 -> els_table GOBJ str n -> 0 <= n1 -> 0 <= n2 -> 0 <= n -> g_items g + n1 + n2 + n < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_err_const m)))
    (fun c => exists (Σ' : rts RT) (L' : list (Z * Z)) (B' : Z) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m'
           /\ cl_env m' lb' canary /\ lh_repE GOBJ m' L' lh B' g' bks'
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ err_statics m' LK lh) c
       /\ Permutation (rt_live RT Σ') (L' ++ REST) /\ Z.of_nat (length L') <= Z.of_nat (length L) + n1 + n2 + n
       /\ g_items g <= g_items g' <= g_items g + n1 + n2 + n
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_const_cps : err_const_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary L REST lh B g bks LK n1 n2 str n
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV STC INLK AL4 MC REPE PERM RPOS TAB1 TAB2 TAB N1 N2 N0 ITEMS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 464 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-32) EU1.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 464).
  { intros a Ha. apply (cl_split RT AF Σ m usp 464 a ART0 ltac:(lia) ltac:(lia)). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros e He; exact He| lia]. }
  assert (STATR : forall a, G_ERR_LOCK <= a < G_ERR_FLAG + 4 -> aclient REST (rt_frames RT Σ) (usp - 32) a) by (intros a Ha; right; left; apply client_static_intro; unfold G_ERR_LOCK, G_ERR_FLAG in Ha; lia).
  destruct (TAB 0 ltac:(lia)) as (e0 & _ & _ & _ & _ & SLO & SHI & _). rewrite Z.mul_0_r, Z.add_0_r in SLO, SHI.
  assert (SR : 0 <= str < 2^64) by (unfold SEGTOP_A in *; lia).
  (* [comment removed for export] *)
  pose proof (elc_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo str
                SR ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j8 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 32, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 32) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
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
    destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R3 & _). lia. }
  pose proof (Permutation_length PERM) as PL0. rewrite length_app in PL0.
  (* [comment removed for export] *)
  assert (FR16 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { change ([CB 8 j8; C8 s1; C8 s0; C8 ra]) with ([CB 8 j8; C8 s1] ++ [C8 s0; C8 ra]) in FR1.
    pose proof (rw_cells_skip m1 _ _ _ FR1) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -32 + 16) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ) e_err_const e_err_strings SITE_elc_1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH (SITE_elc_1, e_err_const) ltac:(left; reflexivity)) (proj2 CGH (SITE_elc_1, e_err_strings) ltac:(left; reflexivity)) UWC1 ltac:(intros a _; reflexivity)
              FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  apply (C_OELS Σ PMc (Z_to_bv 64 SITE_elc_1) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 str) (Z_to_bv 64 str) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary L REST lh B g bks LK n1 n2 FDO MST eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_elc_1) by (unfold SITE_elc_1; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold ELC_SITES, ELC_CALLS, OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { lia. }
  { exact Hcr. }
  { exact ENV1. }
  { exact STC1. }
  { exact INLK. }
  { exact AL4. }
  { exact MC1. }
  { exact REPE1. }
  { exact PERM. }
  { exact RPOS. }
  { exact TAB1. }
  { exact TAB2. }
  { lia. }
  { lia. }
  { lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & L2 & B2 & g2 & bks2 & lb2 & Hc2 & PERM2 & LL2 & IT2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & REPE2 & MC2 & STC2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. fold usp in ST2, PRES2. rewrite (ret_pc_even SITE_elc_1) in Hc2' by (unfold SITE_elc_1; lia).
  pose proof (Permutation_length PERM2) as PL2. rewrite length_app in PL2.
  assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 32) x /\ x <> G_ALLOW_CUST /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m1 m2).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES2; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR2 : rw_cells asegs m2 (usp + -32) _).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; lia|]; unfold G_ALLOW_CUST, USTACK_TOP, STACK_WIN in *; lia)) as UWC2.
  (* [comment removed for export] *)
  pose proof (elc_w1 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo str
                ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  rewrite <- CG2 in CTX, CGH.
  assert (FR16b : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { change ([CB 8 j8; C8 s1; C8 s0; C8 ra]) with ([CB 8 j8; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
    pose proof (rw_cells_skip m2 _ _ _ FR2) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -32 + 16) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ2) e_err_const e_err_load_strings SITE_elc_2 m2 m2 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGH (SITE_elc_2, e_err_const) ltac:(right; left; reflexivity)) (proj2 CGH (SITE_elc_2, e_err_load_strings) ltac:(right; left; reflexivity)) UWC2 ltac:(intros a _; reflexivity)
              FR16b ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXd & UWCd).
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  destruct STC2 as (ONC2 & FLC2 & LKC2 & LHC2).
  apply (C_ELS Σ2 PMc (Z_to_bv 64 SITE_elc_2) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 str) (Z_to_bv 64 str) e1 e2 e3 e4 e5 e6 e7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo (bv_unsigned ra :: outer) lb2 canary L2 REST lh B2 g2 bks2 LK str n FDO MST eq_refl eq_refl ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW2 SPA 2. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_elc_2) by (unfold SITE_elc_2; lia). exact CTXd. }
  { exact UWCd. }
  { clear - CGH. unfold ELC_SITES, ELC_CALLS, OELS_SITES, OELS_CALLS, ELS_SITES, ELS_CALLS in *. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In app] in Hx |- *; tauto. }
  { lia. }
  { rewrite CR2. exact Hcr. }
  { exact ENV2. }
  { exact LKC2. }
  { exact LHC2. }
  { exact INLK. }
  { exact AL4. }
  { exact MC2. }
  { exact REPE2. }
  { exact PERM2. }
  { exact RPOS. }
  { exact TAB. }
  { lia. }
  { lia. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ4 & L4 & B4 & g4 & bks4 & lb4 & Hc4 & PERM4 & LL4 & IT4 & FRS4 & SP4 & CR4 & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & ENV4 & REPE4 & MC4 & LKC4 & LHC4) & Hc4'). clear Hc4.
  destruct RS4 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_elc_2) in Hc4' by (unfold SITE_elc_2; lia).
  rewrite FRS2 in PRES4.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 32) x /\ x <> G_ALLOW_CUST /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2 & X3). apply PRES4; [| cbn [outside]; repeat split; try exact I; lia].
    apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
  eassert (FR4 : rw_cells asegs m4 (usp + -32) _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FR2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (ONC4 : rw_cells asegs m4 G_ERR_ONCE _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ ONC2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_ONCE, G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_ONCE, G_ALLOW_CUST, STACK_WIN in *. lia. }
  eassert (FLC4 : rw_cells asegs m4 G_ERR_FLAG _).
  { apply (rw_cells_agree_nw asegs m2 m4 _ _ FLC2). apply AG4. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_LOCK, G_ERR_FLAG in *; lia|]. unfold G_ERR_FLAG, G_ALLOW_CUST, STACK_WIN in *. lia. }
  (* [comment removed for export] *)
  pose proof (elc_w2 (Z_to_bv 64 SITE_elc_2) sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 str) (Z_to_bv 64 1) d1 d2 d3 d4 d5 d6 d7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F4 fc4 m4 lo ra s0 s1 j8
                FR4 ST4 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI4) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ4 _ _ c5 Hc5) as (ms5 & (-> & ST5) & Hc5'). clear Hc5.
  apply Hk. exists Σ4, L4, B4, g4, bks4, lb4.
  split.
  - apply (ASTA_conseq RT Σ4 PMc _ _ c5 Hc5'). intros ms5 <-. exists m4. fold usp in ST5.
    split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F4, fc4; reflexivity|].
    split; [exact (conj ART4 (conj MI4 ST5))|].
    split. { intros a Ha Ho. cbn [outside] in Ho.
             assert (Ha' : aclient REST (rt_frames RT Σ) (usp - 32) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]).
             rewrite (PRES4 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)). rewrite (PRES2 a Ha' ltac:(cbn [outside]; repeat split; try exact I; lia)).
             apply MU1'. cbn [outside app]. destruct (OFFS _ Ha); split; try exact I; lia. }
    split; [exact ENV4|]. split; [exact REPE4|]. split; [exact MC4|].
    split; [exact ONC4|]. split; [exact FLC4|]. exact (conj LKC4 LHC4).
  - split; [exact PERM4|]. split; [lia|]. split; [lia|].
    split; [rewrite FRS4; exact FRS2|]. split; [rewrite SP4; exact SP2|]. split; [rewrite CR4; exact CR2| rewrite CG4; exact CG2].
Qed.
End ErrConst.
