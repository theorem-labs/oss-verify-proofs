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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Th_mutex Fz_T_lock Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx Fz_I1_insert Fz_I1_loadw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Section ErrLoad.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_LHI : lh_insert_stmt RT GOBJ.

(* [comment removed for export] *)
Definition els_word (d e : Z) : Prop := forall m : mem, mem_inv asegs m -> img_untouched m -> ro_cells asegs m d [C8 (Z_to_bv 64 e)].
(* [comment removed for export] *)
Definition els_table (str n : Z) : Prop :=
  forall j, 0 <= j <= n -> exists e, 0 <= e < 2^64 /\ els_word (str + 16 * j) e /\ (e = 0 <-> j = n)
    /\ (str + 16 * j) mod 8 = 0 /\ 0x10000 <= str + 16 * j /\ str + 16 * j + 16 <= SEGTOP_A
    /\ (exists b sz, GOBJ b sz /\ b <= str + 16 * j /\ str + 16 * j + 16 <= b + sz) /\ (j < n -> DVerr GOBJ (str + 16 * j)).

Definition ELS_SITES : list (Z * Z) :=
  [(SITE_els_insert, e_err_load_strings); (SITE_lhi_realloc, e_lh_insert); (SITE_lhi_malloc, e_lh_insert); (SITE_cr_realloc, e_CRYPTO_realloc); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition ELS_CALLS : list (Z * Z) :=
  [(SITE_els_insert, e_lh_insert); (SITE_lhi_realloc, e_CRYPTO_realloc); (SITE_lhi_malloc, e_CRYPTO_malloc); (SITE_cr_realloc, e_realloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Definition err_load_strings_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (L REST : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (LK str n : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 str -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 416 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_err_load_strings (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) ELS_SITES ELS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) + n < LIVE_MAX -> 0 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  rw_cells asegs m G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> rw_cells asegs m G_ERR_HASH [C8 (Z_to_bv 64 lh)] ->
  In (LK, 40) REST -> LK mod 4 = 0 -> rw_cells asegs m LK (mutex_cells z64 z64) ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  els_table str n -> 0 <= n -> g_items g + n < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_err_load_strings m)))
    (fun c => exists (Σ' : rts RT) (L' : list (Z * Z)) (B' : Z) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m'
           /\ cl_env m' lb' canary /\ lh_repE GOBJ m' L' lh B' g' bks'
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' G_ERR_LOCK [C8 (Z_to_bv 64 LK)] /\ rw_cells asegs m' G_ERR_HASH [C8 (Z_to_bv 64 lh)]) c
       /\ Permutation (rt_live RT Σ') (L' ++ REST) /\ Z.of_nat (length L') <= Z.of_nat (length L) + n
       /\ g_items g <= g_items g' <= g_items g + n
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_load_strings_cps : err_load_strings_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary L REST lh B g bks LK str n
    FDO MST -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV LKC LHC INLK AL4 MC REPE PERM RPOS TAB N0 ITEMS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 416 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-64) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  unfold G_ERR_LOCK in LKC. unfold G_ERR_HASH in LHC.
  assert (INR : forall x, In x REST -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 (INR _ INLK)) as (LK0 & LKLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 (INR _ INLK) ltac:(lia)) as LKHI.
  assert (LKR : 0 <= LK < 2^64) by (unfold STACK_WIN, USTACK_TOP in *; lia).
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 416).
  { intros a Ha. apply (cl_split RT AF Σ m usp 416 a ART0 ltac:(lia) ltac:(lia)). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR| intros e He; exact He| lia]. }
  assert (STATR : forall a, G_ERR_LOCK <= a < G_ERR_HASH + 8 -> aclient REST (rt_frames RT Σ) (usp - 64) a) by (intros a Ha; right; left; apply client_static_intro; unfold G_ERR_LOCK, G_ERR_HASH in Ha; lia).
  (* [comment removed for export] *)
  assert (EXITK : forall (Σ1 : rts RT) (m1 : mem) (L1 : list (Z * Z)) (B1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z))) (lb1 : byte) (j6 : list byte)
      (rax s1x a0x b1 b2 b3 b4 b5 b6 b7 s2x s4x s5x u0 u1 u2 u3 u4 u5 u6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (c1 : config),
    ART RT Σ1 m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -64) ->
    rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_cg RT Σ1 = rt_cg RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ ->
    rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    lh_repE GOBJ m1 L1 lh B1 g1 bks1 -> Permutation (rt_live RT Σ1) (L1 ++ REST) -> Z.of_nat (length L1) <= Z.of_nat (length L) + n -> g_items g <= g_items g1 <= g_items g + n ->
    cl_env m1 lb1 canary -> rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m1 ->
    rw_cells asegs m1 LK (mutex_cells z64 (Z_to_bv 64 16)) -> rw_cells asegs m1 G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> rw_cells asegs m1 G_ERR_HASH [C8 (Z_to_bv 64 lh)] ->
    ASTA RT Σ1 PMc (eq (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1x a0x b1 b2 b3 b4 b5 b6 b7
                                 s2x (Z_to_bv 64 0xb9f658) s4x s5x s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F1 (Z_to_bv 64 ELS_EXIT) fc1 None m1 (seg_rom asegs))) c1 ->
    realizes asegs c1 T).
  { intros Σ1 m1 L1 B1 g1 bks1 lb1 j6 rax s1x a0x b1 b2 b3 b4 b5 b6 b7 s2x s4x s5x u0 u1 u2 u3 u4 u5 u6 F1 fc1 c1
           ART1 MI1 ST1 FRS1 SP1 CG1 CR1 FR1 REPE1 PERM1 LL1 IT1 ENV1 PRES1 MC1 LKC1 LHC1 Hc1.
    destruct (af_client_consts RT AF Σ1 m1 ART1) as (_ & _ & _ & _ & UT1).
    pose proof (els_w3 rax sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1x a0x b1 b2 b3 b4 b5 b6 b7 s2x s4x s5x s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 lo LK ra s0 s1 s2 s3 s4 s5 j6
                  LKC1 LKR FR1 UT1 ST1 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI1) as W3.
    cl_lift W3 Hc1 c2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (-> & ST2) & Hc2'). clear Hc2.
    pose proof (T_unlock_proof ra sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 s0 s1 (Z_to_bv 64 LK) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 lo) as WU.
    rewrite (unsigned_lit LK) in WU by lia. specialize (WU MC1 AL4 ST2 ltac:(lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(left; lia) MI1).
    cl_lift WU Hc2' c3 Hc3.
    apply Hk. exists Σ1, L1, B1, g1, bks1, lb1.
    assert (INR1 : forall x, In x REST -> In x (rt_live RT Σ1)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; right; exact Hx]).
    assert (INL1 : forall x, In x L1 -> In x (rt_live RT Σ1)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; left; exact Hx]).
    split.
    - apply (ASTA_conseq RT Σ1 PMc _ _ c3 Hc3). intros ms3 (b1' & b2' & b3' & m3 & -> & MU3 & WM3 & MI3 & ST3 & MC3). exists m3. fold usp in MU3, ST3.
      split; [exists u0, u1, u2, b1', b2', b3', b4, b5, b6, b7, u3, u4, u5, u6, F1, fc1; reflexivity|].
      assert (ART3 : ART RT Σ1 m3).
      { apply (af_frame RT AF Σ1 m1 m3 (usp - 112) ART1 ltac:(rewrite SP1; lia)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
        split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I]. intros X. apply Ha. right; right; left. exists LK, 40. split; [exact (INR1 _ INLK)| lia]. }
      split; [exact (conj ART3 (conj MI3 ST3))|].
      split. { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply MU3. cbn [outside] in Ho |- *. split; [destruct (OFFS _ Ha); lia|]. split; [lia| exact I]. }
      split. { apply (cl_env_seg _ m1 m3 lb1 canary ENV1 MU3). intros x Hx. cbn [outside]. pose proof (client_static_range _ (cl_cell_static _ Hx)). unfold SEGTOP_A, USTACK_TOP in *. repeat split; try exact I; lia. }
      split. { destruct REPE1 as (REP1 & PERML1 & ALN1). split; [| exact (conj PERML1 ALN1)]. eapply lh_rep_agree; [exact REP1| | intros ? ? ? ? _ X; exact X].
               eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU3 WM3)|].
               assert (INLHL : In (lh, 104) L1) by (eapply Permutation_in; [apply Permutation_sym; exact PERML1| left; reflexivity]).
               assert (INBL : In (B1, 8 * g_na g1) L1) by (eapply Permutation_in; [apply Permutation_sym; exact PERML1| right; left; reflexivity]).
               pose proof (af_live_range RT AF Σ1 m1 lh 104 ART1 (INL1 _ INLHL)) as (_ & R1 & _). pose proof (af_live_range RT AF Σ1 m1 B1 (8 * g_na g1) ART1 (INL1 _ INBL)) as (_ & R2 & _).
               rewrite SP1 in R1, R2. pose proof (lh_geo_bounds g1 (proj1 REP1)) as GB1.
               intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside].
               + split; [lia|]. split; [| exact I]. destruct (lrest_apart RT AF Σ1 m1 L1 REST lh 104 LK 40 ART1 PERM1 INLHL INLK ltac:(lia) ltac:(lia)); lia.
               + split; [lia|]. split; [| exact I]. destruct (lrest_apart RT AF Σ1 m1 L1 REST B1 (8 * g_na g1) LK 40 ART1 PERM1 INBL INLK ltac:(lia) ltac:(lia)); lia.
               + destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP1 q A Hq) as [O _].
                 pose proof (af_live_range RT AF Σ1 m1 A 24 ART1 (INL1 _ O)) as (_ & R3 & _). rewrite SP1 in R3.
                 split; [lia|]. split; [| exact I]. destruct (lrest_apart RT AF Σ1 m1 L1 REST A 24 LK 40 ART1 PERM1 O INLK ltac:(lia) ltac:(lia)); lia. }
      split; [exact MC3|].
      split; [apply (rw_cells_agree asegs m1 m3 _ _ LKC1); [| exact WM3]| apply (rw_cells_agree asegs m1 m3 _ _ LHC1); [| exact WM3]];
        (intros a Ha; apply MU3; cbn [cells_size csize Nat.add outside] in Ha |- *; unfold G_ERR_LOCK, G_ERR_HASH, USTACK_TOP in *; repeat split; try exact I; lia).
    - split; [exact PERM1|]. split; [exact LL1|]. split; [exact IT1|]. split; [exact FRS1|]. split; [exact SP1|]. split; [exact CR1| exact CG1]. }
  pose proof REPE as (REP & PERML & ALN). pose proof (lh_geo_bounds g (proj1 REP)) as GB.
  assert (LHR : 0 <= lh < 2^64) by (pose proof REP as (_ & _ & RL & _); unfold LH_CEIL, USTACK_TOP in RL; lia).
  (* [comment removed for export] *)
  assert (LOOP : forall (k : nat) (Σ1 : rts RT) (m1 : mem) (L1 : list (Z * Z)) (B1 : Z) (g1 : lh_geo) (bks1 : list (list (bptr * Z))) (lb1 : byte) (j6 : list byte)
      (u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (c1 : config),
    (0 < k)%nat -> Z.of_nat k <= n ->
    ART RT Σ1 m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -64) ->
    rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_cg RT Σ1 = rt_cg RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ ->
    Z.of_nat (length (rt_live RT Σ1)) <= Z.of_nat (length (rt_live RT Σ)) + (n - Z.of_nat k) ->
    rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 j6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    lh_repE GOBJ m1 L1 lh B1 g1 bks1 -> Permutation (rt_live RT Σ1) (L1 ++ REST) ->
    Z.of_nat (length L1) <= Z.of_nat (length L) + (n - Z.of_nat k) -> g_items g <= g_items g1 <= g_items g + (n - Z.of_nat k) ->
    cl_env m1 lb1 canary -> uw_chain m1 sp s0 outer -> rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m1 ->
    rw_cells asegs m1 LK (mutex_cells z64 (Z_to_bv 64 16)) -> rw_cells asegs m1 G_ERR_LOCK [C8 (Z_to_bv 64 LK)] -> rw_cells asegs m1 G_ERR_HASH [C8 (Z_to_bv 64 lh)] ->
    ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp
                                 (Z_to_bv 64 (str + 16 * (n - Z.of_nat k))) (Z_to_bv 64 lh) (Z_to_bv 64 (str + 16 * (n - Z.of_nat k))) b2 b3 b4 b5 b6 b7
                                 (Z_to_bv 64 (str + 16 * (n - Z.of_nat k) + 16)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                            F1 (Z_to_bv 64 e_lh_insert) fc1 None m1 (seg_rom asegs))) c1 ->
    realizes asegs c1 T).
  { induction k as [|k IH]; [intros; lia|].
    intros Σ1 m1 L1 B1 g1 bks1 lb1 j6 u0 u1 u2 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 c1 _ KN
           ART1 MI1 ST1 FRS1 SP1 CG1 CR1 LEN1 FR1 REPE1 PERM1 LL1 IT1 ENV1 UWC1 PRES1 MC1 LKC1 LHC1 Hc1.
    set (j := n - Z.of_nat (S k)) in *. assert (JR : 0 <= j /\ j + 1 <= n) by lia.
    set (cur := str + 16 * j) in *.
    destruct (TAB j ltac:(lia)) as (ej & _ & _ & _ & ALj & GLj & GHj & _ & DVJ). pose proof (DVJ ltac:(lia)) as DVj. clear DVJ.
    destruct (TAB (j + 1) ltac:(lia)) as (e' & ER' & W' & EZ' & ALj1 & GLj1 & GHj1 & (gb1 & gs1 & G1 & GB1 & GS1) & _).
    replace (str + 16 * (j + 1)) with (cur + 16) in W', ALj1, GLj1, GHj1, GB1, GS1 by lia.
    assert (INR1 : forall x, In x REST -> In x (rt_live RT Σ1)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; right; exact Hx]).
    (* [comment removed for export] *)
    assert (FR16 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
    { change ([CB 8 j6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR1.
      pose proof (rw_cells_skip m1 _ _ _ FR1) as X. cbn [cells_size csize Nat.add] in X. fold usp in X. replace (usp + -64 + 48) with (usp - 16) in X by lia. exact X. }
    destruct (cl_chain_call (rt_cg RT Σ) e_err_load_strings e_lh_insert SITE_els_insert m1 m1 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTX
                (proj1 CGH (SITE_els_insert, e_err_load_strings) ltac:(left; reflexivity)) (proj2 CGH (SITE_els_insert, e_lh_insert) ltac:(left; reflexivity)) UWC1 ltac:(intros a _; reflexivity)
                FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
    (* [comment removed for export] *)
    apply (C_LHI Σ1 PMc (Z_to_bv 64 SITE_els_insert) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 cur) (Z_to_bv 64 lh) (Z_to_bv 64 cur) b2 b3 b4 b5 b6 b7
             (Z_to_bv 64 (cur + 16)) (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) (Z_to_bv 64 0xb9f690) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F1 fc1 m1 lo (bv_unsigned ra :: outer) lb1 canary
             L1 REST lh B1 cur g1 bks1 FDO MST eq_refl eq_refl eq_refl ART1 MI1).
    { assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW). fold usp in SPA. cl_call_ok EU1 ST1 LOW1 SPA 4. }
    { rewrite EU1. unfold RT_STACK in *. lia. }
    { rewrite CG1. rewrite (unsigned_lit SITE_els_insert) by (unfold SITE_els_insert; lia). exact CTXc. }
    { exact UWCc. }
    { clear - CGH CG1. rewrite CG1. unfold ELS_SITES, ELS_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
    { lia. }
    { rewrite CR1. exact Hcr. }
    { exact ENV1. }
    { exact REPE1. }
    { exact PERM1. }
    { exact RPOS. }
    { exact DVj. }
    { lia. }
    { exact Hc1. }
    clear Hc1. intros c2 (Σ2 & v & L2 & B2 & g2 & bks2 & lb2 & Hc2 & PERM2 & LL2 & IT2 & NA2 & FRS2 & SP2 & CR2 & CG2 & _).
    destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & REPE2) & Hc2'). clear Hc2.
    destruct RS2 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
    rewrite EU1 in ST2, PRES2. fold usp in ST2, PRES2. rewrite (ret_pc_even SITE_els_insert) in Hc2' by (unfold SITE_els_insert; lia).
    assert (FRS2' : rt_frames RT Σ2 = rt_frames RT Σ) by (rewrite FRS2; exact FRS1). assert (SP2' : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP2; exact SP1).
    assert (CG2' : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite CG2; exact CG1). assert (CR2' : rt_credit RT Σ2 = rt_credit RT Σ) by (rewrite CR2; exact CR1).
    pose proof (Permutation_length PERM1) as PL1. pose proof (Permutation_length PERM2) as PL2. rewrite length_app in PL1, PL2.
    (* [comment removed for export] *)
    assert (AG2 : forall P : Z -> Prop, (forall x, P x -> aclient REST (rt_frames RT Σ) (usp - 64) x /\ x <> G_ALLOW_CUST) -> agree_on P m1 m2).
    { intros P HP a Ha. destruct (HP _ Ha) as (X1 & X2). apply PRES2; [| cbn [outside]; split; [lia| exact I]].
      rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ X1); [intros e He; exact He| intros e He; exact He| lia]. }
    assert (PRES_2 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m2).
    { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply PRES2; [| cbn [outside] in Ho |- *; split; [lia| exact I]]. rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
    eassert (FR2 : rw_cells asegs m2 (usp + -64) _).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [left; unfold USTACK_TOP in *; lia|]. unfold G_ALLOW_CUST. lia. }
    eassert (LKC2 : rw_cells asegs m2 G_ERR_LOCK _).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ LKC1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_LOCK, G_ERR_HASH in *; lia|]. unfold G_ERR_LOCK, G_ALLOW_CUST in *. lia. }
    eassert (LHC2 : rw_cells asegs m2 G_ERR_HASH _).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ LHC1). apply AG2. cbn [cells_size csize Nat.add]. intros x Hx. split; [apply STATR; unfold G_ERR_LOCK, G_ERR_HASH in *; lia|]. unfold G_ERR_HASH, G_ALLOW_CUST in *. lia. }
    eassert (MC2 : rw_cells asegs m2 LK _).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ MC1). apply AG2. cbn [cells_size csize Nat.add mutex_cells]. intros x Hx. split; [right; right; left; exists LK, 40; split; [exact INLK| lia]|]. unfold G_ALLOW_CUST in *. lia. }
    pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 ltac:(apply AG2; intros x Hx; split; [left; lia|]; unfold G_ALLOW_CUST, USTACK_TOP in *; lia)) as UWC2.
    destruct (af_client_consts RT AF Σ2 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
    pose proof (afp_acc_global RT GOBJ AFP Σ2 m2 gb1 gs1 (cur + 16) 8 ART2 G1 ltac:(lia) ltac:(lia)) as ACCj1. pose proof (W' m2 MI2 UT2) as EC2.
    unfold G_ERR_HASH in LHC2.
    pose proof (els_w2 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 v) e1 e2 e3 e4 e5 e6 e7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m2 lo cur lh e'
                  EC2 ER' ACCj1 ALj1 ltac:(lia) ltac:(lia) ltac:(lia) LHC2 ltac:(lia) UT2 SHC2 ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W2.
    cl_lift W2 Hc2' c3 Hc3.
    destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
    destruct (e' =? 0) eqn:EZ.
    - (* [comment removed for export] *)
      apply Z.eqb_eq in EZ. assert (KZ : k = 0%nat) by (apply EZ' in EZ; lia).
      eapply (EXITK Σ2 m2 L2 B2 g2 bks2 lb2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 c3 ART2 MI2 ST2 FRS2' SP2' CG2' CR2' FR2 REPE2 PERM2 ltac:(lia) ltac:(lia) ENV2 PRES_2 MC2 LKC2 LHC2 Hc3').
    - (* [comment removed for export] *)
      apply Z.eqb_neq in EZ.
      eapply (IH Σ2 m2 L2 B2 g2 bks2 lb2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 c3 ltac:(lia) ltac:(lia) ART2 MI2 ST2 FRS2' SP2' CG2' CR2' ltac:(lia) FR2 REPE2 PERM2 ltac:(lia) ltac:(lia) ENV2 UWC2 PRES_2 MC2 LKC2 LHC2).
      replace (str + 16 * (n - Z.of_nat k)) with (cur + 16) by lia. replace (cur + 16 + 16) with (cur + 32) by lia. exact Hc3'. }
  (* [comment removed for export] *)
  pose proof (els_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 str) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo LK
                LKC LKR UT SHC ST LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j6 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1, FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 64, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (BELOW1 : forall P : Z -> Prop, (forall x, P x -> x < usp - 64) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  assert (MC1 : rw_cells asegs m1 LK (mutex_cells z64 z64)) by (apply (rw_cells_agree asegs m m1 _ _ MC); [apply BELOW1; cbn [cells_size csize Nat.add mutex_cells]; intros; lia| exact WM1]).
  pose proof (T_write_lock_proof (Z_to_bv 64 ELS_LOCK_RET) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 str) (Z_to_bv 64 LK) (Z_to_bv 64 LK) a2 a3 a4 a5 a6 a7
                s2 (Z_to_bv 64 0xb9f658) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo) as WL.
  rewrite (unsigned_lit LK), EU1 in WL by lia. specialize (WL MC1 AL4 ST1 ltac:(lia) ltac:(unfold RT_STACK in *; lia) ltac:(left; lia) MI1).
  cl_lift WL Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (a1' & a2' & a3' & a4' & a5' & m2 & -> & MU2 & WM2 & MI2 & ST2 & MC2) & Hc2'). clear Hc2.
  rewrite (ret_pc_even ELS_LOCK_RET) in Hc2' by (unfold ELS_LOCK_RET; lia).
  assert (ART2 : ART RT Σ m2).
  { apply (af_frame RT AF Σ m1 m2 (usp - 80) ART1 ltac:(lia)); [| exact WM2]. intros a Ha. apply MU2. cbn [outside].
    split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I]. intros X. apply Ha. right; right; left. exists LK, 40. split; [exact (INR _ INLK)| lia]. }
  assert (OFF2 : forall P : Z -> Prop, (forall x, P x -> ~ (usp - 80 <= x < usp - 64) /\ ~ (LK + 4 <= x < LK + 8)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply MU2. cbn [outside]. destruct (HP _ Ha) as [X1 X2]. repeat split; try exact I; lia. }
  assert (PRES_2 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (LK + 4, LK + 8)] m m2).
  { intros a Ha Ho. cbn [outside] in Ho. rewrite (MU2 a ltac:(cbn [outside]; destruct (OFFS _ Ha); repeat split; try exact I; lia)). apply MU1. cbn [outside]. destruct (OFFS _ Ha); split; try exact I; lia. }
  eassert (FR2 : rw_cells asegs m2 (usp + -64) _) by (apply (rw_cells_agree asegs m1 m2 _ _ FR1); [apply OFF2; cbn [cells_size csize Nat.add]; intros; lia| exact WM2]).
  assert (LKC2 : rw_cells asegs m2 G_ERR_LOCK [C8 (Z_to_bv 64 LK)]).
  { apply (rw_cells_agree asegs m m2 _ _ LKC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. eapply agree_trans; [apply BELOW1| apply OFF2]; cbn [cells_size csize Nat.add]; unfold G_ERR_LOCK, SEGTOP_A in *; intros; lia. }
  assert (LHC2 : rw_cells asegs m2 12187648 [C8 (Z_to_bv 64 lh)]).
  { apply (rw_cells_agree asegs m m2 _ _ LHC); [| exact (wmono_trans asegs _ _ _ WM1 WM2)]. eapply agree_trans; [apply BELOW1| apply OFF2]; cbn [cells_size csize Nat.add]; unfold SEGTOP_A in *; intros; lia. }
  assert (ENV2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 lb canary ENV). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. unfold SEGTOP_A in CR.
    rewrite (MU2 a ltac:(cbn [outside]; repeat split; try exact I; lia)). apply MU1. cbn [outside]. split; [lia| exact I]. }
  assert (ABOVE1 : forall P : Z -> Prop, (forall x, P x -> usp <= x) -> agree_on P m m1) by (intros P HP a Ha; apply MU1; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
  pose proof (uw_chain_agree outer m m2 sp s0 UWC ltac:(eapply agree_trans; [apply ABOVE1| apply OFF2]; cbv beta; unfold USTACK_TOP in *; intros; lia)) as UWC2.
  assert (REPE2 : lh_repE GOBJ m2 L lh B g bks).
  { split; [| exact (conj PERML ALN)]. eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X].
    assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
    assert (INLHL : In (lh, 104) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
    assert (INBL : In (B, 8 * g_na g) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
    pose proof (af_live_range RT AF Σ m lh 104 ART0 (INL _ INLHL)) as (_ & R1 & _). pose proof (af_live_range RT AF Σ m B (8 * g_na g) ART0 (INL _ INBL)) as (_ & R2 & _).
    intros a Ha HP. assert (E : m2 (wa a) = m (wa a)); [| split; [exact E| intros Hw; apply WM2; apply WM1; exact Hw]].
    assert (BL : a < usp - 80 /\ ~ (LK + 4 <= a < LK + 8)).
    { destruct HP as [X|[X|(q & A & Hq & X)]].
      + split; [lia|]. destruct (lrest_apart RT AF Σ m L REST lh 104 LK 40 ART0 PERM INLHL INLK ltac:(lia) ltac:(lia)); lia.
      + split; [lia|]. destruct (lrest_apart RT AF Σ m L REST B (8 * g_na g) LK 40 ART0 PERM INBL INLK ltac:(lia) ltac:(lia)); lia.
      + destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _]. pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R3 & _).
        split; [lia|]. destruct (lrest_apart RT AF Σ m L REST A 24 LK 40 ART0 PERM O INLK ltac:(lia) ltac:(lia)); lia. }
    rewrite (MU2 (wa a)); [apply MU1|]; unfold wa; rewrite unsigned_lit by lia; cbn [outside]; repeat split; try exact I; lia. }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  destruct (TAB 0 ltac:(lia)) as (e0 & ER0 & W0 & EZ0 & AL0 & GL0 & GH0 & (gb0 & gs0 & G0 & GB0 & GS0) & _). rewrite Z.mul_0_r, Z.add_0_r in W0, AL0, GL0, GH0, GB0, GS0.
  pose proof (afp_acc_global RT GOBJ AFP Σ m2 gb0 gs0 str 8 ART2 G0 ltac:(lia) ltac:(lia)) as ACC0. pose proof (W0 m2 MI2 UT2) as EC0.
  pose proof (els_w1 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp a1' a2' a3' a4' a5' a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo str lh e0
                EC0 ER0 ACC0 AL0 GL0 GH0 ltac:(lia) LHC2 LHR UT2 SHC2 ST2 LO0 ltac:(fold usp; unfold RT_STACK in *; lia) HT1 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  pose proof (Permutation_length PERM) as PL0. rewrite length_app in PL0.
  destruct (e0 =? 0) eqn:EZ.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in EZ. assert (NZ : n = 0) by (apply EZ0 in EZ; lia).
    eapply (EXITK Σ m2 L B g bks lb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc c3 ART2 MI2 ST2 eq_refl eq_refl eq_refl eq_refl FR2 REPE2 PERM ltac:(lia) ltac:(lia) ENV2 PRES_2 MC2 LKC2 LHC2 Hc3').
  - apply Z.eqb_neq in EZ. assert (NP : 1 <= n) by (destruct (Z.eq_dec n 0) as [E|NE]; [exfalso; apply EZ; apply EZ0; lia| lia]).
    eapply (LOOP (Z.to_nat n) Σ m2 L B g bks lb _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc c3 ltac:(lia) ltac:(lia) ART2 MI2 ST2 eq_refl eq_refl eq_refl eq_refl ltac:(lia) FR2 REPE2 PERM
              ltac:(lia) ltac:(lia) ENV2 UWC2 PRES_2 MC2 LKC2 LHC2).
    rewrite Z2Nat.id by lia. replace (str + 16 * (n - n)) with str by lia. exact Hc3'.
Qed.
End ErrLoad.
