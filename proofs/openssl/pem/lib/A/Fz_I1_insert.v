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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_mkit Fz_G_kit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_retrieve Fz_I1_split Fz_I1_expand Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_I1_insx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma perm_dup_split {X : Type} : forall (x : X) (L R live : list X), Permutation live (L ++ R) -> In x L -> In x R ->
  exists l1 l2, live = l1 ++ x :: l2 /\ In x (l1 ++ l2).
Proof.
  intros x L R live HP HL HR. destruct (in_split _ _ HL) as (L1 & L2 & ->).
  assert (HP1 : Permutation live (x :: (L1 ++ L2 ++ R))).
  { eapply Permutation_trans; [exact HP|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  assert (IX : In x live) by (eapply Permutation_in; [apply Permutation_sym; exact HP1| left; reflexivity]).
  destruct (in_split _ _ IX) as (l1 & l2 & EL). exists l1, l2. split; [exact EL|].
  rewrite EL in HP1. apply Permutation_sym in HP1. apply Permutation_cons_app_inv in HP1.
  eapply Permutation_in; [exact HP1|]. apply in_or_app; right. apply in_or_app; right. exact HR.
Qed.

(* [comment removed for export] *)
Lemma concat_lupd_snoc {X : Type} : forall (bks : list (list X)) (i : nat) (x : X), (i < length bks)%nat ->
  Permutation (concat (lupd i (nth i bks [] ++ [x]) bks)) (x :: concat bks).
Proof.
  intros bks i x Hi.
  eapply Permutation_trans; [apply concat_lupd; exact Hi|].
  eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
  apply Permutation_sym. rewrite <- (lupd_same bks i []) at 1 by exact Hi. apply concat_lupd. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma split_munch2 : forall lh cp cn NS (m m' : mem),
  LhRep.agree_on asegs (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W cp cn NS a)) m m' -> munch ((lh + 56, lh + 68) :: split_ivs cp cn NS) m m'.
Proof.
  intros lh cp cn NS m m' AG x [H1 Hx]. apply split_ivs_outside in Hx. pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
  destruct (AG (bv_unsigned x) XR ltac:(intros [Y|Y]; [exact (H1 Y)| exact (Hx Y)])) as [E _]. rewrite Nodes.wa_unsigned_id in E. exact E.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_glue : forall (m : mem) A pre cs post, rw_cells asegs m A (pre ++ cs ++ post) -> rw_cells asegs m A (pre ++ CB (cells_size cs) (cells_bytes cs) :: post).
Proof.
  intros m A pre cs post H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W0 W12]. apply cells_wf_app in W12. destruct W12 as [W1 W2].
  eapply LhRep.rw_cells_recast; [exact H| | |].
  - apply cells_wf_app. split; [exact W0|]. cbn [cells_wf]. split; [| exact W2]. cbn [cell_wf]. apply cells_bytes_length. exact W1.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite ?cells_bytes_app. reflexivity.
  - rewrite !cells_size_app. cbn [cells_size csize]. rewrite ?cells_size_app. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_remove_permM : forall p (l l' : list (Z * Z)), Permutation l l' -> Permutation (live_remove p l) (live_remove p l').
Proof.
  intros p l l' H. unfold live_remove. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (decide _); [apply perm_skip|]; exact IH.
  - destruct (decide _), (decide _); [apply perm_swap| apply perm_skip| apply perm_skip|]; apply Permutation_refl.
  - exact (Permutation_trans IH1 IH2).
Qed.
Lemma live_remove_inM : forall p (l : list (Z * Z)) e, In e (live_remove p l) -> In e l /\ fst e <> p.
Proof.
  intros p l e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He. apply stdpp.list_basics.list.list_elem_of_filter in He.
  destruct He as [Hf Hin]. split; [apply stdpp.base.list_elem_of_In; exact Hin|]. intros E. rewrite E, Z.eqb_refl in Hf. exact Hf.
Qed.
Lemma live_remove_appM : forall p (l r : list (Z * Z)), live_remove p (l ++ r) = live_remove p l ++ live_remove p r.
Proof. intros p l r. unfold live_remove. apply stdpp.list_basics.list.filter_app. Qed.
Lemma live_remove_length_lt : forall p n (l : list (Z * Z)), In (p, n) l -> (length (live_remove p l) < length l)%nat.
Proof.
  intros p n l H. unfold live_remove. apply (stdpp.list_basics.list.length_filter_lt _ l (p, n)).
  - apply stdpp.base.list_elem_of_In. exact H.
  - cbn [fst]. rewrite Z.eqb_refl. cbn. intros X. exact X.
Qed.

Section LhInsert.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CRA : crypto_realloc_array_env_stmt RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.

(* [comment removed for export] *)
Lemma lrest_apart : forall Σ m L REST A n A' n', ART RT Σ m -> Permutation (rt_live RT Σ) (L ++ REST) ->
  In (A, n) L -> In (A', n') REST -> 0 < n -> 0 < n' -> A + n <= A' \/ A' + n' <= A.
Proof using AF.
  intros Σ m L REST A n A' n' HA HP IL IR Hn Hn'.
  destruct (Z.eq_dec A A') as [EA|NA]; [destruct (Z.eq_dec n n') as [EN|NN]|].
  - subst A' n'. destruct (perm_dup_split (A, n) L REST _ HP IL IR) as (l1 & l2 & EL & I2).
    destruct (af_live_disj RT AF Σ m A n A n l1 l2 HA EL I2); lia.
  - apply (live_apart RT AF Σ m (A, n) (A', n') HA); [eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact IL]
      | eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; right; exact IR]| intros E; injection E; lia].
  - apply (live_apart RT AF Σ m (A, n) (A', n') HA); [eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact IL]
      | eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; right; exact IR]| intros E; injection E; lia].
Qed.

(* [comment removed for export] *)
Lemma lblock_not_rest : forall Σ m L REST A n usp a, ART RT Σ m -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> In (A, n) L -> A <= a < A + n -> ~ aclient REST (rt_frames RT Σ) usp a.
Proof using AF.
  intros Σ m L REST A n usp a HA HP HR HU IL Ha H.
  assert (INl : In (A, n) (rt_live RT Σ)) by (eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact IL]).
  pose proof (af_live_range RT AF Σ m A n HA INl) as (R0 & R1 & R2).
  destruct H as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p' & n' & Hin' & Hx). pose proof (proj1 (Forall_forall _ _) HR _ Hin') as P'. cbn [snd] in P'.
    destruct (lrest_apart Σ m L REST A n p' n' HA HP IL Hin' ltac:(lia) P'); lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k HA Hin) as (_ & _ & _ & R3). destruct (R3 A n INl); lia.
  - destruct H as (f & k & Hin & Hf). pose proof (af_fshadow_apart RT AF Σ m f k HA Hin) as (SL & _). destruct (SL A n INl); lia.
Qed.

(* [comment removed for export] *)
Definition lh_insert_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (L REST : list (Z * Z)) (lh : Z) (g : lh_geo) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : Z) (L' : list (Z * Z)) (B' : Z) (g' : lh_geo) (bks' : list (list (bptr * Z))) (lb' : byte),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 v) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp REST (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' lb' canary /\ lh_repE GOBJ m' L' lh B' g' bks') c
       /\ Permutation (rt_live RT Σ') (L' ++ REST) /\ Z.of_nat (length L') <= Z.of_nat (length L) + 1
       /\ g_items g <= g_items g' <= g_items g + 1 /\ g_na g <= g_na g' <= 2 * g_na g
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ (v = 0 \/ DVerr GOBJ v).

Definition lh_insert_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (L REST : list (Z * Z)) (lh B data : Z) (g : lh_geo) (bks : list (list (bptr * Z))),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 352 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_lh_insert (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_lhi_realloc, e_lh_insert); (SITE_lhi_malloc, e_lh_insert); (SITE_cr_realloc, e_CRYPTO_realloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_lhi_realloc, e_CRYPTO_realloc); (SITE_lhi_malloc, e_CRYPTO_malloc); (SITE_cr_realloc, e_realloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  lh_repE GOBJ m L lh B g bks -> Permutation (rt_live RT Σ) (L ++ REST) -> Forall (fun x => 0 < snd x) REST -> DVerr GOBJ data -> g_items g + 1 < LH_KMAX ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_lh_insert m)))
      (lh_insert_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary L REST lh g).

Theorem lh_insert_cps : lh_insert_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary L REST lh B data g bks
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV (REP & PERML & ALN) PERM RPOS DVD ITEMS.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB. pose proof G as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 352 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-192) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  (* [comment removed for export] *)
  assert (INL : forall x, In x L -> In x (rt_live RT Σ)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; left; exact Hx]).
  assert (INLH : In (lh, 104) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
  assert (INB : In (B, 8 * g_na g) (rt_live RT Σ)) by (apply INL; eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
  destruct (af_acc_live RT AF Σ m lh 104 ART0 INLH) as [WRL ACL]. pose proof (af_live_range RT AF Σ m lh 104 ART0 INLH) as (L0 & LLO & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m lh 104 ART0 INLH ltac:(lia)) as LHI.
  destruct g as [nn na p pmax items]. cbn [g_nn g_na g_p g_pmax g_items] in *.
  unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  assert (ALL : lh mod 8 = 0).
  { pose proof (proj1 (Forall_forall _ _) ALN (lh, 104) ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity])) as X. cbn [fst] in X. Z.div_mod_to_equations. lia. }
  assert (NN : 0 < nn < 2^31) by lia. assert (IT : 0 <= items < 2^40) by (unfold LH_KMAX in *; lia).
  assert (LO1 : lh + 104 <= lo) by lia. assert (LO2 : lo <= bv_unsigned sp - 192) by (fold usp; unfold RT_STACK in *; lia). assert (HT1 : bv_unsigned sp <= 2 ^ 47) by (fold usp; unfold USTACK_TOP in *; lia).
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (LO3 : lo <= bv_unsigned sp - 304) by (fold usp; unfold RT_STACK in *; lia).
  pose proof DVD as (KAL & DLO & DHI & _). unfold IMG_UT_LO, IMG_UT_HI in DLO, DHI.
  assert (UTLO : IMG_UT_HI <= lo) by (unfold IMG_UT_HI, SEGTOP_A in *; lia). assert (KLO : data + 8 <= lo) by (unfold SEGTOP_A in *; lia).
  assert (KSEP : data + 8 <= lh \/ lh + 104 <= data) by (left; lia).
  (* [comment removed for export] *)
  assert (TAIL : forall (Σ1 : rts RT) (m1 : mem) (L1 : list (Z * Z)) (B1 nn1 na1 p1 pmax1 : Z) (bks1 : list (list (bptr * Z))) (jl jh : list byte)
      (ra' u0 u1 u2 s1' b0 b1 b2 b3 b4 b5 b6 b7 s3' s5' s10' s11' u3 u4 u5 u6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (c1 : config),
    ART RT Σ1 m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -192) ->
    rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_cg RT Σ1 = rt_cg RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ ->
    Z.of_nat (length (rt_live RT Σ1)) <= Z.of_nat (length (rt_live RT Σ)) ->
    rw_cells asegs m1 (bv_unsigned sp + -192) (CB 80 jl :: CB 8 jh :: lhi_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    lh_rep asegs LH_CEIL (DVerr GOBJ) m1 (ownL L1) ERR_FNS_A lh (bp lh) (bp B1) B1 (8 * na1) (mkGeo nn1 na1 p1 pmax1 items) bks1 ->
    Permutation L1 ((lh, 104) :: (B1, 8 * na1) :: map (fun x => (snd x, 24)) (concat bks1)) -> Forall (fun x => fst x mod 16 = 0) L1 ->
    Permutation (rt_live RT Σ1) (L1 ++ REST) -> Z.of_nat (length L1) <= Z.of_nat (length L) -> na <= na1 <= 2 * na ->
    cl_env m1 lb canary -> uw_chain m1 sp s0 outer ->
    rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m1 ->
    ASTA RT Σ1 PMc (eq (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -192)) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1' b0 b1 b2 b3 b4 b5 b6 b7
                                 (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) s5' s3'
                                 (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10' s11' u3 u4 u5 u6)
                            F1 (Z_to_bv 64 LHI_SPLIT_EXIT) fc1 None m1 (seg_rom asegs))) c1 ->
    realizes asegs c1 T).
  { intros Σ1 m1 L1 B1 nn1 na1 p1 pmax1 bks1 jl jh ra' u0 u1 u2 s1' b0 b1 b2 b3 b4 b5 b6 b7 s3' s5' s10' s11' u3 u4 u5 u6 F1 fc1 c1
           ART1 MI1 ST1 FRS1 SP1 CG1 CR1 LEN1 FR1 REP1 PERML1 ALN1 PERM1 LL1 NA1 ENV1 UWC1 PRES1 Hc1.
    pose proof REP1 as (G_1 & OL_1 & RL_1 & (y40 & y48 & err1 & pad1 & SC1) & OB_1 & RB_1 & LENB1 & CH1 & EMP1 & ND1).
    pose proof (lh_geo_bounds _ G_1) as GB1. pose proof G_1 as (G1_1 & G1_2 & G1_3 & G1_4 & G1_5 & G1_6). cbn [g_nn g_na g_p g_pmax g_items] in *.
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INL1 : forall x, In x L1 -> In x (rt_live RT Σ1)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; left; exact Hx]).
    assert (INR1 : forall x, In x REST -> In x (rt_live RT Σ1)) by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact PERM1| apply in_or_app; right; exact Hx]).
    assert (INLH1 : In (lh, 104) (rt_live RT Σ1)) by (apply INL1; eapply Permutation_in; [apply Permutation_sym; exact PERML1| left; reflexivity]).
    assert (INB1 : In (B1, 8 * na1) (rt_live RT Σ1)) by (apply INL1; eapply Permutation_in; [apply Permutation_sym; exact PERML1| right; left; reflexivity]).
    pose proof (live_lapart RT AF Σ1 m1 L1 ART1 INL1) as LAP1.
    destruct (af_client_consts RT AF Σ1 m1 ART1) as (_ & SHC1 & _ & _ & UT1).
    destruct (af_acc_live RT AF Σ1 m1 lh 104 ART1 INLH1) as [_ ACL1]. destruct (af_acc_live RT AF Σ1 m1 B1 (8 * na1) ART1 INB1) as [_ ACB1].
    pose proof (af_live_range RT AF Σ1 m1 B1 (8 * na1) ART1 INB1) as (B0 & BLO1 & _). rewrite SP1 in BLO1.
    pose proof (afp_live_hi RT GOBJ AFP Σ1 m1 B1 (8 * na1) ART1 INB1 ltac:(lia)) as BHI.
    pose proof (proj1 (Forall_forall _ _) ALN1 (B1, 8 * na1) ltac:(eapply Permutation_in; [apply Permutation_sym; exact PERML1| right; left; reflexivity])) as ALB. cbn [fst] in ALB.
    assert (ALB8 : B1 mod 8 = 0) by (clear - ALB; Z.div_mod_to_equations; lia). assert (BLO2 : B1 + 8 * na1 <= lo) by lia.
    destruct (dverr_cells RT GOBJ AF AFP Σ1 m1 data ART1 DVD) as ((kw & KC1) & KA1 & _).
    pose proof (af_acc_stack RT AF Σ1 m1 (usp - 192) 192 ART1 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)) as ACCF1.
    destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L1 LAP1) REP1) as (S_LB & S_N & S_X & S_F). cbn [g_na g_nn g_p g_pmax g_items] in S_LB, S_N.
    assert (NODESF : forall q A, In (q, A) (concat bks1) -> In (A, 24) L1 /\ A + 24 <= lo /\ 0x10007fff8000 <= A /\ A mod 16 = 0 /\ (A + 24 <= lh \/ lh + 104 <= A)).
    { intros q A Hq. destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP1 q A Hq) as [O _].
      pose proof (af_live_range RT AF Σ1 m1 A 24 ART1 (INL1 _ O)) as (_ & R1 & _). pose proof (afp_live_hi RT GOBJ AFP Σ1 m1 A 24 ART1 (INL1 _ O) ltac:(lia)) as R2.
      pose proof (proj1 (Forall_forall _ _) ALN1 (A, 24) O) as R3. cbn [fst] in R3.
      apply in_concat in Hq. destruct Hq as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & <-). destruct (S_N _ q A Hi Hin) as [R4 _].
      split; [exact O|]. split; [lia|]. split; [exact R2|]. split; [exact R3| exact R4]. }
    assert (NODES1 : forall q A, In (q, A) (concat bks1) -> acc asegs m1 A 24 /\ A mod 8 = 0 /\ A + 24 <= lo).
    { intros q A Hq. destruct (NODESF q A Hq) as (O & X2 & X3 & X4 & X5). destruct (af_acc_live RT AF Σ1 m1 A 24 ART1 (INL1 _ O)) as [_ X1]. split; [exact X1|].
      split; [clear - X4; Z.div_mod_to_equations; lia| exact X2]. }
    assert (NHI1 : forall q A, In (q, A) (concat bks1) -> 0x10007fff8000 <= A) by (intros q A Hq; destruct (NODESF q A Hq) as (_ & _ & X3 & _); exact X3).
    assert (DVF1 : forall d, DVerr GOBJ d -> (exists e : word, ro_cells asegs m1 d [C8 e]) /\ acc asegs m1 d 8).
    { intros d Hd. destruct (dverr_cells RT GOBJ AF AFP Σ1 m1 d ART1 Hd) as (X1 & X2 & _). exact (conj X1 X2). }
    (* [comment removed for export] *)
    assert (OFFL : forall A n a, In (A, n) L1 -> A <= a < A + n -> ~ aclient REST (rt_frames RT Σ) usp a).
    { intros A n a Hin Ha. rewrite <- FRS1. apply (lblock_not_rest Σ1 m1 L1 REST A n usp a ART1 PERM1 RPOS ltac:(lia) Hin Ha). }
    assert (OFFS : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 304).
    { intros a Ha. apply (cl_split RT AF Σ1 m1 usp 304 a ART1 ltac:(lia) ltac:(lia)). rewrite FRS1.
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR1| intros e He; exact He| lia]. }
    assert (INLHL : In (lh, 104) L1) by (eapply Permutation_in; [apply Permutation_sym; exact PERML1| left; reflexivity]).
    assert (INBL : In (B1, 8 * na1) L1) by (eapply Permutation_in; [apply Permutation_sym; exact PERML1| right; left; reflexivity]).
    pose proof (lhi_wg ra' sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 s1' b0 b1 b2 b3 b4 b5 b6 b7 s3' s5' s10' s11' u3 u4 u5 u6 F1 fc1 m1 GOBJ L1 lh B1 (mkGeo nn1 na1 p1 pmax1 items) bks1 data lo kw
                  jl jh ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  REP1 LAP1 ACL1 ALL LO1 LHI ACB1 ALB8 BLO2 BHI NODES1 NHI1 DVF1
                  UTLO KC1 KA1 KAL KLO DVD KSEP FR1 ACCF1 SPA UT1 SHC1 ST1 LO0 LO3 HT1 MI1) as W.
    cl_lift W Hc1 c2 Hc2.
    destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m3 & i & ns1 & ns2 & rn & h
                                                  & HI & ENTH & MI3 & WM3 & ARMS) & Hc2'). clear Hc2.
    cbn [g_nn g_na g_p g_pmax g_items] in HI, ARMS.
    destruct ARMS as [(-> & S1 & CRN & -> & MU3 & FR3 & ST3 & REP3) | (pk & Ak & d0 & rest & -> & DVd0 & -> & MU3 & ST3 & REP3)].
    + (* [comment removed for export] *)
      assert (LI : (Z.to_nat i < length bks1)%nat) by lia.
      assert (MU3' : munch ([] ++ [(usp - 304, usp)]) m1 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
      pose proof (cl_seg_ART RT AF Σ1 m1 m3 usp 304 [] ART1 ltac:(rewrite SP1; lia) ltac:(lia) MU3' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
      assert (ENV3 : cl_env m3 lb canary).
      { apply (cl_env_seg _ m1 m3 lb canary ENV1 MU3). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
        pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
      assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m3) by (intros a Ha; apply MU3; cbn [outside]; unfold USTACK_TOP in *; lia).
      pose proof (uw_chain_agree outer m1 m3 sp s0 UWC1 AGs3) as UWC3.
      assert (PRES3 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
      { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply MU3. cbn [outside]. split; [| exact I]. destruct (OFFS _ Ha); lia. }
      assert (FR16 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
      { unfold lhi_saved in FR3. change (CB 80 jl :: C8 h :: ?sv) with ((CB 80 jl :: C8 h :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]) ++ [C8 s0; C8 ra]) in FR3.
        pose proof (rw_cells_skip m3 _ _ _ FR3) as X. cbn [cells_size csize Nat.add] in X. fold usp in X. replace (usp + -192 + 176) with (usp - 16) in X by lia. exact X. }
      destruct (cl_chain_call (rt_cg RT Σ) e_lh_insert e_CRYPTO_malloc SITE_lhi_malloc m3 m3 ra s0 sp (Z_to_bv 64 (usp + -192)) outer CTX
                  (proj1 CGH (SITE_lhi_malloc, e_lh_insert) ltac:(right; left; reflexivity)) (proj2 CGH (SITE_lhi_malloc, e_CRYPTO_malloc) ltac:(right; left; reflexivity)) UWC3 ltac:(intros a _; reflexivity)
                  FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
      (* [comment removed for export] *)
      apply (C_CM Σ1 PMc (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
               (Z_to_bv 64 24) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 130) d3 d4 d5 d6 d7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5' s3'
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10' s11' v3 v4 v5 v6
               F2 fc2 m3 24 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART3 MI3).
      { fold usp in SPA. cl_call_ok EU1 ST3 LOW1 SPA 12. }
      { rewrite EU1. unfold RT_STACK in *. lia. }
      { rewrite CG1. rewrite (unsigned_lit SITE_lhi_malloc) by (unfold SITE_lhi_malloc; lia). exact CTXc. }
      { exact UWCc. }
      { clear - CGH CG1. rewrite CG1. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
      { lia. }
      { rewrite CR1. unfold mcost. cbn. lia. }
      { exact ENV3. }
      { exact Hc2'. }
      clear Hc2'. intros c3 (Σ2 & qn & Hc3 & LV3 & FRS3 & SP3 & CR3 & Q0 & Q16 & QU & CG3).
      destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ENV4 & WRQ & ACQ) & Hc3'). clear Hc3.
      destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_lhi_malloc) in Hc3' by (unfold SITE_lhi_malloc; lia).
      (* [comment removed for export] *)
      assert (INL2 : forall x, In x L1 -> In x (rt_live RT Σ2)) by (intros x Hx; rewrite LV3; right; exact (INL1 _ Hx)).
      assert (INQ : In (qn, 24) (rt_live RT Σ2)) by (rewrite LV3; left; reflexivity).
      assert (FRESHQ : forall p2 n2, In (p2, n2) (rt_live RT Σ1) -> qn + 24 <= p2 \/ p2 + n2 <= qn) by (intros p2 n2 H; exact (wg_live_apart RT AF Σ2 m4 [] qn 24 (rt_live RT Σ1) p2 n2 ART4 LV3 H)).
      pose proof (af_live_range RT AF Σ2 m4 qn 24 ART4 INQ) as (_ & QLO & _). rewrite SP3, SP1 in QLO.
      pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 qn 24 ART4 INQ ltac:(lia)) as QHI.
      assert (AG4 : forall a k, usp + -192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
      { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [outside]. unfold G_ALLOW_CUST, USTACK_TOP in *. split; [lia| exact I]. }
      fold usp in MU3, FR3, ST3.
      eassert (FR4 : rw_cells asegs m4 _ _).
      { apply (rw_cells_agree asegs m3 m4 _ _ FR3); [| exact WM4]. apply AG4; cbn [cells_size csize Nat.add lhi_saved]; unfold USTACK_TOP in *; lia. }
      assert (AGL4 : forall P : Z -> Prop, (forall x, P x -> exists A n, In (A, n) L1 /\ n <= 64512 /\ A <= x < A + n) -> agree_on P m3 m4).
      { intros P HP a Ha. destruct (HP _ Ha) as (A & n & Hin & Hn & Hx). apply PRES4.
        - right; right; left. exists A, n. split; [exact (INL1 _ Hin)| exact Hx].
        - cbn [outside]. pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 A n ART3 (INL1 _ Hin) Hn). unfold G_ALLOW_CUST. split; [lia| exact I]. }
      assert (AGP4 : forall P : Z -> Prop, agree_on P m3 m4 -> LhRep.agree_on asegs P m3 m4).
      { intros P AG a Ha HP. assert (E : m4 (wa a) = m3 (wa a)) by (apply AG; unfold wa; rewrite unsigned_lit by lia; exact HP). split; [exact E| intros Hw; apply WM4; exact Hw]. }
      assert (REP4 : lh_rep asegs LH_CEIL (DVerr GOBJ) m4 (ownL L1) ERR_FNS_A lh (bp lh) (bp B1) B1 (8 * na1) (mkGeo nn1 na1 p1 pmax1 items) bks1).
      { eapply lh_rep_agree; [exact REP3| | intros ? ? ? ? _ X; exact X]. apply AGP4. apply AGL4. intros x [Hx|[Hx|(q & A & Hq & Hx)]].
        - exists lh, 104. split; [exact INLHL|]. lia.
        - exists B1, (8 * na1). cbn [g_na] in Hx. split; [exact INBL|]. lia.
        - destruct (NODESF q A Hq) as (O & _). exists A, 24. split; [exact O|]. lia. }
      assert (S1_4 : lseg asegs LH_CEIL (DVerr GOBJ) m4 (ownL L1) (B1 + 8 * i) ns1 rn).
      { eapply lseg_agree; [exact S1| | intros ? ? _ X; exact X]. apply AGP4. apply AGL4. intros x Hx.
        destruct (lseg_fp_where _ _ _ Hx) as [H8|(q & A & Hq & HA8)].
        - exists B1, (8 * na1). split; [exact INBL|]. lia.
        - pose proof (in_concat_nth bks1 _ _ LI ltac:(rewrite ENTH; apply in_or_app; left; exact Hq)) as IQ. destruct (NODESF q A IQ) as (O & _). exists A, 24. split; [exact O|]. lia. }
      assert (RNP : exists pa na', In (pa, na') L1 /\ pa mod 8 = 0 /\ pa <= rn /\ rn + 8 <= pa + na' /\ (rn + 8 <= lh \/ lh + 104 <= rn) /\ na' <= 64512).
      { destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & EE & ->)].
        - exists B1, (8 * na1). split; [exact INBL|]. split; [exact ALB8|]. lia.
        - pose proof (in_concat_nth bks1 _ _ LI ltac:(rewrite ENTH, EE; apply in_or_app; left; apply in_or_app; right; left; reflexivity) : In (q, A) (concat bks1)) as IQ.
          destruct (NODESF q A IQ) as (O & X2 & X3 & X4 & X5). exists A, 24. split; [exact O|]. split; [clear - X4; Z.div_mod_to_equations; lia|]. lia. }
      destruct RNP as (pa & na' & INP & PAL & PA1 & PA2 & SRL & SMALL).
      destruct (af_acc_live RT AF Σ2 m4 pa na' ART4 (INL2 _ INP)) as [_ PACC4].
      pose proof (af_live_range RT AF Σ2 m4 pa na' ART4 (INL2 _ INP)) as (PA0 & PLO & _). rewrite SP3, SP1 in PLO.
      pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 pa na' ART4 (INL2 _ INP) SMALL) as PHI.
      pose proof (FRESHQ pa na' (INL1 _ INP)) as SQP. pose proof (FRESHQ lh 104 INLH1) as SQL.
      assert (CRN4 : rw_cells asegs m4 rn [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_agree asegs m3 m4 _ _ CRN); [| exact WM4]. apply AGL4. cbn [cells_size csize Nat.add]. intros x Hx. exists pa, na'. split; [exact INP|]. lia. }
      destruct (af_acc_live RT AF Σ2 m4 lh 104 ART4 (INL2 _ INLHL)) as [_ ACL4].
      pose proof REP4 as (_ & _ & _ & (z40 & z48 & err4 & pad4 & SC4) & _).
      destruct (wr_at_rw_CB m4 qn 24 WRQ ltac:(lia)) as (jq & NQ). change (Z.to_nat 24) with 24%nat in NQ.
      pose proof (lhi_w5 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 s3' s5' s10' s11' w3 w4 w5 w6 F4 fc4 m4 lo lh qn rn data B1 nn1 na1 p1 pmax1 items pa na'
                    z40 z48 err4 pad4 h jq jl ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    SC4 ltac:(unfold LH_KMAX in *; lia) ACL4 ALL LHI LO1 NQ ACQ ltac:(clear - Q16; Z.div_mod_to_equations; lia) QHI ltac:(lia) CRN4 PACC4 PAL ltac:(lia) PA1 PA2
                    ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SRL FR4 ST4 LO0 LO2 HT1 MI4) as W5.
      cl_lift W5 Hc3' c4 Hc4.
      apply Hk. exists Σ2, 0, ((qn, 24) :: L1), B1, (mkGeo nn1 na1 p1 pmax1 (items + 1)), (lupd (Z.to_nat i) (ns1 ++ [(bp qn, qn)]) bks1), (Z_to_bv 8 1).
      split.
      { apply (ASTA_conseq RT Σ2 PMc _ _ c4 Hc4). intros ms4 (w0' & w1' & w2' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & w3' & w4' & w5' & w6' & F5 & fc5 & m5 & -> & MU5 & WM5 & MI5 & ST5 & ND1' & NX1 & NH1 & RN1 & SC5).
        exists m5. fold usp in ST5.
        split; [exists w0', w1', w2', e1', e2', e3', e4', e5', e6', e7', w3', w4', w5', w6', F5, fc5; reflexivity|].
        assert (ART5 : ART RT Σ2 m5).
        { apply (af_frame RT AF Σ2 m4 m5 usp ART4 ltac:(rewrite SP3, SP1; lia)); [| exact WM5]. intros a Ha. apply MU5. cbn [outside].
          split; [| split; [| split; [| exact I]]]; intros X; apply Ha; right; right; left.
          - exists qn, 24. split; [exact INQ| lia].
          - exists pa, na'. split; [exact (INL2 _ INP)| lia].
          - exists lh, 104. split; [exact (INL2 _ INLHL)| lia]. }
        split; [exact (conj ART5 (conj MI5 ST5))|].
        split.
        { intros a Ha Ho. rewrite <- (PRES3 a Ha Ho).
          assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (rewrite FRS1; apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact INR1| intros e He; exact He| lia]).
          rewrite (MU5 a); [apply PRES4; [apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; exact He| intros e He; exact He| lia]| exact Ho]|].
          cbn [outside]. split; [| split; [| split; [| exact I]]].
          - exact (wg_newchunk_apart RT AF Σ1 Σ2 m4 [(qn, 24)] qn 24 usp (bv_unsigned a) ART4 LV3 ltac:(left; reflexivity) FRS3 SP3 ltac:(rewrite SP1; lia) ltac:(lia) Ha1).
          - intros X. exact (OFFL pa na' (bv_unsigned a) INP ltac:(lia) Ha).
          - intros X. exact (OFFL lh 104 (bv_unsigned a) INLHL ltac:(lia) Ha). }
        split.
        { apply (cl_env_seg _ m4 m5 _ canary ENV4 MU5). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
          pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
        split; [| split].
        - apply (lh_rep_add_node GOBJ m4 m5 L1 lh B1 (mkGeo nn1 na1 p1 pmax1 items) bks1 i ns1 rn qn data h LAP1 REP4 ltac:(cbn [g_nn]; lia)
                   ltac:(rewrite ENTH; apply app_nil_r) S1_4 ltac:(cbn [g_items]; lia) ltac:(intros A n Hin; exact (FRESHQ A n (INL1 _ Hin))) Q0
                   ltac:(unfold LH_CEIL, USTACK_TOP in *; lia) DVD ND1' NX1 NH1 RN1 ltac:(exists z40, z48, err4, pad4; exact SC5)).
          eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU5 WM5)|]. intros a (FP & NR & NL). cbn [outside].
          split; [| split; [exact NR| split; [intros X; apply NL; lia| exact I]]]. intros X.
          destruct FP as [FP1|[FP1|(q & A & Hq & FP1)]]; [apply NL; exact FP1| cbn [g_na] in FP1; destruct (FRESHQ B1 (8 * na1) INB1); lia|].
          destruct (NODESF q A Hq) as (O & _). destruct (FRESHQ A 24 (INL1 _ O)); lia.
        - cbn [g_na]. eapply Permutation_trans; [apply perm_skip; exact PERML1|].
          eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
          rewrite app_nil_r in ENTH. rewrite <- ENTH. eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply concat_lupd_snoc; exact LI]. cbn [map snd]. apply Permutation_refl.
        - constructor; [cbn [fst]; exact Q16| exact ALN1]. }
      cbn [g_items g_na length]. split; [rewrite LV3; apply perm_skip; exact PERM1|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [rewrite FRS3; exact FRS1|]. split; [rewrite SP3; exact SP1|]. split; [rewrite CR3, CR1; unfold mcost; cbn; lia|]. split; [rewrite CG3; exact CG1|].
      left; reflexivity.
    + (* [comment removed for export] *)
      assert (LI : (Z.to_nat i < length bks1)%nat) by lia.
      pose proof (in_concat_nth bks1 _ _ LI ltac:(rewrite ENTH; apply in_or_app; right; left; reflexivity) : In (pk, Ak) (concat bks1)) as INK.
      destruct (NODESF pk Ak INK) as (OK & KLO2 & KHI & K16 & KSL).
      assert (ART3 : ART RT Σ1 m3).
      { apply (af_frame RT AF Σ1 m1 m3 (usp - 304) ART1 ltac:(lia)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
        split; [| split; [| exact I]].
        - intros X. apply Ha. left. unfold USTACK_TOP in *. lia.
        - intros X. apply Ha. right; right; left. exists Ak, 24. split; [exact (INL1 _ OK)| lia]. }
      apply Hk. exists Σ1, d0, L1, B1, (mkGeo nn1 na1 p1 pmax1 items), bks1, lb.
      split.
      { apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2'). intros ms <-. exists m3.
        split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2; reflexivity|].
        split; [exact (conj ART3 (conj MI3 ST3))|].
        split. { intros a Ha Ho. rewrite <- (PRES1 a Ha Ho). apply MU3. cbn [outside]. split; [| split; [| exact I]].
                 - destruct (OFFS _ Ha); lia.
                 - intros X. exact (OFFL Ak 24 (bv_unsigned a) OK ltac:(lia) Ha). }
        split. { apply (cl_env_seg _ m1 m3 lb canary ENV1 MU3). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
                 pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
        split; [exact REP3|]. split; [exact PERML1| exact ALN1]. }
      cbn [g_items g_na]. split; [exact PERM1|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FRS1|]. split; [exact SP1|]. split; [exact CR1|]. split; [exact CG1|].
      right. exact DVd0. }
  (* [comment removed for export] *)
  pose proof (lhi_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lh data B nn na p pmax items x40 x48 err pad
                eq_refl eq_refl SC NN IT ACL ALL LHI LO1 UT SHC ST LO0 LO2 HT1 MI0) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (jl & m1 & -> & MU1 & WM1 & MI1 & FR1 & SC1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, FR1, Hc1'. unfold lhi_frame in FR1.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 192) ART0 ltac:(lia)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [| split; [| exact I]].
    - intros X. apply Ha. left. unfold USTACK_TOP in *. lia.
    - intros X. apply Ha. right; right; left. exists lh, 104. split; [exact INLH| lia]. }
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [outside]; unfold USTACK_TOP in *; lia).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWC1.
  assert (INLHL0 : In (lh, 104) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| left; reflexivity]).
  assert (INBL0 : In (B, 8 * na) L) by (eapply Permutation_in; [apply Permutation_sym; exact PERML| right; left; reflexivity]).
  assert (OFFL0 : forall A n a, In (A, n) L -> A <= a < A + n -> ~ aclient REST (rt_frames RT Σ) usp a).
  { intros A n a Hin Ha. apply (lblock_not_rest Σ m L REST A n usp a ART0 PERM RPOS ltac:(lia) Hin Ha). }
  assert (OFFS0 : forall a, aclient REST (rt_frames RT Σ) usp a -> usp <= a \/ a < usp - 304).
  { intros a Ha. apply (cl_split RT AF Σ m usp 304 a ART0 ltac:(lia) ltac:(lia)).
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [| intros e He; exact He| lia]. intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hx]. }
  assert (PRES_1 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m1).
  { intros a Ha Ho. apply MU1. cbn [outside]. split; [destruct (OFFS0 _ Ha); lia|]. split; [| exact I]. intros X. exact (OFFL0 lh 104 (bv_unsigned a) INLHL0 ltac:(lia) Ha). }
  assert (ENV_1 : cl_env m1 lb canary).
  { apply (cl_env_seg _ m m1 lb canary ENV MU1). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
    pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
  destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L (live_lapart RT AF Σ m L ART0 INL)) REP) as (S_LB & S_N & S_X & S_F).
  cbn [g_na g_nn g_p g_pmax g_items] in S_LB, S_N.
  assert (NODESF0 : forall q A, In (q, A) (concat bks) -> In (A, 24) L /\ A + 24 <= lo /\ 0x10007fff8000 <= A /\ A mod 16 = 0 /\ (A + 24 <= lh \/ lh + 104 <= A)).
  { intros q A Hq. destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP q A Hq) as [O _].
    pose proof (af_live_range RT AF Σ m A 24 ART0 (INL _ O)) as (_ & R1 & _). pose proof (afp_live_hi RT GOBJ AFP Σ m A 24 ART0 (INL _ O) ltac:(lia)) as R2.
    pose proof (proj1 (Forall_forall _ _) ALN (A, 24) O) as R3. cbn [fst] in R3.
    apply in_concat in Hq. destruct Hq as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & <-). destruct (S_N _ q A Hi Hin) as [R4 _].
    split; [exact O|]. split; [lia|]. split; [exact R2|]. split; [exact R3| exact R4]. }
  (* [comment removed for export] *)
  assert (REP1 : lh_rep asegs LH_CEIL (DVerr GOBJ) m1 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * na) (mkGeo nn na p pmax items) bks).
  { eapply (lh_rep_upd asegs LH_CEIL (DVerr GOBJ) m m1 (ownL L) (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * na) _ _ bks bks (fun _ => False) REP); try reflexivity; try assumption.
    - intros i. right. intros X. exact X.
    - exists x40, x48, (Z_to_bv 64 0), pad. unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk.
      cbn [g_nn g_na g_p g_pmax g_items]. exact SC1.
    - intros q A n nm _ X. exact X.
    - intros i Hi [].
    - intros i Hi _. split; [reflexivity|]. eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU1 WM1)|].
      cbn [g_na] in Hi. pose proof (af_live_range RT AF Σ m B (8 * na) ART0 INB) as (_ & RB1 & _).
      intros a [Ha|(q & A & Hq & Ha)]; cbn [outside]; [unfold RT_STACK, STACK_WIN in *; split; [lia|]; split; [lia| exact I]|].
      assert (LI : (Z.to_nat i < length bks)%nat) by lia. destruct (NODESF0 q A (in_concat_nth bks _ _ LI Hq)) as (_ & X2 & _ & _ & X5). unfold RT_STACK in *. lia. }
  destruct (512 <=? items * 256 / nn) eqn:LT.
  - (* [comment removed for export] *)
    assert (LOAD : 2 * nn <= items).
    { apply Z.leb_le in LT. pose proof (Z.mul_div_le (items * 256) nn ltac:(lia)) as X. clear - LT X NN. nia. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m1 _ [] 88 jl _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in FR1.
    lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: CB 8 ?bs :: ?sv) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: CB 8 bs :: sv) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ CB 8 bs :: sv) in FR1 end.
    apply cb8_c8_in in FR1.
    lazymatch type of FR1 with rw_cells _ _ _ (?pre ++ C8 ?hsv :: ?sv) => set (hs := hsv) in FR1; change (pre ++ C8 hs :: sv) with ((pre ++ [C8 hs]) ++ sv) in FR1 end.
    apply (proj1 (rw_cells_app _ _ _ _)) in FR1. destruct FR1 as [FRL1 FRS1]. cbn [app] in FRL1. cbn [cells_size csize Nat.add app Z.of_nat Pos.of_succ_nat Pos.succ] in FRS1.
    replace (usp + -192 + 88) with (usp + -104) in FRS1 by lia.
    epose proof (lhi_w1 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 _ _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m1 lo lh data B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad
                  _ _ _ _ _ _ _ _ _ _ hs SC1 ltac:(lia) ltac:(lia) ltac:(lia) (proj2 (af_acc_live RT AF Σ m1 lh 104 ART1 INLH)) ALL LHI LO1 FRL1 ST1 LO0 LO2 HT1 MI1) as W1.
    cl_lift W1 Hc1' c2 Hc2.
    destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & -> & MU2 & WM2 & MI2 & FRL2 & ST2) & Hc2'). clear Hc2. fold usp in MU2, ST2, FRL2, Hc2'.
    assert (MU2' : munch ([] ++ [(usp - 192, usp)]) m1 m2) by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside app]; intros; lia).
    pose proof (cl_seg_ART RT AF Σ m1 m2 usp 192 [] ART1 ltac:(lia) ltac:(lia) MU2' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
    assert (ENV2 : cl_env m2 lb canary).
    { apply (cl_env_seg _ m1 m2 lb canary ENV_1 MU2). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
      pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
    assert (AGs2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; apply MU2; cbn [outside]; unfold USTACK_TOP in *; lia).
    pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 AGs2) as UWC2.
    assert (PRES_2 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m2).
    { intros a Ha Ho. rewrite <- (PRES_1 a Ha Ho). apply MU2. cbn [outside]. split; [destruct (OFFS0 _ Ha); lia| exact I]. }
    assert (BELOW2 : forall P : Z -> Prop, (forall x, P x -> x < usp - 192) -> agree_on P m1 m2) by (intros P HP a Ha; apply MU2; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
    assert (FRS2 : rw_cells asegs m2 (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRS1); [| exact WM2]. intros a Ha. apply MU2. cbn [cells_size csize Nat.add outside] in Ha |- *. split; [lia| exact I]. }
    assert (SC2 : rw_cells asegs m2 lh (lhs_cells B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad)).
    { apply (rw_cells_agree asegs m1 m2 _ _ SC1); [| exact WM2]. apply BELOW2. cbn [cells_size csize Nat.add lhs_cells]. intros; lia. }
    assert (REP2 : lh_rep asegs LH_CEIL (DVerr GOBJ) m2 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * na) (mkGeo nn na p pmax items) bks).
    { eapply lh_rep_agree; [exact REP1| | intros ? ? ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU2 WM2)|].
      pose proof (af_live_range RT AF Σ m B (8 * na) ART0 INB) as (_ & RB1 & _).
      intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside g_na] in Ha |- *; (split; [| exact I]); [lia| lia|]. destruct (NODESF0 q A Hq) as (_ & X2 & _). lia. }
    destruct (af_acc_live RT AF Σ m2 lh 104 ART2 INLH) as [_ ACL2]. destruct (af_acc_live RT AF Σ m2 B (8 * na) ART2 INB) as [_ ACB2].
    pose proof (af_live_range RT AF Σ m2 B (8 * na) ART2 INB) as (B0 & BLO & _).
    pose proof (afp_live_hi RT GOBJ AFP Σ m2 B (8 * na) ART2 INB ltac:(lia)) as BHI.
    pose proof (proj1 (Forall_forall _ _) ALN (B, 8 * na) INBL0) as ALB. cbn [fst] in ALB. assert (ALB8 : B mod 8 = 0) by (clear - ALB; Z.div_mod_to_equations; lia).
    pose proof REP2 as (_ & _ & _ & _ & _ & _ & _ & CH2 & EMP2 & _). cbn [g_na g_nn] in CH2, EMP2.
    assert (FSP2 : rw_cells asegs m2 (usp + -144) (lhi_spill lh data)).
    { pose proof (rw_cells_skip m2 _ _ _ FRL2) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -192 + Z.of_nat 48) with (usp + -144) in X by lia.
      apply (proj1 (rw_cells_app _ _ _ _)) in X. destruct X as [X _]. exact X. }
    destruct (p + 1 <? pmax) eqn:LT2.
    + (* [comment removed for export] *)
      apply Z.ltb_lt in LT2. assert (LP : (Z.to_nat p < length bks)%nat) by lia.
      assert (SLN : Forall (fun A => A + 24 <= lh \/ lh + 104 <= A) (map snd (nth (Z.to_nat p) bks []))).
      { apply Forall_forall. intros A HA0. apply in_map_iff in HA0. destruct HA0 as ([q A'] & E & Hq). cbn [snd] in E. subst A'.
        destruct (NODESF0 q A (in_concat_nth bks _ _ LP Hq)) as (_ & _ & _ & _ & X). exact X. }
      assert (SLU : Forall (fun A => A + 24 <= usp - 192) (map snd (nth (Z.to_nat p) bks []))).
      { apply Forall_forall. intros A HA0. apply in_map_iff in HA0. destruct HA0 as ([q A'] & E & Hq). cbn [snd] in E. subst A'.
        destruct (NODESF0 q A (in_concat_nth bks _ _ LP Hq)) as (_ & X & _). lia. }
      assert (ACCS : forall X, In X (map snd (nth (Z.to_nat p) bks [])) -> acc asegs m2 X 24 /\ X mod 8 = 0 /\ 0x10007fff8000 <= X /\ X + 24 <= 2^47).
      { intros X HX. apply in_map_iff in HX. destruct HX as ([q X'] & E & Hq). cbn [snd] in E. subst X'.
        destruct (NODESF0 q X (in_concat_nth bks _ _ LP Hq)) as (O & X2 & X3 & X4 & _). destruct (af_acc_live RT AF Σ m2 X 24 ART2 (INL _ O)) as [_ X1].
        split; [exact X1|]. split; [clear - X4; Z.div_mod_to_equations; lia|]. unfold USTACK_TOP in *. lia. }
      epose proof (lhi_split ra (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp _ _ _ _ _ _ _ _ _ t3 t4 t5 t6 F fc m2 GOBJ L lh B nn na p (p + 1) pmax pmax na items data usp
                    x40 x48 (Z_to_bv 64 0) pad (nth (Z.to_nat p) bks [])
                    SC2 FSP2 (CH2 p ltac:(lia)) ltac:(rewrite <- (EMP2 nn ltac:(lia)); exact (CH2 nn ltac:(lia)))
                    (bucket_nsep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ p nn (ownL_apart L (live_lapart RT AF Σ m L ART0 INL)) REP2 ltac:(cbn [g_na]; lia) ltac:(cbn [g_na]; lia) ltac:(lia))
                    G2 G3 G4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ACL2 ALL LHI ltac:(unfold USTACK_TOP in *; lia) ACB2 ALB8 BHI ltac:(unfold USTACK_TOP in *; lia)
                    ACCS S_LB SLN (eq_sym (Z_to_bv_bv_unsigned sp)) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) SLU MI2) as WS.
      cl_lift WS Hc2' c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (ra3 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & stay' & moved' & -> & MI3 & WM3 & SC3 & CHS & CHM & PMsm & AG3) & Hc3'). clear Hc3.
      pose proof (split_munch2 lh _ _ _ m2 m3 AG3) as MU3.
      (* [comment removed for export] *)
      assert (W3CL : forall a, ((lh + 56 <= a < lh + 68) \/ split_W (B + 8 * p) (B + 8 * nn) (nth (Z.to_nat p) bks []) a) -> exists A n, In (A, n) L /\ A <= a < A + n /\ A + n <= lo /\ n <= 64512).
      { intros a [X|[X|[X|(q & A & Hq & X)]]].
        - exists lh, 104. split; [exact INLHL0|]. lia.
        - exists B, (8 * na). split; [exact INBL0|]. lia.
        - exists B, (8 * na). split; [exact INBL0|]. lia.
        - destruct (NODESF0 q A (in_concat_nth bks _ _ LP Hq)) as (O & X2 & _). exists A, 24. split; [exact O|]. lia. }
      assert (OUT3 : forall a, (forall A n, In (A, n) L -> A <= a < A + n -> A + n <= lo -> n <= 64512 -> False) -> outside ((lh + 56, lh + 68) :: split_ivs (B + 8 * p) (B + 8 * nn) (nth (Z.to_nat p) bks [])) a).
      { intros a Ha. cbn [outside]. split; [intros X| apply (proj2 (split_ivs_outside _ _ _ _)); intros X].
        - destruct (W3CL a (or_introl X)) as (A & n & Hin & Hx & Hlo & Hn). exact (Ha A n Hin Hx Hlo Hn).
        - destruct (W3CL a (or_intror X)) as (A & n & Hin & Hx & Hlo & Hn). exact (Ha A n Hin Hx Hlo Hn). }
      assert (ART3 : ART RT Σ m3).
      { apply (af_frame RT AF Σ m2 m3 usp ART2 ltac:(lia)); [| exact WM3]. intros a Ha. apply MU3. apply OUT3. intros A n Hin Hx _ _. apply Ha. right; right; left. exists A, n. split; [exact (INL _ Hin)| exact Hx]. }
      assert (PRES_3 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
      { intros a Ha Ho. rewrite <- (PRES_2 a Ha Ho). apply MU3. apply OUT3. intros A n Hin Hx _ _. exact (OFFL0 A n _ Hin Hx Ha). }
      assert (ENV3 : cl_env m3 lb canary).
      { apply (cl_env_seg _ m2 m3 lb canary ENV2 MU3). intros x Hx. apply OUT3. intros A n Hin HAx _ Hn. pose proof (afp_live_hi RT GOBJ AFP Σ m2 A n ART2 (INL _ Hin) Hn).
        pose proof (client_static_range _ (cl_cell_static _ Hx)). unfold SEGTOP_A in *. lia. }
      assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; apply OUT3; intros A n Hin HAx Hlo _; lia).
      pose proof (uw_chain_agree outer m2 m3 sp s0 UWC2 AGs3) as UWC3.
      assert (ST3 : stk asegs m3 lo (usp + -192)) by (apply (stk_munch _ m2 m3 lo (usp + -192) ST2 MU3 WM3); intros x Hx; apply OUT3; intros A n Hin HAx Hlo _; lia).
      eassert (FRL3 : rw_cells asegs m3 (usp + -192) _).
      { apply (rw_cells_agree asegs m2 m3 _ _ FRL2); [| exact WM3]. intros a Ha. apply MU3. apply OUT3. cbn [cells_size csize Nat.add app lhi_spill] in Ha. intros A n Hin HAx Hlo _. lia. }
      assert (FRS3 : rw_cells asegs m3 (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree asegs m2 m3 _ _ FRS2); [| exact WM3]. intros a Ha. apply MU3. apply OUT3. cbn [cells_size csize Nat.add] in Ha. intros A n Hin HAx Hlo _. lia. }
      lazymatch type of FRL3 with rw_cells _ _ _ (?X ++ ?Y ++ [C8 hs]) =>
        assert (FR3 : rw_cells asegs m3 (usp + -192) ((X ++ Y ++ [C8 hs]) ++ lhi_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
          by (apply rw_cells_app; split; [exact FRL3| cbn [cells_size csize Nat.add app lhi_spill Z.of_nat Pos.of_succ_nat Pos.succ]; replace (usp + -192 + 88) with (usp + -104) by lia; exact FRS3]);
        rewrite (app_assoc X Y [C8 hs]) in FR3; rewrite <- (app_assoc (X ++ Y) [C8 hs]) in FR3;
        apply (rw_cells_glue m3 _ [] (X ++ Y)) in FR3; apply (rw_cells_glue m3 _ [_] [C8 hs]) in FR3;
        cbn [cells_size csize Nat.add app lhi_spill cells_bytes cbytes] in FR3 end.
      (* [comment removed for export] *)
      destruct (split_raw asegs LH_CEIL (DVerr GOBJ) m2 m3 (ownL L) lh (bp lh) (bp B) B (8 * na) na bks p nn stay' moved' (ownL_apart L (live_lapart RT AF Σ m L ART0 INL))
                  (lh_rep_raw asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP2) ltac:(lia) ltac:(lia) (EMP2 nn ltac:(lia)) CHS CHM PMsm AG3) as [RAW3 PMC3].
      assert (EMP3 : forall i, nn + 1 <= i < na -> nth (Z.to_nat i) (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks)) [] = []).
      { intros i Hi. rewrite !nth_lupd_ne by lia. apply EMP2. lia. }
      pose proof (lh_rep_of_raw asegs LH_CEIL (DVerr GOBJ) m3 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * na) (mkGeo (nn + 1) na (p + 1) pmax items) _ RAW3
                    (lh_geo_ok_split (mkGeo nn na p pmax items) G LOAD LT2) ltac:(exists x40, x48, (Z_to_bv 64 0), pad; exact SC3) EMP3) as REP3.
      assert (PERML3 : Permutation L ((lh, 104) :: (B, 8 * na) :: map (fun x => (snd x, 24)) (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' bks))))).
      { eapply Permutation_trans; [exact PERML|]. apply perm_skip. apply perm_skip. apply Permutation_map. apply Permutation_sym. exact PMC3. }
      eapply (TAIL Σ m3 L B (nn + 1) na (p + 1) pmax _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c3
                ART3 MI3 ST3 eq_refl eq_refl eq_refl eq_refl (Z.le_refl _) FR3 REP3 PERML3 ALN PERM (Z.le_refl _) ltac:(lia) ENV3 UWC3 PRES_3 Hc3').
    + (* [comment removed for export] *)
      apply Z.ltb_ge in LT2. assert (PMX : pmax = p + 1) by lia. assert (NNA : nn = na - 1) by lia.
      assert (NA4000 : na <= 4000) by (unfold LH_KMAX in *; lia). assert (LP : (Z.to_nat p < length bks)%nat) by lia.
      assert (MC0 : mcost (2 * na * 8) = 0) by (unfold mcost; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity).
      assert (LPOS : forall A n, In (A, n) L -> 0 < n).
      { intros A n Hin. pose proof (Permutation_in _ PERML Hin) as X. destruct X as [E|[E|X]]; [injection E; lia| injection E; lia|].
        apply in_map_iff in X. destruct X as (y & E & _). injection E; lia. }
      pose proof (live_lapart RT AF Σ m L ART0 INL) as LAP0.
      assert (KEEPL : forall A n, In (A, n) L -> (A, n) <> (B, 8 * na) -> In (A, n) (live_remove B (rt_live RT Σ))).
      { intros A n Hin NE. apply live_remove_keep; [exact (INL _ Hin)|]. cbn [fst]. intros ->.
        destruct (LAP0 B n B (8 * na) Hin INBL0 NE); pose proof (LPOS _ _ Hin); lia. }
      assert (RESTK : forall e, In e REST -> fst e <> B).
      { intros [p' n'] Hin. cbn [fst]. intros ->. pose proof (proj1 (Forall_forall _ _) RPOS _ Hin) as P'. cbn [snd] in P'.
        destruct (lrest_apart Σ m L REST B (8 * na) B n' ART0 PERM INBL0 Hin ltac:(lia) P'); lia. }
      assert (NODEK : forall q0 A, In (q0, A) (concat bks) -> (A, 24) <> (B, 8 * na)) by (intros q0 A Hq E; injection E; lia).
      assert (LHK : (lh, 104) <> (B, 8 * na)) by (intros E; injection E; lia).
      (* [comment removed for export] *)
      epose proof (lhi_w1b sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 ra _ _ t3 t4 t5 t6 F fc m2 lo lh data B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad _ _ _ _ _ _ hs
                    SC2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ACL2 ALL LHI LO1 FRL2 ST2 LO0 LO2 HT1 MI2) as W1b.
      cl_lift W1b Hc2' c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & FRL3 & ST3) & Hc3'). clear Hc3. fold usp in MU3, ST3, FRL3, Hc3'.
      assert (MU3' : munch ([] ++ [(usp - 192, usp)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
      pose proof (cl_seg_ART RT AF Σ m2 m3 usp 192 [] ART2 ltac:(lia) ltac:(lia) MU3' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM3) as ART3.
      assert (ENV3 : cl_env m3 lb canary).
      { apply (cl_env_seg _ m2 m3 lb canary ENV2 MU3). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
        pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
      assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [outside]; unfold USTACK_TOP in *; lia).
      pose proof (uw_chain_agree outer m2 m3 sp s0 UWC2 AGs3) as UWC3.
      assert (PRES_3 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
      { intros a Ha Ho. rewrite <- (PRES_2 a Ha Ho). apply MU3. cbn [outside]. split; [destruct (OFFS0 _ Ha); lia| exact I]. }
      assert (BELOW3 : forall P : Z -> Prop, (forall x, P x -> x < usp - 192) -> agree_on P m2 m3) by (intros P HP a Ha; apply MU3; cbn [outside]; pose proof (HP _ Ha); split; [lia| exact I]).
      assert (FRS3 : rw_cells asegs m3 (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { apply (rw_cells_agree asegs m2 m3 _ _ FRS2); [| exact WM3]. intros a Ha. apply MU3. cbn [cells_size csize Nat.add outside] in Ha |- *. split; [lia| exact I]. }
      assert (REP3 : lh_rep asegs LH_CEIL (DVerr GOBJ) m3 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * na) (mkGeo nn na p pmax items) bks).
      { eapply lh_rep_agree; [exact REP2| | intros ? ? ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU3 WM3)|].
        intros a [Ha|[Ha|(q & A & Hq & Ha)]]; cbn [outside g_na] in Ha |- *; (split; [| exact I]); [lia| lia|]. destruct (NODESF0 q A Hq) as (_ & X2 & _). lia. }
      pose proof REP3 as (_ & _ & _ & _ & _ & _ & _ & CH3 & EMP3 & _). cbn [g_na g_nn] in CH3, EMP3.
      assert (FR16 : rw_cells asegs m3 (usp - 16) [C8 s0; C8 ra]).
      { change ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FRS3.
        pose proof (rw_cells_skip m3 _ _ _ FRS3) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -104 + 88) with (usp - 16) in X by lia. exact X. }
      destruct (cl_chain_call (rt_cg RT Σ) e_lh_insert e_CRYPTO_realloc SITE_lhi_realloc m3 m3 ra s0 sp (Z_to_bv 64 (usp + -192)) outer CTX
                  (proj1 CGH (SITE_lhi_realloc, e_lh_insert) ltac:(left; reflexivity)) (proj2 CGH (SITE_lhi_realloc, e_CRYPTO_realloc) ltac:(left; reflexivity)) UWC3 ltac:(intros a _; reflexivity)
                  FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXr & UWCr).
      (* [comment removed for export] *)
      destruct (cells_assemble asegs (Z.to_nat na) m3 B ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
                  ltac:(intros i Hi; destruct (chain_chainv asegs LH_CEIL _ _ _ _ _ (CH3 (Z.of_nat i) ltac:(lia))) as (v & CV & _); exists (wz v); exact CV)) as [src OLD].
      pose proof (rw_cells_bytes_at asegs m3 B _ OLD) as OLDB. cbn [cells_bytes cbytes] in OLDB. rewrite app_nil_r in OLDB.
      pose proof (rw_cells_CB_length asegs m3 B _ _ OLD) as SRCL.
      (* [comment removed for export] *)
      apply (C_CRA Σ PMc (Z_to_bv 64 SITE_lhi_realloc) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880))
               (Z_to_bv 64 B) (Z_to_bv 64 (2 * na)) (Z_to_bv 64 8) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 253) (Z_to_bv 64 ((lh + 60) ≫ 3 + 2147450880)) (Z_to_bv 64 (lh ≫ 3)) a7
               (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 2147450880)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 2147450880))
               (Z_to_bv 64 ((lh + 68) ≫ 3 + 2147450880)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 2147450880) (Z_to_bv 64 na) (Z_to_bv 64 p) t3 t4 t5 t6
               F fc m3 B (8 * na) (2 * na) 8 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) INB ltac:(lia) ltac:(lia) ART3 MI3).
      { fold usp in SPA. cl_call_ok EU1 ST3 LOW SPA 12. }
      { rewrite EU1. unfold RT_STACK in *. lia. }
      { rewrite (unsigned_lit SITE_lhi_realloc) by (unfold SITE_lhi_realloc; lia). exact CTXr. }
      { exact UWCr. }
      { clear - CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
      { exact Hlen. }
      { rewrite MC0. exact Hcr. }
      { exact ENV3. }
      { exact Hc3'. }
      clear Hc3'. intros c4 (Σr & q & Hc4 & LVr & FRSr & SPr & CRr & Q0 & Q16 & QU & CGr).
      destruct (ASTA_unpack RT Σr _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & ENV4 & WRQ & ACQ & COPY) & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_lhi_realloc) in Hc4' by (unfold SITE_lhi_realloc; lia).
      pose proof (COPY src OLDB ltac:(rewrite SRCL; lia)) as NEWB. clear COPY.
      rewrite MC0, Z.sub_0_r in CRr. replace (2 * na * 8) with (8 * (2 * na)) in LVr, QU, WRQ, ACQ by lia.
      (* [comment removed for export] *)
      assert (INLr : forall A n, In (A, n) L -> (A, n) <> (B, 8 * na) -> In (A, n) (rt_live RT Σr)) by (intros A n Hin NE; rewrite LVr; right; exact (KEEPL A n Hin NE)).
      assert (INQr : In (q, 8 * (2 * na)) (rt_live RT Σr)) by (rewrite LVr; left; reflexivity).
      assert (LOWr : rt_sp0 RT Σr - STACK_WIN <= lo) by (rewrite SPr; exact LOW).
      assert (FRESHQ : forall p2 n2, In (p2, n2) (live_remove B (rt_live RT Σ)) -> q + 8 * (2 * na) <= p2 \/ p2 + n2 <= q)
        by (intros p2 n2 H; exact (wg_live_apart RT AF Σr m4 [] q (8 * (2 * na)) (live_remove B (rt_live RT Σ)) p2 n2 ART4 LVr H)).
      assert (FRESHL : forall A n, In (A, n) L -> (A, n) <> (B, 8 * na) -> q + 16 * na <= A \/ A + n <= q) by (intros A n Hin NE; destruct (FRESHQ A n (KEEPL A n Hin NE)); lia).
      pose proof (af_live_range RT AF Σr m4 q (8 * (2 * na)) ART4 INQr) as (_ & QLO & _). rewrite SPr in QLO.
      pose proof (afp_live_hi RT GOBJ AFP Σr m4 q (8 * (2 * na)) ART4 INQr ltac:(lia)) as QHI.
      assert (AGS4 : forall a k, usp + -192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
      { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4. left. lia. }
      assert (AGL4 : forall P : Z -> Prop, (forall x, P x -> exists A n, In (A, n) L /\ (A, n) <> (B, 8 * na) /\ A <= x < A + n) -> agree_on P m3 m4).
      { intros P HP a Ha. destruct (HP _ Ha) as (A & n & Hin & NE & Hx). apply PRES4. right; right; left. exists A, n. split; [exact (KEEPL A n Hin NE)| exact Hx]. }
      pose proof (uw_chain_agree outer m3 m4 sp s0 UWC3 ltac:(intros a Ha; apply PRES4; left; lia)) as UWC4.
      assert (PRES_4 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m4).
      { intros a Ha Ho. rewrite <- (PRES_3 a Ha Ho). apply PRES4. apply (aclient_mono _ _ _ _ _ _ _ Ha); [| intros e He; exact He| lia].
        intros e He. apply live_remove_keep; [| exact (RESTK e He)]. eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact He]. }
      eassert (FRL4 : rw_cells asegs m4 (usp + -192) _).
      { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRL3). apply AGS4; cbn [cells_size csize Nat.add app lhi_spill]; unfold USTACK_TOP in *; lia. }
      eassert (FRS4 : rw_cells asegs m4 (usp + -104) _).
      { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRS3). apply AGS4; cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; lia. }
      assert (SC4 : rw_cells asegs m4 lh (lhs_cells B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad)).
      { pose proof REP3 as (_ & _ & _ & (z40 & z48 & err3 & pad3 & SC3) & _).
        assert (SC2' : rw_cells asegs m3 lh (lhs_cells B nn na p pmax items x40 x48 (Z_to_bv 64 0) pad)) by (apply (rw_cells_agree asegs m2 m3 _ _ SC2); [| exact WM3]; apply BELOW3; cbn [cells_size csize Nat.add lhs_cells]; intros; lia).
        apply (rw_cells_agree_nw asegs m3 m4 _ _ SC2'). apply AGL4. cbn [cells_size csize Nat.add lhs_cells]. intros x Hx. exists lh, 104. split; [exact INLHL0|]. split; [exact LHK| lia]. }
      destruct (af_acc_live RT AF Σr m4 lh 104 ART4 (INLr lh 104 INLHL0 LHK)) as [_ ACL4].
      pose proof (afp_live_mem RT GOBJ AFP Σr m4 q (8 * (2 * na)) ART4 INQr ltac:(lia)) as [_ QT].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (FR152 : rw_cells asegs m4 (bv_unsigned sp + -152) [C8 (Z_to_bv 64 (lh + 96))]).
      { lazymatch type of FRL4 with rw_cells _ _ _ ([?c0; ?c1; ?c2; ?c3; ?c4; ?c5] ++ ?rest) =>
          assert (X : rw_cells asegs m4 (usp + -192) ([c0; c1; c2; c3; c4] ++ [c5] ++ rest)) by exact FRL4 end.
        apply rw_cells_skip in X. cbn [cells_size csize Nat.add] in X. replace (usp + -192 + Z.of_nat 40) with (usp + -152) in X by lia.
        apply (proj1 (rw_cells_app _ _ _ _)) in X. destruct X as [X _]. exact X. }
      epose proof (lhi_w2 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 fc4 m4 lo lh q B nn na p pmax items x40 x48 pad
                    SC4 ltac:(lia) Q0 ltac:(lia) ACL4 ALL LHI LO1 FR152 ST4 LO0 LO2 HT1 MI4) as W2.
      cl_lift W2 Hc4' c5 Hc5.
      destruct (ASTA_unpack RT Σr _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & SC5) & Hc5'). clear Hc5.
      assert (ART5 : ART RT Σr m5).
      { apply (af_frame RT AF Σr m4 m5 usp ART4 ltac:(lia)); [| exact WM5]. intros a Ha. apply MU5. cbn [outside]. split; [| exact I]. intros X. apply Ha.
        right; right; left. exists lh, 104. split; [exact (INLr lh 104 INLHL0 LHK)| lia]. }
      assert (ST5 : stk asegs m5 lo (usp + -192)) by (apply (stk_munch _ m4 m5 lo (usp + -192) ST4 MU5 WM5); intros x Hx; cbn [outside]; split; [lia| exact I]).
      assert (ENV5 : cl_env m5 lb canary).
      { apply (cl_env_seg _ m4 m5 lb canary ENV4 MU5). intros x Hx. cbn [outside]. pose proof (client_static_range _ (cl_cell_static _ Hx)). unfold SEGTOP_A in *. split; [lia| exact I]. }
      pose proof (uw_chain_agree outer m4 m5 sp s0 UWC4 ltac:(intros a Ha; apply MU5; cbn [outside]; split; [lia| exact I])) as UWC5.
      assert (PRES_5 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m5).
      { intros a Ha Ho. rewrite <- (PRES_4 a Ha Ho). apply MU5. cbn [outside]. split; [| exact I]. intros X. exact (OFFL0 lh 104 (bv_unsigned a) INLHL0 ltac:(lia) Ha). }
      assert (OFFLH5 : forall P : Z -> Prop, (forall x, P x -> ~ (lh <= x < lh + 8)) -> agree_on P m4 m5) by (intros P HP a Ha; apply MU5; cbn [outside]; split; [exact (HP _ Ha)| exact I]).
      eassert (FRL5 : rw_cells asegs m5 (usp + -192) _) by (apply (rw_cells_agree asegs m4 m5 _ _ FRL4); [apply OFFLH5; cbn [cells_size csize Nat.add app lhi_spill]; intros; lia| exact WM5]).
      eassert (FRS5 : rw_cells asegs m5 (usp + -104) _) by (apply (rw_cells_agree asegs m4 m5 _ _ FRS4); [apply OFFLH5; cbn [cells_size csize Nat.add]; intros; lia| exact WM5]).
      pose proof (bytes_at_agree asegs m4 m5 q src NEWB ltac:(apply OFFLH5; intros x Hx; destruct (FRESHL lh 104 INLHL0 LHK); lia)) as NEWB5.
      destruct (af_acc_live RT AF Σr m5 q (8 * (2 * na)) ART5 INQr) as [WRQ5 ACQ5].
      (* [comment removed for export] *)
      apply (MSET Σr PMc (Z_to_bv 64 SITE_lhi_memset) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880))
               (Z_to_bv 64 (q + 8 * na)) (Z_to_bv 64 0) (Z_to_bv 64 (8 * na)) e3 e4 e5 e6 e7
               (Z_to_bv 64 pmax) (Z_to_bv 64 ((lh + 64) ≫ 3 + 2147450880)) (Z_to_bv 64 lh) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh ≫ 3 + 2147450880))
               (Z_to_bv 64 ((lh + 68) ≫ 3 + 2147450880)) (Z_to_bv 64 (lh + 68)) (Z_to_bv 64 2147450880) (Z_to_bv 64 na) (Z_to_bv 64 p) w3 w4 w5 w6
               F4 fc4 m5 (q + 8 * na) (8 * na) (Z_to_bv 8 0) lo FDO MST eq_refl eq_refl eq_refl ltac:(unfold USTACK_TOP in *; lia) ltac:(lia)).
      { split; [intros _; split; [apply (acc_sub asegs m5 _ _ _ _ ACQ5); lia| left; exists q, (8 * (2 * na)); split; [exact INQr| lia]]|].
        split; [intros i Hi; right; right; left; exists q, (8 * (2 * na)); split; [exact INQr| lia]| apply (wr_at_sub m5 _ _ _ _ WRQ5); lia]. }
      { exact ART5. } { exact MI5. }
      { fold usp in SPA. cl_call_ok EU1 ST5 LOWr SPA 12. }
      { exact Hc5'. }
      clear Hc5'. intros c6 Hc6.
      destruct (ASTA_unpack RT Σr _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & ZER6) & Hc6'). clear Hc6.
      destruct RS6 as (w0' & w1' & w2' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & w3' & w4' & w5' & w6' & F6 & fc6 & ->).
      rewrite EU1 in ST6, PRES6. fold usp in ST6, PRES6. rewrite (ret_pc_even SITE_lhi_memset) in Hc6' by (unfold SITE_lhi_memset; lia).
      (* [comment removed for export] *)
      assert (QOFF : forall a, aclient REST (rt_frames RT Σ) usp a -> ~ (q <= a < q + 8 * (2 * na))).
      { intros a [H|[H|[H|[H|H]]]].
        - lia.
        - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
        - destruct H as (p' & n' & Hin' & Hx). destruct (FRESHQ p' n' ltac:(apply live_remove_keep; [| exact (RESTK _ Hin')]; eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact Hin'])); lia.
        - destruct H as (f & k & Hin & Hf). rewrite <- FRSr in Hin. pose proof (af_frames_range RT AF Σr m6 f k ART6 Hin) as (_ & _ & _ & R3). destruct (R3 _ _ INQr); lia.
        - destruct H as (f & k & Hin & Hf). rewrite <- FRSr in Hin. pose proof (af_fshadow_apart RT AF Σr m6 f k ART6 Hin) as (SL & _). destruct (SL _ _ INQr); lia. }
      assert (AGS6 : forall a k, usp + -192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
      { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; lia| lia]. }
      assert (AGL6 : forall P : Z -> Prop, (forall x, P x -> exists A n, In (A, n) L /\ (A, n) <> (B, 8 * na) /\ A <= x < A + n) -> agree_on P m5 m6).
      { intros P HP a Ha. destruct (HP _ Ha) as (A & n & Hin & NE & Hx). apply PRES6; [right; right; left; exists A, n; split; [exact (INLr A n Hin NE)| exact Hx]|].
        destruct (FRESHL A n Hin NE); lia. }
      assert (AGQ6 : agree_on (fun x => q <= x < q + 8 * na) m5 m6) by (intros a Ha; apply PRES6; [right; right; left; exists q, (8 * (2 * na)); split; [exact INQr| lia]| lia]).
      pose proof (uw_chain_agree outer m5 m6 sp s0 UWC5 ltac:(intros a Ha; apply PRES6; [left; lia| lia])) as UWC6.
      assert (PRES_6 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m6).
      { intros a Ha Ho. rewrite <- (PRES_5 a Ha Ho). apply PRES6; [| pose proof (QOFF _ Ha); lia]. rewrite FRSr. apply (aclient_mono _ _ _ _ _ _ _ Ha); [| intros e He; exact He| lia].
        intros e He. rewrite LVr. right. apply live_remove_keep; [| exact (RESTK e He)]. eapply Permutation_in; [apply Permutation_sym; exact PERM| apply in_or_app; right; exact He]. }
      assert (ENV6 : cl_env m6 lb canary).
      { apply (cl_env_agree m5 m6 lb canary ENV5). intros a Ha. pose proof (client_static_range _ (cl_cell_static _ Ha)) as CR. apply PRES6; [right; left; exact (cl_cell_static _ Ha)| unfold SEGTOP_A in CR; lia]. }
      eassert (FRL6 : rw_cells asegs m6 (usp + -192) _) by (apply (rw_cells_agree asegs m5 m6 _ _ FRL5); [apply AGS6; cbn [cells_size csize Nat.add app lhi_spill]; unfold USTACK_TOP in *; lia| exact WM6]).
      eassert (FRS6 : rw_cells asegs m6 (usp + -104) _) by (apply (rw_cells_agree asegs m5 m6 _ _ FRS5); [apply AGS6; cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; lia| exact WM6]).
      eassert (SC6 : rw_cells asegs m6 lh _).
      { apply (rw_cells_agree asegs m5 m6 _ _ SC5); [| exact WM6]. apply AGL6. cbn [cells_size csize Nat.add lhs_cells]. intros x Hx. exists lh, 104. split; [exact INLHL0|]. split; [exact LHK| lia]. }
      pose proof (bytes_at_agree asegs m5 m6 q src NEWB5 ltac:(rewrite SRCL; eapply agree_sub; [exact AGQ6|]; cbv beta; intros; lia)) as NEWB6.
      destruct (af_acc_live RT AF Σr m6 lh 104 ART6 (INLr lh 104 INLHL0 LHK)) as [_ ACL6].
      (* [comment removed for export] *)
      epose proof (lhi_w3 sp gp (Z_to_bv 64 0xba3ef0) w0' w1' w2' _ e1' e2' e3' e4' e5' e6' e7' w3' w4' w5' w6' F6 fc6 m6 lo lh data q nn na p pmax items x40 x48 pad hs
                    SC6 ltac:(lia) ACL6 ALL LHI LO1 FRL6 ST6 LO0 LO2 HT1 MI6) as W3.
      cl_lift W3 Hc6' c7 Hc7.
      destruct (ASTA_unpack RT Σr _ _ c7 Hc7) as (ms7 & (a2x & m7 & -> & MU7 & WM7 & MI7 & SC7) & Hc7'). clear Hc7.
      assert (INLH1 : In (lh, 104) (rt_live RT Σr)) by exact (INLr lh 104 INLHL0 LHK).
      assert (OFFLH7 : forall P : Z -> Prop, (forall x, P x -> ~ (lh + 56 <= x < lh + 72)) -> agree_on P m6 m7) by (intros P HP a Ha; apply MU7; cbn [outside]; pose proof (HP _ Ha); repeat split; try exact I; lia).
      assert (ART7 : ART RT Σr m7).
      { apply (af_frame RT AF Σr m6 m7 usp ART6 ltac:(lia)); [| exact WM7]. intros a Ha. apply MU7. cbn [outside].
        repeat split; try exact I; intros X; apply Ha; right; right; left; exists lh, 104; (split; [exact INLH1| lia]). }
      assert (ST7 : stk asegs m7 lo (usp + -192)) by (apply (stk_munch _ m6 m7 lo (usp + -192) ST6 MU7 WM7); intros x Hx; cbn [outside]; repeat split; try exact I; lia).
      assert (ENV7 : cl_env m7 lb canary).
      { apply (cl_env_seg _ m6 m7 lb canary ENV6 MU7). intros x Hx. cbn [outside]. pose proof (client_static_range _ (cl_cell_static _ Hx)). unfold SEGTOP_A in *. repeat split; try exact I; lia. }
      pose proof (uw_chain_agree outer m6 m7 sp s0 UWC6 ltac:(apply OFFLH7; intros; lia)) as UWC7.
      assert (PRES_7 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m7).
      { intros a Ha Ho. rewrite <- (PRES_6 a Ha Ho). apply MU7. cbn [outside]. repeat split; try exact I; intros X; exact (OFFL0 lh 104 (bv_unsigned a) INLHL0 ltac:(lia) Ha). }
      eassert (FRL7 : rw_cells asegs m7 (usp + -192) _) by (apply (rw_cells_agree asegs m6 m7 _ _ FRL6); [apply OFFLH7; cbn [cells_size csize Nat.add app lhi_spill]; intros; lia| exact WM7]).
      eassert (FRS7 : rw_cells asegs m7 (usp + -104) _) by (apply (rw_cells_agree asegs m6 m7 _ _ FRS6); [apply OFFLH7; cbn [cells_size csize Nat.add]; intros; lia| exact WM7]).
      destruct (af_acc_live RT AF Σr m7 q (8 * (2 * na)) ART7 INQr) as [WRQ7 ACQ7].
      destruct (af_acc_live RT AF Σr m7 lh 104 ART7 INLH1) as [_ ACL7].
      (* [comment removed for export] *)
      assert (NEW7 : rw_cells asegs m7 q [CB (8 * Z.to_nat na) (src ++ [])]).
      { rewrite app_nil_r. split; [split; [cbn; split; [exact SRCL| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r]|].
        - apply (bytes_at_agree asegs m6 m7 q src NEWB6). rewrite SRCL. apply OFFLH7. intros x Hx. destruct (FRESHL lh 104 INLHL0 LHK); lia.
        - cbn [cells_size csize Nat.add]. apply (wr_at_sub m7 _ _ _ _ WRQ7); lia. }
      assert (ZER7 : rw_cells asegs m7 (q + 8 * na) [CB (8 * Z.to_nat na) (repeat (Z_to_bv 8 0) (8 * Z.to_nat na))]).
      { split; [split; [cbn; split; [apply repeat_length| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r]|].
        - replace (8 * Z.to_nat na)%nat with (Z.to_nat (8 * na)) by lia. apply (bytes_at_agree asegs m6 m7 _ _ ZER6). rewrite repeat_length. apply OFFLH7. intros x Hx. destruct (FRESHL lh 104 INLHL0 LHK); lia.
        - cbn [cells_size csize Nat.add]. apply (wr_at_sub m7 _ _ _ _ WRQ7); lia. }
      assert (AGN7 : LhRep.agree_on asegs (fun a => exists p0 X, In (p0, X) (concat bks) /\ X <= a < X + 24) m3 m7).
      { intros a Ha (p0 & X & Hin & HX). destruct (NODESF0 p0 X Hin) as (O & X2 & X3 & X4 & X5). pose proof (NODEK p0 X Hin) as NE.
        assert (P7 : forall x, X <= x < X + 24 -> ~ (lh + 56 <= x < lh + 72)) by (clear - X5; intros; lia).
        assert (P5 : forall x, X <= x < X + 24 -> ~ (lh <= x < lh + 8)) by (clear - X5; intros; lia).
        assert (PL : forall x, X <= x < X + 24 -> exists A n, In (A, n) L /\ (A, n) <> (B, 8 * na) /\ A <= x < A + n) by (intros x Hx; exists X, 24; split; [exact O|]; split; [exact NE| exact Hx]).
        assert (HXa : (fun x => X <= x < X + 24) (bv_unsigned (wa a))) by (unfold wa; rewrite unsigned_lit by lia; exact HX).
        split.
        - rewrite (OFFLH7 _ P7 (wa a) HXa), (AGL6 _ PL (wa a) HXa), (OFFLH5 _ P5 (wa a) HXa), (AGL4 _ PL (wa a) HXa). reflexivity.
        - intros _. destruct (af_acc_live RT AF Σr m7 X 24 ART7 (INLr X 24 O NE)) as [(_ & _ & W) _]. replace (wa a) with (wa (X + (a - X))) by (f_equal; lia). apply W. lia. }
      pose proof (lh_raw_double GOBJ m3 m7 L lh B q na bks src [] LAP0 LPOS (lh_rep_raw asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP3) OLD NEW7 ZER7 AGN7 FRESHL Q0
                    ltac:(unfold LH_CEIL, USTACK_TOP in *; lia)) as RAW7.
      replace (16 * na) with (8 * (2 * na)) in RAW7 by lia.
      set (L1 := (q, 8 * (2 * na)) :: live_remove B L) in *.
      assert (INL1r : forall x, In x L1 -> In x (rt_live RT Σr)).
      { intros x [<-|Hx]; [exact INQr|]. destruct (live_remove_inM B L x Hx) as [H1 H2]. rewrite LVr. right. apply live_remove_keep; [exact (INL _ H1)| exact H2]. }
      pose proof (live_lapart RT AF Σr m7 L1 ART7 INL1r) as LAP1.
      assert (LHL1 : In (lh, 104) L1) by (right; apply live_remove_keep; [exact INLHL0| cbn [fst]; intros E; apply LHK; rewrite E; destruct (S_LB); pose proof (LPOS _ _ INBL0); first [lia| reflexivity]]).
      pose proof RAW7 as (_ & _ & _ & _ & _ & CH7 & _).
      assert (ENTH7 : forall i, 0 <= i < na -> nth (Z.to_nat i) (bks ++ repeat [] (Z.to_nat na)) [] = nth (Z.to_nat i) bks []) by (intros i Hi; apply app_nth1; lia).
      assert (FSP7 : rw_cells asegs m7 (usp + -144) (lhi_spill lh data)).
      { pose proof (rw_cells_skip m7 _ _ _ FRL7) as X. cbn [cells_size csize Nat.add] in X. replace (usp + -192 + Z.of_nat 48) with (usp + -144) in X by lia.
        apply (proj1 (rw_cells_app _ _ _ _)) in X. destruct X as [X _]. exact X. }
      assert (NODES7 : forall q0 A, In (q0, A) (nth (Z.to_nat p) bks []) -> In (A, 24) L1 /\ acc asegs m7 A 24 /\ A + 24 <= lo /\ 0x10007fff8000 <= A /\ A mod 16 = 0 /\ (A + 24 <= lh \/ lh + 104 <= A)).
      { intros q0 A Hq. pose proof (in_concat_nth bks _ _ LP Hq) as IQ. destruct (NODESF0 q0 A IQ) as (O & X2 & X3 & X4 & X5). pose proof (NODEK q0 A IQ) as NE.
        destruct (af_acc_live RT AF Σr m7 A 24 ART7 (INLr A 24 O NE)) as [_ X1].
        split; [right; apply live_remove_keep; [exact O| cbn [fst]; intros ->; destruct (proj2 (S_N (Z.to_nat p) q0 B LP Hq)); pose proof (LPOS _ _ INBL0); lia]|].
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact X5]. }
      assert (SLN : Forall (fun A => A + 24 <= lh \/ lh + 104 <= A) (map snd (nth (Z.to_nat p) bks []))).
      { apply Forall_forall. intros A HA0. apply in_map_iff in HA0. destruct HA0 as ([q0 A'] & E & Hq). cbn [snd] in E. subst A'. destruct (NODES7 q0 A Hq) as (_ & _ & _ & _ & _ & X). exact X. }
      assert (SLU : Forall (fun A => A + 24 <= usp - 192) (map snd (nth (Z.to_nat p) bks []))).
      { apply Forall_forall. intros A HA0. apply in_map_iff in HA0. destruct HA0 as ([q0 A'] & E & Hq). cbn [snd] in E. subst A'. destruct (NODES7 q0 A Hq) as (_ & _ & X & _). lia. }
      assert (ACCS : forall X, In X (map snd (nth (Z.to_nat p) bks [])) -> acc asegs m7 X 24 /\ X mod 8 = 0 /\ 0x10007fff8000 <= X /\ X + 24 <= 2^47).
      { intros X HX. apply in_map_iff in HX. destruct HX as ([q0 X'] & E & Hq). cbn [snd] in E. subst X'.
        destruct (NODES7 q0 X Hq) as (_ & X1 & X2 & X3 & X4 & _). split; [exact X1|]. split; [clear - X4; Z.div_mod_to_equations; lia|]. unfold USTACK_TOP in *. lia. }
      epose proof (lhi_split (Z_to_bv 64 SITE_lhi_memset) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) w0' w1' w2' sp _ a2x _ e5' e7' _ _ _ _ w3' w4' w5' w6' F6 fc6 m7 GOBJ L1 lh q nn (2 * na) p 0 pmax na na items data usp
                    x40 x48 (Z_to_bv 64 0) pad (nth (Z.to_nat p) bks [])
                    SC7 FSP7 ltac:(rewrite <- (ENTH7 p ltac:(lia)); exact (CH7 p ltac:(lia))) ltac:(rewrite <- (EMP3 nn ltac:(lia)), <- (ENTH7 nn ltac:(lia)); exact (CH7 nn ltac:(lia)))
                    ltac:(rewrite <- (ENTH7 p ltac:(lia)); exact (bucket_nsep_raw asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ p nn (ownL_apart L1 LAP1) RAW7 ltac:(lia) ltac:(lia) ltac:(lia)))
                    G2 G3 G4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ACL7 ALL LHI ltac:(unfold USTACK_TOP in *; lia) ACQ7 ltac:(clear - Q16; Z.div_mod_to_equations; lia) QHI ltac:(unfold USTACK_TOP in *; lia)
                    ACCS ltac:(destruct (FRESHL lh 104 INLHL0 LHK); lia) SLN (eq_sym (Z_to_bv_bv_unsigned sp)) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) SLU MI7) as WS.
      cl_lift WS Hc7' c8 Hc8.
      destruct (ASTA_unpack RT Σr _ _ c8 Hc8) as (ms8 & (ra8 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m8 & stay' & moved' & -> & MI8 & WM8 & SC8 & CHS & CHM & PMsm & AG8) & Hc8'). clear Hc8.
      pose proof (split_munch2 lh _ _ _ m7 m8 AG8) as MU8.
      assert (W8CL : forall a, ((lh + 56 <= a < lh + 68) \/ split_W (q + 8 * p) (q + 8 * nn) (nth (Z.to_nat p) bks []) a) -> exists A n, In (A, n) L1 /\ A <= a < A + n /\ A + n <= lo /\ n <= 64512).
      { intros a [X|[X|[X|(q0 & A & Hq & X)]]].
        - exists lh, 104. split; [exact LHL1|]. lia.
        - exists q, (8 * (2 * na)). split; [left; reflexivity|]. lia.
        - exists q, (8 * (2 * na)). split; [left; reflexivity|]. lia.
        - destruct (NODES7 q0 A Hq) as (O & _ & X2 & _). exists A, 24. split; [exact O|]. lia. }
      assert (OUT8 : forall a, (forall A n, In (A, n) L1 -> A <= a < A + n -> A + n <= lo -> n <= 64512 -> False) -> outside ((lh + 56, lh + 68) :: split_ivs (q + 8 * p) (q + 8 * nn) (nth (Z.to_nat p) bks [])) a).
      { intros a Ha. cbn [outside]. split; [intros X| apply (proj2 (split_ivs_outside _ _ _ _)); intros X].
        - destruct (W8CL a (or_introl X)) as (A & n & Hin & Hx & Hlo & Hn). exact (Ha A n Hin Hx Hlo Hn).
        - destruct (W8CL a (or_intror X)) as (A & n & Hin & Hx & Hlo & Hn). exact (Ha A n Hin Hx Hlo Hn). }
      assert (PERMr : Permutation (rt_live RT Σr) (L1 ++ REST)).
      { rewrite LVr. subst L1. cbn [app]. apply perm_skip. rewrite <- (live_remove_notin B REST RESTK). rewrite <- live_remove_appM. apply live_remove_permM. exact PERM. }
      assert (OFFL1 : forall A n a, In (A, n) L1 -> A <= a < A + n -> ~ aclient REST (rt_frames RT Σ) usp a).
      { intros A n a Hin Ha. rewrite <- FRSr. apply (lblock_not_rest Σr m7 L1 REST A n usp a ART7 PERMr RPOS ltac:(lia) Hin Ha). }
      assert (ART8 : ART RT Σr m8).
      { apply (af_frame RT AF Σr m7 m8 usp ART7 ltac:(lia)); [| exact WM8]. intros a Ha. apply MU8. apply OUT8. intros A n Hin Hx _ _. apply Ha. right; right; left. exists A, n. split; [exact (INL1r _ Hin)| exact Hx]. }
      assert (PRES_8 : rt_pres_fp REST (rt_frames RT Σ) usp [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m8).
      { intros a Ha Ho. rewrite <- (PRES_7 a Ha Ho). apply MU8. apply OUT8. intros A n Hin Hx _ _. exact (OFFL1 A n _ Hin Hx Ha). }
      assert (ENV8 : cl_env m8 lb canary).
      { apply (cl_env_seg _ m7 m8 lb canary ENV7 MU8). intros x Hx. apply OUT8. intros A n Hin HAx _ Hn. pose proof (afp_live_hi RT GOBJ AFP Σr m7 A n ART7 (INL1r _ Hin) Hn).
        pose proof (client_static_range _ (cl_cell_static _ Hx)). unfold SEGTOP_A in *. lia. }
      assert (AGs8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; apply MU8; apply OUT8; intros A n Hin HAx Hlo _; lia).
      pose proof (uw_chain_agree outer m7 m8 sp s0 UWC7 AGs8) as UWC8.
      assert (ST8 : stk asegs m8 lo (usp + -192)) by (apply (stk_munch _ m7 m8 lo (usp + -192) ST7 MU8 WM8); intros x Hx; apply OUT8; intros A n Hin HAx Hlo _; lia).
      eassert (FRL8 : rw_cells asegs m8 (usp + -192) _).
      { apply (rw_cells_agree asegs m7 m8 _ _ FRL7); [| exact WM8]. intros a Ha. apply MU8. apply OUT8. cbn [cells_size csize Nat.add app lhi_spill] in Ha. intros A n Hin HAx Hlo _. lia. }
      eassert (FRS8 : rw_cells asegs m8 (usp + -104) _).
      { apply (rw_cells_agree asegs m7 m8 _ _ FRS7); [| exact WM8]. intros a Ha. apply MU8. apply OUT8. cbn [cells_size csize Nat.add] in Ha. intros A n Hin HAx Hlo _. lia. }
      lazymatch type of FRL8 with rw_cells _ _ _ (?X ++ ?Y ++ [C8 hs]) =>
        assert (FR8 : rw_cells asegs m8 (usp + -192) ((X ++ Y ++ [C8 hs]) ++ lhi_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
          by (apply rw_cells_app; split; [exact FRL8| cbn [cells_size csize Nat.add app lhi_spill Z.of_nat Pos.of_succ_nat Pos.succ]; replace (usp + -192 + 88) with (usp + -104) by lia; exact FRS8]);
        rewrite (app_assoc X Y [C8 hs]) in FR8; rewrite <- (app_assoc (X ++ Y) [C8 hs]) in FR8;
        apply (rw_cells_glue m8 _ [] (X ++ Y)) in FR8; apply (rw_cells_glue m8 _ [_] [C8 hs]) in FR8;
        cbn [cells_size csize Nat.add app lhi_spill cells_bytes cbytes] in FR8 end.
      (* [comment removed for export] *)
      destruct (split_raw asegs LH_CEIL (DVerr GOBJ) m7 m8 (ownL L1) lh (bp lh) (bp q) q (8 * (2 * na)) (2 * na) (bks ++ repeat [] (Z.to_nat na)) p nn stay' moved' (ownL_apart L1 LAP1)
                  RAW7 ltac:(lia) ltac:(lia) ltac:(rewrite (ENTH7 nn ltac:(lia)); exact (EMP3 nn ltac:(lia))) CHS CHM ltac:(rewrite (ENTH7 p ltac:(lia)); exact PMsm)
                  ltac:(rewrite (ENTH7 p ltac:(lia)); exact AG8)) as [RAW8 PMC8].
      assert (EMP8 : forall i, nn + 1 <= i < 2 * na -> nth (Z.to_nat i) (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' (bks ++ repeat [] (Z.to_nat na)))) [] = []).
      { intros i Hi. rewrite !nth_lupd_ne by lia. destruct (Z_lt_le_dec i na) as [Hlt|Hge].
        - rewrite (ENTH7 i ltac:(lia)). apply EMP3. lia.
        - rewrite app_nth2 by lia. apply nth_repeat. }
      pose proof (lh_rep_of_raw asegs LH_CEIL (DVerr GOBJ) m8 (ownL L1) ERR_FNS_A lh (bp lh) (bp q) q (8 * (2 * na)) (mkGeo (nn + 1) (2 * na) 0 na items) _ RAW8
                    (lh_geo_ok_double (mkGeo nn na p pmax items) G LOAD LT2) ltac:(exists x40, x48, (Z_to_bv 64 0), pad; exact SC8) EMP8) as REP8.
      assert (PERML8 : Permutation L1 ((lh, 104) :: (q, 8 * (2 * na)) :: map (fun x => (snd x, 24)) (concat (lupd (Z.to_nat p) stay' (lupd (Z.to_nat nn) moved' (bks ++ repeat [] (Z.to_nat na))))))).
      { subst L1. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip.
        eapply Permutation_trans; [apply live_remove_permM; exact PERML|].
        rewrite (live_remove_cons_ne B lh 104) by (intros E; apply LHK; rewrite E; destruct S_LB; pose proof (LPOS _ _ INBL0); first [lia| reflexivity]).
        rewrite live_remove_head; [apply perm_skip; apply Permutation_map; apply Permutation_sym; rewrite concat_app, concat_repeat_nil, app_nil_r in PMC8; exact PMC8|].
        intros e He. apply in_map_iff in He. destruct He as ([q0 A] & <- & Hq). cbn [fst snd]. intros ->.
        apply in_concat in Hq. destruct Hq as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & <-). destruct (proj2 (S_N i q0 B Hi Hin)); pose proof (LPOS _ _ INBL0); lia. }
      assert (ALN1 : Forall (fun x => fst x mod 16 = 0) L1).
      { subst L1. constructor; [cbn [fst]; exact Q16|]. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) ALN x (proj1 (live_remove_inM B L x Hx))). }
      assert (LENr : Z.of_nat (length (rt_live RT Σr)) <= Z.of_nat (length (rt_live RT Σ))) by (rewrite LVr; cbn [length]; pose proof (live_remove_length_lt B (8 * na) (rt_live RT Σ) INB); lia).
      assert (LL1 : Z.of_nat (length L1) <= Z.of_nat (length L)) by (subst L1; cbn [length]; pose proof (live_remove_length_lt B (8 * na) L INBL0); lia).
      eapply (TAIL Σr m8 L1 q (nn + 1) (2 * na) 0 na _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c8
                ART8 MI8 ST8 FRSr SPr CGr CRr LENr FR8 REP8 PERML8 ALN1 PERMr LL1 ltac:(lia) ENV8 UWC8 PRES_8 Hc8').
  - (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m1 _ [] 88 jl _ [80; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in FR1.
    eapply (TAIL Σ m1 L B nn na p pmax bks _ _ ra t0 t1 t2 _ _ _ _ a3 a4 a5 a6 a7 _ _ _ s11 t3 t4 t5 t6 F fc c1
              ART1 MI1 ST1 eq_refl eq_refl eq_refl eq_refl (Z.le_refl _) FR1 REP1 PERML ALN PERM (Z.le_refl _) ltac:(lia) ENV_1 UWC1 PRES_1 Hc1').
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End LhInsert.
