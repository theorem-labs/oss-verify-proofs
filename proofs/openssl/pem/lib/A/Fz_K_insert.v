(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_I1_getrn Fz_I1_retrieve Fz_I1_split Fz_I1_insw Fz_I1_insx Fz_env Fz_M_malloc Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_insw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Definition KI_SITES : list (Z * Z) := [(SITE_lhi_malloc, e_lh_insert); (SITE_cm_malloc, e_CRYPTO_malloc)].
Definition KI_CALLS : list (Z * Z) := [(SITE_lhi_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)].

(* [comment removed for export] *)
Lemma plh_rep_restruct : forall m m' lh B items items' bks,
  plh_rep m lh B items bks -> rw_cells asegs m' lh (plh_cells B items') -> 0 <= items' ->
  agree_on (fun a => (B <= a < B + 128) \/ exists n, In n (concat bks) /\ fst n <= a < fst n + 24) m m' ->
  plh_rep m' lh B items' bks.
Proof.
  intros m m' lh B items items' bks (SC & AL & BL & LEN & IT & CH & EMP & ND) SC' IT' AG.
  split; [exact SC'|]. split; [exact AL|]. split; [exact BL|]. split; [exact LEN|]. split; [exact IT'|].
  split; [| split; [exact EMP| exact ND]].
  intros i Hi. eapply pchain_agree; [exact (CH i Hi)|]. eapply agree_sub; [exact AG|].
  intros a [Ha|(n & Hn & Ha)]; [left; lia| right; exists n; split; [exact (in_concat_nthZ _ _ _ Hn)| exact Ha]].
Qed.

Section CKIns.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CM : crypto_malloc_env_stmt RT.

(* [comment removed for export] *)
Definition plh_insert_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem) (canary : word)
    (lh B items : Z) (bks : list (list pnode)) (d : Z) (str : list byte) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
                [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (lh + 88, lh + 104);
                 (pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks []), pend (B + 8 * (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) + 8)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ plh_rep m' lh B (items + 1) (lupd (Z.to_nat (lh_strhash str mod 8)) (nth (Z.to_nat (lh_strhash str mod 8)) bks [] ++ [(q, lh_strhash str)]) bks)
           /\ rw_cells asegs m' q [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (lh_strhash str))]) c
       /\ rt_live RT Σ' = (q, 24) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost 24 /\ 0 < q /\ q mod 16 = 0 /\ q + 24 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ.

Definition plh_insert_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (lh B items : Z) (bks : list (list pnode)) (d nd S : Z) (str : list byte),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 d -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 304 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_lh_insert (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) KI_SITES KI_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ -> cl_env m lb canary ->
  plh_rep m lh B items bks -> incl (plh_L lh B bks) (rt_live RT Σ) -> items < 15 ->
  In (d, nd) (rt_live RT Σ) -> nd <= 64512 -> rw_cells asegs m d [C8 (Z_to_bv 64 S)] -> d mod 8 = 0 -> (d + nd <= lh \/ lh + 104 <= d) -> d + 8 <= S -> S + Z.of_nat (length str) + 1 <= d + nd ->
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> str <> [] -> Z.of_nat (length str) < 2 ^ 40 ->
  Forall (fun n : pnode => snd n <> lh_strhash str) (nth (Z.to_nat (lh_strhash str mod 8)) bks []) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_lh_insert m)))
      (plh_insert_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m canary lh B items bks d str).

Theorem plh_insert_cps : plh_insert_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary lh B items bks d nd S str
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV REP INL ITEMS IND NDB DC DAL DSEP DS SND STR NONUL NE LEN HASHES.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  pose proof REP as (SC & LAL & BAL & LEN16 & IT & CH & EMP & ND).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 304 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  cl_eu usp (-192) EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  destruct (plh_live_facts RT GOBJ AF AFP Σ m lh B items bks lo ART0 REP INL LOW) as ((ACL & L0 & LAL8 & LLO & LHI & LTOP) & (ACB & B0 & BAL8 & BLO & BHI & BTOP) & NODESF & APLB & APN & APNN).
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (af_live_range RT AF Σ m d nd ART0 IND) as (D0 & DLO & _). pose proof (afp_live_hi RT GOBJ AFP Σ m d nd ART0 IND NDB) as DHI.
  destruct (af_acc_live RT AF Σ m d nd ART0 IND) as [_ DACC].
  pose proof (lh_strhash_range str) as HR.
  set (h := lh_strhash str) in *. set (idx := h mod 8) in *. assert (IDXR : 0 <= idx < 8) by (subst idx; apply Z.mod_pos_bound; lia).
  set (rn := pend (B + 8 * idx) (nth (Z.to_nat idx) bks [])) in *.
  assert (LO1 : lh + 104 <= lo) by lia. assert (LO2 : lo <= usp - 192) by (unfold RT_STACK in *; lia). assert (HT1 : usp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (LO0 : 0x10007fff8000 <= lo) by lia. assert (LO3 : lo <= usp - 304) by (unfold RT_STACK in *; lia).
  (* [comment removed for export] *)
  assert (RNW : (B <= rn /\ rn + 8 <= B + 128 /\ nth (Z.to_nat idx) bks [] = []) \/ (exists pre Ar hr, nth (Z.to_nat idx) bks [] = pre ++ [(Ar, hr)] /\ rn = Ar + 8 /\ In (Ar, hr) (concat bks))).
  { destruct (pend_where (nth (Z.to_nat idx) bks []) (B + 8 * idx)) as [[E1 E2]|(pre & Ar & hr & E1 & E2)]; fold rn in E2.
    - left. rewrite E2. split; [lia|]. split; [lia| exact E1].
    - right. exists pre, Ar, hr. split; [exact E1|]. split; [exact E2|]. eapply in_concat_nthZ. rewrite E1. apply in_or_app. right. left. reflexivity. }
  assert (RNP : exists pa na', In (pa, na') (plh_L lh B bks) /\ pa mod 8 = 0 /\ pa <= rn /\ rn + 8 <= pa + na' /\ (rn + 8 <= lh \/ lh + 104 <= rn) /\ na' <= 64512 /\ pa + na' <= lo /\ 0x10007fff8000 <= pa /\ pa + na' <= 2 ^ 47).
  { destruct RNW as [(R1 & R2 & _)|(pre & Ar & hr & E1 & -> & INA)].
    - exists B, 128. split; [right; left; reflexivity|]. split; [exact BAL8|]. lia.
    - destruct (NODESF _ INA) as (_ & X2 & X3 & X4 & X5 & X6). cbn [fst] in X2, X3, X4, X5, X6. destruct (APN _ INA) as [Y1 _]. cbn [fst] in Y1.
      exists Ar, 24. split; [exact (plh_L_node lh B bks _ INA)|]. split; [exact X3|]. lia. }
  destruct RNP as (pa & na' & INP & PAL & PA1 & PA2 & SRL & SMALL & PLO & PHI & PTOP).
  (* [comment removed for export] *)
  pose proof (ki_w0 ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lh d B items
                eq_refl eq_refl SC ltac:(lia) ACL LAL8 LHI LO1 UT SHC ST LO0 LO2 HT1 MI0) as W.
  cl_lift W HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (jl & m1 & -> & MU1 & WM1 & MI1 & FR1 & SC1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, FR1, Hc1'. unfold lhi_frame in FR1.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 192) ART0 ltac:(lia)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [| split; [| exact I]].
    - intros X. apply Ha. left. unfold USTACK_TOP in *. lia.
    - intros X. apply Ha. right; right; left. exists lh, 104. split; [apply INL; left; reflexivity| lia]. }
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [outside]; unfold USTACK_TOP in *; lia).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWC1.
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_seg _ m m1 lb canary ENV MU1). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
    pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
  assert (REP1 : plh_rep m1 lh B items bks).
  { eapply (plh_rep_restruct m m1); [exact REP| exact SC1| lia|]. apply (agree_of_munch _ _ _ _ MU1).
    intros a [Ha|(n & Hn & Ha)]; cbn [outside].
    - split; [lia|]. split; [lia| exact I].
    - destruct (NODESF n Hn) as (_ & _ & _ & X4 & _). destruct (APN n Hn) as [Y1 _]. split; [lia|]. split; [lia| exact I]. }
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs m1 _ [] 88 jl _ [80; 8]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in FR1.
  destruct (plh_live_facts RT GOBJ AF AFP Σ m1 lh B items bks lo ART1 REP1 INL LOW) as ((ACL1 & _) & (ACB1 & _) & NODESF1 & _).
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  destruct (af_acc_live RT AF Σ m1 d nd ART1 IND) as [_ DACC1].
  pose proof (af_acc_stack RT AF Σ m1 (usp - 192) 192 ART1 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)) as ACCF1.
  assert (DC1 : rw_cells asegs m1 d [C8 (Z_to_bv 64 S)]).
  { eapply rw_cells_transport; [exact DC| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. clear - DLO LOW LO3 DSEP SB DS SND. lia. }
  assert (STR1 : bytes_at asegs m1 S (str ++ [Z_to_bv 8 0])).
  { eapply bytes_at_transport; [exact STR| exact MU1|]. cbn [disjoint_from]. rewrite length_app. cbn [length]. clear - DLO LOW LO3 DSEP SB DS SND. lia. }
  assert (NODES1 : forall n, In n (concat bks) -> acc asegs m1 (fst n) 24 /\ 0 < fst n /\ fst n + 24 <= lo).
  { intros n Hn. destruct (NODESF1 n Hn) as (X1 & X2 & _ & X4 & _). exact (conj X1 (conj X2 X4)). }
  assert (DA1 : acc asegs m1 d 8) by (apply (acc_sub asegs m1 d nd d 8 DACC1); clear - DS SND SB; lia).
  assert (SA1 : acc asegs m1 S (Z.of_nat (length str) + 1)) by (apply (acc_sub asegs m1 d nd S _ DACC1); clear - DS SND SB; lia).
  assert (DLO8 : d + 8 <= lo) by (clear - DLO LOW DS SND SB; lia). assert (S0 : 0 < S) by (clear - D0 DS; lia).
  assert (SLO : S + Z.of_nat (length str) + 1 <= lo) by (clear - SND DLO LOW; lia).
  pose proof (ki_wg ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 ((lh + 56) ≫ 3 + 2147450880)) (Z_to_bv 64 512) (Z_to_bv 64 (items * 256 / 8)) (Z_to_bv 64 8)
                 a3 a4 a5 a6 a7 (Z_to_bv 64 (lh + 96)) (Z_to_bv 64 (lh + 56)) s10 s11 t3 t4 t5 t6 F fc m1 lh B items bks d S lo str
                 (firstn 80 jl) (firstn 8 (skipn 80 jl)) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 REP1 ACL1 L0 LO1 ACB1 B0 BLO NODES1 DC1 DA1 DAL D0 DLO8 S0 STR1 NONUL NE LEN SA1 SLO HASHES
                 FR1 ACCF1 SPA UT1 SHC1 ST1 LO0 LO3 HT1 MI1) as W.
  cl_lift W Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (v0 & v1 & v2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & rn' & ERN & MI2 & WM2 & -> & MU2 & FR2 & TERM2 & ST2 & REP2) & Hc2'). clear Hc2.
  fold h idx in ERN. fold rn in ERN. subst rn'. fold usp in MU2, FR2, ST2, Hc2'. fold h in FR2.
  assert (MU2' : munch ([] ++ [(usp - 304, usp)]) m1 m2) by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside app]; intros; lia).
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp 304 [] ART1 ltac:(lia) ltac:(lia) MU2' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  assert (ENV2 : cl_env m2 lb canary).
  { apply (cl_env_seg _ m1 m2 lb canary ENV1 MU2). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
    pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
  assert (AGs2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; apply MU2; cbn [outside]; unfold USTACK_TOP in *; lia).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWC1 AGs2) as UWC2.
  assert (FR16 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { unfold lhi_saved in FR2.
    lazymatch type of FR2 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15] =>
      pose proof (rw_cells_skip m2 _ [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] [c14; c15] FR2) as X end.
    cbn [cells_size csize Nat.add] in X. replace (usp + -192 + 176) with (usp - 16) in X by lia. exact X. }
  destruct (cl_chain_call (rt_cg RT Σ) e_lh_insert e_CRYPTO_malloc SITE_lhi_malloc m2 m2 ra s0 sp (Z_to_bv 64 (usp + -192)) outer CTX
              (proj1 CGH (SITE_lhi_malloc, e_lh_insert) ltac:(left; reflexivity)) (proj2 CGH (SITE_lhi_malloc, e_CRYPTO_malloc) ltac:(left; reflexivity)) UWC2 ltac:(intros a _; reflexivity)
              FR16 ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc & UWCc).
  (* [comment removed for export] *)
  apply (C_CM Σ PMc (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (usp + -192)) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
           (Z_to_bv 64 24) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 130) d3 d4 d5 d6 d7
           (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 d) (Z_to_bv 64 rn) (Z_to_bv 64 (lh + 56)) (Z_to_bv 64 (lh + 96))
           (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 v3 v4 v5 v6
           F2 fc2 m2 24 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART2 MI2).
  { fold usp in SPA. cl_call_ok EU1 ST2 LOW SPA 12. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_lhi_malloc) by (unfold SITE_lhi_malloc; lia). exact CTXc. }
  { exact UWCc. }
  { clear - CGH. unfold KI_SITES, KI_CALLS in CGH. split; intros x Hx; [apply (proj1 CGH)| apply (proj2 CGH)]; cbn [In] in Hx |- *; tauto. }
  { lia. }
  { unfold mcost. cbn. lia. }
  { exact ENV2. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ2 & q & Hc3 & LV3 & FRS3 & SP3 & CR3 & Q0 & Q16 & QU & CG3).
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ENV4 & WRQ & ACQ) & Hc3'). clear Hc3.
  destruct RS4 as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. fold usp in ST4, PRES4. rewrite (ret_pc_even SITE_lhi_malloc) in Hc3' by (unfold SITE_lhi_malloc; lia).
  (* [comment removed for export] *)
  assert (INL1 : forall x, In x (plh_L lh B bks) -> In x (rt_live RT Σ)) by (intros x Hx; exact (INL _ Hx)).
  assert (INL2 : forall x, In x (plh_L lh B bks) -> In x (rt_live RT Σ2)) by (intros x Hx; rewrite LV3; right; exact (INL _ Hx)).
  assert (INQ : In (q, 24) (rt_live RT Σ2)) by (rewrite LV3; left; reflexivity).
  assert (FRESHQ : forall p2 n2, In (p2, n2) (rt_live RT Σ) -> q + 24 <= p2 \/ p2 + n2 <= q) by (intros p2 n2 H; exact (wg_live_apart RT AF Σ2 m4 [] q 24 (rt_live RT Σ) p2 n2 ART4 LV3 H)).
  pose proof (af_live_range RT AF Σ2 m4 q 24 ART4 INQ) as (_ & QLO & _). rewrite SP3 in QLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 q 24 ART4 INQ ltac:(lia)) as QHI.
  assert (AG4 : forall a k, usp + -192 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [outside]. unfold G_ALLOW_CUST, USTACK_TOP in *. split; [lia| exact I]. }
  eassert (FR4 : rw_cells asegs m4 _ _).
  { apply (rw_cells_agree asegs m2 m4 _ _ FR2); [| exact WM4]. apply AG4; cbn [cells_size csize Nat.add lhi_saved]; unfold USTACK_TOP in *; lia. }
  assert (AGL4 : forall P : Z -> Prop, (forall x, P x -> exists A n, In (A, n) (rt_live RT Σ) /\ n <= 64512 /\ A <= x < A + n) -> agree_on P m2 m4).
  { intros P HP a Ha. destruct (HP _ Ha) as (A & n & Hin & Hn & Hx). apply PRES4.
    - right; right; left. exists A, n. split; [exact Hin| exact Hx].
    - cbn [outside]. pose proof (afp_live_hi RT GOBJ AFP Σ m2 A n ART2 Hin Hn). unfold G_ALLOW_CUST. split; [lia| exact I]. }
  assert (AGT4 : agree_on (plh_fp lh B bks) m2 m4).
  { apply AGL4. intros x [Hx|[Hx|(n & Hn & Hx)]].
    - exists lh, 104. split; [apply INL1; left; reflexivity|]. lia.
    - exists B, 128. split; [apply INL1; right; left; reflexivity|]. lia.
    - exists (fst n), 24. split; [apply INL1; exact (plh_L_node lh B bks n Hn)|]. lia. }
  pose proof (plh_rep_agree m2 m4 lh B items bks REP2 AGT4) as REP4.
  destruct (plh_live_facts RT GOBJ AF AFP Σ2 m4 lh B items bks lo ART4 REP4 (fun x Hx => INL2 x Hx) ltac:(rewrite SP3; exact LOW)) as ((ACL4 & _) & (ACB4 & _) & NODESF4 & _).
  destruct (af_acc_live RT AF Σ2 m4 pa na' ART4 (INL2 _ INP)) as [_ PACC4].
  pose proof (FRESHQ pa na' (INL1 _ INP)) as SQP. pose proof (FRESHQ lh 104 (INL1 _ ltac:(left; reflexivity))) as SQL.
  assert (TERM4 : rw_cells asegs m4 rn [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m2 m4 _ _ TERM2); [| exact WM4]. apply AGL4. cbn [cells_size csize Nat.add]. intros x Hx. exists pa, na'. split; [exact (INL1 _ INP)|]. lia. }
  pose proof REP4 as (SC4 & _).
  destruct (wr_at_rw_CB m4 q 24 WRQ ltac:(lia)) as (jq & NQ). change (Z.to_nat 24) with 24%nat in NQ.
  pose proof (ki_w5 sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 (lh + 96)) (Z_to_bv 64 (lh + 56)) s10 s11 w3 w4 w5 w6 F4 fc4 m4 lo lh q rn d B items pa na' h
                jq (firstn 80 jl) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                SC4 ltac:(lia) HR ACL4 LAL8 LHI LO1 NQ ACQ ltac:(clear - Q16; Z.div_mod_to_equations; lia) QHI ltac:(lia) TERM4 PACC4 PAL ltac:(lia) PA1 PA2 PTOP
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SRL FR4 ST4 LO0 LO2 HT1 MI4) as W5.
  cl_lift W5 Hc3' c4 Hc4.
  apply Hk. exists Σ2, q.
  split.
  { apply (ASTA_conseq RT Σ2 PMc _ _ c4 Hc4). intros ms4 (w0' & w1' & w2' & e1' & e2' & e3' & e4' & e5' & e6' & e7' & w3' & w4' & w5' & w6' & F5 & fc5 & m5 & -> & MU5 & WM5 & MI5 & ST5 & NQ5 & RN5 & SC5).
    exists m5. fold usp in ST5.
    split; [exists w0', w1', w2', e1', e2', e3', e4', e5', e6', e7', w3', w4', w5', w6', F5, fc5; reflexivity|].
    assert (ART5 : ART RT Σ2 m5).
    { apply (af_frame RT AF Σ2 m4 m5 usp ART4 ltac:(rewrite SP3; lia)); [| exact WM5]. intros a Ha. apply MU5. cbn [outside].
      split; [| split; [| split; [| exact I]]]; intros X; apply Ha; right; right; left.
      - exists q, 24. split; [exact INQ| lia].
      - exists pa, na'. split; [exact (INL2 _ INP)| lia].
      - exists lh, 104. split; [exact (INL2 _ ltac:(left; reflexivity))| lia]. }
    split; [exact (conj ART5 (conj MI5 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 WM5))) ST5)))|].
    split.
    { intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (O1 & O2 & O3 & _).
      assert (SPL : usp <= bv_unsigned a \/ bv_unsigned a < usp - 304) by exact (cl_split RT AF Σ m usp 304 _ ART0 ltac:(lia) ltac:(lia) Ha).
      rewrite (MU5 a). 2:{ cbn [outside]. split; [| split; [exact O3| split; [clear - O2; lia| exact I]]].
                            exact (wg_newchunk_apart RT AF Σ Σ2 m4 [(q, 24)] q 24 usp (bv_unsigned a) ART4 LV3 ltac:(left; reflexivity) FRS3 SP3 ltac:(lia) ltac:(lia) Ha). }
      rewrite (PRES4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| cbn [outside]; exact (conj O1 I)].
      rewrite (MU2 a) by (cbn [outside]; split; [clear - SPL; lia| exact I]).
      apply MU1. cbn [outside]. split; [clear - SPL; lia|]. split; [clear - O2; lia| exact I]. }
    split; [| split; [| exact NQ5]].
    { apply (cl_env_seg _ m4 m5 _ canary ENV4 MU5). intros x Hx. cbn [outside]. unfold USTACK_TOP in *.
      pose proof (cl_cell_static _ Hx) as CS. pose proof (client_static_range _ CS) as CR. unfold SEGTOP_A in CR. repeat split; try exact I; lia. }
    apply (plh_rep_append m2 m4 m5 lh B items bks idx rn q h (Z_to_bv 64 d) [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z REP2 APLB APN APNN); try assumption.
    - apply (plh_fresh_apart RT AF Σ2 m4 lh B bks q 24 (rt_live RT Σ) ART4 LV3 ltac:(lia) INL).
    - reflexivity.
    - intros a FP NR NL. cbn [outside]. split; [| split; [exact NR| split; [clear - NL; lia| exact I]]]. intros X.
      destruct FP as [F1|[F1|(n & Hn & F1)]]; [clear - SQL F1 X; lia| |].
      + pose proof (FRESHQ B 128 (INL1 _ ltac:(right; left; reflexivity))). clear - H F1 X. lia.
      + pose proof (FRESHQ (fst n) 24 (INL1 _ (plh_L_node lh B bks n Hn))). clear - H F1 X. lia. }
  split; [exact LV3|]. split; [exact FRS3|]. split; [exact SP3|]. split; [exact CR3|]. split; [exact Q0|]. split; [exact Q16|]. split; [exact QU| exact CG3].
Qed.
End CKIns.
