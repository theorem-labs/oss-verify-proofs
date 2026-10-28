(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts D_kit X_ixdefs TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Definition W_CTR : list ivl := [(LSAN_CTR, LSAN_CTR + 4)].

Lemma W_CTR_off : forall a n, (a + n <= 0x10000 \/ SEGTOP_A <= a) -> disjoint_from W_CTR a n.
Proof. intros a n H. unfold W_CTR, LSAN_CTR, SEGTOP_A in *. cbn. split; [lia| exact I]. Qed.

Lemma lits_ctr : forall l, forallb (fun r => dsjb W_CTR (fst r) (snd r)) l = true -> dsjl W_CTR l.
Proof.
  intros l H. apply Forall_forall. intros [a n] Hin. exact (dsjb_sound _ _ _ (proj1 (forallb_forall _ _) H _ Hin)).
Qed.

Section Ctr.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma rc_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W_CTR a n.
Proof.
  intros b gn a n Hin _ _ H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (_ & _ & _ & _ & G5). apply W_CTR_off. lia.
Qed.
Lemma rc_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
  (hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> disjoint_from W_CTR a n.
Proof.
  intros lo hi a n _ _ H0 _ H1 _ _ _. apply W_CTR_off. right. unfold shad, SHB, SEGTOP_A in *. pose proof (Z.div_pos lo 8 H0 ltac:(lia)). lia.
Qed.
Lemma rc_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') -> a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) ->
  disjoint_from W_CTR a n.
Proof.
  intros a n H1 H2 _. pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & _ & G5).
  apply W_CTR_off. lia.
Qed.
Lemma rc_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W_CTR a n.
Proof.
  intros k0 s0 a n Hk H1 H2 _. destruct (map_geo Σ m HA k0 s0 Hk) as (_ & (_ & _ & _ & _ & G5) & _). apply W_CTR_off. lia.
Qed.
Lemma rc_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 ->
  (forall f k, In (f, k) (frames Σ) -> a + n <= f \/ f + fs_size k - 8 <= a) -> disjoint_from W_CTR a n.
Proof.
  intros a n H1 H2 _. pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; do 5 right; left; reflexivity)) as (_ & _ & _ & _ & G5).
  apply W_CTR_off. lia.
Qed.

Lemma rc_shad7 : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from W_CTR a n.
Proof.
  intros lo hi a n _ _ H0 _ H1 _ _. apply W_CTR_off. right. unfold shad, SHB, SEGTOP_A in *. pose proof (Z.div_pos lo 8 H0 ltac:(lia)). lia.
Qed.

Lemma cav_sec : sec_avoid W_CTR Σ.
Proof.
  split; [apply lits_ctr; vm_compute; reflexivity|]. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
  apply (ac_PAB Σ m W_CTR HA rc_grant); lia.
Qed.

Lemma cav_quar : quar_avoid W_CTR Σ.
Proof.
  split; [unfold qcacheT; apply (ac_T Σ m W_CTR HA rc_grant); lia|]. split; [apply lits_ctr; vm_compute; reflexivity|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  apply (ac_slot Σ m W_CTR HA rc_prb 24 i CkBatch); [lia | exact Hi | lia | change (ClassSize 24) with 8192; lia | intros n' E; discriminate E].
Qed.

Lemma cav_dep : dep_avoid W_CTR L.
Proof. split; [apply lits_ctr; vm_compute; reflexivity|]. split; [apply (ac_DNB Σ m W_CTR HA rc_grant) | apply (ac_SSB Σ m W_CTR HA rc_grant)]; lia. Qed.

Lemma cav_ia : dsjl W_CTR ia_lits.
Proof. apply lits_ctr; vm_compute; reflexivity. Qed.

Lemma cav_fs : fs_avoid W_CTR Σ.
Proof.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split.
  { apply fs_gavoid_of_fsb. intros a n Ha Hn. apply rc_fsb; [lia | lia|]. intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & _). left. lia. }
  split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 5%nat ltac:(lia))|]. split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 0%nat ltac:(lia))|].
  split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 4%nat ltac:(lia))|]. split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 1%nat ltac:(lia))|].
  split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 3%nat ltac:(lia))|]. split; [exact (av_fs_cls Σ m W_CTR HA rc_shad7 rc_fsb 2%nat ltac:(lia))|].
  split; [apply lits_ctr; vm_compute; reflexivity|]. split; [apply (ac_DTV Σ m W_CTR HA rc_grant); lia|]. split; [apply (ac_T Σ m W_CTR HA rc_grant); lia|].

  apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X & Y & Zp).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
  apply W_CTR_off. lia.
Qed.

End Ctr.

Local Ltac sideC Hx := cbn [cells_size csize Nat.add length RT_rep.Z15] in Hx; unfold LSAN_CTR, SEGTOP_A, g_MFHooks, i_q_max, g_asan_flags in *; unfold_consts; lia.
Local Ltac rwcC AG WM := eapply rw_cells_agree; [eassumption | eapply agree_sub; [exact AG|] | exact WM];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; sideC Hx.
Local Ltac rocC AG := eapply ro_cells_agree; [eassumption | eapply agree_sub; [exact AG|]];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; sideC Hx.
Local Ltac rwcX X AG WM := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [exact AG|] | exact WM];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; sideC Hx.
Local Ltac rocX X AG := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [exact AG|];
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; sideC Hx.

Lemma consts_rep_frame_ctr : forall L (m m' : mem), consts_rep L m ->
  agree_on (fun x => ~ (LSAN_CTR <= x < LSAN_CTR + 4)) m m' -> wmono bsegs m m' ->
  rw_cells bsegs m' LSAN_CTR [C4 (Z_to_bv 64 0)] ->
  grant_ok L (l_T L) 4096 -> grant_ok L (l_TCX L) 0x10000 -> grant_ok L (l_MT L) 0x38e000 ->
  consts_rep L m'.
Proof.
  intros L m m' H AG W CTR (_ & _ & _ & _ & GT) (_ & _ & _ & _ & GX) (_ & _ & _ & _ & GM).
  destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
                 & (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
                    & X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43 & X44 & X45 & X46)).
  assert (M' : m2s_cells m') by (split; [rwcC AG W | split; [rwcC AG W | rwcC AG W]]).
  split; [split; [rwcC AG W | rwcC AG W]|].
  split; [split; [rwcC AG W | split; [rwcC AG W | split; [rwcC AG W | split; [rwcC AG W | rwcC AG W]]]]|].
  split; [split; [split; [rwcC AG W | split; [rwcC AG W | split; [rwcC AG W | rwcC AG W]]] | rwcC AG W]|].
  split; [exact M'|].
  split; [split; [rwcC AG W | split; [exact M' | split; [split; [rwcC AG W | rwcC AG W] | split; [rwcC AG W | rwcC AG W]]]]|].
  split; [split; [rwcC AG W | rwcC AG W]|].
  split; [split; [rocC AG | split; [rocC AG | split; [rocC AG | rocC AG]]]|].
  split; [rwcX X1 AG W|]. split; [rocX X2 AG|]. split; [rocX X3 AG|]. split; [rocX X4 AG|]. split; [rocX X5 AG|]. split; [rocX X6 AG|].
  split; [rocX X7 AG|]. split; [rwcX X8 AG W|]. split; [rocX X9 AG|]. split; [rocX X10 AG|]. split; [rocX X11 AG|]. split; [rocX X12 AG|].
  split; [rocX X13 AG|]. split; [rocX X14 AG|]. split; [rocX X15 AG|]. split; [rocX X16 AG|]. split; [rocX X17 AG|]. split; [rocX X18 AG|].
  split; [rwcX X19 AG W|]. split; [rwcX X20 AG W|]. split; [rwcX X21 AG W|]. split; [rwcX X22 AG W|]. split; [rwcX X23 AG W|]. split; [rwcX X24 AG W|].
  split; [rwcX X25 AG W|]. split; [rwcX X26 AG W|].
  split; [exact CTR|].
  split; [rwcX X28 AG W|]. split; [rwcX X29 AG W|]. split; [rwcX X30 AG W|].
  split; [rwcX X31 AG W|].
  split; [exact (stk_wmono m m' _ _ X32 W)|].
  split; [rwcX X33 AG W|]. split; [rwcX X34 AG W|]. split; [rwcX X35 AG W|]. split; [rwcX X36 AG W|].
  split; [rwcX X37 AG W|]. split; [rwcX X38 AG W|]. split; [rwcX X39 AG W|]. split; [rwcX X40 AG W|]. split; [rwcX X41 AG W|].
  split; [destruct X42 as (Q1 & Q2 & Q3 & Q4); split; [rwcX Q1 AG W|]; split; [rwcX Q2 AG W|]; split; [rwcX Q3 AG W | rwcX Q4 AG W]|].
  unfold io_rw, io_ro in *. refine (conj _ (conj _ (conj _ _))); [ | | rwcX X45 AG W | rocX X46 AG].
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwcX Y AG W|] end.
    apply Forall_nil.
  - repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
      let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rocX Y AG|] end.
    apply Forall_nil.
Qed.

Section Main.
Variables (Σ : rtsA) (m m' : mem) (sp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : rtA_sp0 Σ - STACK_WIN <= sp.
Hypothesis AGR : forall a : word, ~ aclient (rtA_live Σ) (frames Σ) sp (bv_unsigned a) -> ~ (LSAN_CTR <= bv_unsigned a < LSAN_CTR + 4) -> m' a = m a.
Hypothesis CTR : rw_cells bsegs m' LSAN_CTR [C4 (Z_to_bv 64 0)].
Hypothesis WM : wmono bsegs m m'.

Definition mh : mem := fun a => if ((LSAN_CTR <=? bv_unsigned a) && (bv_unsigned a <? LSAN_CTR + 4))%bool then m a else m' a.

Lemma mh_in : forall a : word, LSAN_CTR <= bv_unsigned a < LSAN_CTR + 4 -> mh a = m a.
Proof. intros a H. unfold mh. destruct (Z.leb_spec LSAN_CTR (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) (LSAN_CTR + 4)); cbn; try reflexivity; lia. Qed.
Lemma mh_out : forall a : word, ~ (LSAN_CTR <= bv_unsigned a < LSAN_CTR + 4) -> mh a = m' a.
Proof. intros a H. unfold mh. destruct (Z.leb_spec LSAN_CTR (bv_unsigned a)); destruct (Z.ltb_spec (bv_unsigned a) (LSAN_CTR + 4)); cbn; try reflexivity; lia. Qed.

Lemma ART_mh : ART_A Σ mh.
Proof.
  apply (ART_client_frame_vis Σ m mh sp HA Hsp).
  - intros a Ha. destruct (Z_lt_le_dec (bv_unsigned a) LSAN_CTR) as [Hl|Hl]; [rewrite mh_out by lia; apply AGR; [exact Ha| lia]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (LSAN_CTR + 4)) as [Hh|Hh]; [rewrite mh_in by lia; reflexivity|].
    rewrite mh_out by lia. apply AGR; [exact Ha| lia].
  - intros a Hw. destruct (Z_lt_le_dec (bv_unsigned a) LSAN_CTR) as [Hl|Hl]; [| destruct (Z_lt_le_dec (bv_unsigned a) (LSAN_CTR + 4)) as [Hh|Hh]].
    + rewrite (wview_agree bsegs m' mh a (mh_out a ltac:(lia))). exact (WM a Hw).
    + rewrite (wview_agree bsegs m mh a (mh_in a ltac:(lia))). exact Hw.
    + rewrite (wview_agree bsegs m' mh a (mh_out a ltac:(lia))). exact (WM a Hw).
Qed.

Lemma MU_mh : munch W_CTR mh m'.
Proof. intros x Hx. unfold W_CTR in Hx. cbn in Hx. symmetry. apply mh_out. tauto. Qed.

Lemma WM_mh : wmono bsegs mh m'.
Proof.
  intros a Hw. destruct (Z_lt_le_dec (bv_unsigned a) LSAN_CTR) as [Hl|Hl]; [| destruct (Z_lt_le_dec (bv_unsigned a) (LSAN_CTR + 4)) as [Hh|Hh]].
  - rewrite <- (wview_agree bsegs m' mh a (mh_out a ltac:(lia))). exact Hw.
  - apply WM. rewrite <- (wview_agree bsegs m mh a (mh_in a ltac:(lia))). exact Hw.
  - rewrite <- (wview_agree bsegs m' mh a (mh_out a ltac:(lia))). exact Hw.
Qed.

Theorem ctr_frame : ART_A Σ m'.
Proof.
  pose proof ART_mh as H. pose proof (ART_wf Σ mh H) as Hwf. pose proof MU_mh as MU. pose proof WM_mh as WM'.
  pose proof (rc_grant Σ mh H) as RG. pose proof (rc_shad Σ) as RS. pose proof (rc_prb Σ mh H) as RP. pose proof (rc_secmap Σ mh H) as RM.
  apply ART_intro; [exact Hwf | | | | | | | | | | |].
  - apply (consts_rep_frame_ctr (lay Σ) mh m' (ART_consts Σ mh H)); [intros a Ha; symmetry; exact (mh_out a Ha) | exact WM' | exact CTR | | |];
      apply (geo_grant Σ mh H); unfold startup_grants; [do 2 right; left | do 3 right; left | do 8 right; left]; reflexivity.
  - intros c Hc. exact (reg_rep_transport W_CTR _ c _ mh m' (ART_prim Σ mh H c Hc) MU WM' (proj1 (av_reg Σ mh W_CTR H RG RS RP c Hc))).
  - intros c Hc. exact (pclass_rep_transport W_CTR _ c _ _ mh m' (ART_cache Σ mh H c Hc) MU WM' (proj2 (av_reg Σ mh W_CTR H RG RS RP c Hc))).
  - destruct (ART_chunk Σ mh H) as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W_CTR _ c i st mh m' (P c i st Hc Hn) MU WM' (av_pchunk Σ mh W_CTR H RS RP c i st Hc Hn)).
    + intros k s0 Hk. exact (schunk_transport W_CTR k s0 mh m' (S k s0 Hk) MU WM' (av_schunk Σ mh W_CTR H RS RM k s0 Hk)).
  - exact (sec_rep_transport W_CTR Σ mh m' (ART_sec Σ mh H) MU WM' (cav_sec Σ mh H)).
  - exact (quar_rep_transport W_CTR Σ mh m' (ART_quar Σ mh H) MU WM' (cav_quar Σ mh H)).
  - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
    exact (dep_rep_transport W_CTR _ _ mh m' (ART_dep Σ mh H) Hdok MU WM' (cav_dep Σ mh H)).
  - exact (fs_rep_transport W_CTR Σ mh m' (ART_fs Σ mh H) MU WM' (cav_fs Σ mh H)).
  - exact (ia_rep_transport W_CTR Σ mh m' (ART_ia Σ mh H) MU WM' cav_ia).
  - exact (shadow_rep_transport W_CTR _ mh m' (ART_shadow Σ mh H) MU WM' (av_shadow Σ mh W_CTR H RS)).
  - exact (vis_rep_wmono _ mh m' (ART_vis Σ mh H) WM').
Qed.

End Main.

Theorem rta_ctr_frame : forall Σ (m m' : mem) (sp : Z), ART RTA Σ m -> rt_sp0 RTA Σ - STACK_WIN <= sp ->
  (forall a : word, ~ aclient (rt_live RTA Σ) (rt_frames RTA Σ) sp (bv_unsigned a) -> ~ (LSAN_CTR <= bv_unsigned a < LSAN_CTR + 4) -> m' a = m a) ->
  rw_cells bsegs m' LSAN_CTR [C4 (Z_to_bv 64 0)] -> wmono bsegs m m' -> ART RTA Σ m'.
Proof. intros Σ m m' sp HA Hsp AGR CTR WM. exact (ctr_frame Σ m m' sp HA Hsp AGR CTR WM). Qed.
