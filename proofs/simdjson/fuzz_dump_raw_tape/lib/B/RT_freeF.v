(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Section Stk.
Variables (Σ : rtsA) (a b : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Ha : l_ACEIL (lay Σ) <= a.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := [(a, b)].

Lemma sk_below : forall x k, x + k <= l_ACEIL L -> disjoint_from W x k.
Proof using Ha. clear - Ha. intros x k H. cbn [disjoint_from]. split; [lia | exact I]. Qed.

Lemma sk_geo : 0 < l_PRB L /\ l_PRB L + 0x2000011000 <= l_ACEIL L /\ l_PRB L <= SB /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47.
Proof using HG.
  clear - HG. pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4). pose proof (fk_aceil Σ HG) as (X1 & X2). repeat split; lia.
Qed.

Lemma sk_shad : forall lo hi x k, 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= x -> x + k <= shad hi -> disjoint_from W x k.
Proof using HG Ha.
  intros lo hi x k H0 H1 H2 H3. apply sk_below. pose proof sk_geo as (_ & _ & _ & _ & X1 & _). pose proof (shad_hi hi H1). clear - X1 H3 H. lia.
Qed.

Lemma sk_img : forall x k, 0x10000 <= x -> x + k <= SEGTOP_A -> disjoint_from [] x k -> disjoint_from W x k.
Proof using HG Ha. intros x k H1 H2 _. apply sk_below. pose proof sk_geo as (_ & _ & _ & _ & X1 & _). clear - X1 H2. unfold SEGTOP_A, SHB in *. lia. Qed.
Lemma sk_T : forall x k, l_T L <= x -> x + k <= l_T L + 4096 -> disjoint_from [] x k -> disjoint_from W x k.
Proof using HG Ha.
  intros x k H1 H2 _. apply sk_below. pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & G3 & _). clear - G3 H2. lia.
Qed.
Lemma sk_grant : forall j g gn x k, nth_error (startup_grants L) j = Some (g, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  g <= x -> x + k <= g + gn -> disjoint_from W x k.
Proof using HG Ha. intros j g gn x k Hj _ H1 H2. apply sk_below. pose proof (g_grant Σ HG g gn (nth_error_In _ _ Hj)) as (_ & _ & G3 & _). clear - G3 H2. lia. Qed.
Lemma sk_grant67 : forall j g gn x k, nth_error (startup_grants L) j = Some (g, gn) -> (j = 6 \/ j = 7)%nat ->
  g <= x -> x + k <= g + gn -> disjoint_from W x k.
Proof using HG Ha. intros j g gn x k Hj _ H1 H2. apply sk_below. pose proof (g_grant Σ HG g gn (nth_error_In _ _ Hj)) as (_ & _ & G3 & _). clear - G3 H2. lia. Qed.
Lemma sk_ris : forall c x k, 1 <= c <= 31 -> ~ In c [] -> rinfo (RIS_of SB) c <= x -> x + k <= rinfo (RIS_of SB) c + 120 -> disjoint_from W x k.
Proof using HG Ha. intros c x k Hc _ H1 H2. apply sk_below. pose proof sk_geo as (_ & X1 & _ & X3 & _). unfold rinfo, RIS_of in *.
  clear - X1 X3 H2 Hc. lia. Qed.
Lemma sk_fa : forall c x k, 1 <= c <= 31 -> ~ In c [] -> fa SB c <= x -> x + k <= fa SB c + kFaCap -> disjoint_from W x k.
Proof using HG Ha. intros c x k Hc _ H1 H2. apply sk_below. pose proof sk_geo as (_ & X1 & _ & X3 & _). clear - X1 X3 H2 Hc. unfold fa, rb, kFaCap in *. lia. Qed.
Lemma sk_slot : forall c i st x k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  p_abeg SB c i <= x -> x + k <= p_abeg SB c i + ClassSize c -> disjoint_from W x k.
Proof using HG Ha.
  intros c i st x k Hc Hn _ H1 H2. apply sk_below. pose proof (fk_slot Σ HG c i st Hc Hn) as (S1 & S2 & S3 & S4).
  pose proof sk_geo as (_ & X1 & _ & X3 & _). clear - X1 X3 H2 S1 S2 S3 Hc. unfold rb, kUserCap in *. lia.
Qed.
Lemma sk_shad_slot : forall c i st x k, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> ~ In (c, i) [] ->
  shad (p_abeg SB c i) <= x -> x + k <= shad (p_abeg SB c i + ClassSize c) -> disjoint_from W x k.
Proof using HG Ha.
  intros c i st x k Hc Hn _ H1 H2. pose proof (fk_slot Σ HG c i st Hc Hn) as (S1 & S2 & S3 & S4). pose proof sk_geo as (X0 & X1 & X2 & X3 & X5 & X6).
  apply (sk_shad (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [clear - S1 X0 X2 Hc; unfold rb in *; lia | clear - S1 S2 S3 X1 X3 X6 Hc; unfold rb, kUserCap in *; lia | exact H1 | exact H2].
Qed.
Lemma sk_shad_reg : forall c x k, 1 <= c <= 31 -> ~ In c [] -> shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) <= x ->
  x + k <= shad (rb SB c + 2 ^ 32) -> disjoint_from W x k.
Proof using HG Ha.
  intros c x k Hc _ H1 H2. pose proof sk_geo as (X0 & X1 & X2 & X3 & X5 & X6).
  assert (0 <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) by (clear - Hc; apply Z.mul_nonneg_nonneg; [pose proof (ClassSize_range c Hc); lia | lia]).
  apply (sk_shad (rb SB c + ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (rb SB c + 2 ^ 32)); [clear - H X0 X2 Hc; unfold rb in *; lia | clear - X1 X3 X6 Hc; unfold rb in *; lia | exact H1 | exact H2].
Qed.
Lemma sk_shad_app : forall lo hi x k, 0 <= lo -> hi <= 2 ^ 47 -> (hi <= l_PRB L \/ l_PRB L + 0x2000011000 <= lo) ->
  (forall k' s', nth_error (sec Σ) k' = Some s' -> In k' [] -> hi <= s_mb s' \/ s_mb s' + smsz (s_n s') <= lo) ->
  shad lo <= x -> x + k <= shad hi -> disjoint_from W x k.
Proof using HG Ha. intros lo hi x k H0 H1 _ _ H2 H3. exact (sk_shad lo hi x k H0 H1 H2 H3). Qed.
Lemma sk_secmap : forall k s x k', nth_error (sec Σ) k = Some s -> ~ In k [] -> s_mb s <= x -> x + k' <= s_mb s + smsz (s_n s) ->
  disjoint_from W x k'.
Proof using HG Ha. intros k s x k' Hk _ H1 H2. apply sk_below. pose proof (fk_map Σ HG k s Hk) as (_ & _ & Y3 & _). clear - Y3 H2. lia. Qed.

Theorem ARTc_stack : forall (m m' : mem), ARTc Σ m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun bt => exists i, nth_error (r_st (pr Σ 24)) i = Some CkBatch /\ fst bt = p_abeg (l_SB (lay Σ)) 24 i) (ql Σ ++ qg Σ) ->
  depot_ok (dep Σ) (l_DNB L) (l_SSB L) (l_ACEIL L) -> ARTc Σ m'.
Proof using HG Ha.
  intros m m' (CR & PR & CA & CH & SR & QR & DR & FR & IR & SHR & VIS) MU WM HBt Dok.
  apply ARTc_intro.
  - apply (consts_rep_frame L m m' CR); [|exact WM]. intros x Hx. apply MU.
    destruct (Z.eq_dec (bv_unsigned x) (l_T L + 0xc60)) as [E|NE].
    + rewrite E. pose proof (g_grant Σ HG (l_T L) 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (_ & _ & G3 & _).
      cbn [outside]. clear - G3 Ha. split; [lia | exact I].
    + exact (kv_consts Σ W [] [] sk_img sk_T sk_grant ltac:(apply Forall_forall; intros; exact I) I (bv_unsigned x) Hx NE).
  - intros c Hc. exact (reg_rep_transport W _ c _ m m' (PR c Hc) MU WM (kv_reg Σ W [] HG sk_ris sk_fa sk_shad_reg c Hc ltac:(intros []))).
  - intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (CA c Hc) MU WM (kv_pclass Σ W [] sk_T c Hc I)).
  - destruct CH as [P S]. split.
    + intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (kv_pchunk Σ W [] HG sk_slot sk_shad_slot c i st Hc Hn ltac:(intros []))).
    + intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (kv_schunk Σ W [] HG sk_shad_app sk_secmap k s Hk ltac:(intros []))).
  - exact (sec_rep_transport W Σ m m' SR MU WM (kv_sec Σ W [] HG sk_img sk_grant ltac:(apply Forall_forall; intros; exact I))).
  - exact (quar_rep_transport W Σ m m' QR MU WM (kv_quar Σ W [] [] [] HG sk_img sk_T sk_slot I ltac:(apply Forall_forall; intros; exact I)
             ltac:(intros i _ []) HBt)).
  - exact (dep_rep_transport W L _ m m' DR Dok MU WM (kv_dep Σ W [] sk_img ltac:(apply Forall_forall; intros; exact I) sk_grant67)).
  - exact (fs_rep_transport W Σ m m' FR MU WM (kv_fs Σ W [] [] [] HG sk_img sk_T sk_grant sk_shad_app ltac:(apply Forall_forall; intros; exact I) I)).
  - exact (ia_rep_transport W Σ m m' IR MU WM (kv_ia W [] sk_img ltac:(apply Forall_forall; intros; exact I))).
  - exact (shadow_rep_transport W _ m m' SHR MU WM (kv_shadow Σ W [] HG sk_shad_app)).
  - exact (vis_rep_wmono _ m m' VIS WM).
Qed.

End Stk.

Lemma rt_wf_of_x : forall Σ, rt_wfx Σ -> rt_count Σ -> RT_state.qbytes (ql Σ) <= QMAX_L -> rt_wf Σ.
Proof.
  intros Σ (W1 & W2 & W3 & W4 & (Q1 & Q2 & Q3) & W6 & W7 & W8 & W9 & W10 & W11) HC HB.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [split; [exact HB | split; [exact Q2 | exact Q3]]|].
  repeat (split; [assumption|]). exact HC.
Qed.

Lemma qwf_ql_x : forall Σ, rt_wfx Σ -> qwf (l_SB (lay Σ)) (ql Σ).
Proof.
  intros Σ HW. assert (HG : geo_ok Σ) by (destruct HW as (H1 & H2 & _ & H4 & _ & H6 & _); exact (conj H1 (conj H2 (conj H4 H6)))).
  destruct HW as (_ & HR & _ & HS & HQ & _).
  destruct HQ as (_ & _ & QB & QN & QL & QE & _ & _). pose proof (g_prb Σ HG) as (P1 & P2 & P3).
  split.
  - rewrite map_app in QN. apply NoDup_ListNoDup in QN. exact (NoDup_app_remove_r _ _ QN).
  - apply Forall_forall. intros b Hb. assert (Hb' : In b (ql Σ ++ qg Σ)) by (apply in_or_app; left; exact Hb).
    destruct (proj1 (Forall_forall _ _) QB b Hb') as (i & Hi & Eb).
    pose proof (g_slot_geo Σ HG 24 i CkBatch ltac:(lia) Hi) as (S1 & S2 & S3 & _). change (ClassSize 24) with 8192 in *.
    split; [|split; [|split; [|split]]].
    + rewrite Eb. unfold p_abeg. apply Z.mod_divide in P3; [|lia]. destruct P3 as [q Hq]. rewrite Hq.
      replace (q * 2 ^ 16 + 24 * 2 ^ 32 + Z.of_nat i * 8192) with ((q * 8 + 24 * 2 ^ 19 + Z.of_nat i) * 8192) by ring. apply Z.mod_mul. lia.
    + rewrite Eb. unfold r24, rb in *. lia.
    + rewrite Eb. unfold r24, rb, kUserCap in *. lia.
    + exact (proj1 (Forall_forall _ _) QL b Hb').
    + apply Forall_forall. intros e He. assert (Hq : In e (qents Σ)).
      { unfold qents. apply in_flat_map. exists b. split; [exact Hb' | exact He]. }
      destruct (proj1 (Forall_forall _ _) QE e Hq) as [(c & j & Hc & Hj & _)|(s & Hs & _ & Hn & _)].
      * destruct HR as (HR & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
        pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hj)) as X. cbv beta iota in X. lia.
      * destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (X & _). lia.
Qed.

Definition enq_ret_st (usp T : Z) (gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra0 (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 QUAR) (Z_to_bv 64 (T + 80)) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 s4 s5 (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x5db88) fc None m (seg_rom bsegs).

Definition fin_post (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m5 : mem) : machine_state -> Prop :=
  fun ms => exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR ra sp gp (Z_to_bv 64 tpA) t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ ART_A Σ2 m' /\ mem_inv bsegs m' /\ wmono bsegs m5 m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - 2208, bv_unsigned sp)] m5 m'.

Lemma ret_tail : forall (Σ2 : rtsA) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5'
    t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws : word) (F : bvmap 5 word) (fc : bv 32) (m5 : mem) (lo : Z),
  geo_ok Σ2 -> ARTc Σ2 m5 -> rt_wfx Σ2 -> rt_count Σ2 -> RT_state.qbytes (ql Σ2) <= 0x100000 ->
  mem_inv bsegs m5 -> stk bsegs m5 lo (bv_unsigned sp + -2208) -> l_ACEIL (lay Σ2) <= lo -> lo + 0x10000 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP ->
  icpt_frame m5 (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5 ->
  qput_frame m5 (bv_unsigned sp + -2208) wc ws (Z_to_bv 64 0x80bd4) w0 w1 w2 w3 w4 w5 s6 ->
  evt bsegs (fin_post Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m5)
    (enq_ret_st (bv_unsigned sp) (l_T (lay Σ2)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m5).
Proof.
  intros Σ2 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' t3 t4 t5 t6 w0 w1 w2 w3 w4 w5 wc ws F fc m5 lo
    HG ART5 HWX HC HBY MI5 ST5 HLO HLO2 Husp ICF FR5.
  set (usp := bv_unsigned sp) in *.
  pose proof (fk_aceil Σ2 HG) as (X1 & X2).
  assert (RSP2 : 0 <= usp + -2128 < 2 ^ 64) by (clear - HLO HLO2 Husp X1; unfold USTACK_TOP, SHB in *; lia).
  pose proof ART5 as (_ & _ & _ & _ & _ & QR & _). destruct QR as (QT & _).
  pose proof QT as QT'. apply (proj1 (qcache_rep_iff _ _ _)) in QT'. destruct QT' as (QH & _).
  unfold enq_ret_st.
  replace (Z_to_bv 64 (usp + -2208)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (usp + -2128)) + -80))
    by (rewrite (unsigned_lit (usp + -2128)) by exact RSP2; f_equal; lia).
  replace (usp + -2208) with (usp + -2128 - 80) in ST5, FR5 by lia.
  pose proof (qbytes_nonneg _ _ (qwf_ql_x Σ2 HWX)) as QB0.
  eapply evt_cut.
  { apply (qput_B_ret_spec (Z_to_bv 64 0x80bd4) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 s2' s3' s4' s5' a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11
             t3 t4 t5 t6 ra0 w0 w1 w2 w3 w4 w5 s6 wc ws F fc m5 (l_T (lay Σ2) + 80) (R_quar_defs.qbytes (ql Σ2)) lo
             (Z_to_bv 64 (Z.of_nat (length (ql Σ2)))) (Z_to_bv 64 (qfirst (ql Σ2))) (Z_to_bv 64 (qlast (ql Σ2))));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP2.
    all: try exact ST5. all: try exact FR5. all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia).
    rewrite qbytes_eq. clear - QB0 HBY. rewrite qbytes_eq in QB0. lia. }
  intros ms6 P6. destruct P6 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6).
  rewrite (unsigned_lit (usp + -2128)) in MU6, ST6 by exact RSP2. rewrite (ret_pc_even 0x80bd4) by (first [reflexivity | lia]).
  destruct ICF as (FRs & (jp & FRp) & FRt & (wsb & TB & HTB) & (w & FRb)).
  assert (DSF : forall a k, usp - 2128 <= a -> disjoint_from [(usp + -2128 - 80, usp + -2128)] a k).
  { intros a k H1. cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRs MU6 WM6 ltac:(apply DSF; lia)) as FRs6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRp MU6 WM6 ltac:(apply DSF; lia)) as FRp6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRt MU6 WM6 ltac:(apply DSF; lia)) as FRt6.
  pose proof (rw_cells_transport bsegs _ m5 m6 _ _ FRb MU6 WM6 ltac:(apply DSF; lia)) as FRb6.
  pose proof (u64arr_transport bsegs _ m5 m6 _ _ TB MU6 WM6 ltac:(apply DSF; lia)) as TB6.
  clear FRs FRp FRt FRb TB.
  replace (Z_to_bv 64 (usp + -2128)) with (Z_to_bv 64 (bv_unsigned sp + -2128)) by reflexivity.
  eapply evt_mono.
  { apply (free_B_spec ra sp gp (Z_to_bv 64 tpA) y0 y1 y2 w0 w1 y3 y4 y5 y6 y7 y8 y9 y10 w2 w3 w4 w5 s6 s7 s8 s9 s10 s11 y11 y12 y13 y14
             (Z_to_bv 64 0x80bd4) s0 s1 s2 s3 s4 s5 F fc m6 lo wsb w jp); try assumption.
    all: try (clear - HLO2; lia). all: try (clear - X1 HLO; unfold SHB in *; lia). }
  intros ms P7. destruct P7 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m7 & -> & MU7 & WM7 & MI7 & ST7).
  pose proof (wmono_trans bsegs _ _ _ WM6 WM7) as WM57.
  lazymatch type of MU7 with munch ?W7 _ _ => lazymatch type of MU6 with munch ?W6 _ _ =>
    pose proof (munch_trans [(usp - 2208, usp)] m5 m6 m7 (munch_weaken W6 [(usp - 2208, usp)] m5 m6 ltac:(clear - HLO2; solve_sub_fp) MU6)
                  (munch_weaken W7 [(usp - 2208, usp)] m6 m7 ltac:(clear - HLO2; solve_sub_fp) MU7)) as MU57 end end.
  unfold fin_post. exists z3, z0, z1, z2, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m7. split; [reflexivity|].
  split; [|split; [exact MI7 | split; [exact WM57 | split; [exact ST7 | exact MU57]]]].
  apply c_ART; [exact (rt_wf_of_x Σ2 HWX HC ltac:(clear - HBY; unfold QMAX_L; lia))|].
  apply (ARTc_stack Σ2 (usp - 2208) usp HG ltac:(clear - HLO HLO2; lia) m5 m7 ART5 MU57 WM57).
  - destruct HWX as (_ & _ & _ & _ & (_ & _ & QB & _) & _). exact QB.
  - destruct HWX as (_ & _ & _ & _ & _ & _ & _ & DOK & _). exact DOK.
Qed.

End GWIN.
