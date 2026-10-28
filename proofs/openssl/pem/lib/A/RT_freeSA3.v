(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit I_lkit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_deallocate R_qput R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_freelift RT_fkit RT_freestate RT_freeA RT_freeA2 RT_geo0 RT_freeS RT_drain_kit RT_freeSA RT_freeSA2 RT_freeSL1 RT_freeSL2 RT_freeSL3 R_asan_front_k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section SegRunSL.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (usp lo : Z) (tr : list Z) (tb : list word).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis Hlow : s_mb s + smsz (s_n s) <= K_LOW_SHADOW_lo.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis ST : stk asegs m lo (usp + -2128).
Hypothesis MI : mem_inv asegs m.
Hypothesis BC : rw_cells asegs m (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis TB : u64arr asegs m (usp + -2112) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis Htr : free_tr_shape (l_cg (lay Σ)) tr.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation n := (s_n s).
#[local] Notation M := (s_mb s + 6128).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp).

(* [comment removed for export] *)
Lemma srs_facts_L : 0xbc6000 <= M /\ M mod 16 = 0 /\ M + 24 <= lo /\ 1 <= n < 2 ^ 32 /\ M + 16 + ru8 n <= MB + MSZ
  /\ (M + 24 <= T + 2824 \/ T + 2840 <= M) /\ (M + 24 <= TCX + 152 \/ TCX + 160 <= M)
  /\ (M + 24 <= DNB \/ DNB + 2 ^ 20 <= M) /\ (M + 24 <= SSB \/ SSB + 2 ^ 23 <= M) /\ MB + MSZ <= l_ACEIL L /\ 1 <= n <= 2 ^ 28
  /\ MB <= M /\ 0 <= ru8 n / 8 /\ M + 16 + ru8 n <= kLowMemEnd + 1.
Proof using HA Hk Hlow HLO.
  clear - HA Hk Hlow HLO.
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  pose proof (geo_of_ART Σ m HA) as HG.
  pose proof (dk_map Σ HG k s Hk) as (_ & _ & _ & _ & _ & _ & Q7 & _). pose proof (Q7 3%nat TCX 0x10000 eq_refl) as QX.
  pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & _).
  assert (HMB : SEGTOP_A <= MB) by (clear - K7 K9 K15 K16 K17; unfold SEGTOP_A in *; lia).
  unfold kLowMemEnd, K_LOW_SHADOW_lo, SEGTOP_A, SHB in *. repeat split; lia.
Qed.

Lemma segA_run_sL : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
  evt asegs (sA_run_post_s Σ k s usp lo tr gp s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (Z_to_bv 64 0x1c319c) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16))
             (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) a6 a7
             (Z_to_bv 64 0x1c312c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom asegs)).
Proof using HA Hk Hq Hlow Hsp Husp HLO HLO2 ST MI BC TB HTB Htr.
  intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
  pose proof (sr_tcx Σ m HA) as (XC1 & XC3 & XCP & XC4 & XC5 & XCT).
  pose proof (sr_tr _ tr Htr) as (TRM & TRL & TRR).
  pose proof srs_facts_L as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14).
  (* [comment removed for export] *)
  destruct (ART_chunk Σ m HA) as [_ CS]. pose proof (CS k s Hk) as X. unfold schunk in X.
  replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
  destruct X as (SX1 & WrS & LCH & HDR & STSH & SX6 & SHU & SX8). rewrite Hq in HDR, SHU.
  destruct HDR as (b1 & ctx & Hb1 & HD). clear CS.
  (* [comment removed for export] *)
  pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
  destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
    & I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
  assert (ISTK : stk asegs m (T + 2768) (T + 3168)) by assumption.
  assert (IMFH : rw_cells asegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]) by assumption.
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I27 I28 I29 I30
        I31 I32 I33 I34 I35 I36 I37 I38.
  (* [comment removed for export] *)
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.
  (* [comment removed for export] *)
  destruct (fl_CB_of_wr m MB MSZ (M + 16) 8 WrS ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
  destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split asegs m (T + 2768) (T + 2824) (T + 3168) ISTK ltac:(lia)) as [_ X];
                                          destruct (stk_split asegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
                                          replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
  assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
  rewrite <- Eb in HD. clear Eb.
  assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  eapply evt_cut.
  { apply (dealloc_p1_spec_L (Z_to_bv 64 0x1c319c) (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) a6 a7
             (Z_to_bv 64 0x1c312c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             M n (bv_unsigned b1) (usp + -2128) TCX T lo ctx fr fd uw).
    1: exact F1. 1: exact F2. 1: exact F3. 1: exact F4. 1: exact Rb1. 1: exact Hb1. 1: exact HD. 1: exact UW. 1: exact IMFH. 1: exact TC.
    1: exact XC1. 1: clear - XC3 HLO; lia. 1: exact K24. 1: clear - T5; unfold SEGTOP_A in *; lia. 1: clear - K25 HLO; lia. 1: exact STS.
    1: exact F6. 1: exact F7. 1: rewrite (unsigned_lit (usp + -2128)) by exact RSP; exact ST. 1: rewrite (unsigned_lit (usp + -2128)) by exact RSP; clear - HLO2; lia.
    1: rewrite (unsigned_lit (usp + -2128)) by exact RSP; clear - Husp; unfold USTACK_TOP in *; lia. 1: exact MI. }
  intros ms2 P2.
  destruct P2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & fr' & fd' & m2 & -> & MU2 & WM2 & MI2 & HD2 & UW2 & STS2 & ST2).
  rewrite (unsigned_lit (usp + -2128)) in MU2, ST2 by exact RSP.
  assert (MW2 : munch W m m2).
  { lazymatch type of MU2 with munch ?W2 _ _ => apply (munch_weaken W2 _ m m2); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU2] end. }
  pose proof (ss_consts Σ m k s usp HA Hk Hsp m2 MW2 WM2) as CR2.
  destruct CR2 as (_ & _ & TC2 & _ & _ & _ & _ & ICR2).
  destruct ICR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J31 & _ & J33 & _ & _ & _ & _ & _).
  lazymatch type of MU2 with munch ?W2 _ _ =>
    apply (rw_cells_transport asegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; clear - F3 K25 HLO HLO2 Hsp; repeat split; try exact I; lia];
    apply (u64arr_transport asegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
    [| rewrite wr_trace_length by (rewrite HTB; clear - TRL; lia); rewrite HTB; cbn [disjoint_from]; clear - F3 K25 HLO HLO2 Hsp;
       repeat split; try exact I; lia] end.
  assert (HMS : SEGTOP_A <= M) by (clear - F1; unfold SEGTOP_A in *; lia).
  lazymatch type of MU2 with munch ?W2 _ _ => apply (dep_rep_transport W2 L (dep Σ) m m2) in DREP; [| exact DOK | exact MU2 | exact WM2 |] end.
  2:{ split; [|split].
      - unfold dsjl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; repeat split; try exact I;
          first [ (left; clear - HMS; unfold SEGTOP_A in *; lia) | (clear - T5 K24; unfold SEGTOP_A in *; lia)
                | (left; clear - Hsp K32 HLO; unfold SEGTOP_A, SHB in *; lia) ].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - F8; lia | clear - ATD; lia | clear - K28 Hsp; lia].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - F9; lia | clear - ATS; lia | clear - K31 Hsp; lia]. }
  rewrite wr_trace_split in TB. replace (usp + -2112) with (usp + -2128 + 16) in BC, TB by lia.
  rewrite <- (length_map (Z_to_bv 64) tr) in BC.
  (* [comment removed for export] *)
  eapply evt_cut.
  { apply (qchunk_spec_L (Z_to_bv 64 0x1c319c) (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) u3 u4 u5 u6
             (Z_to_bv 64 0x1c312c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
             M n (bv_unsigned b1) (usp + -2128) TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
             (DEP_BK (l_cg (lay Σ)) (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST2.
    all: try (clear - F3 K25 HLO; lia).
    all: try (clear - XC3 HLO; lia).
    all: try (clear - T5; unfold SEGTOP_A in *; lia).
    all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia).
    all: try (rewrite length_map; clear - TRL; lia).
    all: try (rewrite <- wr_trace_split, wr_trace_length by (rewrite HTB; clear - TRL; lia); exact HTB).
    all: try (exact (depot_ok_mono _ _ _ _ _ DOK HLO)).
    all: try (rewrite length_map; clear - DT TRL; lia).
    all: try (rewrite map_unsigned_lits by exact TRR; unfold DEP_BK; right; apply in_map_iff; exists tr; split; [reflexivity | exact TRM]). }
  intros ms3 P3.
  destruct P3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & m3 & -> & MU3 & WM3 & MI3 & W16 & REP3 & TB3 & ST3).
  rewrite (unsigned_lit (usp + -2128)) in MU3, ST3 by exact RSP.
  assert (MW3 : munch W m m3).
  { apply (munch_trans _ m m2 m3 MW2).
    lazymatch type of MU3 with munch ?W3 _ _ => apply (munch_weaken W3 _ m2 m3); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU3] end. }
  pose proof (wmono_trans asegs _ _ _ WM2 WM3) as WM23.
  pose proof (ss_consts Σ m k s usp HA Hk Hsp m3 MW3 WM23) as CR3.
  destruct CR3 as (_ & _ & _ & _ & PS3 & _ & _ & ICR3).
  destruct ICR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & K23' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35' & K36' & _ & _).
  apply (rwc_app asegs _ _ [C8 (Z_to_bv 64 268435456)]) in K35'. destruct K35' as [QM K35']. cbn [cells_size csize Nat.add] in K35'.
  apply (rwc_app asegs _ _ [C8 (Z_to_bv 64 241591905)]) in K35'. destruct K35' as [_ QC]. cbn [cells_size csize Nat.add] in QC.
  change (i_q_max + Z.of_nat 8 + Z.of_nat 8) with 6723584 in QC. change i_q_max with 6723568 in QM.
  (* [comment removed for export] *)
  lazymatch type of MU3 with munch ?W3 _ _ =>
    apply (rw_cells_transport asegs W3 m2 m3 _ _) in HD2; [| exact MU3 | exact WM3 |];
    [| cbn [disjoint_from cells_size csize Nat.add];
       repeat split; try exact I;
       first [ (left; clear; lia) | (right; clear - HMS; unfold SEGTOP_A in *; lia) | (clear - F8; lia) | (clear - F9; lia)
             | (left; clear - F3 HLO HLO2 Hsp; lia) ] ] end.
  (* [comment removed for export] *)
  assert (SHC : rw_cells asegs m (shad (M + 16)) [CB (length (ushadow n)) (ushadow n)]).
  { apply (fl_CB_of_bytes m _ _ _ _ SHU STSH K21). rewrite fl_ushadow_len by lia. exact K22. }
  replace (length (ushadow n)) with (Z.to_nat (ru8' n / 8)) in SHC by (unfold ru8'; pose proof (fl_ushadow_len n ltac:(lia)) as U; unfold ru8 in U; lia).
  lazymatch type of MU2 with munch ?W2 _ _ =>
    apply (rw_cells_transport asegs W2 m m2 _ _) in SHC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
       change (ru8' n) with (ru8 n); repeat split; try exact I;
       first [ (right; clear - Hlow K16 K18 K20 K21; unfold K_LOW_SHADOW_lo, SHB in *; lia)
             | (clear - T4 K20 K21 K22 K23 K19; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (left; clear - K22 K23 K32 HLO Hsp; unfold SHB in *; lia) ] ] end.
  lazymatch type of MU3 with munch ?W3 _ _ =>
    apply (rw_cells_transport asegs W3 m2 m3 _ _) in SHC; [| exact MU3 | exact WM3 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
       change (ru8' n) with (ru8 n); repeat split; try exact I;
       first [ (right; clear - Hlow K16 K18 K20 K21; unfold K_LOW_SHADOW_lo, SHB in *; lia) | (right; clear - K20 K21; unfold SHB in *; lia)
             | (clear - D4 K20 K21 K22 K23 K19; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (clear - S4 K20 K21 K22 K23 K19; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (left; clear - K22 K23 K32 HLO Hsp; unfold SHB in *; lia) ] ] end.
  (* [comment removed for export] *)
  eapply evt_mono.
  { apply (qput_A_spec_L (Z_to_bv 64 0x1c319c) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) v3 v4
             (Z_to_bv 64 0x1c312c) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
             (T + 80) (T + 208) (usp + -2128) M n (bv_unsigned b1) lo ctx (ushadow n)); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST3.
    all: try (change (ru8' n) with (ru8 n); clear - F5 F10 K33; unfold kHighMemEnd; lia).
    all: try (change (ru8' n) with (ru8 n); clear - F5 F10 HLO; lia).
    all: try (clear - HLO2; lia).
    all: try (clear - HLO K32; unfold kHighShadowEnd, SHB in *; lia).
    all: try (clear - HLO K3 K4; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
    all: try (split; [exact F1 | change (ru8' n) with (ru8 n); exact F14]). }
  intros ms4 P4.
  destruct P4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & m4 & -> & MU4 & WM4 & MI4 & SH4 & FR4 & ST4).
  rewrite (unsigned_lit (usp + -2128)) in MU4, ST4, FR4 by exact RSP.
  assert (MW4 : munch W m m4).
  { apply (munch_trans _ m m3 m4 MW3).
    lazymatch type of MU4 with munch ?W4 _ _ => apply (munch_weaken W4 _ m3 m4); [unfold W_A1; clear - Hsp; change (ru8' n) with (ru8 n); solve_sub_fp | exact MU4] end. }
  pose proof (wmono_trans asegs _ _ _ WM23 WM4) as WM24.
  (* [comment removed for export] *)
  assert (HQ : qhdr3 m4 M n).
  { lazymatch type of MU4 with munch ?W4 _ _ =>
      apply (rw_cells_transport asegs W4 m3 m4 _ _) in HD2; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
         first [ (left; clear - Hlow K16 K18 K20 K21; unfold K_LOW_SHADOW_lo, SHB in *; lia) | (left; clear - F3 HLO HLO2 Hsp; lia) ] ];
      apply (rw_cells_transport asegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
         first [ (left; clear - Hlow K16 K18 K20 K21; unfold K_LOW_SHADOW_lo, SHB in *; lia) | (left; clear - F3 HLO HLO2 Hsp; lia) ] ] end.
    exists (Z_to_bv 8 (bv_unsigned b1)), ctx, (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr))))).
    split; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite (Z.mod_small (bv_unsigned b1) 256) by exact Rb1; exact Hb1|].
    change [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx;
            C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]
      with ([C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ++
            [C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]).
    apply rwc_app. split; [exact HD2|]. cbn [cells_size csize Nat.add]. exact W16. }
  (* [comment removed for export] *)
  rewrite map_unsigned_lits in REP3 by exact TRR.
  lazymatch type of MU4 with munch ?W4 _ _ =>
    apply (depot_rep_frame _ _ _ _ lo W4 m3 m4) in REP3; [| | exact MU4 | exact WM4 | | | | | |] end.
  2:{ apply (qc_depot_ok_put_ok _ _ _ _ _ (depot_ok_mono _ _ _ _ _ DOK HLO) DN). clear - DT TRL; lia. }
  all: try (cbn [disjoint_from]; change (ru8' n) with (ru8 n); repeat split; try exact I;
            first [ (right; clear - K20 K21; unfold SHB in *; lia) | (left; clear - K27 K32 HLO Hsp; unfold SEGTOP_A, SHB in *; lia)
                  | (clear - D4 K20 K21 K22 K23 K19; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
                  | (clear - S4 K20 K21 K22 K23 K19; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
                  | (left; clear - K28 Hsp; lia) | (left; clear - K31 Hsp; lia) ]).
  pose proof (segA_ART_s Σ m k s usp HA Hk Hq Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 HQ SH4 REP3
                (qc_depot_ok_put_ok (dep Σ) tr DNB SSB (l_ACEIL L) DOK DN ltac:(clear - DT TRL; lia)) (dep_inv_put (dep Σ) tr DINV TRM ltac:(clear - TRL; lia))
                (dp_hash1 _ _ DINV)) as ART4.
  unfold sA_run_post_s. do 10 eexists. exists m4. split.
  { rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
  split; [exact ART4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
  split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
  replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End SegRunSL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition segA_post_s (Σ : rtsA) (k : nat) (s : secst) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (tr : list Z) (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x19f2dc) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 208))
                 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (s_mb s + 6128)) (Z_to_bv 64 (s_n s)) a5' a6' a7'
                 (Z_to_bv 64 (s_n s)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (l_T (lay Σ) + 208))
                 (Z_to_bv 64 (s_mb s + 6128)) (Z_to_bv 64 0x100000)
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m' (seg_rom asegs)
    /\ ARTc (free_s Σ k s (fst (depot_put (dep Σ) tr))) m'
    /\ free_tr_shape (l_cg (lay Σ)) tr
    /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo (bv_unsigned sp + -2208)
    /\ rt_pres (live_remove (s_ubeg s) (live Σ)) (frames Σ) (bv_unsigned sp) m m'
    /\ icpt_frame m' (bv_unsigned sp) ra s0 s1 s2 s3 s4 s5
    /\ qput_frame m' (bv_unsigned sp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x1c319c)
         (Z_to_bv 64 (bv_unsigned sp)) (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x1c312c) (Z_to_bv 64 1)
         (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6.

Theorem segA_evt_s : forall (Σ : rtsA) (k : nat) (s : secst)
    (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  ART_A Σ m -> mem_inv asegs m -> call_ok RTA Σ m sp lo -> unwind_ok (l_cg (lay Σ)) e_free m ra s0 sp ->
  nth_error (sec Σ) k = Some s -> s_quar s = false ->
  evt asegs (segA_post_s Σ k s ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m).
Proof.
  intros Σ k s ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ART0 MI0 CALL UWOK Hk Hq.
  pose proof (mp_cells Σ m ART0) as (G60 & GCF & _ & _ & AI & MCS & _ & PSC & FUM & TC & SC & UB).
  pose proof (mp_layout Σ m sp lo ART0 CALL) as (HTCX & HTCXl & HTl & HTT & HLOH & Hbt & Htop & HT).
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (ss_geo Σ m k s ART0 Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  destruct (ART_ia Σ m ART0) as (b & IS).
  (* [comment removed for export] *)
  assert (HW : exists tr, free_tr_shape (l_cg (lay Σ)) tr
             /\ evt asegs (free_pre_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (s_ubeg s) (l_T (lay Σ)) lo tr m)
                  (entry_st ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 (s_ubeg s)) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)).
  { apply (free_front_spec ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (s_ubeg s) (l_TCX (lay Σ)) (l_T (lay Σ)) (l_top (lay Σ)) (l_top (lay Σ) - 0x800000) lo b (l_cg (lay Σ)) (ART_cg_wf Σ m ART0));
      try assumption.
    all: try (unfold s_ubeg; clear - K7 K8 K15 K16 K17 K33; lia).
    all: try (clear - LOR; unfold RT_STACK in *; lia).
    all: try (clear - SPT; unfold USTACK_TOP in *; lia).
    all: try (clear - Hbt; lia). all: try (clear - Htop; lia). all: try (clear - HT; unfold img_hull_lo, img_hull_hi, SEGTOP_A in *; lia).
    all: try (pose proof (sr_tcx Σ m ART0) as (_ & _ & _ & _ & X5 & _); clear - X5; unfold SEGTOP_A in *; lia). }
  destruct HW as (tr & Htr & HW).
  eapply evt_cut; [exact HW|]. clear HW.
  intros ms1 P1.
  destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & tb & jp & m1 & -> & MU1 & WM1 & MI1 & IS1 & FRs & FRp & FRt & TB & HTB & FRb & TB1 & ST1).
  set (usp := bv_unsigned sp) in *.
  assert (Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp) by (clear - LOW LOR; unfold l_ACEIL, RT_STACK in *; lia).
  assert (Hsp' : l_ACEIL (lay Σ) + 0xF000 <= usp) by (clear - Hsp; lia).
  pose proof (fn_ART Σ m usp ART0 Hsp' m1 MU1 WM1 IS1 TB1) as ART1.
  replace (s_ubeg s) with (s_mb s + 6128 + 16) by (unfold s_ubeg; clear; lia).
  assert (Husp : usp + 16 <= USTACK_TOP) by (clear - SPT; unfold USTACK_TOP in *; lia).
  assert (HLO' : l_ACEIL (lay Σ) <= lo) by (clear - LOW; unfold l_ACEIL in *; lia).
  assert (HLO2 : lo + 0x10000 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
  eapply evt_mono.
  { destruct K10 as [HL|HH].
    - exact (segA_run_sL Σ m1 k s usp lo tr tb ART1 Hk Hq HL Hsp Husp HLO' HLO2 ST1 MI1 FRb TB HTB Htr
               gp x0 x1 x2 x3 x4 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8 F fc).
    - exact (segA_run_s Σ m1 k s usp lo tr tb ART1 Hk Hq HH Hsp Husp HLO' HLO2 ST1 MI1 FRb TB HTB Htr
               gp x0 x1 x2 x3 x4 s6 s7 s8 s9 s10 s11 x5 x6 x7 x8 F fc). }
  intros ms P. destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m' & -> & ART' & MI' & WM' & MW' & ST' & FR').
  unfold segA_post_s. exists tr, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, m'. split; [reflexivity|].
  split; [exact ART'|].
  split; [exact Htr|]. split; [exact MI'|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM')|]. split; [exact ST'|]. split.
  { intros a Ha. rewrite (MW' a (ss_client Σ m1 k s usp ART1 Hk Hsp _ Ha)).
    exact (MU1 a (fn_client Σ m usp ART0 Hsp' _ (aclient_live_remove _ _ _ _ _ Ha))). }
  split; [|exact FR'].
  apply (icpt_frame_transport (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp)
           m1 m' usp ra s0 s1 s2 s3 s4 s5); [| exact MW' | exact WM' |].
  - split; [exact FRs|]. split; [exists jp; exact FRp|]. split; [exact FRt|]. split; [exists (wr_trace tr tb); split; [exact TB|]|].
    + rewrite wr_trace_length; [exact HTB|]. rewrite HTB. destruct (free_tr_shape_main tr Htr) as (_ & (_ & HL7) & _); lia.
    + exists (Z_to_bv 64 (Z.of_nat (length tr))). exact FRb.
  - unfold W_A1. cbn [disjoint_from].
    clear - K8 K15 K16 K17 K18 K21 K22 K23 K25 K28 K31 K32 Hsp. unfold SHB in *. repeat split; try exact I; lia.
Qed.
