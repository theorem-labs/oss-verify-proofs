(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit I_lkit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_deallocate R_qput R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_freelift RT_fkit RT_freestate RT_freeA RT_freeA2 RT_geo0 RT_freeS RT_drain_kit RT_freeSA RT_freeSL1 RT_freeSL3 RT_drain_defs RT_drain_geo RT_dsec_geo RT_freeP_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Definition sP_run_post (Σ : rtsA) (k : nat) (s : secst) (usp lo : Z) (tr : list Z) (gp s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x5d458) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (usp + -2208)) (Z_to_bv 64 (s_mb s + 6128)) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) (Z_to_bv 64 0x100000)
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x5b2e4) fc None m' (seg_rom bsegs)
    /\ ARTcK (pass_d Σ k s (fst (depot_put (dep Σ) tr))) k m'
    /\ schunkP k s m'
    /\ mem_inv bsegs m' /\ wmono bsegs m m'
    /\ munch (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (s_mb s + 6128) (s_n s) usp) m m'
    /\ stk bsegs m' lo (usp + -2208)
    /\ qput_frame m' (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 0x805b0) (Z_to_bv 64 usp)
         (Z_to_bv 64 (s_mb s + 6128 + 16)) (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128))
         (Z_to_bv 64 (usp + -81)) s6.

Section SegRunP.
Variables (Σ : rtsA) (m : mem) (k : nat) (s : secst) (usp lo : Z) (tr : list Z) (tb : list word).
Hypothesis HA : ART_A Σ m.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis Hq : s_quar s = false.
Hypothesis Hbig : 0x10000000 < s_n s.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis ST : stk bsegs m lo (usp + -2128).
Hypothesis MI : mem_inv bsegs m.
Hypothesis BC : rw_cells bsegs m (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis TB : u64arr bsegs m (usp + -2112) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis Htr : tr_ok tr /\ (1 <= length tr <= 30)%nat.
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

Section High.
Hypothesis Hhi : K_HIGH_SHADOW_hi <= s_mb s.

Lemma srp_facts_H : kHighShadowEnd < M /\ M mod 16 = 0 /\ M + 24 <= lo /\ 1 <= n < 2 ^ 32 /\ M + 16 + ru8 n <= MB + MSZ
  /\ (M + 24 <= T + 2824 \/ T + 2840 <= M) /\ (M + 24 <= TCX + 152 \/ TCX + 160 <= M)
  /\ (M + 24 <= DNB \/ DNB + 2 ^ 20 <= M) /\ (M + 24 <= SSB \/ SSB + 2 ^ 23 <= M) /\ MB + MSZ <= l_ACEIL L
  /\ MB <= M /\ 0 <= ru8 n / 8.
Proof using HA Hk Hhi HLO.
  clear - HA Hk Hhi HLO.
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  pose proof (geo_of_ART Σ m HA) as HG.
  pose proof (dk_map Σ HG k s Hk) as (_ & _ & _ & _ & _ & _ & Q7 & _). pose proof (Q7 3%nat TCX 0x10000 eq_refl) as QX.
  pose proof HG as (_ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as ((Hn1 & Hn2) & _).
  unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. repeat split; lia.
Qed.

Lemma segP_run_H : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
  evt bsegs (sP_run_post Σ k s usp lo tr gp s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16))
             (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) a6 a7
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom bsegs)).
Proof using HA Hk Hq Hbig Hhi Hsp Husp HLO HLO2 ST MI BC TB HTB Htr.
  intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
  pose proof (sr_tcx Σ m HA) as (XC1 & XC3 & XCP & XC4 & XC5 & XCT).
  pose proof (sr_tr tr Htr) as (TRM & TRL & TRR).
  pose proof srp_facts_H as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F12 & F13).

  destruct (ART_chunk Σ m HA) as [_ CS]. pose proof (CS k s Hk) as X. unfold schunk in X.
  replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
  destruct X as (SX1 & WrS & LCH & HDR & STSH & SX6 & SHU & SX8). rewrite Hq in HDR, SHU.
  destruct HDR as (b1 & ctx & Hb1 & HD). clear CS.

  pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
  destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
    & I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
  assert (ISTK : stk bsegs m (T + 2768) (T + 3168)) by assumption.
  assert (IMFH : rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]) by assumption.
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I27 I28 I29 I30
        I31 I32 I33 I34 I35 I36 I37 I38.

  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & BWc & DOK & DNP & DT & DINV & _). assert (DN : d_n (dep Σ) + 2 < 2 ^ 16) by exact (dep_pot_dn2 _ _ _ DNP (proj1 BWc)).
  pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.

  destruct (fl_CB_of_wr m MB MSZ (M + 16) 8 WrS ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
  destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split bsegs m (T + 2768) (T + 2824) (T + 3168) ISTK ltac:(lia)) as [_ X];
                                          destruct (stk_split bsegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
                                          replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
  assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
  rewrite <- Eb in HD. clear Eb.
  assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).

  eapply evt_cut.
  { apply (dealloc_p1_spec (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) a6 a7
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
    apply (rw_cells_transport bsegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; clear - F3 K25 HLO HLO2 Hsp; repeat split; try exact I; lia];
    apply (u64arr_transport bsegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
    [| rewrite wr_trace_length by (rewrite HTB; clear - TRL; lia); rewrite HTB; cbn [disjoint_from]; clear - F3 K25 HLO HLO2 Hsp;
       repeat split; try exact I; lia] end.
  assert (HMS : SEGTOP_A <= M) by (clear - Hhi; unfold K_HIGH_SHADOW_hi, SEGTOP_A, SHB in *; lia).
  lazymatch type of MU2 with munch ?W2 _ _ => apply (dep_rep_transport W2 L (dep Σ) m m2) in DREP; [| exact DOK | exact MU2 | exact WM2 |] end.
  2:{ split; [|split].
      - unfold dsjl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; repeat split; try exact I;
          first [ (left; clear - HMS; unfold SEGTOP_A in *; lia) | (clear - T5 K24; unfold SEGTOP_A in *; lia)
                | (left; clear - Hsp K32 HLO; unfold SEGTOP_A, SHB in *; lia) ].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - F8; lia | clear - ATD; lia | clear - K28 Hsp; lia].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - F9; lia | clear - ATS; lia | clear - K31 Hsp; lia]. }
  rewrite wr_trace_split in TB. replace (usp + -2112) with (usp + -2128 + 16) in BC, TB by lia.
  rewrite <- (length_map (Z_to_bv 64) tr) in BC.

  eapply evt_cut.
  { apply (qchunk_spec (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) u3 u4 u5 u6
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
             M n (bv_unsigned b1) (usp + -2128) TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
             (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
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
    all: try (rewrite map_unsigned_lits by exact TRR; unfold DEP_BK; apply in_BK_ALL; unfold bkt; apply Z.mod_pos_bound; lia). }
  intros ms3 P3.
  destruct P3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & m3 & -> & MU3 & WM3 & MI3 & W16 & REP3 & TB3 & ST3).
  rewrite (unsigned_lit (usp + -2128)) in MU3, ST3 by exact RSP.
  assert (MW3 : munch W m m3).
  { apply (munch_trans _ m m2 m3 MW2).
    lazymatch type of MU3 with munch ?W3 _ _ => apply (munch_weaken W3 _ m2 m3); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU3] end. }
  pose proof (wmono_trans bsegs _ _ _ WM2 WM3) as WM23.
  pose proof (ss_consts Σ m k s usp HA Hk Hsp m3 MW3 WM23) as CR3.
  destruct CR3 as (_ & _ & _ & _ & PS3 & _ & _ & ICR3).
  destruct ICR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & K23' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35' & K36' & _ & _).
  apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 268435456)]) in K35'. destruct K35' as [QM K35']. cbn [cells_size csize Nat.add] in K35'.
  apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 241591905)]) in K35'. destruct K35' as [_ QC]. cbn [cells_size csize Nat.add] in QC.
  change (i_q_max + Z.of_nat 8 + Z.of_nat 8) with 1523200 in QC. change i_q_max with 1523184 in QM.

  lazymatch type of MU3 with munch ?W3 _ _ =>
    apply (rw_cells_transport bsegs W3 m2 m3 _ _) in HD2; [| exact MU3 | exact WM3 |];
    [| cbn [disjoint_from cells_size csize Nat.add];
       repeat split; try exact I;
       first [ (left; clear; lia) | (right; clear - HMS; unfold SEGTOP_A in *; lia) | (clear - F8; lia) | (clear - F9; lia)
             | (left; clear - F3 HLO HLO2 Hsp; lia) ] ] end.

  pose proof (dg_consts L m3 (ss_consts Σ m k s usp HA Hk Hsp m3 MW3 WM23)) as (IC3 & _). destruct IC3 as (IC3 & _).
  apply (proj1 (rwc_app bsegs m3 _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC3.
  destruct IC3 as (SBC & _).
  eapply evt_mono.
  { apply (qput_P_spec (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) v3 v4
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
             (T + 80) (T + 208) (usp + -2128) M n SB lo); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST3.
    all: try (clear - Hbig F4; lia).
    all: try (clear - F1 F3 F10 K33 K8; unfold kHighMemEnd, kHighShadowEnd in *; lia).
    all: try (clear - K1 K4 K5 K6 K33; unfold kHighMemEnd in *; lia).
    all: try (clear - K7 K8 K16 K18 K33; lia).
    all: try (clear - K5 K6 K11 K16 K18; lia).
    all: try (clear - HLO2; lia).
    all: try (clear - HLO K32; unfold kHighShadowEnd, SHB in *; lia).
    all: try (clear - HLO K3 K4; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia). }
  intros ms4 P4.
  destruct P4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & m4 & -> & MU4 & WM4 & MI4 & FR4 & ST4).
  rewrite (unsigned_lit (usp + -2128)) in MU4, ST4, FR4 by exact RSP.
  assert (MW4 : munch W m m4).
  { apply (munch_trans _ m m3 m4 MW3).
    lazymatch type of MU4 with munch ?W4 _ _ => apply (munch_weaken W4 _ m3 m4); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU4] end. }
  pose proof (wmono_trans bsegs _ _ _ WM23 WM4) as WM24.

  assert (HQ : qhdr3 m4 M n).
  { lazymatch type of MU4 with munch ?W4 _ _ =>
      apply (rw_cells_transport bsegs W4 m3 m4 _ _) in HD2; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; left; clear - F3 HLO HLO2 Hsp; lia ];
      apply (rw_cells_transport bsegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; left; clear - F3 HLO HLO2 Hsp; lia ] end.
    exists (Z_to_bv 8 (bv_unsigned b1)), ctx, (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr))))).
    split; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite (Z.mod_small (bv_unsigned b1) 256) by exact Rb1; exact Hb1|].
    change [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx;
            C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]
      with ([C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ++
            [C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]).
    apply rwc_app. split; [exact HD2|]. cbn [cells_size csize Nat.add]. exact W16. }

  rewrite map_unsigned_lits in REP3 by exact TRR.
  lazymatch type of MU4 with munch ?W4 _ _ =>
    apply (depot_rep_frame _ _ _ _ lo W4 m3 m4) in REP3; [| | exact MU4 | exact WM4 | | | | | |] end.
  2:{ apply (qc_depot_ok_put_ok _ _ _ _ _ (depot_ok_mono _ _ _ _ _ DOK HLO) DN). clear - DT TRL; lia. }
  all: try (cbn [disjoint_from]; repeat split; try exact I;
            first [ (left; clear - K27 K32 HLO Hsp; unfold SEGTOP_A, SHB in *; lia)
                  | (left; clear - K28 Hsp; lia) | (left; clear - K31 Hsp; lia) ]).
  pose proof (segP_ARTK Σ m k s usp HA Hk Hq Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 REP3 (dp_hash1 _ _ DINV)) as ART4.
  pose proof (segP_chunk Σ m k s usp HA Hk Hsp m4 MW4 WM24 HQ) as CK4.
  unfold sP_run_post. do 13 eexists. exists m4. split.
  { rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
  split; [exact ART4|]. split; [exact CK4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
  split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
  replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End High.

Section Low.
Hypothesis Hlow : s_mb s + smsz (s_n s) <= K_LOW_SHADOW_lo.

Lemma srp_facts_L : 0x6cd000 <= M /\ M mod 16 = 0 /\ M + 24 <= lo /\ 1 <= n < 2 ^ 32 /\ M + 16 + ru8 n <= MB + MSZ
  /\ (M + 24 <= T + 2824 \/ T + 2840 <= M) /\ (M + 24 <= TCX + 152 \/ TCX + 160 <= M)
  /\ (M + 24 <= DNB \/ DNB + 2 ^ 20 <= M) /\ (M + 24 <= SSB \/ SSB + 2 ^ 23 <= M) /\ MB + MSZ <= l_ACEIL L
  /\ MB <= M /\ 0 <= ru8 n / 8.
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

Lemma segP_run_L : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
  evt bsegs (sP_run_post Σ k s usp lo tr gp s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16))
             (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) a6 a7
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom bsegs)).
Proof using HA Hk Hq Hbig Hlow Hsp Husp HLO HLO2 ST MI BC TB HTB Htr.
  intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
  pose proof (ss_geo Σ m k s HA Hk) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19
  & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34).
  pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
  pose proof (sr_tcx Σ m HA) as (XC1 & XC3 & XCP & XC4 & XC5 & XCT).
  pose proof (sr_tr tr Htr) as (TRM & TRL & TRR).
  pose proof srp_facts_L as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F12 & F13).

  destruct (ART_chunk Σ m HA) as [_ CS]. pose proof (CS k s Hk) as X. unfold schunk in X.
  replace (s_mb s + 4096 + 2032) with M in X by lia. replace (s_mb s + 4096 + 2048) with (M + 16) in X by lia.
  destruct X as (SX1 & WrS & LCH & HDR & STSH & SX6 & SHU & SX8). rewrite Hq in HDR, SHU.
  destruct HDR as (b1 & ctx & Hb1 & HD). clear CS.

  pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
  destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
    & I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
  assert (ISTK : stk bsegs m (T + 2768) (T + 3168)) by assumption.
  assert (IMFH : rw_cells bsegs m (g_MFHooks + 8) [C8 (Z_to_bv 64 0)]) by assumption.
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I23 I24 I25 I26 I27 I28 I29 I30
        I31 I32 I33 I34 I35 I36 I37 I38.

  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & BWc & DOK & DNP & DT & DINV & _). assert (DN : d_n (dep Σ) + 2 < 2 ^ 16) by exact (dep_pot_dn2 _ _ _ DNP (proj1 BWc)).
  pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.

  destruct (fl_CB_of_wr m MB MSZ (M + 16) 8 WrS ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
  destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split bsegs m (T + 2768) (T + 2824) (T + 3168) ISTK ltac:(lia)) as [_ X];
                                          destruct (stk_split bsegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
                                          replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
  assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
  rewrite <- Eb in HD. clear Eb.
  assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).

  eapply evt_cut.
  { apply (dealloc_p1_spec_L (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) a6 a7
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
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
    apply (rw_cells_transport bsegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; clear - F3 K25 HLO HLO2 Hsp; repeat split; try exact I; lia];
    apply (u64arr_transport bsegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
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

  eapply evt_cut.
  { apply (qchunk_spec_L (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) u3 u4 u5 u6
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
             M n (bv_unsigned b1) (usp + -2128) TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
             (DEP_BK (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
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
    all: try (rewrite map_unsigned_lits by exact TRR; unfold DEP_BK; apply in_BK_ALL; unfold bkt; apply Z.mod_pos_bound; lia). }
  intros ms3 P3.
  destruct P3 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & m3 & -> & MU3 & WM3 & MI3 & W16 & REP3 & TB3 & ST3).
  rewrite (unsigned_lit (usp + -2128)) in MU3, ST3 by exact RSP.
  assert (MW3 : munch W m m3).
  { apply (munch_trans _ m m2 m3 MW2).
    lazymatch type of MU3 with munch ?W3 _ _ => apply (munch_weaken W3 _ m2 m3); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU3] end. }
  pose proof (wmono_trans bsegs _ _ _ WM2 WM3) as WM23.
  pose proof (ss_consts Σ m k s usp HA Hk Hsp m3 MW3 WM23) as CR3.
  destruct CR3 as (_ & _ & _ & _ & PS3 & _ & _ & ICR3).
  destruct ICR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & K23' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K35' & K36' & _ & _).
  apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 268435456)]) in K35'. destruct K35' as [QM K35']. cbn [cells_size csize Nat.add] in K35'.
  apply (rwc_app bsegs _ _ [C8 (Z_to_bv 64 241591905)]) in K35'. destruct K35' as [_ QC]. cbn [cells_size csize Nat.add] in QC.
  change (i_q_max + Z.of_nat 8 + Z.of_nat 8) with 1523200 in QC. change i_q_max with 1523184 in QM.

  lazymatch type of MU3 with munch ?W3 _ _ =>
    apply (rw_cells_transport bsegs W3 m2 m3 _ _) in HD2; [| exact MU3 | exact WM3 |];
    [| cbn [disjoint_from cells_size csize Nat.add];
       repeat split; try exact I;
       first [ (left; clear; lia) | (right; clear - HMS; unfold SEGTOP_A in *; lia) | (clear - F8; lia) | (clear - F9; lia)
             | (left; clear - F3 HLO HLO2 Hsp; lia) ] ] end.

  pose proof (dg_consts L m3 (ss_consts Σ m k s usp HA Hk Hsp m3 MW3 WM23)) as (IC3 & _). destruct IC3 as (IC3 & _).
  apply (proj1 (rwc_app bsegs m3 _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC3.
  destruct IC3 as (SBC & _).
  eapply evt_mono.
  { apply (qput_P_spec (Z_to_bv 64 0x805b0) (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 (M + 16)) v3 v4
             (Z_to_bv 64 0x80540) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
             (T + 80) (T + 208) (usp + -2128) M n SB lo); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST3.
    all: try (clear - Hbig F4; lia).
    all: try (clear - F1 F3 F10 K33 K8; unfold kHighMemEnd, kHighShadowEnd in *; lia).
    all: try (clear - K1 K4 K5 K6 K33; unfold kHighMemEnd in *; lia).
    all: try (clear - K7 K8 K16 K18 K33; lia).
    all: try (clear - K5 K6 K11 K16 K18; lia).
    all: try (clear - HLO2; lia).
    all: try (clear - HLO K32; unfold kHighShadowEnd, SHB in *; lia).
    all: try (clear - HLO K3 K4; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia). }
  intros ms4 P4.
  destruct P4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & m4 & -> & MU4 & WM4 & MI4 & FR4 & ST4).
  rewrite (unsigned_lit (usp + -2128)) in MU4, ST4, FR4 by exact RSP.
  assert (MW4 : munch W m m4).
  { apply (munch_trans _ m m3 m4 MW3).
    lazymatch type of MU4 with munch ?W4 _ _ => apply (munch_weaken W4 _ m3 m4); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU4] end. }
  pose proof (wmono_trans bsegs _ _ _ WM23 WM4) as WM24.

  assert (HQ : qhdr3 m4 M n).
  { lazymatch type of MU4 with munch ?W4 _ _ =>
      apply (rw_cells_transport bsegs W4 m3 m4 _ _) in HD2; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; left; clear - F3 HLO HLO2 Hsp; lia ];
      apply (rw_cells_transport bsegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; left; clear - F3 HLO HLO2 Hsp; lia ] end.
    exists (Z_to_bv 8 (bv_unsigned b1)), ctx, (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr))))).
    split; [rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite (Z.mod_small (bv_unsigned b1) 256) by exact Rb1; exact Hb1|].
    change [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx;
            C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]
      with ([C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 (bv_unsigned b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ++
            [C8 (Z_to_bv 64 (snd (depot_put (dep Σ) (map bv_unsigned (map (Z_to_bv 64) tr)))))]).
    apply rwc_app. split; [exact HD2|]. cbn [cells_size csize Nat.add]. exact W16. }

  rewrite map_unsigned_lits in REP3 by exact TRR.
  lazymatch type of MU4 with munch ?W4 _ _ =>
    apply (depot_rep_frame _ _ _ _ lo W4 m3 m4) in REP3; [| | exact MU4 | exact WM4 | | | | | |] end.
  2:{ apply (qc_depot_ok_put_ok _ _ _ _ _ (depot_ok_mono _ _ _ _ _ DOK HLO) DN). clear - DT TRL; lia. }
  all: try (cbn [disjoint_from]; repeat split; try exact I;
            first [ (left; clear - K27 K32 HLO Hsp; unfold SEGTOP_A, SHB in *; lia)
                  | (left; clear - K28 Hsp; lia) | (left; clear - K31 Hsp; lia) ]).
  pose proof (segP_ARTK Σ m k s usp HA Hk Hq Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 REP3 (dp_hash1 _ _ DINV)) as ART4.
  pose proof (segP_chunk Σ m k s usp HA Hk Hsp m4 MW4 WM24 HQ) as CK4.
  unfold sP_run_post. do 13 eexists. exists m4. split.
  { rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
  split; [exact ART4|]. split; [exact CK4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
  split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
  replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End Low.

End SegRunP.

End GWIN.
