(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit I_lkit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_asan_defs R_deallocate R_qput R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_malpre RT_malstate RT_freelift RT_fkit RT_freestate RT_freeA R_asan_front_k RT_freeA2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sA_run_post_g (retw q0 q1 q2 q3 q4 q5 : word) (Bt : Z) (Σ : rtsA) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (gp s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 0x19f2dc) (Z_to_bv 64 (usp + -2208)) gp (Z_to_bv 64 tpA) t0' t1' t2' (Z_to_bv 64 QUAR)
                 (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 80)) (Z_to_bv 64 (l_T (lay Σ) + 208))
                 (Z_to_bv 64 Bt) (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 n) a5' a6' a7'
                 (Z_to_bv 64 n) (Z_to_bv 64 Bt) (Z_to_bv 64 (l_T (lay Σ) + 208))
                 (Z_to_bv 64 (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16)) (Z_to_bv 64 0x100000)
                 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 qenq_entry) fc None m' (seg_rom asegs)
    /\ ARTc (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) m'
    /\ mem_inv asegs m' /\ wmono asegs m m'
    /\ munch (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp) m m'
    /\ stk asegs m' lo (usp + -2208)
    /\ qput_frame m' (usp + -2208) (Z_to_bv 64 (l_T (lay Σ) + 208)) (Z_to_bv 64 Bt) retw q0 q1 q2 q3 q4 q5 s6.

(* [comment removed for export] *)
Lemma dp_hash1_g : forall cg D tr, dep_inv cg D -> hash_of (d_hs (fst (depot_put D tr))) 1 = hash_of (d_hs D) 1.
Proof.
  intros cg D tr (_ & _ & H1 & _). destruct (Z.eqb_spec (find_of (d_hs D) (depot_hash tr)) 0) as [E|E].
  - rewrite (depot_put_miss D tr E). cbn [fst d_hs]. apply hash_of_snoc_old. unfold d_n in H1. lia.
  - rewrite (depot_put_hit D tr E). reflexivity.
Qed.
Arguments dp_hash1_g {cg} D tr _.

Section SegRun.
Variables (retw q0 q1 q2 q3 q4 q5 : word) (Bt : Z) (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n usp lo : Z) (tr : list Z) (tb : list word).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis Hn1 : 1 <= n.
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Husp : usp + 16 <= USTACK_TOP.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x10000 <= usp.
Hypothesis ST : stk asegs m lo (usp + -2128).
Hypothesis MI : mem_inv asegs m.
Hypothesis HBt : usp + -2128 <= Bt /\ Bt + 2064 <= USTACK_TOP.
Hypothesis BC : rw_cells asegs m Bt [C8 (Z_to_bv 64 (Bt + 16)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))].
Hypothesis TB : u64arr asegs m (Bt + 16) (wr_trace tr tb).
Hypothesis HTB : length tb = 255%nat.
Hypothesis Htr : In tr (T_MAIN (l_cg (lay Σ))) /\ (1 <= length tr <= 30)%nat /\ Forall rng64 tr.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) c i).
#[local] Notation S := (ClassSize c).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_A1 (l_T (lay Σ)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n usp).

(* [comment removed for export] *)
Lemma sr_tcx : 0 < TCX /\ TCX + 0x10000 <= l_ACEIL L /\ (TCX + 0x10000 <= PRB \/ PRB + 0x2000011000 <= TCX)
  /\ (TCX + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= TCX) /\ (TCX + 0x10000 <= 0x10000 \/ SEGTOP_A <= TCX)
  /\ (TCX + 0x10000 <= T \/ T + 4096 <= TCX).
Proof using HA.
  clear - HA. pose proof (geo_grant Σ m HA TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
  pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03. pose proof (geo_apart Σ m HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23.
  cbn [fst snd] in *. unfold apart in *. split; [exact X1|]. split; [exact X3|]. split; [lia|]. split; [exact X4|]. split; [exact X5|]. lia.
Qed.

(* [comment removed for export] *)
Lemma sr_tr : In tr (T_MAIN (l_cg (lay Σ))) /\ (1 <= length tr <= 30)%nat /\ Forall rng64 tr.
Proof using Htr.
  exact Htr.
Qed.


(* [comment removed for export] *)
Lemma fl_c8_of_stk : forall (m0 : mem) a, stk asegs m0 a (a + 8) -> exists w, rw_cells asegs m0 a [C8 w].
Proof.
  clear. intros m0 a St. destruct (stk_bytes asegs m0 a (a + 8) St ltac:(lia)) as (bs & Hl & Hb). replace (a + 8 - a) with 8 in Hl by lia.
  exists (le_bytes_to_word bs). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite fl_le8_of_bytes by lia. exact Hb.
  - cbn [cells_size csize Nat.add]. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|]. intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

Lemma fl_two_c8 : forall (m0 : mem) a, stk asegs m0 a (a + 16) -> exists w1 w2, rw_cells asegs m0 a [C8 w1; C8 w2].
Proof.
  clear. intros m0 a St. destruct (stk_split asegs m0 a (a + 8) (a + 16) St ltac:(lia)) as [S1 S2].
  destruct (fl_c8_of_stk m0 a S1) as (w1 & H1). destruct (fl_c8_of_stk m0 (a + 8) ltac:(replace (a + 8 + 8) with (a + 16) by lia; exact S2)) as (w2 & H2).
  exists w1, w2. change [C8 w1; C8 w2] with ([C8 w1] ++ [C8 w2]). apply rwc_app. split; [exact H1|]. exact H2.
Qed.

Lemma sr_geo2 : shad (M + 16) + ru8 n / 8 <= shad (AB + S) /\ SHB <= shad (M + 16) /\ 0 <= ru8 n / 8
  /\ shad (rb SB c) <= shad (M + 16) /\ shad (M + 16) + ru8 n / 8 <= shad (rb SB c + 2 ^ 32).
Proof using HA Hc Hn Hn1.
  clear - HA Hc Hn Hn1.
  pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
  & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
  pose proof (fk_shad_mono (rb SB c) AB K7) as E1. pose proof (fk_shad_mono (AB + S) (rb SB c + 2 ^ 32)) as E2.
  assert (AB + S <= rb SB c + 2 ^ 32) by (clear - K8 K10; unfold kUserCap in *; lia). specialize (E2 H).
  split; [exact K16|]. split; [exact K30|]. split; [exact K40|]. split; [lia|]. lia.
Qed.

Lemma sr_M16 : M mod 16 = 0.
Proof using HA Hc.
  clear - HA Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm). pose proof (rz_facts n) as (R1 & _).
  unfold p_abeg. apply Z.mod_divide in P3, Hm, R1; try (clear; lia). destruct P3 as [q1 E1]. destruct Hm as [q2 E2]. destruct R1 as [q3 E3].
  rewrite E1, E2, E3. replace (q1 * 2 ^ 16 + c * 2 ^ 32 + Z.of_nat i * (q2 * 32) + q3 * 16 - 16) with ((q1 * 4096 + c * 2 ^ 28 + Z.of_nat i * q2 * 2 + q3 - 1) * 16) by ring.
  apply Z.mod_mul. lia.
Qed.

Lemma segA_run : forall gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32),
  evt asegs (sA_run_post_g retw q0 q1 q2 q3 q4 q5 Bt Σ c i n usp lo tr gp s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR retw (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) t0 t1 t2 q0 q1
             (Z_to_bv 64 INST) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 Bt) (Z_to_bv 64 1) a6 a7
             q2 q3 q4 q5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 deallocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp t0 t1 t2 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc.
  pose proof (sa_geo Σ m c i n HA Hc Hn Hn1) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20
  & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & K32 & K33 & K34 & K35 & K36 & K37 & K38 & K39 & K40 & K41).
  pose proof (sa_disj Σ m HA) as (T5 & T4 & D4 & S4 & ATP & ATD & ATS & APD & APS).
  pose proof sr_tcx as (X1 & X3 & XP & X4 & X5 & XT).
  pose proof sr_tr as (TRM & TRL & TRR).
  pose proof sr_geo2 as (G1 & G2 & G3 & G4 & G5).
  pose proof sr_M16 as HM16.
  (* [comment removed for export] *)
  destruct (ART_chunk Σ m HA) as [CP _]. destruct (CP c i (CkAlloc n) Hc Hn) as (WrA & (b1 & ctx & Hb1 & HD) & LCH & SHA1 & SHA2).
  clear CP.
  (* [comment removed for export] *)
  pose proof (ART_consts Σ m HA) as (IC & MMG & TC & M2S & PS & SC & CC & ICR).
  destruct ICR as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18 & I19 & I20
    & I21 & I22 & I23 & I24 & I25 & I26 & I27 & I28 & I29 & I30 & I31 & I32 & I33 & I34 & I35 & I36 & I37 & I38).
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20 I21 I22 I24 I25 I26 I27 I28 I29 I30 I37 I38.
  (* [comment removed for export] *)
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  pose proof (ART_dep Σ m HA) as DREP. unfold dep_rep in DREP.
  (* [comment removed for export] *)
  destruct (fl_CB_of_wr m AB S (M + 16) 8 WrA ltac:(lia) ltac:(cbn; lia)) as (uw & UW).
  destruct (fl_two_c8 m (T + 2824) ltac:(destruct (stk_split asegs m (T + 2768) (T + 2824) (T + 3168) I32 ltac:(lia)) as [_ X];
                                          destruct (stk_split asegs m (T + 2824) (T + 2840) (T + 3168) X ltac:(lia)) as [X' _];
                                          replace (T + 2824 + 16) with (T + 2840) by lia; exact X')) as (fr & fd & STS).
  pose proof (bv_unsigned_in_range 8 b1) as Rb1. unfold bv_modulus in Rb1. change (2 ^ Z.of_N 8) with 256 in Rb1.
  assert (Eb : Z_to_bv 8 (bv_unsigned b1) = b1) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; exact Rb1).
  rewrite <- Eb in HD. clear Eb.
  assert (RSP : 0 <= usp + -2128 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  eapply evt_cut.
  { apply (dealloc_p1_spec retw (Z_to_bv 64 (usp + -2128)) gp t0 t1 t2 q0 q1 a6 a7
             q2 q3 q4 q5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             M n (bv_unsigned b1) Bt TCX T lo ctx fr fd uw); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST.
    all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
    all: try (clear - K33 K4 HLO; lia).
    all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
    all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
    all: try (clear - T5; unfold SEGTOP_A in *; lia).
    all: try (clear - ATP K32 K33; lia). all: try (clear - XP K32 K33; lia).
    all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia). all: try (clear - HBt Husp HLO2; unfold USTACK_TOP in *; lia). }
  intros ms2 P2.
  destruct P2 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & fr' & fd' & m2 & -> & MU2 & WM2 & MI2 & HD2 & UW2 & STS2 & ST2).
  rewrite (unsigned_lit (usp + -2128)) in MU2, ST2 by exact RSP.
  assert (MW2 : munch W m m2).
  { lazymatch type of MU2 with munch ?W2 _ _ => apply (munch_weaken W2 _ m m2); [unfold W_A1; clear - Hsp; solve_sub_fp | exact MU2] end. }
  pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m2 MW2 WM2) as CR2.
  destruct CR2 as (_ & _ & TC2 & _ & _ & _ & _ & ICR2).
  destruct ICR2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J31 & _ & J33 & _ & _ & _ & _ & _).
  lazymatch type of MU2 with munch ?W2 _ _ =>
    apply (rw_cells_transport asegs W2 m m2 _ _) in BC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; clear - K33 K4 K20 Hsp HBt; repeat split; try exact I; lia];
    apply (u64arr_transport asegs W2 m m2 _ _) in TB; [| exact MU2 | exact WM2 |];
    [| rewrite wr_trace_length by (rewrite HTB; clear - TRL; lia); rewrite HTB; cbn [disjoint_from]; clear - K33 K4 K20 Hsp HBt;
       repeat split; try exact I; lia] end.
  lazymatch type of MU2 with munch ?W2 _ _ => apply (dep_rep_transport W2 L (dep Σ) m m2) in DREP; [| exact DOK | exact MU2 | exact WM2 |] end.
  2:{ split; [|split].
      - unfold dsjl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; repeat split; try exact I;
          first [ (left; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - T5 K19; unfold SEGTOP_A in *; lia)
                | (left; clear - Hsp K4 K2; unfold SEGTOP_A in *; lia) ].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - APD K32 K33; lia | clear - ATD; lia | clear - K23 Hsp; lia].
      - cbn [disjoint_from]. repeat split; try exact I; [clear - APS K32 K33; lia | clear - ATS; lia | clear - K26 Hsp; lia]. }
  rewrite wr_trace_split in TB.
  rewrite <- (length_map (Z_to_bv 64) tr) in BC.
  (* [comment removed for export] *)
  eapply evt_cut.
  { apply (qchunk_spec retw (Z_to_bv 64 (usp + -2128)) gp u0 u1 u2 q0 q1 u3 u4 u5 u6
             q2 q3 q4 q5 s6 s7 s8 s9 s10 s11 u7 u8 u9 u10 F fc m2
             M n (bv_unsigned b1) Bt TCX T lo ctx (Z_to_bv 64 18446744069414584320) (dep Σ)
             (DEP_BK (l_cg (lay Σ)) (hash_of (d_hs (dep Σ)) 1)) DNB SSB (map (Z_to_bv 64) tr) (skipn (length tr) tb));
      try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST2.
    all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
    all: try (clear - K33 K4 HLO; lia).
    all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
    all: try (clear - X3 HLO; lia). all: try (clear - K20 HLO; lia).
    all: try (clear - T5; unfold SEGTOP_A in *; lia).
    all: try (clear - APD K32 K33; lia). all: try (clear - APS K32 K33; lia).
    all: try (clear - HLO2; lia). all: try (clear - Husp; unfold USTACK_TOP in *; lia). all: try (clear - HBt Husp HLO2; unfold USTACK_TOP in *; lia).
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
  pose proof (sa_consts Σ m c i n usp HA Hc Hn Hn1 Hsp m3 MW3 WM23) as CR3.
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
       first [ (left; clear; lia) | (right; clear - K2 K32; unfold SEGTOP_A in *; lia) | (clear - APD K32 K33; lia) | (clear - APS K32 K33; lia)
             | (left; clear - K33 K4 Hsp; lia) ] ] end.
  (* [comment removed for export] *)
  apply bytes_at_app in SHA1. destruct SHA1 as [_ SHU]. rewrite farun_lenZ in SHU by lia. rewrite <- K15 in SHU.
  assert (SHC : rw_cells asegs m (shad (M + 16)) [CB (length (ushadow n)) (ushadow n)]).
  { destruct (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & SST).
    apply (fl_CB_of_bytes m _ _ _ _ SHU SST G4). rewrite fl_ushadow_len by lia. exact G5. }
  replace (length (ushadow n)) with (Z.to_nat (ru8' n / 8)) in SHC by (unfold ru8'; pose proof (fl_ushadow_len n ltac:(lia)) as U; unfold ru8 in U; lia).
  lazymatch type of MU2 with munch ?W2 _ _ =>
    apply (rw_cells_transport asegs W2 m m2 _ _) in SHC; [| exact MU2 | exact WM2 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
       change (ru8' n) with (ru8 n); repeat split; try exact I;
       first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (clear - T4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (left; clear - K27 K31 Hsp; lia) ] ] end.
  lazymatch type of MU3 with munch ?W3 _ _ =>
    apply (rw_cells_transport asegs W3 m2 m3 _ _) in SHC; [| exact MU3 | exact WM3 |];
    [| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (unfold ru8'; apply Z.div_pos; lia);
       change (ru8' n) with (ru8 n); repeat split; try exact I;
       first [ (left; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (right; clear - K30; unfold SHB in *; lia)
             | (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
             | (left; clear - K27 K31 Hsp; lia) ] ] end.
  (* [comment removed for export] *)
  eapply evt_mono.
  { apply (qput_A_spec retw (Z_to_bv 64 (usp + -2128)) gp (Z_to_bv 64 tpA) v0 v1 v2 q0 q1 v3 v4
             q2 q3 q4 q5 s6 s7 s8 s9 s10 s11 v5 v6 v7 v8 F fc m3
             (T + 80) (T + 208) Bt M n (bv_unsigned b1) lo ctx (ushadow n)); try assumption; rewrite ?(unsigned_lit (usp + -2128)) by exact RSP.
    all: try exact ST3.
    all: try (clear - K3 K32; unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia).
    all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 K28; unfold kHighMemEnd; lia).
    all: try (change (ru8' n) with (ru8 n); clear - K12 K39 K4 HLO; lia).
    all: try (clear - Hn1 K11 K12 K14 Hc; pose proof (ClassSize_range c Hc); lia).
    all: try (clear - HLO2; lia).
    all: try (clear - HA HLO; pose proof (rta_sp0_win Σ m HA); unfold l_ACEIL, rtA_sp0, STACK_WIN, kHighShadowEnd in *; lia). }
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
         first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ];
      apply (rw_cells_transport asegs W4 m3 m4 _ _) in W16; [| exact MU4 | exact WM4 |];
      [| cbn [disjoint_from cells_size csize Nat.add]; change (ru8' n) with (ru8 n); repeat split; try exact I;
         first [ (right; clear - K3 K31 K32; unfold K_HIGH_SHADOW_hi, SHB in *; lia) | (left; clear - K33 K4 Hsp; lia) ] ] end.
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
            first [ (right; clear - K30; unfold SHB in *; lia) | (left; clear - K2 Hsp K4; unfold SEGTOP_A in *; lia)
                  | (clear - D4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
                  | (clear - S4 K30 K31; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia)
                  | (left; clear - K23 Hsp; lia) | (left; clear - K26 Hsp; lia) ]).
  pose proof (segA_ART Σ m c i n usp HA Hc Hn Hn1 Hsp m4 (fst (depot_put (dep Σ) tr)) MW4 WM24 HQ SH4 REP3
                (qc_depot_ok_put_ok (dep Σ) tr DNB SSB (l_ACEIL L) DOK DN ltac:(clear - DT TRL; lia)) (dep_inv_put (dep Σ) tr DINV TRM ltac:(clear - TRL; lia))
                (dp_hash1_g _ _ DINV)) as ART4.
  unfold sA_run_post_g. do 10 eexists. exists m4. split.
  { rewrite (unsigned_lit (usp + -2128)) by exact RSP. replace (usp + -2128 + -80) with (usp + -2208) by lia. reflexivity. }
  split; [exact ART4|]. split; [exact MI4|]. split; [exact WM24|]. split; [exact MW4|].
  split; [replace (usp + -2208) with (usp + -2128 - 80) by lia; exact ST4|].
  replace (usp + -2208) with (usp + -2128 - 80) by lia. exact FR4.
Qed.

End SegRun.
