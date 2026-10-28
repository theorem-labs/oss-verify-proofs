(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_refill R_refill_ic R_getfrom R_prim_lists R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeC RT_freeA2 RT_refillstmt RT_refillst RT_refillwf RT_rfkit RT_refillart RT_rfbytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rf_post (Σ : rtsA) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists m', ret_st ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
    /\ ARTc (refillΣ Σ c) m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (bv_unsigned sp)) m m'.

Section RfRun.
Variables (Σ : rtsA) (m : mem) (c lo : Z) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis HA : ARTc Σ m.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hca : ca Σ c = [].
Hypothesis HROOM : refill_room Σ c.
Hypothesis MI : mem_inv bsegs m.
Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLO2 : lo + 0x400 <= bv_unsigned sp.
Hypothesis HSP : bv_unsigned sp <= 2 ^ 47.
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation n := (MaxCount c / 2).
#[local] Notation P := (pc_addr (l_T (lay Σ)) c).
#[local] Notation WR := (W_R (l_T (lay Σ)) (l_SB (lay Σ)) c (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) (bv_unsigned sp)).

Lemma rr_c31 : 1 <= c <= 31. Proof using Hc. clear - Hc. lia. Qed.
Lemma rr_sp : l_ACEIL (lay Σ) + 0x400 <= bv_unsigned sp. Proof using HLO HLO2. clear - HLO HLO2. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rr_geo : 0 < T /\ T mod 4096 = 0 /\ T + 4096 <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ 0x7fff7f800000 <= l_ACEIL L
  /\ (T + 4096 <= 0x10000 \/ SEGTOP_A <= T) /\ (T + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= T)
  /\ (T + 4096 <= PRB \/ PRB + 0x2000011000 <= T) /\ K_HIGH_SHADOW_hi <= PRB /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ SB mod 2 ^ 16 = 0 /\ PRB + 0x2000011000 <= l_ACEIL L.
Proof using HW0.
  clear - HW0. pose proof (geo_of_wf0 Σ HW0) as HG. pose proof (g_grant Σ HG T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (GT1 & GT2 & GT3 & GT4 & GT5).
  pose proof (g_aceil Σ HG) as (X1 & X2 & X3). pose proof (se_disj Σ HG) as (T5 & T4 & ATP).
  pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4). pose proof (g_prb Σ HG) as (_ & _ & PM).
  pose proof (g_grant Σ HG PRB 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & PG4 & _).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. repeat split; try assumption; lia.
Qed.

Lemma rr_T : T_ok (l_ACEIL L) T.
Proof using HW0.
  clear - HW0. pose proof rr_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _). unfold T_ok, img_hull_lo, img_hull_hi. unfold SEGTOP_A in G6.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4 | exact G6].
Qed.

Lemma rr_SB : SB_ok (l_ACEIL L) SB.
Proof using HW0.
  clear - HW0. pose proof rr_geo as (_ & _ & _ & G4 & _ & _ & _ & _ & G9 & G10 & G11 & G12 & G13).
  unfold SB_ok, kHighShadowEnd. unfold K_HIGH_SHADOW_hi in G9. split; [lia|]. split; [exact G12|]. split; [lia | exact G4].
Qed.

Lemma rr_tsep : tsep (l_ACEIL L) SB T TCX.
Proof using HW0.
  clear - HW0. pose proof (geo_of_wf0 Σ HW0) as HG. pose proof rr_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof (g_grant Σ HG TCX 0x10000 ltac:(unfold startup_grants; right; right; right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
  pose proof (g_apart Σ HG 0 3 _ _ ltac:(lia) eq_refl eq_refl) as A03. pose proof (g_apart Σ HG 2 3 _ _ ltac:(lia) eq_refl eq_refl) as A23.
  cbn [fst snd] in *. unfold apart in *.
  unfold tsep, img_hull_lo, img_hull_hi, kHighShadowEnd. unfold SEGTOP_A, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  split; [exact rr_T|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma rr_lo : kHighShadowEnd + 8 <= lo.
Proof using HW0 HLO. clear - HW0 HLO. pose proof rr_geo as (_ & _ & _ & _ & G5 & _). unfold kHighShadowEnd. lia. Qed.

Lemma rr_usp : 0 <= usp - 1024 /\ l_ACEIL L + 0x400 <= usp /\ usp <= 2 ^ 47.
Proof using HW0 HLO HLO2 HSP. clear - HW0 HLO HLO2 HSP. pose proof rr_geo as (_ & _ & _ & _ & G5 & _). lia. Qed.

(* [comment removed for export] *)
Lemma rr_pc : pc_cells m P 0 (if ca_init Σ then MaxCount c else 0) (if ca_init Σ then ClassSize c else 0)
  /\ exists chs, u32arr bsegs m (P + 16) chs /\ length chs = 16%nat.
Proof using HA Hc Hca.
  clear - HA Hc Hca. destruct HA as (_ & _ & CA & _). pose proof (CA c ltac:(lia)) as (PC & chs & X1 & X2 & _).
  rewrite Hca in PC. cbn [length Z.of_nat] in PC. split; [exact PC|]. exists chs. split; [exact X1 | exact X2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rr_K (m' : mem) : Prop := forall j, 1 <= j <= 31 -> pclass_rep T j true (ca Σ j) m'.

Lemma rr_front : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
  evt bsegs (refill_A_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c P n lo
               [(cacheT T, cstats T); (usp - 32, usp)] m rr_K)
    (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c m).
Proof using HW0 HA Hc Hca MI ST HLO HLO2 HSP.
  pose proof rr_c31 as Hc31.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6. unfold refill_entry_st, entry_st.
  pose proof rr_T as HT. pose proof rr_lo as HLOH. pose proof rr_usp as (U1 & U2 & U3). pose proof rr_pc as (PC & chs & CH1 & CH2).
  pose proof rr_geo as (G1 & _ & G3 & _).
  pose proof (MaxCount_range c Hc31) as (MC1 & _). pose proof (ClassSize_range c Hc31) as (CS1 & _).
  destruct (ca_init Σ) eqn:EI.
  - (* [comment removed for export] *)
    eapply evt_mono; [apply (refill_A_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               (l_ACEIL L) T c 0 (MaxCount c) (ClassSize c) lo); try assumption|].
    all: try (clear - Hc31 MC1 CS1; lia). all: try (clear - HLO2; lia).
    intros ms Pst. destruct Pst as (t0' & t1' & t2' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & _).
    exists t0', t1', t2', a5', a6', a7', t3', t4', t5', t6', m1, junk. split; [reflexivity|].
    split; [apply (munch_weaken [(usp - 32, usp)]); [clear; solve_sub_fp | exact MU1]|].
    split; [exact WM1|]. split; [exact MI1|]. split; [exact FR1|]. split; [exact ST1|].
    intros j Hj. destruct HA as (_ & _ & CA & _). pose proof (CA j Hj) as X. rewrite EI in X.
    apply (pclass_rep_transport [(usp - 32, usp)] T j true (ca Σ j) m m1 X MU1 WM1). unfold pclass_avoid, pc_addr. cbn [disjoint_from].
    clear - Hj G3 U2. split; [lia | exact I].
  - (* [comment removed for export] *)
    assert (HC0 : forall j, ca Σ j = []) by (pose proof HW0 as (_ & HR & _); destruct HR as (_ & _ & _ & R4 & _); exact (R4 EI)).
    eapply evt_mono; [apply (refill_AI_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               (l_ACEIL L) T c lo (fun _ => 0) (fun _ => 0) (fun _ => 0)); try assumption|].
    + intros j Hj. destruct HA as (_ & _ & CA & _). pose proof (CA j Hj) as (X & _). rewrite EI, HC0 in X. exact X.
    + intros j _. lia.
    + reflexivity.
    + clear - HLO2; lia.
    + intros ms Pst. destruct Pst as (t0' & t1' & t2' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & IC1).
      exists t0', t1', t2', a5', a6', a7', t3', t4', t5', t6', m1, junk. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact FR1|]. split; [exact ST1|].
      intros j Hj. rewrite HC0. split; [exact (IC1 j Hj)|].
      destruct HA as (_ & _ & CA & _). pose proof (CA j Hj) as (_ & chj & X1 & X2 & _).
      pose proof (stk_wmono m m1 _ _ (stk_of_u32arr m _ chj X1) WM1) as X3. rewrite X2 in X3.
      destruct (u32arr_of_stk m1 (pc_addr T j + 16) 16 X3) as (chs1 & L1 & A1). exists chs1. split; [exact A1|]. split; [exact L1 | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rr_regwf : reg_wf c r.
Proof using HW0 Hc. clear - HW0 Hc. pose proof HW0 as (_ & HR & _). exact (proj1 HR c ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma rr_off : forall a k, 0 <= k -> (PRB <= a /\ a + k <= PRB + 0x2000011000) \/ (SHB <= a /\ a + k <= 2 ^ 44 + SHB) ->
  disjoint_from [(P, P + 4); (usp - 32, usp)] a k.
Proof using HW0 Hc HLO HLO2 HSP.
  pose proof rr_c31 as Hc31.
  intros a k Hk Ha. pose proof rr_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). pose proof rr_usp as (U1 & U2 & U3).
  cbn [disjoint_from]. unfold pc_addr. clear - Hc31 Ha G3 G5 G7 G8 G9 G13 U2 Hk. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
  split; [|split; [lia | exact I]]. destruct Ha as [Ha|Ha]; lia.
Qed.

Lemma rr_reg_avoid : forall r', reg_wf c r' -> reg_avoid [(P, P + 4); (usp - 32, usp)] SB c r'.
Proof using HW0 Hc HLO HLO2 HSP.
  pose proof rr_c31 as Hc31.
  intros r' HW'. pose proof rr_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof HW' as (W1 & _ & W3 & W4 & W5 & _). pose proof (ClassSize_range c Hc31) as (CS1 & _).
  assert (Hau : 0 <= ClassSize c * Z.of_nat (length (r_st r'))) by (apply Z.mul_nonneg_nonneg; lia).
  unfold reg_avoid. split; [|split].
  - apply rr_off; [lia | left]. unfold rinfo, RIS_of. clear - Hc31 G10 G11. lia.
  - apply rr_off; [lia | left]. unfold fa, rb, kFaCap, kUserCap in *. clear - Hc31 G10 G11 W5. lia.
  - assert (HSB0 : 0 <= SB) by (clear - G9 G10; unfold K_HIGH_SHADOW_hi in *; lia).
    pose proof (shad_lo (rb SB c + ClassSize c * Z.of_nat (length (r_st r'))) ltac:(unfold rb; clear - HSB0 Hau Hc31; lia)) as Q1.
    pose proof (shad_hi (rb SB c + r_muser r') ltac:(unfold rb, kUserCap in *; clear - W1 G4 G10 G11 G13 Hc31; lia)) as Q2.
    pose proof (fk_shad_le2 (rb SB c + ClassSize c * Z.of_nat (length (r_st r'))) (r_muser r' - ClassSize c * Z.of_nat (length (r_st r')))
                  ltac:(unfold rb; clear - HSB0 Hau Hc31; lia) ltac:(clear - W3; lia)) as E.
    replace (rb SB c + ClassSize c * Z.of_nat (length (r_st r')) + (r_muser r' - ClassSize c * Z.of_nat (length (r_st r')))) with (rb SB c + r_muser r') in E by ring.
    assert (0 <= (r_muser r' - ClassSize c * Z.of_nat (length (r_st r'))) / 8) by (apply Z.div_pos; lia).
    apply rr_off; [lia | right]. rewrite Z.max_r by lia. lia.
Qed.

Lemma rr_finish : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : mem) (junk : list byte),
  munch WR m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
  reg_rep SB c (refill_reg r c) m2 ->
  (exists chs', u32arr bsegs m2 (P + 16) chs' /\ length chs' = 16%nat /\ firstn (Z.to_nat n) chs' = map (cpw c) (refill_ca r c)) ->
  pc_cells m2 P 0 (MaxCount c) (ClassSize c) ->
  (forall j, 1 <= j <= 31 -> j <> c -> pclass_rep T j true (ca Σ j) m2) ->
  (forall i, (length (r_st r) <= i)%nat -> nth_error (r_st (refill_reg r c)) i = Some CkIdle -> pchunk SB c i CkIdle m2) ->
  rw_cells bsegs m2 (usp - 32) [CB 8 junk; C8 s1; C8 s0; C8 ra] ->
  stk bsegs m2 lo (usp - 32) ->
  evt bsegs (rf_post Σ c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
    (MS (mkR (Z_to_bv 64 refill_retB) (Z_to_bv 64 (usp - 32)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 n)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 refill_retB) fc None m2 (seg_rom bsegs)).
Proof using HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP.
  pose proof rr_c31 as Hc31.
  pose proof rr_sp as Hsp.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 junk MU2 WM2 MI2 REG (chs' & CHA & CHL & CHP) PC2 PCO NEW FR2 ST2.
  pose proof rr_T as HT. pose proof rr_lo as HLOH. pose proof rr_usp as (U1 & U2 & U3). pose proof rr_geo as (G1 & _ & G3 & _).
  pose proof (MaxCount_range c Hc31) as (MC1 & MC2). pose proof (ClassSize_range c Hc31) as (CS1 & CS2). pose proof (MaxCount_half c Hc31) as HN.
  pose proof (refill_ca_len r c Hc rr_regwf) as LCA.
  pose proof (rf_reg_wf r c Hc31 rr_regwf HROOM) as HWR.
  replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (Z.to_nat n))) by (rewrite Z2Nat.id by lia; reflexivity).
  eapply evt_mono; [apply (refill_B_spec ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2
                             s0 s1 junk (l_ACEIL L) T c P (Z.of_nat (Z.to_nat n)) 0 (MaxCount c) (ClassSize c) lo); try assumption|].
  all: try (clear - MC1 MC2 CS1 CS2 HN; lia). all: try reflexivity. all: try (clear - HLO2; lia).
  intros ms Pst. destruct Pst as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & -> & MU3 & WM3 & MI3 & PC3 & ST3).
  exists m3. split; [exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, F, fc; reflexivity|].
  assert (MW : munch WR m m3).
  { apply (munch_trans WR m m2 m3 MU2). apply (munch_weaken [(P, P + 4); (usp - 32, usp)]); [|exact MU3].
    unfold W_R, pc_addr. clear - Hc31 U2. solve_sub_fp. }
  split.
  { apply (refill_ART Σ c usp HW0 Hc31 Hsp m m3 HA MW (wmono_trans bsegs _ _ _ WM2 WM3)).
    - exact (reg_rep_transport [(P, P + 4); (usp - 32, usp)] SB c _ m2 m3 REG MU3 WM3 (rr_reg_avoid _ HWR)).
    - split.
      + rewrite LCA. rewrite Z2Nat.id in PC3 by lia. exact PC3.
      + exists chs'. split; [|split; [exact CHL|]].
        * apply (u32arr_transport bsegs _ m2 m3 _ _ CHA MU3 WM3). rewrite CHL. unfold pc_addr. cbn [disjoint_from].
          clear - Hc31 G3 U2. split; [lia|]. split; [lia | exact I].
        * replace (length (refill_ca r c)) with (Z.to_nat n) by lia. exact CHP.
    - intros j Hj Hne. apply (pclass_rep_transport _ T j true _ m2 m3 (PCO j Hj Hne) MU3 WM3). unfold pclass_avoid, pc_addr. cbn [disjoint_from].
      clear - Hj Hne Hc31 G3 U2. split; [|split; [lia | exact I]]. destruct (Z_lt_ge_dec j c); [left | right]; lia.
    - intros i Hi Hn'. apply (pchunk_transport _ SB c i CkIdle m2 m3 (NEW i Hi Hn') MU3 WM3). unfold pchunk_avoid.
      pose proof (nth_error_Some (r_st (refill_reg r c)) i) as X. rewrite Hn' in X. destruct X as (X & _). specialize (X ltac:(discriminate)).
      pose proof HWR as (_ & _ & W3 & _ & _ & _ & _ & _ & _ & _ & W11). unfold kUserCap in *.
      pose proof rr_geo as (_ & _ & _ & G4 & _ & _ & _ & _ & G9 & G10 & G11 & _ & G13).
      assert (HSB0 : 0 <= SB) by (clear - G9 G10; unfold K_HIGH_SHADOW_hi in *; lia).
      assert (Hi2 : 0 <= Z.of_nat i * ClassSize c /\ Z.of_nat i * ClassSize c + ClassSize c <= 2 ^ 31) by (clear - X W11 CS1; nia).
      assert (0 <= ClassSize c / 8) by (apply Z.div_pos; clear - CS1; lia). rewrite Z.max_r by (clear - H; lia).
      pose proof (shad_lo (p_abeg SB c i) ltac:(unfold p_abeg; clear - HSB0 Hi2 Hc31; lia)) as Q1.
      pose proof (shad_hi (p_abeg SB c i + ClassSize c) ltac:(unfold p_abeg; clear - Hi2 G4 G10 G11 G13 Hc31; lia)) as Q2.
      pose proof (fk_shad_le2 (p_abeg SB c i) (ClassSize c) ltac:(unfold p_abeg; clear - HSB0 Hi2 Hc31; lia) ltac:(clear - CS1; lia)) as E.
      apply rr_off; [clear - H; lia | right; clear - Q1 Q2 E; lia]. }
  split; [exact MI3|]. split; [exact (wmono_trans bsegs _ _ _ WM2 WM3)|]. split; [exact ST3 | exact MW].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rr_reg0 : reg_rep SB c r m.
Proof using HA Hc. clear - HA Hc. destruct HA as (_ & PR & _). exact (PR c ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma rr_fl_small : forall fl st, Forall (fun i => 0 <= i < Z.of_nat (length st) /\ nth_error st (Z.to_nat i) = Some CkIdle) fl ->
  ClassSize c * Z.of_nat (length st) <= 2 ^ 31 -> forall i, In i fl -> 0 <= i * ClassSize c / 16 < 2 ^ 31.
Proof using Hc.
  pose proof rr_c31 as Hc31. intros fl st HF HC i Hi. pose proof (proj1 (Forall_forall _ _) HF i Hi) as (X1 & _). pose proof (ClassSize_range c Hc31) as (CS & _).
  split; [apply Z.div_pos; clear - X1 CS; nia|]. apply Z.div_lt_upper_bound; [clear; lia|]. clear - X1 HC CS; nia.
Qed.

Lemma rr_fast : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6, n <= Z.of_nat (length (r_fl r)) ->
  evt bsegs (rf_post Σ c lo ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
    (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T c m).
Proof using HW0 HA Hc Hca HROOM MI ST HLO HLO2 HSP.
  pose proof rr_c31 as Hc31.
  intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hfast.
  pose proof rr_T as HT. pose proof rr_SB as HSB. pose proof rr_lo as HLOH. pose proof rr_usp as (U1 & U2 & U3).
  pose proof rr_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  pose proof (MaxCount_range c Hc31) as (MC1 & MC2). pose proof (ClassSize_range c Hc31) as (CS1 & CS2). pose proof (MaxCount_half c Hc31) as HN.
  pose proof rr_regwf as HWc. pose proof HWc as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
  destruct (rf_fast r c Hfast) as (EF1 & EF2).
  pose proof rr_reg0 as (LK & RC & (rand & exh & pad & nal & nfr & q0 & q1 & q2 & q3 & RT) & (ws & FL & Hws & Hpre) & SU & SH & SS).
  pose proof HA as (CR & _). destruct CR as (IC & _ & _ & _ & _ & _ & _ & _).
  eapply evt_cut; [exact (rr_front t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6)|].
  intros ms P1. destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & K1).
  assert (RS : 0 <= usp - 32 < 2 ^ 64) by (clear - U1 U3; lia).
  (* [comment removed for export] *)
  assert (DF : forall a k, 0 <= k -> (PRB <= a /\ a + k <= PRB + 0x2000011000) \/ (SHB <= a /\ a + k <= 2 ^ 44 + SHB) \/ (0x10000 <= a /\ a + k <= SEGTOP_A) ->
            disjoint_from [(cacheT T, cstats T); (usp - 32, usp)] a k).
  { intros a k Hk Ha. unfold cacheT, cstats. cbn [disjoint_from]. clear - Ha Hk G3 G5 G6 G7 G8 G9 G13 U2.
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB, SEGTOP_A in *. split; [|split; [|exact I]]; destruct Ha as [Ha|[Ha|Ha]]; lia. }
  assert (HR0 : PRB <= R /\ R + 128 <= PRB + 0x2000011000) by (unfold rinfo, RIS_of; clear - G10 G11 Hc31; lia).
  unfold ri_lock, ri_core, ri_tail, fl_arr in *.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ LK MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as LK1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RC MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as RC1.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ RT MU1 WM1 ltac:(apply DF; [cbn; lia | left; cbn [cells_size csize Nat.add]; lia])) as RT1.
  assert (HFA : PRB <= fa SB c /\ fa SB c + r_mfa r <= PRB + 0x2000011000) by (unfold fa, rb, kFaCap in *; clear - G10 G11 Hc31 W5; lia).
  pose proof (u32arr_transport bsegs _ m m1 _ _ FL MU1 WM1 ltac:(rewrite Hws; apply DF; [lia | left; lia])) as FL1.
  destruct IC as (IC1 & IC2).
  pose proof (rw_cells_transport bsegs _ m m1 _ _ IC1 MU1 WM1 ltac:(apply DF; [cbn; lia | right; right; unfold i_spacebeg, INST, g_instance, SEGTOP_A; cbn [cells_size csize Nat.add]; lia])) as IC1'.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ IC2 MU1 WM1 ltac:(apply DF; [cbn; lia | right; right; unfold i_premapped, INST, g_instance, SEGTOP_A; cbn [cells_size csize Nat.add]; lia])) as IC2'.
  pose proof (K1 c Hc31) as (PC1 & chs1 & CH1 & CHL1 & _). rewrite Hca in PC1. cbn [length Z.of_nat] in PC1.
  (* [comment removed for export] *)
  set (nal' := bv_unsigned (Z_to_bv 64 nal)).
  assert (RT1' : rw_cells bsegs m1 (R + 64) [C4 rand; C1 exh; CB 3 pad; C8 (Z_to_bv 64 nal'); C8 (Z_to_bv 64 nfr); C8 (Z_to_bv 64 q0);
                                          C8 (Z_to_bv 64 q1); C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q3)]) by (unfold nal'; rewrite Z_to_bv_bv_unsigned; exact RT1).
  assert (Hnal : 0 <= nal' < 2 ^ 64) by (unfold nal'; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 nal)) as X; unfold bv_modulus in X; cbn [Z.of_N] in X; exact X).
  eapply evt_cut.
  { apply (gfa_fast_spec (Z_to_bv 64 refill_retB) (Z_to_bv 64 (usp - 32)) gp (Z_to_bv 64 tpA) x0 x1 x2 (Z_to_bv 64 P) (Z_to_bv 64 n) x3 x4 x5
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x6 x7 x8 x9 F fc m1 (l_ACEIL L) SB c R (cstats T) (P + 16) n (Z.of_nat (length (r_fl r)))
             (r_mfa r) au (r_muser r) ws chs1 rand exh pad nal' nfr q0 q1 q2 q3 lo); rewrite ?(unsigned_lit (usp - 32)) by exact RS.
    all: try assumption. all: try reflexivity.
    all: try (clear - HN MC1 MC2; lia). all: try (clear - Hfast; lia).
    all: try (clear - W5 W7 Hws; unfold kFaCap in *; lia).
    all: try (unfold pc_addr; clear - Hc31 G1 G3 G8 G10 G11; split; [lia|]; split; [lia|]; destruct G8; [left | right]; lia).
    all: try (clear - W5; unfold kFaCap in *; lia). all: try (clear - W1 W3; unfold kUserCap in *; nia).
    all: try (clear - HLO2; lia).
    all: try (clear - W1 W3 CS1; unfold kUserCap in *; split; [apply Z.mul_nonneg_nonneg; lia | lia]).
    all: try (split; [exact IC1' | exact IC2']).
    all: try (clear - U3; lia). }
  intros ms P2. destruct P2 as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & -> & MU2 & WM2 & MI2 & LK2 & RC2 & RT2 & CHS2 & ST2).
  rewrite (ret_pc_even refill_retB) by (unfold refill_retB; first [reflexivity | lia]).
  rewrite (unsigned_lit (usp - 32)) in ST2 by exact RS. unfold gfa_fast_W in MU2. rewrite (unsigned_lit (usp - 32)) in MU2 by exact RS.
  assert (DG : forall a k, 0 <= k -> (PRB <= a /\ a + k <= PRB + 0x2000011000 /\ (a + k <= R \/ R + 128 <= a)) \/ (SHB <= a /\ a + k <= 2 ^ 44 + SHB)
              \/ (0x10000 <= a /\ a + k <= SEGTOP_A) \/ (T <= a /\ a + k <= T + 4096 /\ (a + k <= P + 16 \/ P + 48 <= a)) \/ usp - 32 <= a ->
            disjoint_from [(R, R + 8); (R + 16, R + 24); (R + 72, R + 80); (P + 16, P + 16 + 4 * n); (usp - 32 - 128, usp - 32)] a k).
  { intros a k Hk Ha. cbn [disjoint_from]. clear - Ha Hk G3 G5 G6 G7 G8 G9 G13 U2 HN HR0 Hc31.
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB, SEGTOP_A, pc_addr in *.
    repeat split; try exact I; destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; lia. }
  apply (rr_finish y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 junk).
  - apply (munch_trans WR m m1 m2).
    + refine (munch_weaken _ WR m m1 _ MU1). unfold W_R, cacheT, cstats; clear - U2; solve_sub_fp.
    + refine (munch_weaken _ WR m1 m2 _ MU2). unfold W_R, pc_addr; clear - U2 HN Hc31; solve_sub_fp.
  - exact (wmono_trans bsegs _ _ _ WM1 WM2).
  - exact MI2.
  - rewrite EF1. unfold reg_rep. cbn [r_muser r_mfa r_st r_fl]. rewrite length_firstn, Nat.min_l by lia.
    replace (Z.of_nat (length (r_fl r) - Z.to_nat n)) with (Z.of_nat (length (r_fl r)) - n) by lia.
    split; [exact LK2|]. split; [exact RC2|]. split; [exists rand, exh, pad, (nal' + n), nfr, q0, q1, q2, q3; exact RT2|].
    split.
    { exists ws. split; [|split; [exact Hws|]].
      - apply (u32arr_transport bsegs _ m1 m2 _ _ FL1 MU2 WM2). rewrite Hws. apply DG; [lia | left; split; [lia|]; split; [lia|]; left; unfold rinfo, RIS_of, fa, rb, kFaCap in *; clear - W5 Hc31; lia].
      - assert (E : firstn (length (r_fl r) - Z.to_nat n) ws = firstn (length (r_fl r) - Z.to_nat n) (firstn (length (r_fl r)) ws))
          by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
        rewrite E, Hpre, firstn_map. reflexivity. }
    split; [exact (stk_wmono m m2 _ _ SU (wmono_trans bsegs _ _ _ WM1 WM2))|].
    split.
    { assert (SHR : SHB <= shad (rb SB c + au) /\ shad (rb SB c + au) + Z.max 0 ((r_muser r - au) / 8) <= 2 ^ 44 + SHB).
      { assert (HSB0 : 0 <= SB) by (clear - G9 G10; unfold K_HIGH_SHADOW_hi in *; lia).
        assert (Hau : 0 <= au) by (clear - CS1; apply Z.mul_nonneg_nonneg; lia).
        pose proof (shad_lo (rb SB c + au) ltac:(unfold rb; clear - HSB0 Hau Hc31; lia)) as Q1.
        pose proof (shad_hi (rb SB c + r_muser r) ltac:(unfold rb, kUserCap in *; clear - W1 G4 G10 G11 G13 Hc31; lia)) as Q2.
        pose proof (fk_shad_le2 (rb SB c + au) (r_muser r - au) ltac:(unfold rb; clear - HSB0 Hau Hc31; lia) ltac:(clear - W3; lia)) as E.
        replace (rb SB c + au + (r_muser r - au)) with (rb SB c + r_muser r) in E by ring.
        assert (0 <= (r_muser r - au) / 8) by (apply Z.div_pos; clear - W3; lia). rewrite Z.max_r by (clear - H; lia). clear - Q1 Q2 E; lia. }
      apply (bytes_at_transport bsegs _ m1 m2 _ _ (bytes_at_transport bsegs _ m m1 _ _ SH MU1 ltac:(rewrite farun_len; apply DF; [lia | right; left; lia])) MU2).
      rewrite farun_len. apply DG; [lia | right; left; lia]. }
    exact (stk_wmono m m2 _ _ SS (wmono_trans bsegs _ _ _ WM1 WM2)).
  - exists (dest ws chs1 (Z.of_nat (length (r_fl r)) - n) (Z.to_nat n)). split; [exact CHS2|]. split; [rewrite dest_length; exact CHL1|].
    replace (Z.of_nat (length (r_fl r)) - n) with (Z.of_nat (length (r_fl r) - Z.to_nat n)) by lia. rewrite EF2.
    apply (dest_prefix (r_fl r) ws chs1 c (length (r_fl r) - Z.to_nat n) (Z.to_nat n) Hpre ltac:(lia) ltac:(rewrite CHL1; lia)).
    exact (rr_fl_small (r_fl r) (r_st r) W9 W11).
  - apply (rw_cells_transport bsegs _ m1 m2 _ _ PC1 MU2 WM2). cbn [cells_size csize Nat.add]. apply DG; [lia | right; right; right; left; unfold pc_addr; clear - Hc31 G3; lia].
  - intros j Hj Hne. apply (pclass_rep_transport _ T j true _ m1 m2 (K1 j Hj) MU2 WM2). unfold pclass_avoid. apply DG; [lia|]. right; right; right; left.
    unfold pc_addr. clear - Hj Hne Hc31 G3 HN. split; [lia|]. split; [lia|]. destruct (Z_lt_ge_dec j c); [left | right]; lia.
  - intros i Hi Hn'. rewrite EF1 in Hn'. cbn [r_st] in Hn'. rewrite (proj2 (nth_error_None _ _) Hi) in Hn'. discriminate Hn'.
  - apply (rw_cells_transport bsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [cells_size csize Nat.add]. apply DG; [lia | right; right; right; right; lia].
  - exact ST2.
Qed.

End RfRun.
