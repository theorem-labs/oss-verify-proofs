(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_asan_malloc R_comballoc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_icfacts RT_malstate RT_maltail RT_freelift RT_fkit RT_freeA RT_geo0 RT_freestate RT_malart RT_malcore_stmt RT_malcore_p RT_caltail RT_calcore_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac piece_of W' k Hx := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W' _ _ _ (nth_error_In W' k eq_refl)); [|exact Hx]; cbn [fst snd]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CoreHit.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z)
          (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hlive : Z.of_nat (length (live Σ)) < LIVE_MAX.
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv bsegs mX.
Hypothesis ST : stk bsegs mX lo (B + -184).
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -184.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 8.
Hypothesis Htr : In tr T_MAIN.
Hypothesis Htrl : (1 <= length tr <= TR_MAX)%nat.
Hypothesis TRC : trc_cells B tr mX tb.
Hypothesis AFC : caf_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0.
Hypothesis Hca : ca Σ (ClassID (needed2 n)) <> [].
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation c := (ClassID (needed2 n)).
#[local] Notation i := (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) (ClassID (needed2 n)) (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0))).
#[local] Notation S := (ClassSize (ClassID (needed2 n))).
#[local] Notation D := (dep Σ).
#[local] Notation D' := (fst (depot_put (dep Σ) tr)).

(* [comment removed for export] *)
Lemma ch_cls : 1 <= c <= 30 /\ rz_size n + n <= S /\ 32 <= S <= 65536 /\ S mod 32 = 0 /\ from_primary n = true
  /\ 1 <= needed2 n <= 65536 /\ c = ClassID (needed n) /\ needed2 n = needed n.
Proof using Hn.
  clear - Hn. pose proof (tl_cls n Hn) as (K1 & K2 & K3 & K4 & K5 & K6 & _). pose proof (tl_fp n Hn) as FP.
  assert (E : needed2 n = needed n) by (unfold needed2; rewrite FP; lia).
  unfold from_primary in FP. apply Z.leb_le in FP.
  split; [exact K1|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [unfold from_primary; apply Z.leb_le; exact FP|].
  split; [lia|]. split; [rewrite E; reflexivity | exact E].
Qed.

Lemma ch_entry : 0 <= last (ca Σ c) 0 < Z.of_nat (length (r_st (pr Σ c))) /\ nth_error (r_st (pr Σ c)) i = Some CkIdle
  /\ ca_init Σ = true /\ 1 <= Z.of_nat (length (ca Σ c)) <= MaxCount c /\ MaxCount c <= 16
  /\ 0 <= last (ca Σ c) 0 * S < 2 ^ 32.
Proof using HA Hn Hca.
  clear - HA Hn Hca. pose proof ch_cls as (K1 & _ & K4 & K5 & _).
  pose proof (tl_entry Σ mX n HA Hn Hca) as (E1 & E2 & E3).
  pose proof (ART_wf Σ mX HA) as (_ & HR & _). destruct HR as (HR & _ & HC & _). destruct (HC c ltac:(lia)) as (C1 & _).
  pose proof (HR c ltac:(lia)) as (_ & _ & W3 & _ & _ & _ & _ & _ & _ & _ & W11).
  assert (Hl : 1 <= Z.of_nat (length (ca Σ c))) by (destruct (ca Σ c); [exfalso; exact (Hca eq_refl) | cbn [length]; lia]).
  assert (MC : MaxCount c <= 16) by (pose proof (MaxCount_range c ltac:(lia)); lia).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [lia|]. split; [exact MC|].
  split; [apply Z.mul_nonneg_nonneg; lia|].
  assert (last (ca Σ c) 0 * S + S <= S * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (S * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * S) by ring.
    replace (last (ca Σ c) 0 * S + S) with ((last (ca Σ c) 0 + 1) * S) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
  lia.
Qed.

Lemma ch_S16 : ClassSize c mod 16 = 0.
Proof using Hn.
  clear - Hn. pose proof ch_cls as (_ & _ & _ & K4 & _). clear - K4. apply Z.mod_divide in K4; [|lia]. apply Z.mod_divide; [lia|].
  destruct K4 as [q Hq]. exists (2 * q). lia.
Qed.

(* [comment removed for export] *)
Lemma ch_stat : forall (m : mem), stk bsegs m (T + 2768) (T + 3168) -> exists v, rw_cells bsegs m (cstat_alloc T) [C8 v].
Proof.
  intros m St. unfold cstat_alloc. destruct (stk_split bsegs m (T + 2768) (T + 2784) (T + 3168) St ltac:(lia)) as [_ X].
  destruct (stk_split bsegs m (T + 2784) (T + 2784 + 8) (T + 3168) X ltac:(lia)) as [X8 _].
  destruct (stk_CB m (T + 2784) 8 X8 ltac:(lia)) as (bs & Hb). destruct (word_of_stk m (T + 2784) (T + 2784 + 8) (T + 2784) X8 ltac:(lia) ltac:(lia)) as (v & Hv).
  exists v. split; [exact Hv | exact (proj2 Hb)].
Qed.

Ltac pieceW W Hx k := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W _ _ _ (nth_error_In W k eq_refl)); [|exact Hx]; cbn [fst snd]; unfold cstat_alloc, pc_addr in *; lia.

(* [comment removed for export] *)
Lemma ch_evt : evt bsegs (ctail_post Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr)
                 (ccore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX).
Proof.
  pose proof ch_cls as (K1 & K2 & K3 & K4 & FP & K6 & K7 & K8).
  pose proof ch_entry as (E1 & E2 & E3 & E4 & E5 & E6).
  pose proof (tl_geo Σ mX B n lo HA Hn Hca LOW LOR SPT SPA)
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof (tl_apart Σ mX HA) as (A02 & A03 & A06 & A07 & A23 & A26 & A27 & A36 & A37 & A67 & TS & XS & TP & XP & DS & BS).
  pose proof (geo_prb Σ mX HA) as (P1 & P2 & P3).
  (* [comment removed for export] *)
  pose proof (ART_cache Σ mX HA c ltac:(lia)) as X. unfold pclass_rep in X. rewrite E3 in X.
  replace (if true then MaxCount c else 0) with (MaxCount c) in X by reflexivity.
  replace (if true then ClassSize c else 0) with (ClassSize c) in X by reflexivity.
  destruct X as (PC & chs & CH1 & CH2 & CH3).
  (* [comment removed for export] *)
  pose proof (ART_consts Σ mX HA) as ((SBC0 & _) & _ & _ & _ & _ & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & St & _).
  assert (SBC : rw_cells bsegs mX i_spacebeg [C8 (Z_to_bv 64 SB)]) by exact (rw_cells_app_l mX _ [C8 (Z_to_bv 64 SB)] _ SBC0).
  destruct (ch_stat mX St) as (stj & STJ).
  assert (HT : T_ok (l_ACEIL L) T).
  { unfold T_ok, img_hull_lo, img_hull_hi. unfold SEGTOP_A in TP. split; [lia|]. split; [exact G9|]. split; [lia|]. split; [lia | exact TP]. }
  assert (HSB : SB_ok (l_ACEIL L) SB).
  { unfold SB_ok, kHighShadowEnd. unfold K_HIGH_SHADOW_hi in G7. split; [lia|]. split; [exact P3|]. split; [lia | lia]. }
  assert (RS : 0 <= B + -184 < 2 ^ 64) by (unfold USTACK_TOP in SPT; lia).
  unfold ccore_entry.
  eapply evt_cut.
  { apply (comballoc_hit_spec (Z_to_bv 64 0x195ec8) (Z_to_bv 64 (B + -184)) gp (Z_to_bv 64 tpA) t0 t1 t2
             (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
             (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6 F fc mX (l_ACEIL L) T SB (needed2 n) (Z.of_nat (length (ca Σ c)))
             (MaxCount c) (ClassSize c) lo chs (cpw c (last (ca Σ c) 0)) stj).
    all: rewrite ?unsigned_lit by exact RS.
    1: lia. 1: exact SBC. 1: exact PC. 1: lia.
    1: pose proof (MaxCount_range c ltac:(lia)); lia.
    1: pose proof (ClassSize_range c ltac:(lia)); lia.
    1: exact CH1. 1: exact CH2.
    1: replace (Z.to_nat (Z.of_nat (length (ca Σ c)) - 1)) with (length (ca Σ c) - 1)%nat by lia; exact (hit_w (cpw c) (ca Σ c) chs Hca CH3).
    1: exact STJ. 1: exact HT. 1: exact HSB. 1: exact ST. 1: exact LOW.
    1: unfold kHighShadowEnd, SHB in *; lia.
    1: lia. 1: unfold USTACK_TOP in SPT; lia. 1: exact MI. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & stj' & -> & MU1 & WM1 & MI1 & PC1 & ARR1 & STA1 & SBC1 & ST1).
  rewrite unsigned_lit in MU1, ST1 by exact RS.
  rewrite (ret_pc_even 0x195ec8) by (lia || reflexivity).
  rewrite (hit_addr SB c (last (ca Σ c) 0) ltac:(lia) E6 ch_S16).
  apply (tl_p2a Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo tr HA Hn Hca LOW LOR SPT SPA Htr Htrl
           m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' tb j0).
  - eapply (munch_weaken _ _ mX m1); [|exact MU1]. intros x Hx. cbn [outside].
    split; [pieceW (W_ctail Σ B n) Hx 0%nat|]. split; [pieceW (W_ctail Σ B n) Hx 1%nat|]. split; [pieceW (W_ctail Σ B n) Hx 2%nat | exact I].
  - exact WM1.
  - exact MI1.
  - exact ST1.
  - apply (caf_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ mX m1 j0 AFC MU1 WM1).
    cbn [disjoint_from]. unfold cstat_alloc, pc_addr. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - destruct TRC as (T1 & T2 & T3). split; [|split; [|exact T3]].
    + apply (rw_cells_transport bsegs _ mX m1 _ _ T1 MU1 WM1). cbn [cells_size csize Nat.add disjoint_from]. unfold cstat_alloc, pc_addr.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
    + apply (u64arr_transport bsegs _ mX m1 _ _ T2 MU1 WM1). cbn [disjoint_from]. unfold cstat_alloc, pc_addr.
      split; [lia|]. split; [lia|]. split; [lia | exact I].
  - pose proof (ART_chunk Σ mX HA) as (P & _). destruct (P c i CkIdle ltac:(lia) E2) as (_ & SH). unfold pshadow_idle in SH.
    apply (bytes_at_transport bsegs _ mX m1 _ _ SH MU1). unfold farun. rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (tl_shad Σ mX B n lo HA Hn Hca LOW LOR SPT SPA) as (S1 & S2 & S3).
    cbn [disjoint_from]. unfold cstat_alloc, pc_addr. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
    split; [clear - S1 S2 S3 TS G8 G10 K1; destruct TS; lia|]. split; [clear - S1 S2 S3 TS G8 G10; destruct TS; lia|].
    split; [clear - S2 S3 G17 G18 G19; lia | exact I].
  - pose proof (tl_dep Σ mX tr HA Htrl) as (OK & _).
    apply (depot_rep_frame _ _ _ _ _ _ mX m1 (ART_dep Σ mX HA) OK MU1 WM1); cbn [disjoint_from]; unfold cstat_alloc, pc_addr;
      unfold apart, SEGTOP_A, SHB in *.
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - A26 K1; destruct A26; lia|]. split; [clear - A26; destruct A26; lia|]. split; [clear - G14 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - TP G8 K1; destruct TP; lia|]. split; [clear - TP G8; destruct TP; lia|]. split; [clear - G17 G18 G19; lia | exact I].
    + split; [clear - A27 K1; destruct A27; lia|]. split; [clear - A27; destruct A27; lia|]. split; [clear - G16 G18 G19; lia | exact I].
  - exact PC1.
Qed.

(* [comment removed for export] *)
Theorem ch_core : cps bsegs (ASTA RTA Σ PMc (eq (ccore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX)))
                            (ccore_post Σ PMc B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo mX).
Proof using FDO MST Hn Hlive Hcr HA MI ST LOW LOR SPT SPA Htr Htrl TRC AFC Hca.
  intros TT cf Hc Hk.
  assert (W1 : forall ms, eq (ccore_entry Σ B gp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc n mX) ms ->
                 evt bsegs (ctail_post Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A n lo tr) ms)
    by (intros ms <-; exact ch_evt).
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (fl_ASTA_mat_stable Σ PMc MST) W1) Hc).
  intros c1 Hc1. apply Hk.
  pose proof ch_cls as (K1 & K2 & K3 & K4 & FP & K6 & K7 & K8).
  pose proof ch_entry as (E1 & E2 & E3 & E4 & E5 & E6).
  pose proof (tl_geo Σ mX B n lo HA Hn Hca LOW LOR SPT SPA)
    as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof (tl_dep Σ mX tr HA Htrl) as (OK & DI & OK' & DN2 & DT).
  pose proof (tl_shadows Σ mX B n lo HA Hn Hca LOW LOR SPT SPA) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  pose proof (tl_room n Hn) as (R1 & R2 & R3 & R4 & R5).
  pose proof (rz_size_mod16 n) as RZ16. pose proof (rz_size_range n) as RZR.
  assert (HDinv : dep_inv D') by (apply dep_inv_put; [exact DI | exact Htr | lia]).
  assert (WF : rt_wf (mal_hit Σ c n D'))
    by exact (mal_hit_wf Σ mX c n D' HA ltac:(lia) Hca ltac:(lia) K2 K7 Hlive Hcr OK' HDinv).
  assert (Hsp' : l_ACEIL L <= B + -56) by lia.
  assert (Husp' : B + -56 <= USTACK_TOP) by lia.
  exists (mal_hit Σ c n D'), (p_ubeg SB c i n). split.
  - unfold ASTA. change (rt_allow RTA (mal_hit Σ c n D')) with (rtA_allow Σ).
    eapply AST_conseq; [exact Hc1 | |].
    + intros ms (m' & RS' & MU & WM & MI' & ST' & TF). exists m'. split; [exact RS'|].
      destruct TF as (HD & HL & US & RZ1 & RZ2 & DR & PC).
      assert (MU' : munch (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) mX m').
      { eapply (munch_weaken _ _ mX m'); [|exact MU]. intros x Hx. unfold W_ctail. cbn [outside].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 0%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 1%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 7%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 5%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 6%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 3%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 2%nat|].
        split; [pieceW (W_mal T c DNB SSB AB S (l_ACEIL L) (B + -56)) Hx 4%nat | exact I]. }
      assert (SH1 : bytes_at bsegs m' (shad AB) (farun (rz_size n / 8) ++ ushadow n)).
      { apply bytes_at_app. split; [exact RZ1|]. rewrite farun_lenZ by (apply Z.div_pos; lia). rewrite <- Q1. exact US. }
      pose proof (mal_ART Σ mX c n (B + -56) HA ltac:(lia) Hca ltac:(lia) K2 Hsp' Husp' m' D' MU' WM HD HL SH1 RZ2 PC DR
                    (mc_hash1 (dep Σ) tr DI) WF) as ART'.
      split; [exact ART'|]. split; [exact MI'|]. split; [exact WM|]. split; [exact ST'|]. split.
      { intros a Ha. apply MU'. exact (ma_client Σ mX c n (B + -56) HA ltac:(lia) Hca ltac:(lia) K2 Hsp' Husp' (bv_unsigned a) Ha). }
      pose proof (tl_chunk_stk Σ mX n HA Hn Hca m' WM) as CH.
      split.
      { unfold p_ubeg. destruct (stk_split bsegs m' AB (AB + rz_size n) (AB + S) CH ltac:(lia)) as [_ X].
        destruct (stk_split bsegs m' (AB + rz_size n) (AB + rz_size n + n) (AB + S) X ltac:(lia)) as [X2 _].
        exact (stk_wr_at' m' _ _ X2). }
      unfold p_ubeg. apply acc_ushadow; [|unfold K_HIGH_SHADOW_hi in *; lia|lia|exact US].
      rewrite Z.add_mod by lia. rewrite (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity)).
      rewrite (mod8_of (rz_size n) 16 ltac:(lia) RZ16 ltac:(exists 2; reflexivity)). reflexivity.
    + intros mo (HM & HP). split; [|exact HP]. cbn [ARTM RTA] in *. unfold ARTM_A in *. rewrite mal_hit_eager. exact HM.
  - cbn [rt_live rt_frames rt_sp0 rt_credit RTA]. unfold rtA_live, rtA_frames, rtA_sp0, rtA_credit, mal_hit.
    cbn [live frames lay credit]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold p_ubeg. split; [unfold K_HIGH_SHADOW_hi in *; lia|]. split.
    + rewrite Z.add_mod by lia. rewrite G3, RZ16. reflexivity.
    + unfold USTACK_TOP, rb, kUserCap in *. lia.
Qed.

End CoreHit.
