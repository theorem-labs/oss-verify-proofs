(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_led RT_drain_kit RT_dsec_nw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Section DsNw.
Variables (Σ : rtsA) (k : nat) (s : secst) (lo zhi : Z).
Hypothesis HG : geo_ok Σ.
Hypothesis Hk : nth_error (sec Σ) k = Some s.
Hypothesis HLO : l_ACEIL (lay Σ) <= lo.
Hypothesis HLZ : lo + 48 <= zhi.
Hypothesis HZ47 : zhi <= 2 ^ 47.
Hypothesis Hdep : depot_ok (dep Σ) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HQB : Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation PRB := (l_PRB (lay Σ)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).
#[local] Notation W := [(s_mb s, s_mb s + smsz (s_n s)); (zhi - 48, zhi)].

Lemma an_HD : forall c i, In (c, i) ([] : list (Z * nat)) -> 1 <= c <= 31 /\ exists st, nth_error (r_st (pr Σ c)) i = Some st.
Proof. intros c i []. Qed.
Lemma an_HDC : forall c, In c ([] : list Z) -> 1 <= c <= 31.
Proof. intros c []. Qed.
Lemma an_IZ : Forall (fun z => 0x10000 <= fst z /\ snd z <= SEGTOP_A) ([] : list ivl).
Proof. constructor. Qed.
Lemma an_TZ : Forall (fun z => l_T (lay Σ) <= fst z /\ snd z <= l_T (lay Σ) + 4096) ([] : list ivl).
Proof. constructor. Qed.

Lemma an_cert : Forall (dzone Σ [] [] [k] [] [] [] lo zhi) W.
Proof using Hk HLZ.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - do 7 right. left. exists k, s. split; [left; reflexivity|]. split; [exact Hk|]. cbn [fst snd]. lia.
  - do 9 right. cbn [fst snd]. lia.
Qed.

Lemma an_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_img Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_Tz : forall a n, T <= a -> a + n <= T + 4096 -> disjoint_from [] a n -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_Tz Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_grant : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 1 \/ j = 3 \/ j = 4 \/ j = 5)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hk HLO HLZ.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert j b gn a n Hj). lia.
Qed.
Lemma an_grant67 : forall j b gn a n, nth_error (startup_grants L) j = Some (b, gn) -> (j = 6 \/ j = 7)%nat ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HG Hk HLO HLZ.
  intros j b gn a n Hj Hjr. apply (dk_grant_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert j b gn a n Hj). lia.
Qed.
Lemma an_ris : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> rinfo (RIS_of SB) c' <= a -> a + n <= rinfo (RIS_of SB) c' + 120 -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_ris_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_fa : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> fa SB c' <= a -> a + n <= fa SB c' + kFaCap -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_fa_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [] ->
  p_abeg SB c' i' <= a -> a + n <= p_abeg SB c' i' + ClassSize c' -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_slot_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_shad_slot : forall c' i' st0 a n, 1 <= c' <= 31 -> nth_error (r_st (pr Σ c')) i' = Some st0 -> ~ In (c', i') [] ->
  shad (p_abeg SB c' i') <= a -> a + n <= shad (p_abeg SB c' i' + ClassSize c') -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_shad_slot_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_shad_reg : forall c' a n, 1 <= c' <= 31 -> ~ In c' [] -> shad (rb SB c' + ClassSize c' * Z.of_nat (length (r_st (pr Σ c')))) <= a ->
  a + n <= shad (rb SB c' + 2 ^ 32) -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_shad_reg_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_shad_app : forall lo0 hi0 a n, 0 <= lo0 -> hi0 <= 2 ^ 47 -> (hi0 <= PRB \/ PRB + 0x2000011000 <= lo0) ->
  (forall k0 s0, nth_error (sec Σ) k0 = Some s0 -> In k0 [k] -> hi0 <= s_mb s0 \/ s_mb s0 + smsz (s_n s0) <= lo0) ->
  shad lo0 <= a -> a + n <= shad hi0 -> disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_shad_app_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.
Lemma an_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> ~ In k0 [k] -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  disjoint_from W a n.
Proof using HG Hk HLO HLZ. exact (dk_secmap_hw Σ [] [] [k] [] [] [] lo zhi HG an_HD an_HD an_HDC an_IZ an_TZ HLO W an_cert). Qed.

Lemma an_map : 0 < MB /\ MB + MSZ <= l_ACEIL L /\ (MB + MSZ <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= MB) /\ SEGTOP_A <= MB
  /\ (MB + MSZ <= PRB \/ PRB + 0x2000011000 <= MB) /\ (MB + MSZ <= T \/ T + 4096 <= MB) /\ 0 < MSZ
  /\ 2 ^ 44 + SHB <= l_ACEIL L /\ PRB + 0x2000011000 <= l_ACEIL L /\ PRB <= SB /\ SB + 2 ^ 37 + 4096 <= PRB + 0x2000011000
  /\ K_HIGH_SHADOW_hi <= PRB.
Proof using HG Hk.
  pose proof (dk_map Σ HG k s Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & _ & M8 & _).
  pose proof (dk_geo Σ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & _).
  pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as ((Hn1 & _) & _).
  pose proof (smsz_big (s_n s) ltac:(lia)) as Hbig.
  split; [lia|]. split; [exact M2|]. split; [exact M4|]. split; [clear - M1 M3 Hbig Hn1; unfold SEGTOP_A in *; lia|].
  split; [exact M5|]. split; [exact M6|]. split; [exact M8|]. repeat split; assumption.
Qed.

Lemma an_av_shadow : forall a n, SHB <= a -> a + n <= 2 ^ 44 + SHB -> 0 <= n -> disjoint_from W a n.
Proof using HG Hk HLO HLZ.
  intros a n H1 H2 H3. pose proof an_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
  cbn [disjoint_from]. clear - H1 H2 H3 M3 G1 HLO HLZ. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
  split; [lia | split; [lia | exact I]].
Qed.
Lemma an_av_prb : forall a n, PRB <= a -> a + n <= PRB + 0x2000011000 -> 0 <= n -> disjoint_from W a n.
Proof using HG Hk HLO HLZ.
  intros a n H1 H2 H3. pose proof an_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
  cbn [disjoint_from]. clear - H1 H2 H3 M5 G4 HLO HLZ. split; [lia | split; [lia | exact I]].
Qed.
Lemma an_av_T : forall a n, T <= a -> a + n <= T + 4096 -> 0 <= n -> disjoint_from W a n.
Proof using HG Hk HLO HLZ.
  intros a n H1 H2 H3. pose proof an_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof (dk_T Σ HG) as (T1 & T2 & _). cbn [disjoint_from]. clear - H1 H2 H3 M6 T2 HLO HLZ. split; [lia | split; [lia | exact I]].
Qed.

Theorem ds_art_nw : forall (m m' : mem), ARTc (recs Σ k) m -> munch W m m' ->
  stk bsegs m' lo zhi ->
  ARTc (recs Σ k) m'.
Proof using HG Hk HLO HLZ HZ47 Hdep HQB.
  intros m m' HA MU STZ.
  pose proof an_map as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  pose proof (kv_reg Σ W [] HG an_ris an_fa an_shad_reg) as KR.
  pose proof (kv_pchunk Σ W [] HG an_slot an_shad_slot) as KP.
  pose proof (kv_schunk Σ W [k] HG an_shad_app an_secmap) as KS.
  pose proof (nth_error_lt _ _ _ Hk) as Hkl.
  pose proof HG as (_ & (HR & _) & HSW & _).
  apply ARTc_intro.
  - apply (consts_rep_nw L m m' A1).
    + intros a Ha. apply MU. destruct (Z.eq_dec (bv_unsigned a) (T + 0xc60)) as [E|NE].
      * apply (disjoint_outside W (T + 0xc60) 1); [apply an_av_T; clear; lia | clear - E; lia].
      * apply (kv_consts Σ W [] [] an_img an_Tz an_grant); [apply dsjb_all; vm_compute; reflexivity | exact I | exact Ha | exact NE].
    + intros a Ha. apply MU. apply (disjoint_outside W (T + 2768) 400); [apply an_av_T; clear; lia | clear - Ha; cbv beta in Ha; lia].
  - intros c' Hc'. change (reg_rep (l_SB (lay Σ)) c' (pr Σ c') m').
    pose proof (dk_rb Σ HG c' Hc') as (R1 & R2 & R3 & R4). pose proof (dk_auser Σ HG c' Hc') as (U1 & U2).
    pose proof (HR c' Hc') as (W1 & _ & W3 & _).
    pose proof (A2 c' Hc') as A2c. change (reg_rep (l_SB (lay Σ)) c' (pr Σ c') m) in A2c.
    apply (reg_rep_nw W _ c' _ m m' A2c MU (KR c' Hc' (fun X => X))).
    + apply an_av_prb; clear - R1 R2 R3 R4 G7 U1 W1 W3; unfold fa, kUserCap, kFaCap in *; lia.
    + pose proof (dk_geo Σ HG) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
      pose proof (dk_shad_rng (rb SB c') ltac:(clear - R1 R2 Y2 Y3 Y4 Y6 Y7; lia)) as X1.
      pose proof (dk_shad_rng (rb SB c' + 2 ^ 32) ltac:(clear - R1 R2 Y2 Y3 Y4 Y6 Y7; lia)) as X2.
      pose proof (dk_shad_mono (rb SB c') (rb SB c' + 2 ^ 32) ltac:(clear; lia)) as X3.
      apply an_av_shadow; clear - X1 X2 X3; lia.
  - intros c' Hc'. exact (pclass_rep_nw W _ c' _ _ m m' (A3 c' Hc') MU (kv_pclass Σ W [] an_Tz c' Hc' I)).
  - destruct A4 as [P Sc]. split.
    + intros c' i' st0 Hc' Hn'. change (nth_error (r_st (pr Σ c')) i' = Some st0) in Hn'.
      pose proof (dk_slot_in Σ HG c' i' st0 Hc' Hn') as (S1 & S2 & _ & _ & _ & S6).
      pose proof (P c' i' st0 Hc' Hn') as Pc. change (pchunk (ann Σ) SB c' i' st0 m) in Pc. change (pchunk (ann Σ) SB c' i' st0 m').
      apply (pchunk_nw W _ c' i' st0 m m' Pc MU (KP c' i' st0 Hc' Hn' (fun X => X))).
      apply an_av_prb; clear - S1 S2 S6 G7; lia.
    + intros j' t Hj'. cbn [recs set_sec sec] in Hj'. destruct (swap_remove_nth k (sec Σ) j' t Hkl Hj') as (Nt & Hlt).
      assert (Hix : (if Nat.eqb j' k then (length (sec Σ) - 1)%nat else j') <> k) by (destruct (Nat.eqb_spec j' k) as [E|E]; clear - Hlt E; lia).
      pose proof (dk_map Σ HG _ t Nt) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
      pose proof (T9 k s Hk (fun E => Hix (eq_sym E))) as AP.
      apply (schunk_nw W j' t m m' (Sc j' t Hj') MU (KS _ t Nt ltac:(intros [E|[]]; exact (Hix (eq_sym E))))).
      * cbn [disjoint_from]. clear - AP T2 HLO HLZ. split; [lia | split; [lia | exact I]].
      * pose proof (dk_geo Σ HG) as (Y1 & Y2 & _).
        pose proof (dk_shad_rng (s_mb t) ltac:(clear - T1 T2 T8 Y2; lia)) as X1.
        pose proof (dk_shad_rng (s_mb t + smsz (s_n t)) ltac:(clear - T1 T2 T8 Y2; lia)) as X2.
        pose proof (dk_shad_mono (s_mb t) (s_mb t + smsz (s_n t)) ltac:(clear - T8; lia)) as X3.
        apply an_av_shadow; clear - X1 X2 X3; lia.
  - exact (sec_rep_nw W (recs Σ k) m m' A5 MU (kv_sec Σ W [] HG an_img an_grant ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - exact (quar_rep_nw W (recs Σ k) m m' A6 MU
             (kv_quar Σ W [] [] [] HG an_img an_Tz an_slot I ltac:(apply dsjb_all'; vm_compute; reflexivity)
                ltac:(intros i' _ []) HQB)).
  - exact (dep_rep_nw W _ _ m m' A7 Hdep MU (kv_dep Σ W [] an_img ltac:(apply dsjb_all'; vm_compute; reflexivity) an_grant67)).
  - change (fs_rep Σ m) in A8. change (fs_rep Σ m').
    apply (fs_rep_nw W Σ m m' A8 MU (kv_fs Σ W [k] [] [] HG an_img an_Tz an_grant an_shad_app
             ltac:(apply dsjb_all'; vm_compute; reflexivity) I)).
    apply Forall_forall. intros (f, k0) Hin. cbn [fst snd]. destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
    pose proof (g_grant Σ HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
    pose proof HSW as (_ & _ & _ & SW4 & _). pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _).
    unfold apart in AF. split.
    + cbn [disjoint_from]. clear - AF Y1 Y2 Y3 Q3 HLO HLZ. split; [lia | split; [lia | exact I]].
    + pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
      pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1.
      pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
      pose proof (fk_shad_le2 f (fs_size k0) ltac:(clear - Y1 Q1; lia) ltac:(clear - Y3; lia)) as X3.
      apply an_av_shadow; [exact (proj1 X1) | | apply Z.div_pos; clear - Y3; lia]. clear - X2 X3. lia.
  - exact (ia_rep_nw W _ m m' A9 MU (kv_ia W [] an_img ltac:(apply dsjb_all'; vm_compute; reflexivity))).
  - change (shadow_rep (lay Σ) m) in A10. change (shadow_rep (lay Σ) m').
    apply (shadow_rep_nw W _ m m' A10 MU (kv_shadow Σ W [k] HG an_shad_app)).
    + pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
      pose proof (dk_shad_rng (l_ACEIL L) ltac:(clear - Z1 Z2; unfold SHB in *; lia)) as X1.
      pose proof (dk_shad_mono (l_ACEIL L) (2 ^ 47) Z2) as X3.
      apply an_av_shadow; [exact (proj1 X1) | change (shad (2 ^ 47)) with (2 ^ 44 + SHB); clear; lia | clear - X3; lia].
    + assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x800d1c00) by reflexivity.
      rewrite E1, E2. apply an_av_shadow; unfold SHB; lia.
    + destruct A10 as (_ & _ & _ & _ & SW). apply (stk_nw_hole W m m' _ _ lo zhi SW MU STZ). intros a Ha Hn.
      cbn [outside]. clear - Ha Hn M2 HLO HLZ. split; [lia | split; [lia | exact I]].
  - change (vis_rep (lay Σ) (rtA_allow Σ) m) in A11. change (vis_rep (lay Σ) (rtA_allow Σ) m').
    apply (vis_rep_nw W _ _ m m' A11 MU). intros z Hz. cbn [outside]. unfold shreg in Hz.
    clear - Hz M3 G1 HLO HLZ. unfold K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
    split; [lia | split; [lia | exact I]].
Qed.

End DsNw.

End GWIN.
