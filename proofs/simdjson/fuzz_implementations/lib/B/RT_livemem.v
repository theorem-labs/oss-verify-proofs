(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs R_m2s R_sec_defs RT_state RT_rep RT_facts0 RT_facts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

Lemma rta_live_appmem0 : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) ->
  (0 <= p /\ p + n <= kLowMemEnd + 1) \/ (kHighShadowEnd < p /\ p + n <= kHighMemEnd + 1).
Proof.
  intros Σ m p n H Hin. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _).
  pose proof HL as HL'. destruct HL' as ((Wlo & Whi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL in P3.
  unfold SEGTOP_A, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, kLowMemEnd, kHighShadowEnd, kHighMemEnd, sp_window_lo, sp_window_hi in *.
  destruct (HVin p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hn) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, kUserCap in *.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    unfold rb in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia.
    destruct P4 as [P4|P4]; [left | right]; lia.
  - destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & (G1 & G2 & G3 & G4 & G5) & _ & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg. unfold l_ACEIL, STACK_WIN in G3. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4.
    destruct G4 as [G4|G4]; [left | right]; lia.
Qed.

Lemma rta_live_appmem : forall Σ m p k, ART_A Σ m -> In (p, k) (rtA_live Σ) ->
  (0 <= p /\ p + k <= kLowMemEnd + 1) \/ (kHighShadowEnd < p /\ p + k <= kHighMemEnd + 1).
Proof.
  intros Σ m p k HA HinV. unfold rtA_live in HinV. destruct (In_vis_live_le (ann Σ) (live Σ) p k HinV) as (n & Hin & Hk & _).
  pose proof (rta_live_appmem0 Σ m p n HA Hin) as X. lia.
Qed.
End GWIN.

Section GWIN2. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

Lemma stk_wr_at_sub : forall (m : mem) lo hi a n, stk bsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at bsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hn Hb. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma rta_live_shadow_wr0 : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> 0 <= n ->
  wr_at bsegs m (shad p) ((n + 7) / 8).
Proof.
  intros Σ m p n H Hin Hn. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _).
  destruct (HVin p n Hin) as [(c & i & Hc & Hni & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hni) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hni; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    pose proof (ART_prim Σ m H c Hc) as (_ & _ & _ & _ & _ & _ & SHW).
    unfold p_ubeg, p_abeg, rb, kUserCap in *.
    apply (stk_wr_at_sub m _ _ _ _ SHW); unfold shad; [ | apply Z.div_pos; lia | ].
    + apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    + assert ((l_SB (lay Σ) + c * 2 ^ 32 + Z.of_nat i * ClassSize c + rz_size n) / 8 + (n + 7) / 8 <= (l_SB (lay Σ) + c * 2 ^ 32 + 2 ^ 32) / 8); [|lia].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - pose proof (ART_chunk Σ m H) as [_ HSR].
    destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & (G1 & G2 & G3 & G4 & G5) & _ & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg.
    destruct (In_nth_error _ _ Hs) as [k Hk].
    pose proof (HSR k s Hk) as (_ & _ & _ & _ & SHW & _). cbv zeta in SHW.
    assert (M8 : exists q, smsz (s_n s) = 8 * q).
    { unfold smsz, pg_up. exists (((needed (s_n s) + rz_size (s_n s) + 4095) / 4096) * 512 + 512). lia. }
    destruct M8 as [q8 Hq8]. unfold grant_ok in *.
    apply (stk_wr_at_sub m _ _ _ _ SHW); unfold shad; [ | apply Z.div_pos; lia | ].
    + apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    + assert ((s_mb s + 4096 + 2048) / 8 + (s_n s + 7) / 8 <= (s_mb s + smsz (s_n s)) / 8); [|lia].
      rewrite Hq8 in *. clear - Hroom G2 G1 Hn Hq8.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rta_live_shadow_wr : forall Σ m p k, ART_A Σ m -> In (p, k) (rtA_live Σ) -> 0 < k -> wr_at bsegs m (shad p) ((k + 7) / 8).
Proof.
  intros Σ m p k HA HinV Hk. unfold rtA_live in HinV. destruct (In_vis_live_le (ann Σ) (live Σ) p k HinV) as (n & Hin & Hkn & _).
  pose proof (rta_live_shadow_wr0 Σ m p n HA Hin ltac:(lia)) as (W1 & W2 & W).
  split; [exact W1|]. split.
  - assert ((k + 7) / 8 <= (n + 7) / 8) by (apply Z.div_le_mono; lia). lia.
  - intros i Hi. apply W. assert ((k + 7) / 8 <= (n + 7) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
End GWIN2.
