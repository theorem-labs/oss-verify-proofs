(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_sizeclass R_cache_defs R_prim_defs R_popfree R_popfree_B R_popfree_T R_getfrom R_prim_lists R_glue_defs RT_state RT_rep RT_malstate RT_refillstmt RT_refillst RT_refillwf RT_rfbytes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma shad_add8 : forall x k, shad (x + 8 * k) = shad x + k.
Proof. intros x k. unfold shad. replace (x + 8 * k) with (x + k * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

Lemma shad_mono' : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

Lemma div8_sub : forall X k, (X - 8 * k) / 8 = X / 8 - k.
Proof. intros X k. replace (X - 8 * k) with (X + (- k) * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

Section RfNew.
Variables (Σ : rtsA) (c : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hslow : Z.of_nat (length (r_fl (pr Σ c))) < MaxCount c / 2.
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation R := (rinfo (RIS_of (l_SB (lay Σ))) c).
#[local] Notation r := (pr Σ c).
#[local] Notation S := (ClassSize c).
#[local] Notation au := (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
#[local] Notation mu := (r_muser (pr Σ c)).
#[local] Notation nf := (Z.of_nat (length (r_fl (pr Σ c)))).
#[local] Notation n := (MaxCount c / 2).
#[local] Notation msz := (rf_msz (pr Σ c) c).
#[local] Notation newc := (rf_newc (pr Σ c) c).

Lemma rn_regwf : reg_wf c r.
Proof using HW0 Hc. clear - HW0 Hc. pose proof HW0 as (_ & HR & _). exact (proj1 HR c Hc). Qed.

Lemma rn_nums : 0 <= au /\ au <= mu /\ n <= nf + newc /\ 0 <= newc /\ newc * S <= mu + msz - au
  /\ 4 * (nf + newc) <= rf_mfa r c /\ S mod 8 = 0 /\ mu mod 8 = 0 /\ msz mod 8 = 0 /\ 1 <= n <= 8 /\ 32 <= S.
Proof using HW0 Hc Hslow.
  clear - HW0 Hc Hslow. pose proof rn_regwf as HWc. pose proof HWc as (W1 & W2 & W3 & _).
  pose proof (rf_msz_facts r c Hc HWc Hslow) as (M1 & M2 & M3 & M4).
  pose proof (rf_newc_facts r c Hc HWc Hslow) as (N1 & (N2 & N3) & N4).
  pose proof (rf_mfa_facts r c HWc) as (A1 & A2 & A3 & _).
  pose proof (ClassSize_range c Hc) as (CS1 & CS2). pose proof (MaxCount_half c Hc) as HN.
  unfold rf_k, rf_au, rf_nf, kUMap in *.
  assert (0 <= au) by (apply Z.mul_nonneg_nonneg; lia).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia | lia].
Qed.

(* [comment removed for export] *)
Theorem rr_newreg : forall (m' : mem) (ws0 : list word),
  ri_lock m' R 0 ->
  ri_core m' R (nf + newc - n) (rf_mfa r c) (au + newc * S) (mu + msz) ->
  (exists rand exh pad nal nfr r0 r1 r2 r3, ri_tail m' R rand exh pad nal nfr r0 r1 r2 r3) ->
  fl_arr m' SB c (carve ws0 (nf + newc) au S (Z.to_nat newc)) ->
  4 * Z.of_nat (length ws0) = rf_mfa r c ->
  firstn (length (r_fl r)) ws0 = map (cpw c) (r_fl r) ->
  stk bsegs m' (rb SB c + au) (rb SB c + (mu + msz)) ->
  bytes_at bsegs m' (shad (rb SB c + au)) (farun ((mu + msz - au) / 8)) ->
  stk bsegs m' (shad (rb SB c)) (shad (rb SB c + 2 ^ 32)) ->
  reg_rep SB c (refill_reg r c) m'
  /\ (forall i, (length (r_st r) <= i)%nat -> nth_error (r_st (refill_reg r c)) i = Some CkIdle -> pchunk SB c i CkIdle m').
Proof using HW0 Hc Hslow.
  intros m' ws0 LK RC RT FL Hws0 Hpre SU SH SS.
  pose proof rn_regwf as HWc. pose proof rn_nums as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
  pose proof HW0 as (HL & _). pose proof HL as HL'.
  assert (HSB : SB mod 8 = 0).
  { unfold layout_ok in HL'. destruct HL' as (_ & _ & _ & _ & _ & X & _). clear - X. lia. }
  clear HL'.
  destruct (rf_slow r c Hc HWc Hslow) as (E1 & _). rewrite E1.
  set (S8 := S / 8). assert (HS8 : S = 8 * S8) by (unfold S8; clear - K7; lia).
  set (A0 := rb SB c + au).
  assert (HA0 : A0 mod 8 = 0).
  { unfold A0, rb. rewrite HS8. clear - HSB. lia. }
  set (X := mu + msz - au).
  assert (HX : X mod 8 = 0 /\ 8 * (newc * S8) <= X).
  { unfold X. rewrite HS8 in *. clear - K1 K2 K5 K7 K8 K9. split; [lia | lia]. }
  destruct HX as (HX1 & HX2).
  assert (HXd : newc * S8 <= X / 8) by (apply Z.div_le_lower_bound; [lia | lia]).
  assert (Hfl2 : Z.of_nat (length (rf_fl r c)) = nf + newc) by (rewrite (rf_fl_len r c K4); unfold rf_nf; reflexivity).
  assert (E_nf : Z.of_nat (length (firstn (length (rf_fl r c) - Z.to_nat n) (rf_fl r c))) = nf + newc - n).
  { rewrite length_firstn, Nat.min_l by lia. lia. }
  assert (E_au : ClassSize c * Z.of_nat (length (r_st r ++ repeat CkIdle (Z.to_nat newc))) = au + newc * S).
  { rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by exact K4. ring. }
  split.
  - unfold reg_rep. cbn [r_muser r_mfa r_st r_fl]. rewrite E_nf, E_au.
    split; [exact LK|]. split; [exact RC|]. split; [exact RT|].
    split.
    { exists (carve ws0 (nf + newc) au S (Z.to_nat newc)). split; [exact FL|]. split; [rewrite carve_length; exact Hws0|].
      assert (HLW : (length (r_fl r) + Z.to_nat newc <= length ws0)%nat) by (clear - Hws0 K6 K4; lia).
      pose proof (carve_prefix (r_fl r) ws0 (length (r_st r)) (Z.to_nat newc) c Hpre HLW) as CP.
      replace (Z.of_nat (length (r_fl r) + Z.to_nat newc)) with (nf + newc) in CP by (clear - K4; lia).
      rewrite length_firstn, Nat.min_l by lia.
      assert (E : firstn (length (rf_fl r c) - Z.to_nat n) (carve ws0 (nf + newc) au S (Z.to_nat newc))
                  = firstn (length (rf_fl r c) - Z.to_nat n) (firstn (length (r_fl r) + Z.to_nat newc) (carve ws0 (nf + newc) au S (Z.to_nat newc)))).
      { rewrite firstn_firstn, Nat.min_l by (clear - Hfl2 K4; lia). reflexivity. }
      rewrite E, CP, firstn_map. reflexivity. }
    split; [exact (proj2 (stk_split bsegs m' A0 (rb SB c + (au + newc * S)) (rb SB c + (mu + msz)) SU ltac:(unfold A0; clear - K4 K5 K11; nia)))|].
    split.
    { replace (rb SB c + (au + newc * S)) with (A0 + 8 * (newc * S8)) by (unfold A0; rewrite HS8; ring). rewrite shad_add8.
      replace ((mu + msz - (au + newc * S)) / 8) with (X / 8 - newc * S8) by (unfold X; rewrite <- div8_sub; f_equal; rewrite HS8; ring).
      apply (bytes_farun_sub m' (shad A0) (X / 8) (shad A0 + newc * S8) (X / 8 - newc * S8) SH); clear - HXd K4 K11 HS8; nia. }
    exact SS.
  - intros i Hi Hn'. cbn [r_st] in Hn'.
    assert (Hi2 : (i < length (r_st r) + Z.to_nat newc)%nat).
    { pose proof (proj1 (nth_error_Some (r_st r ++ repeat CkIdle (Z.to_nat newc)) i) ltac:(rewrite Hn'; discriminate)) as Y.
      rewrite length_app, repeat_length in Y. exact Y. }
    set (k := Z.of_nat i - Z.of_nat (length (r_st r))).
    assert (Hk : 0 <= k /\ k + 1 <= newc) by (unfold k; clear - Hi Hi2 K4; lia).
    assert (EAB : p_abeg SB c i = A0 + 8 * (k * S8)).
    { unfold p_abeg, A0, rb, k. rewrite HS8. ring. }
    unfold pchunk. cbn [pshadow_idle]. rewrite EAB. split.
    + pose proof (stk_split bsegs m' A0 (A0 + 8 * (k * S8)) (rb SB c + (mu + msz)) SU ltac:(clear - Hk HS8 K11 K5 K4; nia)) as (_ & Y).
      pose proof (stk_split bsegs m' (A0 + 8 * (k * S8)) (A0 + 8 * (k * S8) + S) (rb SB c + (mu + msz)) Y
                    ltac:(unfold A0 in *; rewrite HS8 in *; clear - Hk K5 K11 K4; nia)) as (Y2 & _).
      exact Y2.
    + unfold pshadow_idle. rewrite shad_add8. fold S8.
      apply (bytes_farun_sub m' (shad A0) (X / 8) (shad A0 + k * S8) S8 SH); [clear - Hk K11 HS8; nia | clear - K11 HS8; lia |].
      clear - Hk HXd K11 HS8. nia.
Qed.

End RfNew.
