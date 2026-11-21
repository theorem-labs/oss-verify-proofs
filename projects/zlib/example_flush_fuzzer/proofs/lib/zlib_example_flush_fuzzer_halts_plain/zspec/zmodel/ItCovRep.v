(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain ItCovIface.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Ltac liaq_prune_logic :=
  repeat match goal with
         | H : _ -> _ |- _ => clear H
         | H : _ \/ _ |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         | H : forall _, _ |- _ => clear H
         end.
Ltac liaq_nonlit e := lazymatch isZcst e with true => fail | _ => idtac end.
Ltac liaq_prune_nl :=
  repeat match goal with
         | H : context [Z.modulo _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.div _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.pow _ ?e] |- _ => liaq_nonlit e; clear H
         | H : context [Z.shiftl _ _] |- _ => clear H
         | H : context [Z.shiftr _ _] |- _ => clear H
         end.
Ltac liaq := first [ solve [liaq_prune_logic; liaq_prune_nl; lia] | solve [liaq_prune_logic; lia] | lia ].
Ltac niaq := first [ solve [liaq_prune_logic; liaq_prune_nl; nia] | solve [liaq_prune_logic; nia] | nia ].


Lemma mod_pow2_split : forall x a b, 0 <= a -> 0 <= b ->
  x mod 2 ^ (a + b) = x mod 2 ^ a + 2 ^ a * ((x / 2 ^ a) mod 2 ^ b).
Proof.
  intros x a b Ha Hb.
  pose proof (pow2_pos a Ha) as Pa. pose proof (pow2_pos b Hb) as Pb.
  rewrite pow2_split by lia.
  symmetry. apply Z.mod_unique with (q := (x / 2 ^ a) / 2 ^ b).
  - left. pose proof (Z.mod_pos_bound x (2 ^ a) Pa). pose proof (Z.mod_pos_bound (x / 2 ^ a) (2 ^ b) Pb). nia.
  - pose proof (Z.div_mod x (2 ^ a) ltac:(lia)) as E1.
    pose proof (Z.div_mod (x / 2 ^ a) (2 ^ b) ltac:(lia)) as E2. nia.
Qed.

Lemma mod_pow2_mod : forall x a b, 0 <= a <= b -> (x mod 2 ^ b) mod 2 ^ a = x mod 2 ^ a.
Proof.
  intros x a b Hab. replace b with (a + (b - a)) by lia. rewrite mod_pow2_split by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. pose proof (pow2_pos a ltac:(lia)). lia.
Qed.

Lemma fill_hits_iff : forall B h incr q x, 0 < incr -> 0 <= h < incr -> 0 <= q ->
  fill_hits (B + h) incr q x = true <-> (B <= x < B + q * incr /\ (x - B) mod incr = h).
Proof.
  intros B h incr q x Hi Hh Hq. unfold fill_hits.
  rewrite !Bool.andb_true_iff, Z.leb_le, Z.ltb_lt, Z.eqb_eq.
  split.
  - intros [[H1 H2] H3].
    pose proof (Z.div_mod (x - (B + h)) incr ltac:(lia)) as E. rewrite H3, Z.add_0_r in E.
    assert (T0 : 0 <= (x - (B + h)) / incr) by (apply Z.div_pos; lia).
    set (t := (x - (B + h)) / incr) in *.
    assert (T1 : t < q) by (apply Z.lt_nge; intros C; pose proof (proj1 (Z.mul_le_mono_pos_l q t incr Hi) C); lia).
    pose proof (proj1 (Z.mul_le_mono_pos_r (t + 1) q incr Hi) ltac:(lia)) as T2.
    split; [lia|].
    replace (x - B) with (h + ((x - (B + h)) / incr) * incr) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - intros [[H1 H2] H3].
    pose proof (Z.div_mod (x - B) incr ltac:(lia)) as E. rewrite H3 in E.
    assert (T0 : 0 <= (x - B) / incr) by (apply Z.div_pos; lia).
    split; [split; [lia | lia]|].
    replace (x - (B + h)) with (0 + ((x - B) / incr) * incr) by lia.
    rewrite Z_mod_plus_full. reflexivity.
Qed.


Section CanonPF.
  Variables (N : Z) (Lf : Z -> Z).
  Hypothesis HL : forall i, 0 <= i < N -> 1 <= Lf i <= 15.
  Hypothesis Hsorted : forall i j, 0 <= i <= j -> j < N -> Lf i <= Lf j.
  Hypothesis Hcomplete : SK Lf N = 2 ^ 15.

  Lemma cc_prefix_gt : forall i j, 0 <= i < j -> j < N -> cc Lf i < cc Lf j / 2 ^ (Lf j - Lf i).
  Proof.
    intros i j Hij Hj.
    pose proof (HL i ltac:(lia)) as HLi. pose proof (HL j ltac:(lia)) as HLj.
    pose proof (Hsorted i j ltac:(lia) ltac:(lia)) as Hs.
    pose proof (cc_S N Lf HL Hsorted i ltac:(lia)) as Ei.
    pose proof (cc_S N Lf HL Hsorted j ltac:(lia)) as Ej.
    pose proof (S_step Lf i ltac:(lia)) as St.
    pose proof (S_mono Lf (i + 1) j ltac:(lia)) as Mo.
    assert (P : 2 ^ (15 - Lf i) = 2 ^ (Lf j - Lf i) * 2 ^ (15 - Lf j)) by (rewrite <- pow2_split by lia; f_equal; lia).
    pose proof (pow2_pos (15 - Lf j) ltac:(lia)) as Q1. pose proof (pow2_pos (Lf j - Lf i) ltac:(lia)) as Q2.
    enough (cc Lf i + 1 <= cc Lf j / 2 ^ (Lf j - Lf i)) by lia.
    apply Z.div_le_lower_bound; [lia|].
    apply Z.mul_le_mono_pos_r with (p := 2 ^ (15 - Lf j)); [lia|]. nia.
  Qed.

  Theorem hf_prefix_free : forall i j, 0 <= i < j -> j < N -> hf Lf j mod 2 ^ Lf i <> hf Lf i.
  Proof.
    intros i j Hij Hj E.
    pose proof (HL i ltac:(lia)) as HLi. pose proof (HL j ltac:(lia)) as HLj.
    pose proof (Hsorted i j ltac:(lia) ltac:(lia)) as Hs.
    pose proof (cc_range N Lf HL Hcomplete i ltac:(lia)) as Ri.
    pose proof (cc_range N Lf HL Hcomplete j ltac:(lia)) as Rj.
    pose proof (cc_prefix_gt i j Hij Hj) as GT.
    unfold hf in E.
    replace (2 ^ Lf i) with (2 ^ Z.of_nat (Z.to_nat (Lf i))) in E by (f_equal; lia).
    rewrite (brv_mod_pow2 (Z.to_nat (Lf j)) (Z.to_nat (Lf i)) (cc Lf j)) in E by lia.
    replace (Z.of_nat (Z.to_nat (Lf j) - Z.to_nat (Lf i))) with (Lf j - Lf i) in E by lia.
    pose proof (pow2_pos (Lf j - Lf i) ltac:(lia)) as Q2.
    assert (Rq : 0 <= cc Lf j / 2 ^ (Lf j - Lf i) < 2 ^ Z.of_nat (Z.to_nat (Lf i))).
    { replace (Z.of_nat (Z.to_nat (Lf i))) with (Lf i) by lia.
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      rewrite <- pow2_split by lia. replace (Lf j - Lf i + Lf i) with (Lf j) by lia. lia. }
    apply brv_inj in E; [| exact Rq | replace (Z.of_nat (Z.to_nat (Lf i))) with (Lf i) by lia; lia].
    lia.
  Qed.
End CanonPF.


Section RepLoop.
  Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.
  Local Notation Nn := (N lens lens_ofs codes).
  Local Notation Lg := (Lf lens lens_ofs codes).
  Local Notation mx := (max lens lens_ofs codes).
  Local Notation mn := (min lens lens_ofs codes).
  Hypothesis Hmax : 1 <= mx.
  Hypothesis Hcomplete : kraft lens lens_ofs codes 15 = 2 ^ 15.
  Variable root : Z.
  Hypothesis Hroot : mn <= root <= 15.
  Variable table : Z.

  Local Notation mC := (m Nn Lg root).
  Local Notation hfj := (hf Lg).
  Local Notation ppj := (pp Lg root).
  Local Notation SBq := (SB Nn Lg root).
  Local Notation Dq := (Dp Nn Lg root).
  Local Notation drj := (dr lens lens_ofs codes root).
  Local Notation cuj := (cu lens lens_ofs codes root).
  Local Notation nxj := (nx lens lens_ofs codes root table).
  Local Notation loj := (lo lens lens_ofs codes root).
  Local Notation nbk := (newblk lens lens_ofs codes root).
  Local Notation hits := (hitsF lens lens_ofs codes root table).
  Local Notation STW := (STEPW ty lens lens_ofs codes root table).
  Local Notation LWn := (LW ty lens lens_ofs codes root table).
  Local Notation HVj := (HV ty lens lens_ofs codes root).
  Local Notation LINKk := (LINK lens lens_ofs codes root table).

  Let CN' : 1 <= Nn := CN lens lens_ofs codes Hcodes Hlens Hmax.
  Let CL' : forall i, 0 <= i < Nn -> 1 <= Lg i <= 15 := CL lens lens_ofs codes Hcodes.
  Let CS' : forall i j, 0 <= i <= j -> j < Nn -> Lg i <= Lg j := CS lens lens_ofs codes Hcodes.
  Let CC' : SK Lg Nn = 2 ^ 15 := CC lens lens_ofs codes Hcodes Hcomplete.
  Let CR' : 1 <= root <= 15 := CR lens lens_ofs codes Hcodes Hlens Hmax root Hroot.
  Let Lm' := Lm lens lens_ofs codes Hcodes Hlens Hmax root Hroot.
  Let PF := hf_prefix_free Nn Lg CL' CS' CC'.
  Let Lhf_low' := Lhf_low lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot.
  Let Lhf_range' := Lhf_range lens lens_ofs codes Hcodes.
  Let Lpp_range' := Lpp_range lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot.
  Let LSB_step' := LSB_step lens lens_ofs codes root.
  Let hitsF_range' := hitsF_range lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot table.
  Let newblk_true_facts' := newblk_true_facts lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot table.
  Let Lbrv_pp' := Lbrv_pp lens lens_ofs codes Hcodes Hlens Hmax root Hroot.

  Lemma short_fields : forall j, 0 <= j < mC -> drj j = 0 /\ cuj j = root /\ nxj j = table.
  Proof.
    intros j Hj. unfold dr, cu, nx. replace (j <? mC) with true by (symmetry; apply Z.ltb_lt; lia). repeat split; reflexivity.
  Qed.
  Lemma long_fields : forall j, mC <= j -> drj j = root /\ cuj j = Dq (ppj j) /\ nxj j = table + 2 ^ root + SBq (ppj j)
                                          /\ loj j = brv (Z.to_nat root) (ppj j).
  Proof.
    intros j Hj. unfold dr, cu, nx, lo. replace (j <? mC) with false by (symmetry; apply Z.ltb_ge; lia). repeat split; reflexivity.
  Qed.

  Lemma hits_short_iff : forall j i, 0 <= j < mC ->
    hits j i = true <-> (table <= i < table + 2 ^ root /\ (i - table) mod 2 ^ Lg j = hfj j).
  Proof.
    intros j i Hj. destruct Lm' as (Lm1 & Lm2 & Lm3). pose proof (Lm2 j Hj) as HLr. pose proof (CL' j ltac:(lia)) as HL.
    destruct (short_fields j Hj) as (Edr & Ecu & Enx). pose proof (Lhf_range' j ltac:(lia)) as HR.
    unfold hitsF. rewrite Edr, Ecu, Enx, Z.shiftr_0_r, Z.sub_0_r.
    pose proof (pow2_pos (Lg j) ltac:(lia)). pose proof (pow2_pos (root - Lg j) ltac:(lia)).
    rewrite (fill_hits_iff table (hfj j) (2 ^ Lg j) (2 ^ (root - Lg j)) i) by lia.
    rewrite <- pow2_split by lia. replace (root - Lg j + Lg j) with root by lia. tauto.
  Qed.

  Lemma hits_long_iff : forall j i, mC <= j < Nn ->
    hits j i = true <-> (nxj j <= i < nxj j + 2 ^ cuj j /\ (i - nxj j) mod 2 ^ (Lg j - root) = hfj j / 2 ^ root).
  Proof.
    intros j i Hj. destruct Lm' as (Lm1 & Lm2 & Lm3). pose proof (Lm3 j Hj) as HLr. pose proof (CL' j ltac:(lia)) as HL.
    destruct (long_fields j ltac:(lia)) as (Edr & Ecu & Enx & _). pose proof (Lhf_range' j ltac:(lia)) as HR.
    pose proof (phase_facts lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot table j ltac:(lia)) as (_ & F2 & _).
    rewrite Edr in F2.
    unfold hitsF. rewrite Edr, Z.shiftr_div_pow2 by lia.
    pose proof (pow2_pos (Lg j - root) ltac:(lia)). pose proof (pow2_pos (cuj j - (Lg j - root)) ltac:(lia)). pose proof (pow2_pos root ltac:(lia)).
    assert (Hh : 0 <= hfj j / 2 ^ root < 2 ^ (Lg j - root)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- pow2_split by lia.
      replace (root + (Lg j - root)) with (Lg j) by lia. lia. }
    rewrite (fill_hits_iff (nxj j) (hfj j / 2 ^ root) (2 ^ (Lg j - root)) (2 ^ (cuj j - (Lg j - root))) i) by lia.
    rewrite <- pow2_split by lia. replace (cuj j - (Lg j - root) + (Lg j - root)) with (cuj j) by lia. tauto.
  Qed.

  Lemma same_block : forall j j2 c, mC <= j < Nn -> mC <= j2 < Nn ->
    nxj j <= c < nxj j + 2 ^ cuj j -> nxj j2 <= c < nxj j2 + 2 ^ cuj j2 -> ppj j = ppj j2.
  Proof.
    intros j j2 c Hj Hj2 Hc Hc2.
    destruct (long_fields j ltac:(lia)) as (_ & Ecu & Enx & _). destruct (long_fields j2 ltac:(lia)) as (_ & Ecu2 & Enx2 & _).
    rewrite Ecu, Enx in Hc. rewrite Ecu2, Enx2 in Hc2.
    pose proof (Lpp_range' j Hj) as P1. pose proof (Lpp_range' j2 Hj2) as P2.
    destruct (Z.lt_total (ppj j) (ppj j2)) as [LT|[EQ|GT]]; [| exact EQ |].
    - pose proof (LSB_step' (ppj j) ltac:(lia)) as S1.
      pose proof (SB_mono Nn Lg root (ppj j + 1) (ppj j2) ltac:(lia)) as S2. unfold Dp in *. lia.
    - pose proof (LSB_step' (ppj j2) ltac:(lia)) as S1.
      pose proof (SB_mono Nn Lg root (ppj j2 + 1) (ppj j) ltac:(lia)) as S2. unfold Dp in *. lia.
  Qed.

  Lemma LW_none : forall n j0 i, (forall j2, j0 <= j2 < j0 + Z.of_nat n -> STW j2 i = None) -> LWn n j0 i = None.
  Proof.
    induction n as [|n IH]; intros j0 i H; cbn [LW]; [reflexivity|].
    rewrite (IH (j0 + 1)) by (intros j2 Hj2; apply H; lia). apply H. lia.
  Qed.

  Lemma LW_at : forall n j0 i j v, j0 <= j < j0 + Z.of_nat n -> STW j i = Some v ->
    (forall j2, j < j2 < j0 + Z.of_nat n -> STW j2 i = None) -> LWn n j0 i = Some v.
  Proof.
    induction n as [|n IH]; intros j0 i j v Hj Hs Hn; cbn [LW]; [lia|].
    destruct (Z.eq_dec j j0) as [->|NE].
    - rewrite LW_none by (intros j2 Hj2; apply Hn; lia). exact Hs.
    - rewrite (IH (j0 + 1) i j v) by (first [lia | exact Hs | intros j2 Hj2; apply Hn; lia]). reflexivity.
  Qed.

  Lemma link_pos : forall j2 i, 0 <= j2 -> j2 + 1 < Nn ->
    (j2 + 1 <? Nn) && nbk (j2 + 1) && (i =? table + loj (j2 + 1)) = true ->
    mC <= j2 + 1 /\ i = table + hfj (j2 + 1) mod 2 ^ root.
  Proof.
    intros j2 i Hj2 Hj2N E.
    apply andb_prop in E. destruct E as [E1 E3]. apply andb_prop in E1. destruct E1 as [E1 E2]. apply Z.eqb_eq in E3.
    destruct (newblk_true_facts' j2 Hj2 Hj2N E2) as (HmC & _ & _ & _ & _ & _ & Elo).
    rewrite Lhf_low' by lia. rewrite <- Elo. split; [exact HmC | exact E3].
  Qed.

  Lemma rep_root_core : forall j x x', 0 <= j < mC -> 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
    hits j (table + x) = true -> x mod 2 ^ Lg j = x' mod 2 ^ Lg j ->
    LWn (Z.to_nat Nn) 0 (table + x') = Some (HVj j).
  Proof.
    intros j x x' Hj Hx Hx' Hh Exx. destruct Lm' as (Lm1 & Lm2 & Lm3). pose proof (Lm2 j Hj) as HLr.
    pose proof (CL' j ltac:(lia)) as HL. pose proof (Lhf_range' j ltac:(lia)) as HR.
    apply (hits_short_iff j (table + x) Hj) in Hh. destruct Hh as [_ Hh]. replace (table + x - table) with x in Hh by lia.
    assert (NOLINK : forall j2, j <= j2 < Nn ->
              (j2 + 1 <? Nn) && nbk (j2 + 1) && (table + x' =? table + loj (j2 + 1)) = false).
    { intros j2 Hj2. destruct (Z_lt_le_dec (j2 + 1) Nn) as [LT|GE].
      2:{ replace (j2 + 1 <? Nn) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      match goal with |- ?b = false => destruct b eqn:E; [exfalso | reflexivity] end.
      destruct (link_pos j2 (table + x') ltac:(lia) LT E) as [HmC Ei].
      apply (PF j (j2 + 1) ltac:(lia) ltac:(lia)).
      rewrite <- (mod_pow2_mod (hfj (j2 + 1)) (Lg j) root) by lia.
      replace (hfj (j2 + 1) mod 2 ^ root) with x' by lia. rewrite <- Exx. exact Hh. }
    apply (LW_at (Z.to_nat Nn) 0 (table + x') j (HVj j)); [lia| |].
    - unfold STEPW. rewrite (NOLINK j) by lia.
      replace (hits j (table + x')) with true; [reflexivity|]. symmetry.
      apply (hits_short_iff j (table + x') Hj). split; [lia|]. replace (table + x' - table) with x' by lia. rewrite <- Exx. exact Hh.
    - intros j2 Hj2. unfold STEPW. rewrite (NOLINK j2) by lia.
      destruct (hits j2 (table + x')) eqn:F; [exfalso | reflexivity].
      destruct (Z_lt_le_dec j2 mC) as [S2|L2].
      + apply (hits_short_iff j2 (table + x') ltac:(lia)) in F. destruct F as [_ F].
        replace (table + x' - table) with x' in F by lia.
        pose proof (CS' j j2 ltac:(lia) ltac:(lia)) as LE.
        apply (PF j j2 ltac:(lia) ltac:(lia)). rewrite <- F. rewrite mod_pow2_mod by lia. rewrite <- Exx. exact Hh.
      + pose proof (hitsF_range' j2 (table + x') ltac:(lia) F) as RG.
        destruct (long_fields j2 L2) as (_ & _ & Enx & _). rewrite Enx in RG.
        pose proof (SB_nonneg Nn Lg root) as SB0.
        pose proof (LSB_nonneg lens lens_ofs codes root (ppj j2)). lia.
  Qed.

  Lemma rep_sub_core : forall j k i i', mC <= k < Nn -> mC <= j < Nn -> 0 <= i < 2 ^ cuj k -> 0 <= i' < 2 ^ cuj k ->
    hits j (nxj k + i) = true -> i mod 2 ^ (Lg j - root) = i' mod 2 ^ (Lg j - root) ->
    LWn (Z.to_nat Nn) 0 (nxj k + i') = Some (HVj j) /\ ppj j = ppj k.
  Proof.
    intros j k i i' Hk Hj Hi Hi' Hh Eii. destruct Lm' as (Lm1 & Lm2 & Lm3). pose proof (Lm3 j Hj) as HLr.
    pose proof (CL' j ltac:(lia)) as HL. pose proof (Lhf_range' j ltac:(lia)) as HR. pose proof CR' as RR.
    pose proof (hitsF_range' j (nxj k + i) ltac:(lia) Hh) as RG.
    pose proof (same_block j k (nxj k + i) Hj Hk RG ltac:(lia)) as EP.
    destruct (long_fields j ltac:(lia)) as (Edrj & Ecuj & Enxj & _). destruct (long_fields k ltac:(lia)) as (Edrk & Ecuk & Enxk & Elok).
    assert (Enx : nxj j = nxj k) by (rewrite Enxj, Enxk, EP; reflexivity).
    assert (Ecu : cuj j = cuj k) by (rewrite Ecuj, Ecuk, EP; reflexivity).
    apply (hits_long_iff j (nxj k + i) Hj) in Hh. destruct Hh as [_ Hh]. rewrite <- Enx in *.
    replace (nxj j + i - nxj j) with i in Hh by lia.
    pose proof (SB_nonneg Nn Lg root (ppj j)) as SB0. pose proof (pow2_pos root ltac:(lia)) as PR.
    assert (ABOVE : table + 2 ^ root <= nxj j) by (rewrite Enxj; lia).
    assert (NOLINK : forall j2, j <= j2 < Nn ->
              (j2 + 1 <? Nn) && nbk (j2 + 1) && (nxj j + i' =? table + loj (j2 + 1)) = false).
    { intros j2 Hj2. destruct (Z_lt_le_dec (j2 + 1) Nn) as [LT|GE].
      2:{ replace (j2 + 1 <? Nn) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      match goal with |- ?b = false => destruct b eqn:E; [exfalso | reflexivity] end.
      destruct (link_pos j2 (nxj j + i') ltac:(lia) LT E) as [HmC Ei].
      pose proof (Z.mod_pos_bound (hfj (j2 + 1)) (2 ^ root) PR). lia. }
    split; [| exact EP].
    apply (LW_at (Z.to_nat Nn) 0 (nxj j + i') j (HVj j)); [lia| |].
    - unfold STEPW. rewrite (NOLINK j) by lia.
      replace (hits j (nxj j + i')) with true; [reflexivity|]. symmetry.
      apply (hits_long_iff j (nxj j + i') Hj). split; [rewrite Ecu; lia|]. replace (nxj j + i' - nxj j) with i' by lia. rewrite <- Eii. exact Hh.
    - intros j2 Hj2. unfold STEPW. rewrite (NOLINK j2) by lia.
      destruct (hits j2 (nxj j + i')) eqn:F; [exfalso | reflexivity].
      pose proof (hitsF_range' j2 (nxj j + i') ltac:(lia) F) as RG2.
      destruct (Z_lt_le_dec j2 mC) as [S2|L2]; [lia|].
      pose proof (same_block j2 j (nxj j + i') ltac:(lia) Hj RG2 ltac:(rewrite Ecu; lia)) as EP2.
      destruct (long_fields j2 L2) as (_ & Ecu2 & Enx2 & _).
      assert (Enx' : nxj j2 = nxj j) by (rewrite Enx2, Enxj, EP2; reflexivity).
      apply (hits_long_iff j2 (nxj j + i') ltac:(lia)) in F. destruct F as [_ F]. rewrite Enx' in F.
      replace (nxj j + i' - nxj j) with i' in F by lia.
      pose proof (CS' j j2 ltac:(liaq) ltac:(liaq)) as LE. pose proof (CL' j2 ltac:(liaq)) as HL2.
      pose proof (Lhf_range' j2 ltac:(liaq)) as HR2.
      apply (PF j j2 ltac:(liaq) ltac:(liaq)).
      replace (2 ^ Lg j) with (2 ^ (root + (Lg j - root))) by (f_equal; lia).
      rewrite mod_pow2_split by lia.
      rewrite (Lhf_low' j2) by liaq. rewrite EP2. rewrite <- (Lhf_low' j) by lia.
      rewrite <- F. rewrite mod_pow2_mod by lia. rewrite <- Eii, Hh.
      pose proof (Z.div_mod (hfj j) (2 ^ root) ltac:(lia)). liaq.
  Qed.
End RepLoop.


Lemma ent_op_not_link : forall ty codes w, 0 <= w < codes -> codes <= 288 ->
  (ty = CODES -> codes <= 19) -> (ty = DISTS -> codes <= 32) ->
  ~ (1 <= wrap8 (ItCovLoop.ent_op ty w) <= 15).
Proof.
  intros ty codes w Hw Hc HC HD. destruct ty.
  - destruct (ent_CODES w ltac:(specialize (HC eq_refl); lia)) as [-> _]. rewrite w8_small by lia. lia.
  - pose proof (ent_LENS_L w ltac:(lia)) as X. cbv zeta in X.
    destruct X as [(-> & _) | [(-> & _) | [[-> | ->] | (R & _)]]]; rewrite w8_small by lia; lia.
  - pose proof (ent_DISTS w ltac:(specialize (HD eq_refl); lia)) as X. cbv zeta in X.
    destruct X as (E & _ & [[R _] | [R _]]); rewrite E in *; rewrite w8_small by (pose proof (w8_range (arr_get dext_a w)); lia); lia.
Qed.


Section Rep.
  Variables (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr).

  Local Notation r := (inflate_table ty lens lens_ofs codes tbl table bits work).
  Local Notation ret := (fst (fst (fst (fst r)))).
  Local Notation tbl' := (snd (fst (fst (fst r)))).
  Local Notation table' := (snd (fst (fst r))).
  Local Notation bits' := (snd (fst r)).

  Definition it_rep_root : Prop :=
    forall x x', 0 <= x < 2 ^ bits' -> 0 <= x' < 2 ^ bits' ->
      let e := arr_get tbl' (table + x) in
      ~ (1 <= code_op e <= 15) ->
      x mod 2 ^ (InflateState.code_bits e) = x' mod 2 ^ (InflateState.code_bits e) ->
      arr_get tbl' (table + x') = e.

  Definition it_rep_sub : Prop :=
    forall x, 0 <= x < 2 ^ bits' ->
      let l := arr_get tbl' (table + x) in
      1 <= code_op l <= 15 ->
      forall i i', 0 <= i < 2 ^ (code_op l) -> 0 <= i' < 2 ^ (code_op l) ->
        let e := arr_get tbl' (table + code_val l + i) in
        i mod 2 ^ (InflateState.code_bits e) = i' mod 2 ^ (InflateState.code_bits e) ->
        arr_get tbl' (table + code_val l + i') = e.

  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.
  Hypothesis HtyC : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get lens (lens_ofs + s) <= 7.
  Hypothesis HtyD : ty = DISTS -> codes <= 32.
  Hypothesis Hbits : 1 <= bits <= 15.
  Hypothesis Htable : 0 <= table.
  Hypothesis Hroom : table + it_room ty <= arr_len tbl.
  Hypothesis Hwork : codes <= arr_len work.


  Lemma cb1 : forall op val, InflateState.code_bits (code_pack op 1 val) = 1.
  Proof. intros. rewrite code_bits_pack. apply w8_small. lia. Qed.
  Lemma mod2_eq : forall x x', 0 <= x < 2 -> 0 <= x' < 2 -> x mod 2 ^ 1 = x' mod 2 ^ 1 -> x = x'.
  Proof. intros x x' Hx Hx' E. change (2 ^ 1) with 2 in E. rewrite !Z.mod_small in E by lia. exact E. Qed.

  Theorem it_replicated : ret = 0 ->
    it_rep_root /\ it_rep_sub.
  Proof.
    intros Hret. unfold it_rep_root, it_rep_sub. cbv zeta.
    pose proof (max_spec lens lens_ofs codes Hcodes Hlens) as (MA & MB & MC).
    pose proof (room2 ty tbl table Hroom) as R2.
    assert (HC19 : ty = CODES -> codes <= 19) by (intros E; destruct (HtyC E) as (A & _ & _); exact A).
    destruct (Z.eq_dec (max lens lens_ofs codes) 0) as [M0|M0].
    {
      rewrite (it_empty ty lens lens_ofs codes tbl table bits work M0) in *. cbn [fst snd] in *.
      assert (CELL : forall x, 0 <= x < 2 ->
                arr_get (arr_set (arr_set tbl table (code_pack 64 1 0)) (table + 1) (code_pack 64 1 0)) (table + x) = code_pack 64 1 0).
      { intros x Hx. destruct (Z.eq_dec x 1) as [->|NE].
        - apply arr_get_set_same. rewrite arr_len_set. lia.
        - rewrite arr_get_set_other by lia. replace (table + x) with table by lia. apply arr_get_set_same. lia. }
      split.
      - intros x x' Hx Hx' _ E. rewrite (CELL x Hx) in E |- *. rewrite cb1 in E.
        rewrite <- (mod2_eq x x' Hx Hx' E). apply CELL. exact Hx.
      - intros x Hx Hl. exfalso. rewrite (CELL x Hx), code_op_pack, w8_small in Hl by lia. lia. }
    destruct (Z_lt_le_dec (2 ^ 15) (kraft lens lens_ofs codes 15)) as [K|K].
    { rewrite (it_over ty lens lens_ofs codes tbl table bits work Hcodes Hlens M0 K) in Hret. cbn in Hret. discriminate Hret. }
    destruct (Z.eq_dec (kraft lens lens_ofs codes 15) (2 ^ 15)) as [KC|KC].
    -
      set (root := itm_root bits (max lens lens_ofs codes) (min lens lens_ofs codes)) in *.
      pose proof (Hmax1 lens lens_ofs codes Hcodes Hlens M0) as M1.
      pose proof (ItCovMain.Hroot lens lens_ofs codes bits Hcodes Hlens Hbits M0) as HR. fold root in HR.
      pose proof (CR lens lens_ofs codes Hcodes Hlens M1 root HR) as RR.
      pose proof (Lm lens lens_ofs codes Hcodes Hlens M1 root HR) as (Lm1 & Lm2 & Lm3).
      pose proof (CN lens lens_ofs codes Hcodes Hlens M1) as N1. pose proof (N_range lens lens_ofs codes Hcodes Hlens) as NR.
      destruct (it_not_enough ty (2 ^ root)) eqn:NE.
      { rewrite (it_big ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Hroom M0 KC NE) in Hret. cbn in Hret. discriminate Hret. }
      set (kf := findZ (fun k => NF ty lens lens_ofs codes root k) 1 (N lens lens_ofs codes)).
      destruct (findZ_spec (fun k => NF ty lens lens_ofs codes root k) 1 (N lens lens_ofs codes) ltac:(lia)) as (R & P & Q). fold kf in R, P, Q.
      destruct (Z_lt_le_dec kf (N lens lens_ofs codes)) as [KF|KF].
      { destruct (it_fail ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Hroom Hwork M0 KC NE
                    ltac:(exists kf; split; [lia | exact (P KF)])) as (A1 & _). cbv zeta in A1. rewrite A1 in Hret. discriminate Hret. }
      assert (HNF : forall k, 0 < k < N lens lens_ofs codes -> NF ty lens lens_ofs codes root k = false) by (intros k Hk; apply Q; lia).
      destruct (it_ok ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork M0 KC NE HNF)
        as (A1 & T1 & B1 & L1 & G1 & _ & _ & _ & U1 & RB1 & RB1').
      cbv zeta in A1, T1, B1, L1, G1, U1. fold root in A1, T1, B1, G1, U1, RB1, RB1'.
      rewrite B1.
      pose proof (cover ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table) as COV.
      pose proof (fun i v => LW_kind ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table (Z.to_nat (N lens lens_ofs codes)) 0 i v
                             ltac:(lia) ltac:(lia)) as KIND.
      pose proof (usF_lt lens lens_ofs codes Hcodes Hlens M1 KC root HR) as UF.
      pose proof (pow2_pos root ltac:(lia)) as PR.
      split.
      +
        intros x x' Hx Hx' Hnl Exx. rewrite (G1 (table + x)) in Hnl, Exx |- *. rewrite (G1 (table + x')).
        destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 (table + x)) as [v|] eqn:E;
          [| exfalso; exact (COV (table + x) ltac:(lia) E)].
        destruct (KIND (table + x) v E) as [(j & Hj & -> & Edr & Ecu & Enx & Hh & Hi) | [(k & Hk & Hnb & -> & Hik & Hi & Hcu & Hnx1 & Hnx2) | (j & Hj & -> & Edr & Hcu & Hh & Hnx & Hi & Hus)]].
        * unfold HV in Exx. rewrite code_bits_pack, Edr, Z.sub_0_r in Exx.
          pose proof (CL lens lens_ofs codes Hcodes j ltac:(liaq)) as HL. rewrite w8_small in Exx by lia.
          rewrite (rep_root_core ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table j x x' Hj Hx Hx' Hh Exx). reflexivity.
        * exfalso. apply Hnl. unfold LINK. rewrite code_op_pack, w8_small by liaq. liaq.
        * exfalso. liaq.
      +
        intros x Hx Hlk i i' Hi Hi' Eii. rewrite (G1 (table + x)) in Hlk, Hi, Hi', Eii |- *.
        destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 (table + x)) as [v|] eqn:E;
          [| exfalso; exact (COV (table + x) ltac:(lia) E)].
        destruct (KIND (table + x) v E) as [(j & Hj & -> & Edr & Ecu & Enx & Hh & Hix) | [(k & Hk & Hnb & -> & Hik & Hix & Hcu & Hnx1 & Hnx2) | (j & Hj & -> & Edr & Hcu & Hh & Hnx & Hix & Hus)]].
        * exfalso. unfold HV in Hlk. rewrite code_op_pack in Hlk.
          apply (ent_op_not_link ty codes (znth 0 (W lens lens_ofs codes) j) (LWr lens lens_ofs codes Hcodes j ltac:(liaq)) ltac:(liaq) HC19 HtyD). exact Hlk.
        *
          unfold LINK in Hlk, Hi, Hi', Eii |- *. rewrite code_op_pack in Hlk, Hi, Hi'. rewrite w8_small in Hlk, Hi, Hi' by liaq.
          rewrite code_val_pack in Eii |- *. rewrite w16_small in Eii |- * by liaq.
          replace (table + (nx lens lens_ofs codes root table k - table) + i) with (nx lens lens_ofs codes root table k + i) in Eii |- * by lia.
          replace (table + (nx lens lens_ofs codes root table k - table) + i') with (nx lens lens_ofs codes root table k + i') by lia.
          rewrite (G1 (nx lens lens_ofs codes root table k + i)) in Eii |- *. rewrite (G1 (nx lens lens_ofs codes root table k + i')).
          destruct (LW ty lens lens_ofs codes root table (Z.to_nat (N lens lens_ofs codes)) 0 (nx lens lens_ofs codes root table k + i)) as [v|] eqn:E2;
            [| exfalso; exact (COV (nx lens lens_ofs codes root table k + i) ltac:(liaq) E2)].
          destruct (KIND _ v E2) as [(j & Hj & -> & Edr & Ecu & Enx & Hh & Hi2) | [(k2 & Hk2 & Hnb2 & -> & Hik2 & Hi2 & Hcu2 & Hnx12 & Hnx22) | (j & Hj & -> & Edr & Hcu' & Hh & Hnx & Hi2 & Hus)]].
          -- exfalso. lia.
          -- exfalso. lia.
          -- unfold HV in Eii. rewrite code_bits_pack, Edr in Eii.
             pose proof (CL lens lens_ofs codes Hcodes j ltac:(lia)) as HL. pose proof (Lm3 j Hj) as HLr. rewrite w8_small in Eii by lia.
             destruct (rep_sub_core ty lens lens_ofs codes Hcodes Hlens M1 KC root HR table j k i i' ltac:(lia) Hj Hi Hi' Hh Eii) as [-> _].
             reflexivity.
        * exfalso. lia.
    -
      assert (KL : kraft lens lens_ofs codes 15 < 2 ^ 15) by lia.
      destruct (codetype_eqb ty CODES || negb (max lens lens_ofs codes =? 1)) eqn:E.
      { assert (C : ty = CODES \/ max lens lens_ofs codes <> 1).
        { apply Bool.orb_true_iff in E. destruct E as [E|E]; [left; destruct ty; [reflexivity|discriminate|discriminate] | right].
          apply negb_true_iff in E. apply Z.eqb_neq in E. exact E. }
        rewrite (it_incomp ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hroom M0 KL C) in Hret. cbn in Hret. discriminate Hret. }
      apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply negb_false_iff in E2. apply Z.eqb_eq in E2.
      assert (Hty : ty <> CODES) by (intros X; rewrite X in E1; discriminate).
      destruct (single_facts lens lens_ofs codes bits Hcodes Hlens Hbits E2 KL) as (C1 & N1 & MN & RT & Wr & WL).
      destruct (it_single ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC HtyD Hbits Htable Hroom Hwork E2 KL Hty)
        as (A1 & T1 & B1 & L1 & G1 & _).
      cbv zeta in A1, T1, B1, L1, G1. rewrite B1.
      assert (CELLb : forall x, 0 <= x < 2 -> InflateState.code_bits (arr_get (snd (fst (fst (fst r)))) (table + x)) = 1).
      { intros x Hx. rewrite G1. destruct (Z.eqb_spec (table + x) (table + 1)); [apply cb1|]. replace (table + x =? table) with true by (symmetry; apply Z.eqb_eq; lia). apply cb1. }
      assert (CELLo : forall x, 0 <= x < 2 -> ~ (1 <= code_op (arr_get (snd (fst (fst (fst r)))) (table + x)) <= 15)).
      { intros x Hx. rewrite G1. destruct (Z.eqb_spec (table + x) (table + 1)); [rewrite code_op_pack, w8_small by lia; lia|].
        replace (table + x =? table) with true by (symmetry; apply Z.eqb_eq; lia). rewrite code_op_pack.
        apply (ent_op_not_link ty codes _ Wr ltac:(lia) HC19 HtyD). }
      split.
      + intros x x' Hx Hx' _ Ex. rewrite (CELLb x Hx) in Ex. rewrite <- (mod2_eq x x' Hx Hx' Ex). reflexivity.
      + intros x Hx Hl. exfalso. exact (CELLo x Hx Hl).
  Qed.
End Rep.
