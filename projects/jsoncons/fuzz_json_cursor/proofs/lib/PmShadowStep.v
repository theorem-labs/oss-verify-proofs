(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIfaceA PmHeapIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sstep_lo (o m : Z) : Z := if o <? m then o / 8 else (m + 7) / 8.
Definition sstep_hi (o m : Z) : Z := if o <? m then m / 8 else (o + 7) / 8.
Definition sstep_v (o m : Z) : Z := if o <? m then 0 else 252.

Lemma sstep_div : forall u k, u mod 8 = 0 -> (u + k) / 8 = u / 8 + k / 8.
Proof. intros u k U8. pose proof (Z.div_mod u 8 ltac:(lia)) as D. rewrite U8, Z.add_0_r in D. rewrite D at 1. replace (8 * (u / 8) + k) with (k + u / 8 * 8) by ring. rewrite Z.div_add by lia. ring. Qed.
Lemma sstep_mod : forall u k, u mod 8 = 0 -> (u + k) mod 8 = k mod 8.
Proof. intros u k U8. pose proof (Z.div_mod u 8 ltac:(lia)) as D. rewrite U8, Z.add_0_r in D. rewrite D at 1. replace (8 * (u / 8) + k) with (k + u / 8 * 8) by ring. apply Z.mod_add. lia. Qed.

Lemma shadow_cont_step : forall (M M' : word -> option byte) u n om nm, 0 <= u -> u mod 8 = 0 -> 0 <= om <= n -> 0 <= nm <= n ->
  shadow_cont M u n om ->
  let o := u + om in let m := u + nm in
  (forall j, 0 <= j < (n + 7) / 8 -> ~ (o <> m /\ sstep_lo o m <= u / 8 + j < sstep_hi o m) -> ~ (o <> m /\ m mod 8 <> 0 /\ u / 8 + j = m / 8) ->
             M' (Z_to_bv 64 (S u + j)) = M (Z_to_bv 64 (S u + j))) ->
  (o <> m -> forall g, sstep_lo o m <= g < sstep_hi o m -> M' (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 (sstep_v o m))) ->
  (o <> m -> m mod 8 <> 0 -> M' (Z_to_bv 64 (SB + m / 8)) = Some (Z_to_bv 8 (m mod 8))) ->
  shadow_cont M' u n nm.
Proof.
  intros M M' u n om nm Hu U8 Hom Hnm (Z0 & P0 & F0) o m KEEP FILL PART.
  assert (Eo : o / 8 = u / 8 + om / 8) by (apply sstep_div; exact U8). assert (Em : m / 8 = u / 8 + nm / 8) by (apply sstep_div; exact U8).
  assert (Eo7 : (o + 7) / 8 = u / 8 + (om + 7) / 8) by (unfold o; rewrite <- Z.add_assoc; apply sstep_div; exact U8).
  assert (Em7 : (m + 7) / 8 = u / 8 + (nm + 7) / 8) by (unfold m; rewrite <- Z.add_assoc; apply sstep_div; exact U8).
  assert (Emm : m mod 8 = nm mod 8) by (apply sstep_mod; exact U8).
  assert (ES : forall j, SB + (u / 8 + j) = S u + j) by (intros j; unfold S; ring).
  assert (Q : (om / 8 <= (om + 7) / 8 <= om / 8 + 1 /\ (om mod 8 = 0 -> (om + 7) / 8 = om / 8) /\ (om mod 8 <> 0 -> (om + 7) / 8 = om / 8 + 1))
              /\ (nm / 8 <= (nm + 7) / 8 <= nm / 8 + 1 /\ (nm mod 8 = 0 -> (nm + 7) / 8 = nm / 8) /\ (nm mod 8 <> 0 -> (nm + 7) / 8 = nm / 8 + 1))).
  { split.
    - pose proof (Z.div_mod om 8 ltac:(lia)). pose proof (Z.mod_pos_bound om 8 ltac:(lia)). pose proof (Z.div_mod (om + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (om + 7) 8 ltac:(lia)). lia.
    - pose proof (Z.div_mod nm 8 ltac:(lia)). pose proof (Z.mod_pos_bound nm 8 ltac:(lia)). pose proof (Z.div_mod (nm + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nm + 7) 8 ltac:(lia)). lia. }
  destruct Q as ((Qo1 & Qo2 & Qo3) & (Qm1 & Qm2 & Qm3)).
  assert (Qn : om / 8 <= n / 8 /\ nm / 8 <= n / 8 /\ (om + 7) / 8 <= (n + 7) / 8 /\ (nm + 7) / 8 <= (n + 7) / 8 /\ n / 8 <= (n + 7) / 8) by (repeat split; apply Z.div_le_mono; lia).
  destruct Qn as (Qn1 & Qn2 & Qn3 & Qn4 & Qn5).
  assert (Qlt : (om < nm -> om / 8 <= nm / 8 /\ (om / 8 = nm / 8 -> om mod 8 < nm mod 8)) /\ (nm < om -> nm / 8 <= om / 8 /\ (om / 8 = nm / 8 -> nm mod 8 < om mod 8))).
  { pose proof (Z.div_mod om 8 ltac:(lia)). pose proof (Z.mod_pos_bound om 8 ltac:(lia)). pose proof (Z.div_mod nm 8 ltac:(lia)). pose proof (Z.mod_pos_bound nm 8 ltac:(lia)). lia. }
  destruct Qlt as (Qinc & Qshr).
  assert (Rom : 0 <= om mod 8 < 8) by (apply Z.mod_pos_bound; lia). assert (Rnm : 0 <= nm mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (N0 : 0 <= om / 8 /\ 0 <= nm / 8) by (split; apply Z.div_pos; lia). destruct N0 as (No0 & Nm0).
  destruct (Z.eq_dec om nm) as [E|NE].
  -
    subst nm. assert (K : forall j, 0 <= j < (n + 7) / 8 -> M' (Z_to_bv 64 (S u + j)) = M (Z_to_bv 64 (S u + j))) by (intros j Hj; apply KEEP; [exact Hj|intros (X & _); apply X; reflexivity|intros (X & _); apply X; reflexivity]).
    split; [|split].
    + intros j Hj. unfold byte_at. rewrite K by lia. exact (Z0 j Hj).
    + intros Hne. unfold byte_at. rewrite K by lia. exact (P0 Hne).
    + intros j Hj. unfold byte_at. rewrite K by lia. exact (F0 j Hj).
  - assert (NEo : o <> m) by (unfold o, m; lia).
    destruct (Z_lt_ge_dec om nm) as [INC|SHR].
    +
      assert (LT : (o <? m) = true) by (apply Z.ltb_lt; unfold o, m; lia).
      unfold sstep_lo, sstep_hi, sstep_v in KEEP, FILL. rewrite LT in KEEP, FILL. rewrite Eo, Em in KEEP, FILL. destruct (Qinc INC) as (Q1 & Q2).
      split; [|split].
      * intros j Hj. unfold byte_at. destruct (Z_lt_ge_dec j (om / 8)) as [Old|New].
        -- rewrite KEEP by (first [lia | intros (_ & X); lia | intros (_ & _ & X); lia]). exact (Z0 j ltac:(lia)).
        -- rewrite <- ES. apply (FILL NEo). lia.
      * intros Hne. unfold byte_at. rewrite <- ES, <- Em, <- Emm. apply (PART NEo). rewrite Emm. exact Hne.
      * intros j Hj. unfold byte_at. rewrite KEEP by (first [lia | intros (_ & X); lia | intros (_ & _ & X); lia]). apply (F0 j). lia.
    +
      assert (SHR' : nm < om) by lia.
      assert (GE : (o <? m) = false) by (apply Z.ltb_ge; unfold o, m; lia).
      unfold sstep_lo, sstep_hi, sstep_v in KEEP, FILL. rewrite GE in KEEP, FILL. rewrite Eo7, Em7 in KEEP, FILL. rewrite Em in KEEP. destruct (Qshr SHR') as (Q1 & Q2).
      split; [|split].
      * intros j Hj. unfold byte_at. rewrite KEEP by (first [lia | intros (_ & X); lia | intros (_ & _ & X); lia]). exact (Z0 j ltac:(lia)).
      * intros Hne. unfold byte_at. rewrite <- ES, <- Em, <- Emm. apply (PART NEo). rewrite Emm. exact Hne.
      * intros j Hj. unfold byte_at. destruct (Z_lt_ge_dec j ((om + 7) / 8)) as [New|Old].
        -- rewrite <- ES. unfold CONT_OOB. apply (FILL NEo). lia.
        -- rewrite KEEP by (first [lia | intros (_ & X); lia | intros (_ & _ & X); lia]). apply (F0 j). lia.
Qed.
