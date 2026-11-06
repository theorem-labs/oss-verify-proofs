(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Stage1Model Stage2Ghost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Module S1G.
Section WithSegs.
Context {fx : FPState}.
Variable SEGS : list Segment.

Notation mem := (S2G.mem).
Notation nthb := S2G.nthb.
Definition input := S2G.input SEGS.
Definition u32_at := S2G.u32_at SEGS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Model.
Variable b : Z -> Z.
Variable len : Z.

(* [comment removed for export] *)
Fixpoint iterk (k : nat) (s : S1M.st) : option S1M.st :=
  match k with
  | O => Some s
  | S k' => if S1M.s_idx s <? len then iterk k' (S1M.iter b len s) else None
  end.
Definition runs (J : Z) (out : list Z) (E : Z) (F : bool) : Prop :=
  exists k, iterk k S1M.init = Some (S1M.ST J out E F).

(* [comment removed for export] *)
Definition nostop (lo hi : Z) : Prop := forall k, lo <= k < hi -> S1M.is_ascii_stop (b k) = false.
Definition spaces (lo hi : Z) : Prop := forall k, lo <= k < hi -> S1M.is_space (b k) = true.
(* [comment removed for export] *)
Inductive vsreach (q : Z) (e0 : Z) : Z -> Z -> Prop :=
| VS0 : vsreach q e0 (q + 1) e0
| VSbs : forall idx err i, vsreach q e0 idx err -> idx < len -> idx <= i < len -> nostop idx i ->
    S1M.is_ascii_stop (b i) = true -> b i = S1M.BACKSLASH -> vsreach q e0 (i + 2) err
| VSu8 : forall idx err i i' err', vsreach q e0 idx err -> idx < len -> idx <= i < len -> nostop idx i ->
    S1M.is_ascii_stop (b i) = true -> b i <> S1M.QUOTE -> b i <> S1M.BACKSLASH -> Z.land (b i) 128 <> 0 ->
    S1M.vutf8 b len i err = (i', err') -> vsreach q e0 i' err'
| VSch : forall idx err i, vsreach q e0 idx err -> idx < len -> idx <= i < len -> nostop idx i ->
    S1M.is_ascii_stop (b i) = true -> b i <> S1M.QUOTE -> b i <> S1M.BACKSLASH -> Z.land (b i) 128 = 0 ->
    vsreach q e0 (i + 1) (if b i <? 32 then S1M.UNESCAPED_CHARS else err).
End Model.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ModelLemmas.
Variable b : Z -> Z.
Variable len : Z.
Ltac rd := cbn -[S1M.is_space S1M.is_op S1M.is_space_or_op S1M.is_ascii_stop S1M.is_cont S1M.char_class Z.add Z.sub Z.mul Z.of_nat Z.to_nat].
Ltac rdin H := cbn -[S1M.is_space S1M.is_op S1M.is_space_or_op S1M.is_ascii_stop S1M.is_cont S1M.char_class Z.add Z.sub Z.mul Z.of_nat Z.to_nat] in H.

(* [comment removed for export] *)
Lemma wsrun_char : forall n J0 p, Z.of_nat n = p - J0 -> J0 <= p -> p < len ->
  spaces b J0 p -> S1M.is_space (b p) = false ->
  forall fuel, (n < fuel)%nat -> S1M.wsrun b len fuel J0 = p.
Proof.
  induction n as [|n IH]; intros J0 p Hn HJ Hp Hsp Hns fuel Hf.
  - assert (J0 = p) by lia. subst J0. destruct fuel as [|f]; [lia|]. rd. rewrite Hns. reflexivity.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hsp J0) by lia.
    destruct (Z.ltb_spec (J0 + 1) len); [|lia].
    apply (IH (J0 + 1) p); try lia. intros k Hk. apply Hsp. lia. exact Hns.
Qed.
(* [comment removed for export] *)
Lemma wsrun_end : forall n J0, Z.of_nat n = len - 1 - J0 -> J0 < len -> spaces b J0 len ->
  forall fuel, (n < fuel)%nat -> S1M.wsrun b len fuel J0 = len.
Proof.
  induction n as [|n IH]; intros J0 Hn HJ Hsp fuel Hf.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hsp J0) by lia. destruct (Z.ltb_spec (J0 + 1) len); [lia|]. lia.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hsp J0) by lia. destruct (Z.ltb_spec (J0 + 1) len); [|lia].
    apply (IH (J0 + 1)); try lia. intros k Hk. apply Hsp. lia.
Qed.

(* [comment removed for export] *)
Lemma stoprun_char : forall n idx i, Z.of_nat n = i - idx -> idx <= i -> i < len ->
  nostop b idx i -> S1M.is_ascii_stop (b i) = true ->
  forall fuel, (n < fuel)%nat -> S1M.stoprun b len fuel idx = i.
Proof.
  induction n as [|n IH]; intros idx i Hn Hi Hl Hns Hst fuel Hf.
  - assert (idx = i) by lia. subst idx. destruct fuel as [|f]; [lia|]. rd. rewrite Hst. reflexivity.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hns idx) by lia. destruct (Z.ltb_spec (idx + 1) len); [|lia].
    apply (IH (idx + 1) i); try lia. intros k Hk. apply Hns. lia. exact Hst.
Qed.
Lemma stoprun_end : forall n idx, Z.of_nat n = len - 1 - idx -> idx < len -> nostop b idx len ->
  forall fuel, (n < fuel)%nat -> S1M.stoprun b len fuel idx = len.
Proof.
  induction n as [|n IH]; intros idx Hn Hi Hns fuel Hf.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hns idx) by lia. destruct (Z.ltb_spec (idx + 1) len); [lia|]. lia.
  - destruct fuel as [|f]; [lia|]. rd. rewrite (Hns idx) by lia. destruct (Z.ltb_spec (idx + 1) len); [|lia].
    apply (IH (idx + 1)); try lia. intros k Hk. apply Hns. lia.
Qed.

(* [comment removed for export] *)
Definition prim_ok (k : Z) : bool := (negb (S1M.is_space_or_op (b k)) && negb (b k =? S1M.RS))%bool.
Lemma primrun_char : forall n i0 p, Z.of_nat n = p - i0 -> i0 <= p ->
  (forall k, i0 < k <= p -> k < len /\ prim_ok k = true) ->
  (len <= p + 1 \/ prim_ok (p + 1) = false) ->
  forall fuel, (n < fuel)%nat -> S1M.primrun b len fuel i0 = p.
Proof.
  induction n as [|n IH]; intros i0 p Hn Hi Hok Hend fuel Hf.
  - assert (i0 = p) by lia. subst i0. destruct fuel as [|f]; [lia|]. rd. unfold prim_ok in Hend.
    destruct (Z.ltb_spec (p + 1) len); rd; [|reflexivity].
    destruct Hend as [Hend|Hend]; [lia|]. rewrite Hend. reflexivity.
  - destruct fuel as [|f]; [lia|]. rd. destruct (Hok (i0 + 1)) as [Hl1 Hp1]; [lia|]. unfold prim_ok in Hp1.
    destruct (Z.ltb_spec (i0 + 1) len); rd; [|lia]. rewrite Hp1.
    apply (IH (i0 + 1) p); try lia. intros k Hk. apply Hok. lia. exact Hend.
Qed.

(* [comment removed for export] *)
Lemma vsreach_bound : forall q e0 idx err, vsreach b len q e0 idx err -> q + 1 <= idx.
Proof.
  intros q e0 idx err H. induction H as [ | idx err i Hv IH Hlt Hi Hns Hst Hbs | idx err i i' err' Hv IH Hlt Hi Hns Hst Hnq Hnb Hhi Hu8 | idx err i Hv IH Hlt Hi Hns Hst Hnq Hnb Hlo ]; try lia.
  pose proof (S1M.vutf8_gt b len i err) as Hg. rewrite Hu8 in Hg. cbn in Hg. lia.
Qed.
Lemma vsreach_unfold : forall q e0 idx err, vsreach b len q e0 idx err ->
  exists m : nat, (Z.of_nat m <= idx - q - 1 /\ (m = O \/ Z.of_nat m <= len - q - 1)) /\
    forall f, S1M.vstring_loop b len (m + f) (q + 1) e0 = S1M.vstring_loop b len f idx err.
Proof.
  intros q e0 idx err H.
  induction H as [ | idx err i Hv IH Hlt Hi Hns Hst Hbs | idx err i i' err' Hv IH Hlt Hi Hns Hst Hnq Hnb Hhi Hu8 | idx err i Hv IH Hlt Hi Hns Hst Hnq Hnb Hlo ].
  - exists O. split; [lia|]. intros f. reflexivity.
  - destruct IH as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv). exists (S m). split; [lia|]. intros f.
    replace (S m + f)%nat with (m + S f)%nat by lia. rewrite Hf. rd.
    destruct (Z.ltb_spec idx len); [|lia].
    rewrite (stoprun_char (Z.to_nat (i - idx)) idx i ltac:(lia) ltac:(lia) ltac:(lia) Hns Hst (Z.to_nat (len - idx)) ltac:(lia)).
    destruct (Z.leb_spec len i); [lia|]. rewrite Hbs. rd. reflexivity.
  - destruct IH as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv). pose proof (S1M.vutf8_gt b len i err) as Hg. rewrite Hu8 in Hg. cbn in Hg.
    exists (S m). split; [lia|]. intros f.
    replace (S m + f)%nat with (m + S f)%nat by lia. rewrite Hf. rd.
    destruct (Z.ltb_spec idx len); [|lia].
    rewrite (stoprun_char (Z.to_nat (i - idx)) idx i ltac:(lia) ltac:(lia) ltac:(lia) Hns Hst (Z.to_nat (len - idx)) ltac:(lia)).
    destruct (Z.leb_spec len i); [lia|].
    destruct (Z.eqb_spec (b i) S1M.QUOTE); [contradiction|]. destruct (Z.eqb_spec (b i) S1M.BACKSLASH); [contradiction|].
    destruct (Z.eqb_spec (Z.land (b i) 128) 0); [contradiction|]. rd. rewrite Hu8. reflexivity.
  - destruct IH as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv). exists (S m). split; [lia|]. intros f.
    replace (S m + f)%nat with (m + S f)%nat by lia. rewrite Hf. rd.
    destruct (Z.ltb_spec idx len); [|lia].
    rewrite (stoprun_char (Z.to_nat (i - idx)) idx i ltac:(lia) ltac:(lia) ltac:(lia) Hns Hst (Z.to_nat (len - idx)) ltac:(lia)).
    destruct (Z.leb_spec len i); [lia|].
    destruct (Z.eqb_spec (b i) S1M.QUOTE); [contradiction|]. destruct (Z.eqb_spec (b i) S1M.BACKSLASH); [contradiction|].
    rewrite Hlo. rd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vstring_closed : forall q e0 idx err i, 0 <= q -> vsreach b len q e0 idx err -> idx < len -> idx <= i < len ->
  nostop b idx i -> S1M.is_ascii_stop (b i) = true -> b i = S1M.QUOTE -> idx <= len ->
  S1M.vstring b len q e0 = (i, err, false).
Proof.
  intros q e0 idx err i Hq0 Hv Hlt Hi Hns Hst Hq Hle. unfold S1M.vstring.
  destruct (vsreach_unfold _ _ _ _ Hv) as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv).
  replace (Z.to_nat (len + 2)) with (m + S (Z.to_nat (len + 1 - Z.of_nat m)))%nat by lia. rewrite Hf. rd.
  destruct (Z.ltb_spec idx len); [|lia].
  rewrite (stoprun_char (Z.to_nat (i - idx)) idx i ltac:(lia) ltac:(lia) ltac:(lia) Hns Hst (Z.to_nat (len - idx)) ltac:(lia)).
  destruct (Z.leb_spec len i); [lia|]. rewrite Hq. rd. reflexivity.
Qed.
Lemma vstring_unclosed_run : forall q e0 idx err, 0 <= q -> vsreach b len q e0 idx err -> idx < len -> nostop b idx len ->
  S1M.vstring b len q e0 = (len, err, true).
Proof.
  intros q e0 idx err Hq0 Hv Hlt Hns. unfold S1M.vstring.
  destruct (vsreach_unfold _ _ _ _ Hv) as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv).
  replace (Z.to_nat (len + 2)) with (m + S (Z.to_nat (len + 1 - Z.of_nat m)))%nat by lia. rewrite Hf. rd.
  destruct (Z.ltb_spec idx len); [|lia].
  rewrite (stoprun_end (Z.to_nat (len - 1 - idx)) idx ltac:(lia) ltac:(lia) Hns (Z.to_nat (len - idx)) ltac:(lia)).
  destruct (Z.leb_spec len len); [|lia]. reflexivity.
Qed.
Lemma vstring_unclosed_at : forall q e0 idx err, 0 <= q -> 0 <= len -> vsreach b len q e0 idx err -> len <= idx -> idx <= len + 4 ->
  S1M.vstring b len q e0 = (idx, err, true).
Proof.
  intros q e0 idx err Hq0 Hl0 Hv Hge Hle. unfold S1M.vstring.
  destruct (vsreach_unfold _ _ _ _ Hv) as (m & [Hm Hm2] & Hf). pose proof (vsreach_bound _ _ _ _ Hv).
  replace (Z.to_nat (len + 2)) with (m + S (Z.to_nat (len + 1 - Z.of_nat m)))%nat by lia. rewrite Hf. rd.
  destruct (Z.ltb_spec idx len); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iterk_extend : forall k s0 s, iterk b len k s0 = Some s -> S1M.s_idx s < len -> iterk b len (S k) s0 = Some (S1M.iter b len s).
Proof.
  induction k as [|k IH]; intros s0 s H Hlt; cbn in H |- *.
  - injection H as <-. destruct (Z.ltb_spec (S1M.s_idx s0) len); [reflexivity|lia].
  - destruct (S1M.s_idx s0 <? len); [|discriminate]. cbn. apply IH; assumption.
Qed.
Lemma runs_step : forall J out E F s', runs b len J out E F -> J < len -> S1M.iter b len (S1M.ST J out E F) = s' ->
  runs b len (S1M.s_idx s') (S1M.s_out s') (S1M.s_err s') (S1M.s_unclosed s').
Proof.
  intros J out E F s' [k Hk] Hlt Hit. exists (S k). rewrite (iterk_extend k _ _ Hk Hlt). rewrite Hit. destruct s'; reflexivity.
Qed.
Lemma iter_gt : forall s, S1M.s_idx s < len -> S1M.s_idx s + 1 <= S1M.s_idx (S1M.iter b len s).
Proof.
  intros [idx out err u] Hlt. cbn in Hlt. unfold S1M.iter. rd.
  pose proof (S1M.wsrun_ge b len (Z.to_nat (len - idx)) idx) as Hw. set (i := S1M.wsrun b len (Z.to_nat (len - idx)) idx) in *.
  destruct (Z.leb_spec len i); [rd; lia|].
  destruct (b i =? S1M.QUOTE).
  - destruct (S1M.vstring b len i err) as [[i' err'] u'] eqn:Hv. rd.
    pose proof (S1M.vstring_loop_ge b len (Z.to_nat (len + 2)) (i + 1) err) as Hg. unfold S1M.vstring in Hv. rewrite Hv in Hg. cbn in Hg. lia.
  - destruct (S1M.is_op (b i)); rd; [lia|]. pose proof (S1M.primrun_ge b len (Z.to_nat (len - i)) i). lia.
Qed.
Lemma iterk_idx : forall k s0 s, iterk b len k s0 = Some s -> S1M.s_idx s0 + Z.of_nat k <= S1M.s_idx s /\ (k = O \/ S1M.s_idx s0 + Z.of_nat k - 1 < len).
Proof.
  induction k as [|k IH]; intros s0 s H; cbn in H.
  - injection H as <-. lia.
  - destruct (Z.ltb_spec (S1M.s_idx s0) len); [|discriminate].
    destruct (IH _ _ H) as [H1 H2]. pose proof (iter_gt s0 ltac:(assumption)). split; [lia|]. right. destruct H2 as [->|H2]; [cbn in H1 |- *; lia|lia].
Qed.
Lemma iterk_run : forall k s0 s, iterk b len k s0 = Some s -> len <= S1M.s_idx s -> forall f, (k <= f)%nat -> S1M.run b len f s0 = s.
Proof.
  induction k as [|k IH]; intros s0 s H Hge f Hf; cbn in H.
  - injection H as <-. destruct f; cbn; [reflexivity|]. destruct (Z.ltb_spec (S1M.s_idx s0) len); [lia|reflexivity].
  - destruct (Z.ltb_spec (S1M.s_idx s0) len); [|discriminate]. destruct f as [|f]; [lia|]. cbn.
    destruct (Z.ltb_spec (S1M.s_idx s0) len); [|lia]. apply IH; [assumption|assumption|lia].
Qed.
Lemma runs_final : forall J out E F, 0 <= len -> runs b len J out E F -> len <= J -> S1M.final b len = S1M.ST J out E F.
Proof.
  intros J out E F Hl [k Hk] HJ. unfold S1M.final. apply (iterk_run k); [exact Hk|cbn; lia|].
  destruct (iterk_idx k _ _ Hk) as [H1 H2]. cbn in H1, H2. destruct H2 as [->|H2]; lia.
Qed.
Lemma runs_init : runs b len 0 [] S1M.SUCCESS false.
Proof. exists O. reflexivity. Qed.
End ModelLemmas.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb (F : Z) : bool := negb (F =? 0).
(* [comment removed for export] *)
Definition prefix_at (M : mem) (a1 : Z) (out : list Z) : Prop :=
  forall k, (k < length out)%nat -> u32_at M (a1 + 4 * Z.of_nat k) = Some (nth k out 0).
Definition wfctx (buf len a1 C : Z) : Prop :=
  0 <= len /\ buf + len + 64 < two64 /\ 0 <= a1 /\ a1 + 4 * len + 48 < two64 /\ 0 <= C <= len.

Definition p_s1a (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; J; C; E; F] =>
      wfctx buf len a1 C /\ (F = 0 \/ F = 1) /\
      exists bs out, input M buf len = Some bs /\
        runs (nthb bs) len J out E (zb F) /\ Z.of_nat (length out) = C /\ prefix_at M a1 out
  | _ => False
  end.

Definition p_s1w (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; p; C; E; F] =>
      wfctx buf len a1 C /\ (F = 0 \/ F = 1) /\
      exists bs out J0, input M buf len = Some bs /\
        runs (nthb bs) len J0 out E (zb F) /\ Z.of_nat (length out) = C /\ prefix_at M a1 out /\
        J0 <= p /\ J0 < len /\ spaces (nthb bs) J0 p
  | _ => False
  end.

Definition p_s1s (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; p; C; Ec; F] =>
      wfctx buf len a1 C /\ (F = 0 \/ F = 1) /\ C < len /\
      exists bs out J0 E0 q cur0, input M buf len = Some bs /\
        runs (nthb bs) len J0 out E0 (zb F) /\ Z.of_nat (length out) = C /\ prefix_at M a1 out /\
        u32_at M (a1 + 4 * C) = Some q /\
        J0 <= q /\ q < len /\ spaces (nthb bs) J0 q /\ nthb bs q = S1M.QUOTE /\
        vsreach (nthb bs) len q E0 cur0 Ec /\ cur0 <= p /\ nostop (nthb bs) cur0 p
  | _ => False
  end.

Definition p_s1p (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; p; C; E; F] =>
      wfctx buf len a1 C /\ (F = 0 \/ F = 1) /\ C < len /\
      exists bs out J0 i0, input M buf len = Some bs /\
        runs (nthb bs) len J0 out E (zb F) /\ Z.of_nat (length out) = C /\ prefix_at M a1 out /\
        u32_at M (a1 + 4 * C) = Some i0 /\
        J0 <= i0 /\ i0 < len /\ spaces (nthb bs) J0 i0 /\
        S1M.is_space (nthb bs i0) = false /\ S1M.is_op (nthb bs i0) = false /\ nthb bs i0 <> S1M.QUOTE /\
        i0 <= p /\ p + 1 < len /\
        (forall k, i0 < k <= p + 1 -> S1M.is_space_or_op (nthb bs k) = false /\ nthb bs k <> S1M.RS)
  | _ => False
  end.

(* [comment removed for export] *)
Definition p_s1p0 (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; p; C; E; F] =>
      wfctx buf len a1 C /\ (F = 0 \/ F = 1) /\ C < len /\
      exists bs out J0 i0, input M buf len = Some bs /\
        runs (nthb bs) len J0 out E (zb F) /\ Z.of_nat (length out) = C /\ prefix_at M a1 out /\
        u32_at M (a1 + 4 * C) = Some i0 /\
        J0 <= i0 /\ i0 < len /\ spaces (nthb bs) J0 i0 /\
        S1M.is_space (nthb bs i0) = false /\ S1M.is_op (nthb bs i0) = false /\ nthb bs i0 <> S1M.QUOTE /\
        i0 <= p /\ p + 1 < len /\
        (forall k, i0 < k <= p -> S1M.is_space_or_op (nthb bs k) = false /\ nthb bs k <> S1M.RS)
  | _ => False
  end.

(* [comment removed for export] *)
Definition p_s1x (vs : list Z) (M : mem) : Prop :=
  match vs with
  | [buf; len; a1; n; rc] =>
      0 <= len /\ buf + len + 64 < two64 /\ 0 <= a1 /\ a1 + 4 * n + 12 < two64 /\ 0 <= n /\ n <= len /\
      exists bs, input M buf len = Some bs /\
        snd (S1M.result (nthb bs) len) = rc /\
        (rc = S1M.SUCCESS -> S2G.p_s1ok SEGS [buf; len; a1; n] M)
  | _ => False
  end.

Definition GP1 (id : nat) (vs : list Z) (M : mem) : Prop :=
  if Nat.eqb id 71 then p_s1a vs M
  else if Nat.eqb id 72 then p_s1w vs M
  else if Nat.eqb id 73 then p_s1s vs M
  else if Nat.eqb id 74 then p_s1p vs M
  else if Nat.eqb id 75 then p_s1p0 vs M
  else if Nat.eqb id 76 then p_s1x vs M
  else S2G.GP2 SEGS id vs M.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition len64 (len : expr) : expr := mkAlu ALU_ADD len (ELit 64).
Definition len4 (c : expr) (k : Z) : expr := mkAlu ALU_ADD (mkAlu ALU_SLL c (ELit 2)) (ELit k).
Definition fp1 (id : nat) (args : list expr) : list (expr * expr) :=
  if (Nat.eqb id 71 || Nat.eqb id 72)%bool then
    match args with [buf; len; a1; _; c; _; _] => [(buf, len64 len); (a1, len4 c 0)] | _ => [(ELit 0, ELit 0)] end
  else if (Nat.eqb id 73 || Nat.eqb id 74 || Nat.eqb id 75)%bool then
    match args with [buf; len; a1; _; c; _; _] => [(buf, len64 len); (a1, len4 c 4)] | _ => [(ELit 0, ELit 0)] end
  else if Nat.eqb id 76 then
    match args with [buf; len; a1; n; _] => [(buf, len64 len); (a1, len4 n 12)] | _ => [(ELit 0, ELit 0)] end
  else S2G.fp2 id args.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation uD E e := (bv_unsigned (edenot E e)) (only parsing).
Lemma uE_len64 : forall E l, uD E l + 64 < two64 -> uD E (len64 l) = uD E l + 64.
Proof. intros. unfold len64. apply S2G.uE_add_lit; lia. Qed.
Lemma uE_len4 : forall E c k, 0 <= k -> uD E c * 4 + k < two64 -> uD E (len4 c k) = uD E c * 4 + k.
Proof.
  intros E c k Hk H. unfold len4. pose proof (u64_range (edenot E c)).
  rewrite S2G.uE_add_lit; [| lia | rewrite S2G.uE_sll_lit; [lia|lia|unfold two64 in *; lia]].
  rewrite S2G.uE_sll_lit; [lia|lia|unfold two64 in *; lia].
Qed.

Lemma prefix_at_frame : forall M M' a1 out, 0 <= a1 -> a1 + 4 * Z.of_nat (length out) <= two64 ->
  S2G.agree_on M M' a1 (4 * Z.of_nat (length out)) -> prefix_at M a1 out -> prefix_at M' a1 out.
Proof.
  intros M M' a1 out Ha Hn Hag Hp k Hk. rewrite <- (Hp k Hk). unfold u32_at. apply S2G.u32_at_frame; [lia|unfold two64 in *; lia|].
  eapply S2G.agree_on_sub; [exact Hag|lia|lia].
Qed.

(* [comment removed for export] *)
Lemma ctx_agree : forall E M M' (buf len a1 x c y z : expr) (k : Z),
  0 <= k ->
  (forall a, APS.in_fp E [(buf, len64 len); (a1, len4 c k)] a = true -> M' a = M a) ->
  uD E len + 64 < two64 -> uD E c * 4 + k < two64 ->
  S2G.agree_on M M' (uD E buf) (uD E len + 64) /\ S2G.agree_on M M' (uD E a1) (uD E c * 4 + k).
Proof.
  intros E M M' buf len a1 x c y z k Hk Hfp Hl Hc. split.
  - intros w Hw. apply Hfp. apply (proj2 (S2G.in_fp_range2 E _ _ _ _ w)). left. rewrite uE_len64; lia.
  - intros w Hw. apply Hfp. apply (proj2 (S2G.in_fp_range2 E _ _ _ _ w)). right. rewrite uE_len4; lia.
Qed.

Theorem GP1_frame : forall id args E M M',
  (forall a, APS.in_fp E (fp1 id args) a = true -> M' a = M a) ->
  GP1 id (map (APS.uE E) args) M -> GP1 id (map (APS.uE E) args) M'.
Proof.
  intros id args E M M'. unfold GP1, fp1.
  destruct (Nat.eqb id 71) eqn:E71.
  { cbn [orb]. intros Hfp H. unfold p_s1a in *. destruct args as [|buf [|len [|a1 [|J [|C [|Er [|F [|? ?]]]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (W & HF & bs & out & Hin & Hr & Hlen & Hp). unfold wfctx in W.
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E C)).
    destruct (ctx_agree E M M' buf len a1 J C Er F 0 ltac:(lia) Hfp ltac:(unfold two64 in *; lia) ltac:(unfold two64 in *; lia)) as [AG1 AG2].
    split; [exact W|]. split; [exact HF|]. exists bs, out. split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|].
    split; [exact Hr|]. split; [exact Hlen|]. eapply prefix_at_frame; [lia| unfold two64 in *; lia | |exact Hp].
    eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
  destruct (Nat.eqb id 72) eqn:E72.
  { cbn [orb]. intros Hfp H. unfold p_s1w in *. destruct args as [|buf [|len [|a1 [|J [|C [|Er [|F [|? ?]]]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (W & HF & bs & out & J0 & Hin & Hr & Hlen & Hp & Hrest). unfold wfctx in W.
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E C)).
    destruct (ctx_agree E M M' buf len a1 J C Er F 0 ltac:(lia) Hfp ltac:(unfold two64 in *; lia) ltac:(unfold two64 in *; lia)) as [AG1 AG2].
    split; [exact W|]. split; [exact HF|]. exists bs, out, J0. split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|].
    split; [exact Hr|]. split; [exact Hlen|]. split; [|exact Hrest]. eapply prefix_at_frame; [lia| unfold two64 in *; lia | |exact Hp].
    eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
  cbn [orb].
  destruct (Nat.eqb id 73) eqn:E73.
  { cbn [orb]. intros Hfp H. unfold p_s1s in *. destruct args as [|buf [|len [|a1 [|J [|C [|Er [|F [|? ?]]]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (W & HF & HC & bs & out & J0 & E0 & q & cur0 & Hin & Hr & Hlen & Hp & Hq & Hrest). unfold wfctx in W.
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E C)).
    destruct (ctx_agree E M M' buf len a1 J C Er F 4 ltac:(lia) Hfp ltac:(unfold two64 in *; lia) ltac:(unfold two64 in *; lia)) as [AG1 AG2].
    split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, E0, q, cur0.
    split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|].
    split; [exact Hr|]. split; [exact Hlen|]. split. { eapply prefix_at_frame; [lia| unfold two64 in *; lia | |exact Hp]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
    split; [|exact Hrest]. rewrite <- Hq. unfold u32_at. apply S2G.u32_at_frame; [lia|unfold two64 in *; lia|]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
  destruct (Nat.eqb id 74) eqn:E74.
  { cbn [orb]. intros Hfp H. unfold p_s1p in *. destruct args as [|buf [|len [|a1 [|J [|C [|Er [|F [|? ?]]]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (W & HF & HC & bs & out & J0 & i0 & Hin & Hr & Hlen & Hp & Hq & Hrest). unfold wfctx in W.
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E C)).
    destruct (ctx_agree E M M' buf len a1 J C Er F 4 ltac:(lia) Hfp ltac:(unfold two64 in *; lia) ltac:(unfold two64 in *; lia)) as [AG1 AG2].
    split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, i0.
    split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|].
    split; [exact Hr|]. split; [exact Hlen|]. split. { eapply prefix_at_frame; [lia| unfold two64 in *; lia | |exact Hp]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
    split; [|exact Hrest]. rewrite <- Hq. unfold u32_at. apply S2G.u32_at_frame; [lia|unfold two64 in *; lia|]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
  destruct (Nat.eqb id 75) eqn:E75.
  { cbn [orb]. intros Hfp H. unfold p_s1p0 in *. destruct args as [|buf [|len [|a1 [|J [|C [|Er [|F [|? ?]]]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (W & HF & HC & bs & out & J0 & i0 & Hin & Hr & Hlen & Hp & Hq & Hrest). unfold wfctx in W.
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E C)).
    destruct (ctx_agree E M M' buf len a1 J C Er F 4 ltac:(lia) Hfp ltac:(unfold two64 in *; lia) ltac:(unfold two64 in *; lia)) as [AG1 AG2].
    split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, i0.
    split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|].
    split; [exact Hr|]. split; [exact Hlen|]. split. { eapply prefix_at_frame; [lia| unfold two64 in *; lia | |exact Hp]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
    split; [|exact Hrest]. rewrite <- Hq. unfold u32_at. apply S2G.u32_at_frame; [lia|unfold two64 in *; lia|]. eapply S2G.agree_on_sub; [exact AG2|lia|lia]. }
  cbn [orb].
  destruct (Nat.eqb id 76) eqn:E76.
  { intros Hfp H. unfold p_s1x in *. destruct args as [|buf [|len [|a1 [|n [|rc [|? ?]]]]]]; cbn [map] in *; try contradiction.
    unfold APS.uE in *. destruct H as (Hl & Hb & Ha & Hn & Hn0 & Hnl & bs & Hin & Hrc & Hok).
    pose proof (u64_range (edenot E buf)). pose proof (u64_range (edenot E a1)). pose proof (u64_range (edenot E n)).
    assert (AG1 : S2G.agree_on M M' (bv_unsigned (edenot E buf)) (bv_unsigned (edenot E len) + 64)).
    { intros w Hw. apply Hfp. apply (proj2 (S2G.in_fp_range2 E _ _ _ _ w)). left. rewrite uE_len64; lia. }
    split; [exact Hl|]. split; [exact Hb|]. split; [exact Ha|]. split; [exact Hn|]. split; [exact Hn0|]. split; [exact Hnl|]. exists bs.
    split; [rewrite <- Hin; unfold input; apply S2G.input_frame; try lia; exact AG1|]. split; [exact Hrc|].
    intros Hs. pose proof (Hok Hs) as HS1.
    apply (S2G.GP2_frame SEGS 60 [buf; len; a1; n] E M M'); [|exact HS1].
    unfold S2G.fp2. cbn [Nat.eqb]. intros a Ha1. apply Hfp. unfold S2G.fp_s1ok in Ha1.
    apply (proj2 (S2G.in_fp_range2 E _ _ _ _ a)). apply (proj1 (S2G.in_fp_range2 E _ _ _ _ a)) in Ha1.
    destruct Ha1 as [L1|R1]; [left; rewrite uE_len64; [|lia]; rewrite S2G.uE_add_lit in L1; lia | right].
    rewrite uE_len4; [|lia|lia]. rewrite S2G.uE_len4n12 in R1; lia. }
  exact (S2G.GP2_frame SEGS id args E M M').
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint vars_only (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EExt _ lo n a => (match a with EVar n' => Nat.eqb n' v && Nat.eqb lo 0 && Nat.eqb n 1 | _ => false end)%bool || vars_only v a
  | EAlu _ a c => vars_only v a && vars_only v c
  | EAluw _ a c => vars_only v a && vars_only v c
  | EMd _ a c => vars_only v a && vars_only v c
  | EMdw _ a c => vars_only v a && vars_only v c
  | EBlob _ _ _ _ => false
  end.
Definition Eb (b : Z) : env := Env (fun _ => Z_to_bv 64 b) (fun _ => []).

Lemma ext_low_byte : forall sx (w w' : word), bv_unsigned w mod 256 = bv_unsigned w' mod 256 -> ext_val sx 0 1 w = ext_val sx 0 1 w'.
Proof.
  intros sx w w' H. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul]. rewrite !Z.pow_0_r, !Z.div_1_r.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. rewrite H. reflexivity.
Qed.
Lemma vars_only_sound : forall v e E b, vars_only v e = true -> 0 <= b < 256 ->
  bv_unsigned (ev E v) mod 256 = b -> edenot E e = edenot (Eb b) e.
Proof.
  intros v e E b. induction e as [z|n|op a IHa c IHc|op a IHa c IHc|op a IHa c IHc|op a IHa c IHc|sx lo n a IHa|sx k i n]; cbn [vars_only]; intros H Hb Hv.
  - reflexivity.
  - discriminate.
  - apply andb_prop in H as [H1 H2]. cbn [edenot]. rewrite (IHa H1 Hb Hv), (IHc H2 Hb Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. cbn [edenot]. rewrite (IHa H1 Hb Hv), (IHc H2 Hb Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. cbn [edenot]. rewrite (IHa H1 Hb Hv), (IHc H2 Hb Hv). reflexivity.
  - apply andb_prop in H as [H1 H2]. cbn [edenot]. rewrite (IHa H1 Hb Hv), (IHc H2 Hb Hv). reflexivity.
  - apply Bool.orb_prop in H as [H|H].
    + destruct a as [|n'| | | | | |]; try discriminate.
      apply andb_prop in H as [H Hn]. apply andb_prop in H as [Hv' Hlo].
      apply Nat.eqb_eq in Hv'. apply Nat.eqb_eq in Hlo. apply Nat.eqb_eq in Hn. subst n' lo n.
      cbn [edenot ev Eb]. apply ext_low_byte. rewrite Hv. rewrite Z_to_bv_unsigned. symmetry.
      rewrite bv_wrap_small; [apply Z.mod_small; lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
    + cbn [edenot]. rewrite (IHa H Hb Hv). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Definition byte_facts (v : nat) (kn : list kentry) : list kentry :=
  List.filter (fun K => match K with KRange e _ _ => vars_only v e | _ => false end) kn.
Definition byte_fact_ok (b : Z) (K : kentry) : bool :=
  match K with
  | KRange e lo hi => let z := bv_unsigned (edenot (Eb b) e) in Z.leb lo z && Z.leb z hi
  | _ => true
  end.
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
(* [comment removed for export] *)
Fixpoint direct_range (v : nat) (kb : list kentry) (lo hi : Z) : Z * Z :=
  match kb with
  | [] => (lo, hi)
  | KRange (EExt false 0 1 (EVar n)) l h :: rest =>
      if Nat.eqb n v then direct_range v rest (Z.max lo l) (Z.min hi h) else direct_range v rest lo hi
  | _ :: rest => direct_range v rest lo hi
  end.
Definition bset (kn : list kentry) (v : nat) : list Z :=
  let kb := byte_facts v kn in
  let (lo, hi) := direct_range v kb 0 255 in
  List.filter (fun b => forallb (byte_fact_ok b) kb) (zseq lo (Z.to_nat (hi - lo + 1))).

Lemma zseq_In : forall lo n z, lo <= z < lo + Z.of_nat n -> In z (zseq lo n).
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z Hz; [lia|]. cbn [zseq].
  destruct (Z.eq_dec lo z); [left; assumption | right]. apply IH. lia.
Qed.
Lemma direct_range_sound : forall E M v kb lo hi, know_ok SEGS E M kb ->
  lo <= bv_unsigned (ev E v) mod 256 <= hi ->
  fst (direct_range v kb lo hi) <= bv_unsigned (ev E v) mod 256 <= snd (direct_range v kb lo hi).
Proof.
  intros E M v kb. induction kb as [|K rest IH]; intros lo hi Hkb Hb; cbn [direct_range fst snd]; [exact Hb|].
  apply Forall_cons_iff in Hkb as [HK Hrest].
  assert (D : fst (direct_range v rest lo hi) <= bv_unsigned (ev E v) mod 256 <= snd (direct_range v rest lo hi)) by (apply IH; assumption).
  destruct K as [| | | | |e l h| | | |]; try exact D.
  destruct e as [| | | | | |sx elo en a|]; try exact D. destruct sx; [exact D|].
  destruct elo as [|elo']; [|exact D]. destruct en as [|[|en']]; try exact D.
  destruct a as [|n| | | | | |]; try exact D.
  destruct (Nat.eqb_spec n v); [|exact D]. subst n. apply IH; [exact Hrest|].
  cbn [kentry_ok] in HK.
  assert (HX : bv_unsigned (edenot E (EExt false 0 1 (EVar v))) = bv_unsigned (ev E v) mod 256).
  { cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat Z.mul]. rewrite Z.pow_0_r, Z.div_1_r.
    replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). pose proof (Z.mod_pos_bound (bv_unsigned (ev E v)) 256 ltac:(lia)). lia. }
  rewrite HX in HK. lia.
Qed.
Lemma bset_sound : forall E M kn v, know_ok SEGS E M kn -> In (bv_unsigned (ev E v) mod 256) (bset kn v).
Proof.
  intros E M kn v Hkn. unfold bset.
  assert (Hkb : know_ok SEGS E M (byte_facts v kn)).
  { unfold byte_facts, know_ok. apply Forall_forall. intros K HK. apply List.filter_In in HK as [HK _]. exact (proj1 (Forall_forall _ _) Hkn K HK). }
  pose proof (Z.mod_pos_bound (bv_unsigned (ev E v)) 256 ltac:(lia)) as Hb.
  pose proof (direct_range_sound E M v (byte_facts v kn) 0 255 Hkb ltac:(lia)) as D.
  destruct (direct_range v (byte_facts v kn) 0 255) as [lo hi]. cbn [fst snd] in D.
  apply List.filter_In. split.
  - apply zseq_In. lia.
  - apply forallb_forall. intros K HK. unfold byte_facts in HK. apply List.filter_In in HK as [HK Hsel].
    pose proof (proj1 (Forall_forall _ _) Hkn K HK) as Hok.
    destruct K as [| | | | |e klo khi| | | |]; try reflexivity. cbn [byte_fact_ok].
    rewrite <- (vars_only_sound v e E (bv_unsigned (ev E v) mod 256) Hsel ltac:(lia) eq_refl). cbn [kentry_ok] in Hok.
    apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma bset_forall : forall E M kn v (P : Z -> bool), know_ok SEGS E M kn ->
  forallb P (bset kn v) = true -> P (bv_unsigned (ev E v) mod 256) = true.
Proof. intros E M kn v P Hkn H. exact (proj1 (forallb_forall _ _) H _ (bset_sound E M kn v Hkn)). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation find_rec := S2G.find_rec.
Notation recval := S2G.recval.
(* [comment removed for export] *)
Definition xeq (kn : list kentry) (a : expr) (k : Z) (b : expr) : bool :=
  lin_ge0 kn [(a, k)] [(b, 0)] && lin_ge0 kn [(b, 0)] [(a, k)].
Definition xle (kn : list kentry) (a : expr) (k : Z) (b : expr) : bool := lin_ge0 kn [(b, 0)] [(a, k)].
Definition xge (kn : list kentry) (a : expr) (k : Z) (b : expr) : bool := lin_ge0 kn [(a, k)] [(b, 0)].
Lemma xeq_sound : forall E M kn a k b, know_ok SEGS E M kn -> xeq kn a k b = true -> uD E a + k = uD E b.
Proof.
  intros E M kn a k b Hkn H. apply andb_prop in H as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H1) as A. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H2) as B. cbn [xt_den] in A, B. lia.
Qed.
Lemma xle_sound : forall E M kn a k b, know_ok SEGS E M kn -> xle kn a k b = true -> uD E a + k <= uD E b.
Proof. intros E M kn a k b Hkn H. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H) as A. cbn [xt_den] in A. lia. Qed.
Lemma xge_sound : forall E M kn a k b, know_ok SEGS E M kn -> xge kn a k b = true -> uD E b <= uD E a + k.
Proof. intros E M kn a k b Hkn H. pose proof (lin_ge0_sound SEGS E M kn _ _ Hkn H) as A. cbn [xt_den] in A. lia. Qed.

(* [comment removed for export] *)
Fixpoint find_zero (kn allkn : list kentry) (e : xterms) : option Z :=
  match kn with
  | [] => None
  | KZero a (ELit m) :: rest =>
      if (S2G.addr_is allkn a e && Z.leb 0 m && Z.ltb m two64)%bool then Some m else find_zero rest allkn e
  | _ :: rest => find_zero rest allkn e
  end.
Lemma find_zero_sound : forall E M allkn kn e m, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_zero kn allkn e = Some m ->
  0 <= xt_den E e /\ xt_den E e + m <= two64 /\ forall i, 0 <= i < m -> M (Z_to_bv 64 (xt_den E e + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E M allkn kn e m Hall Hkn. induction kn as [|K rest IH]; cbn [find_zero]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [|a n| | | | | | | |]; try exact (IH Hrest H).
  destruct n as [z| | | | | | |]; try exact (IH Hrest H).
  destruct (S2G.addr_is allkn a e && Z.leb 0 z && Z.ltb z two64)%bool eqn:Hb; [|exact (IH Hrest H)].
  injection H as <-. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [Ha Hz0]. apply Z.leb_le in Hz0. apply Z.ltb_lt in Hlt.
  pose proof (S2G.addr_is_sound SEGS E M allkn a e Hall Ha) as He. cbn [kentry_ok] in HK. destruct HK as [Hfl Hz].
  assert (HL : elenZ E (ELit z) = z). { unfold elenZ. cbn [edenot]. rewrite u_lit64a. apply Z.mod_small. unfold two64 in Hlt. lia. }
  rewrite HL in Hfl, Hz. destruct Hfl as (F1 & F2 & F3 & F4). rewrite <- He. unfold two64. split; [lia|]. split; [lia|]. exact Hz.
Qed.

(* [comment removed for export] *)
Fixpoint find_unk (kn allkn : list kentry) (buf len : expr) : bool :=
  match kn with
  | [] => false
  | KUnk a n :: rest => (S2G.addr_is allkn a [(buf, 0)] && xeq allkn n 0 len) || find_unk rest allkn buf len
  | _ :: rest => find_unk rest allkn buf len
  end.
Lemma find_unk_sound : forall E M allkn kn buf len, know_ok SEGS E M allkn -> know_ok SEGS E M kn ->
  find_unk kn allkn buf len = true ->
  uD E buf + uD E len <= two64 /\ forall i, 0 <= i < uD E len -> M (Z_to_bv 64 (uD E buf + i)) <> None.
Proof.
  intros E M allkn kn buf len Hall Hkn. induction kn as [|K rest IH]; cbn [find_unk]; intros H; [discriminate|].
  apply Forall_cons_iff in Hkn as [HK Hrest].
  destruct K as [| | | | | | | | |a n]; try exact (IH Hrest H).
  apply Bool.orb_prop in H as [H|H]; [|exact (IH Hrest H)]. apply andb_prop in H as [Ha Hn].
  pose proof (S2G.addr_is_sound SEGS E M allkn a _ Hall Ha) as He. cbn [xt_den] in He.
  pose proof (xeq_sound E M allkn n 0 len Hall Hn) as Hl.
  cbn [kentry_ok] in HK. destruct HK as [Hfl Hu]. unfold elenZ in Hfl, Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  rewrite He in F4, Hu. unfold two64. split; [lia|]. intros i Hi.
  replace (bv_unsigned (edenot E buf) + i) with (bv_unsigned (edenot E buf) + 0 + 0 + i) by lia. apply Hu. lia.
Qed.

(* [comment removed for export] *)
Lemma input_exists : forall E M kn buf len, know_ok SEGS E M kn ->
  find_unk kn kn buf len = true -> (exists m, find_zero kn kn [(buf, 0); (len, 0)] = Some m /\ 64 <= m) ->
  exists bs, input M (uD E buf) (uD E len) = Some bs.
Proof.
  intros E M kn buf len Hkn Hu [m [Hz Hm]].
  destruct (find_unk_sound E M kn kn buf len Hkn Hkn Hu) as [B1 U].
  destruct (find_zero_sound E M kn kn _ m Hkn Hkn Hz) as (Z1 & Z2 & ZZ). cbn [xt_den] in Z1, Z2, ZZ.
  pose proof (u64_range (edenot E buf)) as RB. pose proof (u64_range (edenot E len)) as RL.
  destruct (rdn_defined SEGS M (Z.to_nat (uD E len + 64)) (Z_to_bv 64 (uD E buf))) as (bs & Hbs & _).
  - rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold two64 in *. lia.
  - intros j Hj. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). unfold rd1.
    destruct (Z.lt_ge_cases (Z.of_nat j) (uD E len)) as [Hlt|Hge].
    + pose proof (U (Z.of_nat j) ltac:(lia)) as X. destruct (M (Z_to_bv 64 (bv_unsigned (edenot E buf) + Z.of_nat j))); [discriminate|exfalso; exact (X eq_refl)].
    + pose proof (ZZ (Z.of_nat j - uD E len) ltac:(lia)) as X.
      replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E len) + 0 + 0) + (Z.of_nat j - bv_unsigned (edenot E len)))
        with (bv_unsigned (edenot E buf) + Z.of_nat j) in X by lia. rewrite X. discriminate.
  - exists (map bv_unsigned bs). unfold input, S2G.input. rewrite Hbs. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma input_zero : forall E M buf len bs kn e m j,
  0 <= buf -> buf + len + 64 < two64 -> 0 <= len -> input M buf len = Some bs -> know_ok SEGS E M kn ->
  find_zero kn kn e = Some m -> xt_den E e = buf + len -> len <= j < len + m -> j < len + 64 -> nthb bs j = 0.
Proof.
  intros E M buf len bs kn e m j Hb Hbl Hl Hin Hkn Hz He Hj Hj64.
  destruct (find_zero_sound E M kn kn _ m Hkn Hkn Hz) as (Z1 & Z2 & ZZ). rewrite He in Z1, Z2, ZZ. unfold two64 in *.
  unfold input, S2G.input in Hin. destruct (rdn SEGS M (Z_to_bv 64 buf) (Z.to_nat (len + 64))) as [bb|] eqn:Hall; [|discriminate].
  injection Hin as <-. pose proof (rdn_length _ _ _ _ _ Hall) as Hlen.
  pose proof (rdn_slice SEGS M (Z.to_nat (len + 64)) (Z_to_bv 64 buf) bb (Z.to_nat j) 1 Hall ltac:(lia)) as Hs.
  rewrite <- S2G.Z_to_bv_plus_nat in Hs by lia.
  rewrite S2G.firstn1_skipn in Hs by lia. cbn [rdn] in Hs.
  pose proof (ZZ (j - len) ltac:(lia)) as X. replace (buf + len + (j - len)) with (buf + j) in X by lia.
  replace (buf + Z.of_nat (Z.to_nat j)) with (buf + j) in Hs by lia. rewrite X in Hs. injection Hs as Hb1.
  rewrite S2G.nthb_map by lia. rewrite <- Hb1. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive bval : Type := BZero | BVar (v : nat).
Definition byte_var (kn : list kentry) (buf x : expr) (k : Z) : option nat :=
  match find_rec kn kn [(buf, 0); (x, k)] 1 with Some (EVar v) => Some v | _ => None end.
Definition byte_info (kn : list kentry) (buf len x : expr) (k : Z) : option bval :=
  if negb (Z.leb 0 k) then None else
  match byte_var kn buf x k with
  | Some v => if xle kn x (k - 63) len then Some (BVar v) else None
  | None => match find_zero kn kn [(buf, 0); (len, 0)] with
            | Some m => if (xge kn x k len && xle kn x (k + 1 - m) len && xle kn x (k - 63) len)%bool then Some BZero else None
            | None => None
            end
  end.
Definition bvals (kn : list kentry) (bi : bval) : list Z := match bi with BZero => [0] | BVar v => bset kn v end.
(* [comment removed for export] *)
Definition ball (P : Z -> bool) (kn : list kentry) (bi : bval) : bool := forallb P (bvals kn bi).

Lemma byte_info_sound : forall E M kn buf len bs x k bi (P : Z -> bool),
  know_ok SEGS E M kn -> 0 <= uD E len -> uD E buf + uD E len + 64 < two64 -> input M (uD E buf) (uD E len) = Some bs ->
  byte_info kn buf len x k = Some bi -> ball P kn bi = true -> P (nthb bs (uD E x + k)) = true.
Proof.
  intros E M kn buf len bs x k bi P Hkn Hl Hbl Hin H HP. unfold byte_info in H.
  destruct (Z.leb_spec 0 k); [|discriminate]. cbn [negb] in H.
  pose proof (u64_range (edenot E buf)) as RB. pose proof (u64_range (edenot E x)) as RX.
  destruct (byte_var kn buf x k) as [n|] eqn:Hv.
  - unfold byte_var in Hv. destruct (find_rec kn kn [(buf, 0); (x, k)] 1) as [v|] eqn:Hr; [|discriminate].
    destruct v as [|n'| | | | | |]; try discriminate. injection Hv as ->.
    destruct (xle kn x (k - 63) len) eqn:Hle; [|discriminate]. injection H as <-.
    apply (xle_sound E M kn) in Hle; [|exact Hkn].
    pose proof (S2G.input_byte SEGS E M (uD E buf) (uD E len) bs kn [(buf, 0); (x, k)] (EVar n) ltac:(lia) Hbl Hl Hin Hkn Hr) as IB.
    cbn [xt_den] in IB. replace (bv_unsigned (edenot E buf) + 0 + (bv_unsigned (edenot E x) + k + 0) - bv_unsigned (edenot E buf)) with (uD E x + k) in IB by lia.
    rewrite (IB ltac:(lia)). rewrite S2G.recval1. cbn [edenot]. change (2 ^ (8 * Z.of_nat 1)) with 256.
    exact (bset_forall E M kn n P Hkn HP).
  - destruct (find_zero kn kn [(buf, 0); (len, 0)]) as [m|] eqn:Hz; [|discriminate].
    destruct (xge kn x k len && xle kn x (k + 1 - m) len && xle kn x (k - 63) len)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply (xge_sound E M kn) in H1; [|exact Hkn]. apply (xle_sound E M kn) in H2; [|exact Hkn]. apply (xle_sound E M kn) in H3; [|exact Hkn].
    cbn [ball bvals forallb] in HP. rewrite andb_true_r in HP.
    destruct (find_zero_sound E M kn kn _ m Hkn Hkn Hz) as (Z1 & Z2 & ZZ). cbn [xt_den] in Z1, Z2.
    rewrite (input_zero E M (uD E buf) (uD E len) bs kn _ m (uD E x + k) ltac:(lia) Hbl Hl Hin Hkn Hz); [exact HP| cbn [xt_den]; lia | lia | lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transitions.
Variable M : mem.
Variables buf len a1 : Z.
Ltac rd := cbn -[S1M.is_space S1M.is_op S1M.is_space_or_op S1M.is_ascii_stop S1M.is_cont S1M.char_class Z.add Z.sub Z.mul Z.of_nat Z.to_nat].

(* [comment removed for export] *)
Definition prim_start (c : Z) : bool := negb (S1M.is_space c) && negb (S1M.is_op c) && negb (c =? S1M.QUOTE).
Definition prim_cont (c : Z) : bool := negb (S1M.is_space_or_op c) && negb (c =? S1M.RS).
(* [comment removed for export] *)
Definition code (n E : Z) (u : bool) : Z := if n =? 0 then S1M.EMPTY else if u then S1M.UNCLOSED_STRING else E.
Definition sentinels (n : Z) : Prop :=
  u32_at M (a1 + 4 * n) = Some len /\ u32_at M (a1 + 4 * n + 4) = Some len /\ u32_at M (a1 + 4 * n + 8) = Some 0.
(* [comment removed for export] *)
Definition finished (bs : list Z) (n rc : Z) : Prop :=
  exists out J E u, runs (nthb bs) len J out E u /\ len <= J /\ Z.of_nat (length out) = n /\ prefix_at M a1 out /\
    rc = code n E u.

Lemma runs_nonneg : forall bf J out E u, runs bf len J out E u -> 0 <= J.
Proof. intros bf J out E u [k Hk]. pose proof (iterk_idx bf len k _ _ Hk) as [A _]. cbn in A. lia. Qed.
Lemma prefix_snoc : forall out C x, Z.of_nat (length out) = C -> prefix_at M a1 out -> u32_at M (a1 + 4 * C) = Some x ->
  prefix_at M a1 (out ++ [x]).
Proof.
  intros out C x HC Hp Hx k Hk. rewrite length_app in Hk. cbn in Hk.
  destruct (Nat.lt_ge_cases k (length out)) as [Hl|Hg].
  - rewrite S1M.nth_app_last by lia. apply Hp. lia.
  - assert (k = length out) by lia. subst k. rewrite S1M.nth_app_new. rewrite <- Hx. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma W_iter : forall bf J0 out E u p, runs bf len J0 out E u -> J0 <= p -> J0 < len -> spaces bf J0 p -> p < len ->
  S1M.is_space (bf p) = false ->
  let s' := (if bf p =? S1M.QUOTE then let '(r, u') := S1M.vstring bf len p E in let '(i', e') := r in S1M.ST (i' + 1) (out ++ [p]) e' (u || u')
             else if S1M.is_op (bf p) then S1M.ST (p + 1) (out ++ [p]) E u
             else S1M.ST (S1M.primrun bf len (Z.to_nat (len - p)) p + 1) (out ++ [p]) E u) in
  runs bf len (S1M.s_idx s') (S1M.s_out s') (S1M.s_err s') (S1M.s_unclosed s').
Proof.
  intros bf J0 out E u p Hr HJ HJl Hsp Hp Hns.
  apply (runs_step bf len J0 out E u); [exact Hr | exact HJl |].
  unfold S1M.iter. rd. rewrite (wsrun_char bf len (Z.to_nat (p - J0)) J0 p ltac:(lia) HJ Hp Hsp Hns (Z.to_nat (len - J0)) ltac:(lia)).
  destruct (Z.leb_spec len p); [lia|].
  destruct (bf p =? S1M.QUOTE); [destruct (S1M.vstring bf len p E) as [[i' e'] u']; reflexivity|].
  destruct (S1M.is_op (bf p)); reflexivity.
Qed.
(* [comment removed for export] *)
Lemma W_end : forall bf J0 out E u p, runs bf len J0 out E u -> J0 <= p -> J0 < len -> spaces bf J0 (p + 1) -> p < len -> len <= p + 1 ->
  runs bf len (p + 1) out E u.
Proof.
  intros bf J0 out E u p Hr HJ HJl Hsp Hp Hp1.
  pose proof (runs_step bf len J0 out E u _ Hr HJl eq_refl) as R. unfold S1M.iter in R. revert R. rd.
  rewrite (wsrun_end bf len (Z.to_nat (len - 1 - J0)) J0 ltac:(lia) HJl ltac:(intros k Hk; apply Hsp; lia) (Z.to_nat (len - J0)) ltac:(lia)).
  destruct (Z.leb_spec len len); [|lia]. rd. replace (p + 1) with len by lia. intros R; exact R.
Qed.

(* [comment removed for export] *)
Lemma T_X : forall C n rc bs, wfctx buf len a1 C -> n <= len -> input M buf len = Some bs -> finished bs n rc ->
  (rc = 0 -> sentinels n /\ nthb bs len = 0) -> p_s1x [buf; len; a1; n; rc] M.
Proof.
  intros C n rc bs W Hn Hin (out & J & E & u & Hr & HJ & Hlen & Hp & Hrc) Hz. unfold wfctx in W.
  unfold p_s1x. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exists bs. split; [exact Hin|].
  assert (HR : S1M.result (nthb bs) len = (out, code n E u)).
  { unfold S1M.result. rewrite (runs_final (nthb bs) len J out E u ltac:(lia) Hr HJ). cbn [S1M.s_out S1M.s_unclosed S1M.s_err]. rewrite Hlen.
    unfold code. destruct (n =? 0); [reflexivity|]. destruct u; reflexivity. }
  rewrite HR. cbn [snd fst]. split; [symmetry; exact Hrc|]. intros Hs. rewrite Hs in Hrc. destruct (Hz Hs) as [(S1 & S2 & S3) Zl].
  assert (Hn1 : n <> 0 /\ u = false /\ E = 0).
  { unfold code in Hrc. destruct (Z.eqb_spec n 0); [discriminate|]. destruct u; [discriminate|]. unfold S1M.SUCCESS in Hrc. repeat split; lia. }
  destruct Hn1 as (N1 & -> & ->).
  unfold S2G.p_s1ok. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. exists bs. split; [exact Hin|]. rewrite HR. cbn [fst snd].
  split; [unfold code; destruct (Z.eqb_spec n 0); [lia|reflexivity]|]. split; [exact Hlen|]. split; [exact Zl|].
  split; [exact Hp|]. exact (conj S1 (conj S2 S3)).
Qed.

(* [comment removed for export] *)
Lemma T_AW : forall J C E F, p_s1a [buf; len; a1; J; C; E; F] M -> J < len -> p_s1w [buf; len; a1; J; C; E; F] M.
Proof.
  intros J C E F (W & HF & bs & out & Hin & Hr & Hl & Hp) HJ. split; [exact W|]. split; [exact HF|].
  exists bs, out, J. repeat (split; [assumption|]). split; [lia|]. split; [lia|]. intros k Hk. lia.
Qed.
(* [comment removed for export] *)
Lemma T_WW : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs -> S1M.is_space (nthb bs p) = true ->
  p_s1w [buf; len; a1; p + 1; C; E; F] M.
Proof.
  intros p C E F bs (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp) Hbs Hs. rewrite Hbs in Hin. injection Hin as <-.
  split; [exact W|]. split; [exact HF|]. exists bs, out, J0. repeat (split; [assumption|]). split; [lia|]. split; [lia|].
  intros k Hk. destruct (Z.eq_dec k p) as [->|]; [exact Hs|]. apply Hsp. lia.
Qed.
(* [comment removed for export] *)
Lemma T_WX_sp : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs -> S1M.is_space (nthb bs p) = true ->
  p < len -> len <= p + 1 -> finished bs C (code C E (zb F)).
Proof.
  intros p C E F bs (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp) Hbs Hs Hpl Hp1. rewrite Hbs in Hin. injection Hin as <-.
  exists out, (p + 1), E, (zb F). split; [|split; [lia|]; split; [exact Hl|]; split; [exact Hp|reflexivity]].
  apply (W_end _ J0); try assumption; try lia. intros k Hk. destruct (Z.eq_dec k p) as [->|]; [exact Hs|]. apply Hsp. lia.
Qed.
(* [comment removed for export] *)
Lemma T_WS : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs -> nthb bs p = S1M.QUOTE ->
  p < len -> C < len -> u32_at M (a1 + 4 * C) = Some p -> p_s1s [buf; len; a1; p + 1; C; E; F] M.
Proof.
  intros p C E F bs (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp) Hbs Hq Hpl HC Hrec. rewrite Hbs in Hin. injection Hin as <-.
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, E, p, (p + 1).
  repeat (split; [assumption|]). split; [apply VS0|]. split; [lia|]. intros k Hk. lia.
Qed.
(* [comment removed for export] *)
Lemma T_WP : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_start (nthb bs p) = true -> prim_cont (nthb bs (p + 1)) = true ->
  p + 1 < len -> C < len -> u32_at M (a1 + 4 * C) = Some p -> p_s1p [buf; len; a1; p; C; E; F] M.
Proof.
  intros p C E F bs (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp) Hbs Hst Hc Hpl HC Hrec. rewrite Hbs in Hin. injection Hin as <-.
  unfold prim_start in Hst. apply andb_prop in Hst as [Hst H3]. apply andb_prop in Hst as [H1 H2].
  unfold prim_cont in Hc. apply andb_prop in Hc as [H4 H5].
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, p.
  repeat (split; [assumption|]). split; [lia|]. split; [exact Hsp|]. split; [destruct (S1M.is_space (nthb bs p)); [discriminate|reflexivity]|].
  split; [destruct (S1M.is_op (nthb bs p)); [discriminate|reflexivity]|].
  split; [destruct (Z.eqb_spec (nthb bs p) S1M.QUOTE); [discriminate|assumption]|].
  split; [lia|]. split; [lia|]. intros k Hk. assert (k = p + 1) by lia. subst k.
  split; [destruct (S1M.is_space_or_op (nthb bs (p + 1))); [discriminate|reflexivity]|].
  destruct (Z.eqb_spec (nthb bs (p + 1)) S1M.RS); [discriminate|assumption].
Qed.
(* [comment removed for export] *)
Lemma T_WA : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  S1M.is_space (nthb bs p) = false -> nthb bs p <> S1M.QUOTE ->
  (S1M.is_op (nthb bs p) = true \/ len <= p + 1 \/ prim_cont (nthb bs (p + 1)) = false) ->
  p < len -> C < len -> u32_at M (a1 + 4 * C) = Some p -> p_s1a [buf; len; a1; p + 1; C + 1; E; F] M.
Proof.
  intros p C E F bs HW Hbs Hns Hnq Hstop Hpl HC Hrec.
  destruct HW as (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp). rewrite Hbs in Hin. injection Hin as <-.
  unfold wfctx in W. split; [unfold wfctx; lia|]. split; [exact HF|]. exists bs, (out ++ [p]). split; [exact Hbs|].
  split.
  - pose proof (W_iter (nthb bs) J0 out E (zb F) p Hr HJ HJl Hsp Hpl Hns) as R. cbv beta in R.
    destruct (Z.eqb_spec (nthb bs p) S1M.QUOTE); [contradiction|].
    destruct (S1M.is_op (nthb bs p)) eqn:Hop; [exact R|].
    rewrite (primrun_char (nthb bs) len O p p ltac:(cbn; lia) ltac:(lia)) in R; [exact R| intros k Hk; lia | | cbn; lia].
    destruct Hstop as [Hx|[Hx|Hx]]; [discriminate|left; exact Hx|right]. unfold prim_ok. unfold prim_cont in Hx. exact Hx.
  - split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C p Hl Hp Hrec).
Qed.
(* [comment removed for export] *)
Lemma T_WX_ns : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  S1M.is_space (nthb bs p) = false -> nthb bs p <> S1M.QUOTE ->
  p < len -> len <= p + 1 -> u32_at M (a1 + 4 * C) = Some p -> finished bs (C + 1) (code (C + 1) E (zb F)).
Proof.
  intros p C E F bs HW Hbs Hns Hnq Hpl Hp1 Hrec.
  destruct HW as (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp). rewrite Hbs in Hin. injection Hin as <-.
  exists (out ++ [p]), (p + 1), E, (zb F). split; [|split; [lia|]; split; [rewrite length_app; cbn; lia|]; split; [exact (prefix_snoc out C p Hl Hp Hrec)|reflexivity]].
  pose proof (W_iter (nthb bs) J0 out E (zb F) p Hr HJ HJl Hsp Hpl Hns) as R. cbv beta in R.
  destruct (Z.eqb_spec (nthb bs p) S1M.QUOTE); [contradiction|].
  destruct (S1M.is_op (nthb bs p)) eqn:Hop; [exact R|].
  rewrite (primrun_char (nthb bs) len O p p ltac:(cbn; lia) ltac:(lia)) in R; [exact R| intros k Hk; lia | left; lia | cbn; lia].
Qed.
(* [comment removed for export] *)
Lemma W_quote_last : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  nthb bs p = S1M.QUOTE -> p < len -> len <= p + 1 ->
  exists out, Z.of_nat (length out) = C /\ prefix_at M a1 out /\ runs (nthb bs) len (p + 2) (out ++ [p]) E true.
Proof.
  intros p C E F bs HW Hbs Hq Hpl Hp1.
  destruct HW as (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp). rewrite Hbs in Hin. injection Hin as <-. unfold wfctx in W.
  exists out. split; [exact Hl|]. split; [exact Hp|].
  pose proof (W_iter (nthb bs) J0 out E (zb F) p Hr HJ HJl Hsp Hpl ltac:(rewrite Hq; reflexivity)) as R. cbv beta in R.
  rewrite Hq in R. cbn [Z.eqb S1M.QUOTE Pos.eqb] in R.
  unfold S1M.vstring in R. replace (Z.to_nat (len + 2)) with (S (Z.to_nat (len + 1))) in R by lia. cbn [S1M.vstring_loop] in R.
  destruct (Z.ltb_spec (p + 1) len); [lia|]. replace (p + 1 + 1) with (p + 2) in R by lia. rewrite Bool.orb_true_r in R. exact R.
Qed.
Lemma T_WX_q : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  nthb bs p = S1M.QUOTE -> p < len -> len <= p + 1 -> u32_at M (a1 + 4 * C) = Some p -> finished bs (C + 1) S1M.UNCLOSED_STRING.
Proof.
  intros p C E F bs HW Hbs Hq Hpl Hp1 Hrec. pose proof HW as HW'. destruct HW' as (W & _). unfold wfctx in W.
  destruct (W_quote_last p C E F bs HW Hbs Hq Hpl Hp1) as (out & Hl & Hp & R).
  exists (out ++ [p]), (p + 2), E, true.
  split; [exact R|]. split; [lia|]. split; [rewrite length_app; cbn; lia|]. split; [exact (prefix_snoc out C p Hl Hp Hrec)|].
  unfold code. destruct (Z.eqb_spec (C + 1) 0); [lia|reflexivity].
Qed.
Lemma T_WAq : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  nthb bs p = S1M.QUOTE -> p < len -> len <= p + 1 -> C < len -> u32_at M (a1 + 4 * C) = Some p ->
  p_s1a [buf; len; a1; p + 2; C + 1; E; 1] M.
Proof.
  intros p C E F bs HW Hbs Hq Hpl Hp1 HC Hrec. pose proof HW as HW'. destruct HW' as (W & _). unfold wfctx in W.
  destruct (W_quote_last p C E F bs HW Hbs Hq Hpl Hp1) as (out & Hl & Hp & R).
  split; [unfold wfctx; lia|]. split; [lia|]. exists bs, (out ++ [p]). split; [exact Hbs|]. split; [exact R|].
  split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C p Hl Hp Hrec).
Qed.

(* [comment removed for export] *)
Definition sstep_sem (bf : Z -> Z) (p Ec d Ec' : Z) : Prop :=
  S1M.is_ascii_stop (bf p) = true /\
  ((bf p = S1M.BACKSLASH /\ d = 2 /\ Ec' = Ec) \/
   (bf p <> S1M.QUOTE /\ bf p <> S1M.BACKSLASH /\ Z.land (bf p) 128 = 0 /\ d = 1 /\ Ec' = (if bf p <? 32 then S1M.UNESCAPED_CHARS else Ec)) \/
   (bf p <> S1M.QUOTE /\ bf p <> S1M.BACKSLASH /\ Z.land (bf p) 128 <> 0 /\ S1M.vutf8 bf len p Ec = (p + d, Ec'))).
Lemma sstep_d : forall bf p Ec d Ec', sstep_sem bf p Ec d Ec' -> 1 <= d <= 4.
Proof.
  intros bf p Ec d Ec' [_ [(_ & -> & _)|[(_ & _ & _ & -> & _)|(_ & _ & _ & Hv)]]]; try lia.
  unfold S1M.vutf8 in Hv.
  repeat match type of Hv with (if ?c then _ else _) = _ => destruct c end; injection Hv as Hd _; lia.
Qed.
Lemma sstep_vsreach : forall bf q E0 cur0 Ec p d Ec', vsreach bf len q E0 cur0 Ec -> cur0 <= p -> p < len ->
  nostop bf cur0 p -> sstep_sem bf p Ec d Ec' -> vsreach bf len q E0 (p + d) Ec'.
Proof.
  intros bf q E0 cur0 Ec p d Ec' Hv Hcur Hpl Hns Hst. pose proof (vsreach_bound _ _ _ _ _ _ Hv) as HB.
  destruct Hst as [Hstop [(Hb & -> & ->)|[(Hnq & Hnb & Hlo & -> & ->)|(Hnq & Hnb & Hhi & Hu8)]]].
  - apply (VSbs _ _ _ _ cur0 Ec p); try assumption; lia.
  - apply (VSch _ _ _ _ cur0 Ec p); try assumption; lia.
  - apply (VSu8 _ _ _ _ cur0 Ec p); try assumption; lia.
Qed.
Lemma T_SS : forall p C Ec F bs d Ec', p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  p < len -> sstep_sem (nthb bs) p Ec d Ec' -> p_s1s [buf; len; a1; p + d; C; Ec'; F] M.
Proof.
  intros p C Ec F bs d Ec' HS Hbs Hpl Hst.
  destruct HS as (W & HF & HC & bs' & out & J0 & E0 & q & cur0 & Hin & Hr & Hl & Hp & Hq & HJq & Hql & Hsp & H34 & Hv & Hcur & Hns).
  rewrite Hbs in Hin. injection Hin as <-. pose proof (sstep_d _ _ _ _ _ Hst) as Hd.
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, E0, q, (p + d).
  repeat (split; [assumption|]). split; [|split; [lia| intros k Hk; lia]].
  exact (sstep_vsreach _ _ _ _ _ _ _ _ Hv Hcur Hpl Hns Hst).
Qed.
(* [comment removed for export] *)
Lemma S_step_end : forall p C Ec F bs d Ec', p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  p < len -> sstep_sem (nthb bs) p Ec d Ec' -> len <= p + d ->
  exists out q, Z.of_nat (length out) = C /\ prefix_at M a1 out /\ u32_at M (a1 + 4 * C) = Some q /\
    runs (nthb bs) len (p + d + 1) (out ++ [q]) Ec' true.
Proof.
  intros p C Ec F bs d Ec' HS Hbs Hpl Hst Hpd.
  destruct HS as (W & HF & HC & bs' & out & J0 & E0 & q & cur0 & Hin & Hr & Hl & Hp & Hq & HJq & Hql & Hsp & H34 & Hv & Hcur & Hns).
  rewrite Hbs in Hin. injection Hin as <-. pose proof (sstep_d _ _ _ _ _ Hst) as Hd. unfold wfctx in W.
  pose proof (sstep_vsreach _ _ _ _ _ _ _ _ Hv Hcur Hpl Hns Hst) as Hv'.
  exists out, q. split; [exact Hl|]. split; [exact Hp|]. split; [exact Hq|].
  pose proof (W_iter (nthb bs) J0 out E0 (zb F) q Hr HJq ltac:(lia) Hsp Hql ltac:(rewrite H34; reflexivity)) as R. cbv beta in R.
  rewrite H34 in R. cbn [Z.eqb S1M.QUOTE Pos.eqb] in R.
  pose proof (vsreach_bound _ _ _ _ _ _ Hv) as HB. pose proof (runs_nonneg _ _ _ _ _ Hr) as HJ0.
  rewrite (vstring_unclosed_at (nthb bs) len q E0 (p + d) Ec' ltac:(lia) ltac:(lia) Hv' ltac:(lia) ltac:(lia)) in R.
  rewrite Bool.orb_true_r in R. exact R.
Qed.
Lemma T_SX_step : forall p C Ec F bs d Ec', p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  p < len -> sstep_sem (nthb bs) p Ec d Ec' -> len <= p + d -> finished bs (C + 1) S1M.UNCLOSED_STRING.
Proof.
  intros p C Ec F bs d Ec' HS Hbs Hpl Hst Hpd. pose proof HS as HS'. destruct HS' as (W & _). unfold wfctx in W.
  destruct (S_step_end p C Ec F bs d Ec' HS Hbs Hpl Hst Hpd) as (out & q & Hl & Hp & Hq & R). pose proof (sstep_d _ _ _ _ _ Hst).
  exists (out ++ [q]), (p + d + 1), Ec', true. split; [exact R|]. split; [lia|]. split; [rewrite length_app; cbn; lia|].
  split; [exact (prefix_snoc out C q Hl Hp Hq)|]. unfold code. destruct (Z.eqb_spec (C + 1) 0); [lia|reflexivity].
Qed.
Lemma T_SAu_step : forall p C Ec F bs d Ec', p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  p < len -> sstep_sem (nthb bs) p Ec d Ec' -> len <= p + d -> p_s1a [buf; len; a1; p + d + 1; C + 1; Ec'; 1] M.
Proof.
  intros p C Ec F bs d Ec' HS Hbs Hpl Hst Hpd. pose proof HS as HS'. destruct HS' as (W & HF & HC & _). unfold wfctx in W.
  destruct (S_step_end p C Ec F bs d Ec' HS Hbs Hpl Hst Hpd) as (out & q & Hl & Hp & Hq & R).
  split; [unfold wfctx; lia|]. split; [lia|]. exists bs, (out ++ [q]). split; [exact Hbs|]. split; [exact R|].
  split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C q Hl Hp Hq).
Qed.
(* [comment removed for export] *)
Lemma T_Srun : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  S1M.is_ascii_stop (nthb bs p) = false -> p_s1s [buf; len; a1; p + 1; C; Ec; F] M.
Proof.
  intros p C Ec F bs HS Hbs Hst.
  destruct HS as (W & HF & HC & bs' & out & J0 & E0 & q & cur0 & Hin & Hr & Hl & Hp & Hq & HJq & Hql & Hsp & H34 & Hv & Hcur & Hns).
  rewrite Hbs in Hin. injection Hin as <-.
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, E0, q, cur0.
  repeat (split; [assumption|]). split; [lia|]. intros k Hk. destruct (Z.eq_dec k p) as [->|]; [exact Hst|]. apply Hns. lia.
Qed.
(* [comment removed for export] *)
Lemma S_run_end : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  S1M.is_ascii_stop (nthb bs p) = false -> p < len -> len <= p + 1 ->
  exists out q, Z.of_nat (length out) = C /\ prefix_at M a1 out /\ u32_at M (a1 + 4 * C) = Some q /\
    runs (nthb bs) len (len + 1) (out ++ [q]) Ec true.
Proof.
  intros p C Ec F bs HS Hbs Hst Hpl Hp1.
  pose proof (T_Srun p C Ec F bs HS Hbs Hst) as HS'.
  destruct HS' as (W & HF & HC & bs' & out & J0 & E0 & q & cur0 & Hin & Hr & Hl & Hp & Hq & HJq & Hql & Hsp & H34 & Hv & Hcur & Hns).
  rewrite Hbs in Hin. injection Hin as <-. unfold wfctx in W.
  exists out, q. split; [exact Hl|]. split; [exact Hp|]. split; [exact Hq|].
  pose proof (W_iter (nthb bs) J0 out E0 (zb F) q Hr HJq ltac:(lia) Hsp Hql ltac:(rewrite H34; reflexivity)) as R. cbv beta in R.
  rewrite H34 in R. cbn [Z.eqb S1M.QUOTE Pos.eqb] in R.
  pose proof (vsreach_bound _ _ _ _ _ _ Hv) as HB. pose proof (runs_nonneg _ _ _ _ _ Hr) as HJ0.
  destruct (Z.lt_ge_cases cur0 len) as [Hcl|Hcg].
  - rewrite (vstring_unclosed_run (nthb bs) len q E0 cur0 Ec ltac:(lia) Hv Hcl ltac:(intros k Hk; apply Hns; lia)) in R.
    rewrite Bool.orb_true_r in R. exact R.
  - rewrite (vstring_unclosed_at (nthb bs) len q E0 cur0 Ec ltac:(lia) ltac:(lia) Hv Hcg ltac:(lia)) in R.
    rewrite Bool.orb_true_r in R. replace (len + 1) with (cur0 + 1) by lia. exact R.
Qed.
Lemma T_SX_run : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  S1M.is_ascii_stop (nthb bs p) = false -> p < len -> len <= p + 1 -> finished bs (C + 1) S1M.UNCLOSED_STRING.
Proof.
  intros p C Ec F bs HS Hbs Hst Hpl Hp1. pose proof HS as HS'. destruct HS' as (W & _). unfold wfctx in W.
  destruct (S_run_end p C Ec F bs HS Hbs Hst Hpl Hp1) as (out & q & Hl & Hp & Hq & R).
  exists (out ++ [q]), (len + 1), Ec, true. split; [exact R|]. split; [lia|]. split; [rewrite length_app; cbn; lia|].
  split; [exact (prefix_snoc out C q Hl Hp Hq)|]. unfold code. destruct (Z.eqb_spec (C + 1) 0); [lia|reflexivity].
Qed.
Lemma T_SAu_run : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  S1M.is_ascii_stop (nthb bs p) = false -> p < len -> len <= p + 1 -> p_s1a [buf; len; a1; p + 2; C + 1; Ec; 1] M.
Proof.
  intros p C Ec F bs HS Hbs Hst Hpl Hp1. pose proof HS as HS'. destruct HS' as (W & HF & HC & _). unfold wfctx in W.
  destruct (S_run_end p C Ec F bs HS Hbs Hst Hpl Hp1) as (out & q & Hl & Hp & Hq & R).
  split; [unfold wfctx; lia|]. split; [lia|]. exists bs, (out ++ [q]). split; [exact Hbs|]. replace (p + 2) with (len + 1) by lia.
  split; [exact R|]. split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C q Hl Hp Hq).
Qed.
(* [comment removed for export] *)
Lemma T_SA : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  nthb bs p = S1M.QUOTE -> p < len -> p_s1a [buf; len; a1; p + 1; C + 1; Ec; F] M.
Proof.
  intros p C Ec F bs HS Hbs H34p Hpl.
  destruct HS as (W & HF & HC & bs' & out & J0 & E0 & q & cur0 & Hin & Hr & Hl & Hp & Hq & HJq & Hql & Hsp & H34 & Hv & Hcur & Hns).
  rewrite Hbs in Hin. injection Hin as <-. unfold wfctx in W.
  split; [unfold wfctx; lia|]. split; [exact HF|]. exists bs, (out ++ [q]). split; [exact Hbs|].
  split; [|split; [rewrite length_app; cbn; lia| exact (prefix_snoc out C q Hl Hp Hq)]].
  pose proof (W_iter (nthb bs) J0 out E0 (zb F) q Hr HJq ltac:(lia) Hsp Hql ltac:(rewrite H34; reflexivity)) as R. cbv beta in R.
  rewrite H34 in R. cbn [Z.eqb S1M.QUOTE Pos.eqb] in R.
  pose proof (vsreach_bound _ _ _ _ _ _ Hv) as HB. pose proof (runs_nonneg _ _ _ _ _ Hr) as HJ0.
  rewrite (vstring_closed (nthb bs) len q E0 cur0 Ec p ltac:(lia) Hv ltac:(lia) ltac:(lia) Hns ltac:(rewrite H34p; reflexivity) H34p ltac:(lia)) in R.
  rewrite Bool.orb_false_r in R. exact R.
Qed.
(* [comment removed for export] *)
Lemma T_SX_q : forall p C Ec F bs, p_s1s [buf; len; a1; p; C; Ec; F] M -> input M buf len = Some bs ->
  nthb bs p = S1M.QUOTE -> p < len -> len <= p + 1 -> finished bs (C + 1) (code (C + 1) Ec (zb F)).
Proof.
  intros p C Ec F bs HS Hbs H34p Hpl Hp1.
  destruct (T_SA p C Ec F bs HS Hbs H34p Hpl) as (W & HF & bs' & out' & Hin & Hr & Hl & Hp).
  rewrite Hbs in Hin. injection Hin as <-.
  exists out', (p + 1), Ec, (zb F). repeat (split; [assumption || lia|]). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma T_PP : forall p C E F bs, p_s1p [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_cont (nthb bs (p + 2)) = true -> p + 2 < len -> p_s1p [buf; len; a1; p + 1; C; E; F] M.
Proof.
  intros p C E F bs HP Hbs Hc Hp2.
  destruct HP as (W & HF & HC & bs' & out & J0 & i0 & Hin & Hr & Hl & Hp & Hi0 & HJ & Hil & Hsp & Hs1 & Hs2 & Hs3 & Hip & Hp1 & Hall).
  rewrite Hbs in Hin. injection Hin as <-. unfold prim_cont in Hc. apply andb_prop in Hc as [H4 H5].
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, i0. repeat (split; [assumption|]).
  split; [lia|]. split; [lia|]. intros k Hk. destruct (Z.eq_dec k (p + 2)) as [->|]; [|apply Hall; lia].
  split; [destruct (S1M.is_space_or_op (nthb bs (p + 2))); [discriminate|reflexivity]|].
  destruct (Z.eqb_spec (nthb bs (p + 2)) S1M.RS); [discriminate|assumption].
Qed.
Lemma P_iter : forall p C E F bs, p_s1p [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  (len <= p + 2 \/ prim_cont (nthb bs (p + 2)) = false) ->
  exists out i0, Z.of_nat (length out) = C /\ prefix_at M a1 out /\ u32_at M (a1 + 4 * C) = Some i0 /\
    runs (nthb bs) len (p + 2) (out ++ [i0]) E (zb F).
Proof.
  intros p C E F bs HP Hbs Hstop.
  destruct HP as (W & HF & HC & bs' & out & J0 & i0 & Hin & Hr & Hl & Hp & Hi0 & HJ & Hil & Hsp & Hs1 & Hs2 & Hs3 & Hip & Hp1 & Hall).
  rewrite Hbs in Hin. injection Hin as <-. exists out, i0. split; [exact Hl|]. split; [exact Hp|]. split; [exact Hi0|].
  pose proof (W_iter (nthb bs) J0 out E (zb F) i0 Hr HJ ltac:(lia) Hsp Hil Hs1) as R. cbv beta in R.
  destruct (Z.eqb_spec (nthb bs i0) S1M.QUOTE); [contradiction|]. rewrite Hs2 in R.
  rewrite (primrun_char (nthb bs) len (Z.to_nat (p + 1 - i0)) i0 (p + 1) ltac:(lia) ltac:(lia)) in R.
  - replace (p + 1 + 1) with (p + 2) in R by lia. exact R.
  - intros k Hk. destruct (Hall k Hk) as [A B]. split; [lia|]. unfold prim_ok. rewrite A. destruct (Z.eqb_spec (nthb bs k) S1M.RS); [contradiction|reflexivity].
  - replace (p + 1 + 1) with (p + 2) by lia. destruct Hstop as [Hx|Hx]; [left; exact Hx|right]. unfold prim_ok. unfold prim_cont in Hx. exact Hx.
  - lia.
Qed.
Lemma T_PA : forall p C E F bs, p_s1p [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  (len <= p + 2 \/ prim_cont (nthb bs (p + 2)) = false) -> p_s1a [buf; len; a1; p + 2; C + 1; E; F] M.
Proof.
  intros p C E F bs HP Hbs Hstop. destruct (P_iter p C E F bs HP Hbs Hstop) as (out & i0 & Hl & Hp & Hi0 & R).
  destruct HP as (W & HF & HC & _). unfold wfctx in W.
  split; [unfold wfctx; lia|]. split; [exact HF|]. exists bs, (out ++ [i0]). split; [exact Hbs|]. split; [exact R|].
  split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C i0 Hl Hp Hi0).
Qed.
Lemma T_PX : forall p C E F bs, p_s1p [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  len <= p + 2 -> finished bs (C + 1) (code (C + 1) E (zb F)).
Proof.
  intros p C E F bs HP Hbs Hp2. destruct (P_iter p C E F bs HP Hbs (or_introl Hp2)) as (out & i0 & Hl & Hp & Hi0 & R).
  exists (out ++ [i0]), (p + 2), E, (zb F). split; [exact R|]. split; [lia|]. split; [rewrite length_app; cbn; lia|].
  split; [exact (prefix_snoc out C i0 Hl Hp Hi0)|reflexivity].
Qed.
(* [comment removed for export] *)
Lemma T_init : 0 <= len -> buf + len + 64 < two64 -> 0 <= a1 -> a1 + 4 * len + 48 < two64 ->
  (exists bs, input M buf len = Some bs) -> p_s1a [buf; len; a1; 0; 0; 0; 0] M.
Proof.
  intros Hl Hb Ha Hal [bs Hin]. split; [unfold wfctx; lia|]. split; [lia|]. exists bs, []. split; [exact Hin|].
  split; [apply runs_init|]. split; [reflexivity|]. intros k Hk. cbn in Hk. lia.
Qed.

(* [comment removed for export] *)
Lemma T_initW : 0 < len -> buf + len + 64 < two64 -> 0 <= a1 -> a1 + 4 * len + 48 < two64 ->
  (exists bs, input M buf len = Some bs) -> p_s1w [buf; len; a1; 0; 0; 0; 0] M.
Proof. intros Hl Hb Ha Hal Hbs. apply T_AW; [apply T_init; try assumption; lia | exact Hl]. Qed.
Lemma T_AX : forall J C E F bs, p_s1a [buf; len; a1; J; C; E; F] M -> input M buf len = Some bs -> len <= J ->
  finished bs C (code C E (zb F)).
Proof.
  intros J C E F bs (W & HF & bs' & out & Hin & Hr & Hl & Hp) Hbs HJ. rewrite Hbs in Hin. injection Hin as <-.
  exists out, J, E, (zb F). repeat (split; [assumption|]). reflexivity.
Qed.
Lemma T_WP0 : forall p C E F bs, p_s1w [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_start (nthb bs p) = true -> p + 1 < len -> C < len -> u32_at M (a1 + 4 * C) = Some p -> p_s1p0 [buf; len; a1; p; C; E; F] M.
Proof.
  intros p C E F bs (W & HF & bs' & out & J0 & Hin & Hr & Hl & Hp & HJ & HJl & Hsp) Hbs Hst Hpl HC Hrec. rewrite Hbs in Hin. injection Hin as <-.
  unfold prim_start in Hst. apply andb_prop in Hst as [Hst H3]. apply andb_prop in Hst as [H1 H2].
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, p.
  repeat (split; [assumption|]). split; [lia|]. split; [exact Hsp|]. split; [destruct (S1M.is_space (nthb bs p)); [discriminate|reflexivity]|].
  split; [destruct (S1M.is_op (nthb bs p)); [discriminate|reflexivity]|].
  split; [destruct (Z.eqb_spec (nthb bs p) S1M.QUOTE); [discriminate|assumption]|].
  split; [lia|]. split; [lia|]. intros k Hk. lia.
Qed.
Lemma T_P0P0 : forall p C E F bs, p_s1p0 [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_cont (nthb bs (p + 1)) = true -> p + 2 < len -> p_s1p0 [buf; len; a1; p + 1; C; E; F] M.
Proof.
  intros p C E F bs HP Hbs Hc Hp2.
  destruct HP as (W & HF & HC & bs' & out & J0 & i0 & Hin & Hr & Hl & Hp & Hi0 & HJ & Hil & Hsp & Hs1 & Hs2 & Hs3 & Hip & Hp1 & Hall).
  rewrite Hbs in Hin. injection Hin as <-. unfold prim_cont in Hc. apply andb_prop in Hc as [H4 H5].
  split; [exact W|]. split; [exact HF|]. split; [exact HC|]. exists bs, out, J0, i0. repeat (split; [assumption|]).
  split; [lia|]. split; [lia|]. intros k Hk. destruct (Z.eq_dec k (p + 1)) as [->|]; [|apply Hall; lia].
  split; [destruct (S1M.is_space_or_op (nthb bs (p + 1))); [discriminate|reflexivity]|].
  destruct (Z.eqb_spec (nthb bs (p + 1)) S1M.RS); [discriminate|assumption].
Qed.
(* [comment removed for export] *)
Lemma P0_iter : forall p C E F bs (e : Z), p_s1p0 [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  (e = 0 /\ prim_cont (nthb bs (p + 1)) = false) \/ (e = 1 /\ prim_cont (nthb bs (p + 1)) = true /\ len <= p + 2) ->
  exists out i0, Z.of_nat (length out) = C /\ prefix_at M a1 out /\ u32_at M (a1 + 4 * C) = Some i0 /\
    runs (nthb bs) len (p + 1 + e) (out ++ [i0]) E (zb F).
Proof.
  intros p C E F bs e HP Hbs Hstop.
  destruct HP as (W & HF & HC & bs' & out & J0 & i0 & Hin & Hr & Hl & Hp & Hi0 & HJ & Hil & Hsp & Hs1 & Hs2 & Hs3 & Hip & Hp1 & Hall).
  rewrite Hbs in Hin. injection Hin as <-. exists out, i0. split; [exact Hl|]. split; [exact Hp|]. split; [exact Hi0|].
  pose proof (W_iter (nthb bs) J0 out E (zb F) i0 Hr HJ ltac:(lia) Hsp Hil Hs1) as R. cbv beta in R.
  destruct (Z.eqb_spec (nthb bs i0) S1M.QUOTE); [contradiction|]. rewrite Hs2 in R.
  rewrite (primrun_char (nthb bs) len (Z.to_nat (p + e - i0)) i0 (p + e) ltac:(lia) ltac:(lia)) in R.
  - replace (p + e + 1) with (p + 1 + e) in R by lia. exact R.
  - intros k Hk. destruct (Z.eq_dec k (p + 1)) as [->|].
    + destruct Hstop as [[He Hx]|[He [Hx Hl2]]]; [lia|]. unfold prim_cont in Hx. apply andb_prop in Hx as [H4 H5]. split; [lia|]. unfold prim_ok.
      rewrite H4. destruct (Z.eqb_spec (nthb bs (p + 1)) S1M.RS); [discriminate|reflexivity].
    + destruct (Hall k ltac:(lia)) as [A B]. split; [lia|]. unfold prim_ok. rewrite A. destruct (Z.eqb_spec (nthb bs k) S1M.RS); [contradiction|reflexivity].
  - destruct Hstop as [[-> Hx]|[-> [Hx Hl2]]]; [right|left; lia]. replace (p + 0 + 1) with (p + 1) by lia. unfold prim_ok. unfold prim_cont in Hx. exact Hx.
  - lia.
Qed.
Lemma T_P0A_stop : forall p C E F bs, p_s1p0 [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_cont (nthb bs (p + 1)) = false -> p_s1a [buf; len; a1; p + 1; C + 1; E; F] M.
Proof.
  intros p C E F bs HP Hbs Hx. destruct (P0_iter p C E F bs 0 HP Hbs (or_introl (conj eq_refl Hx))) as (out & i0 & Hl & Hp & Hi0 & R).
  destruct HP as (W & HF & HC & _). unfold wfctx in W. rewrite Z.add_0_r in R.
  split; [unfold wfctx; lia|]. split; [exact HF|]. exists bs, (out ++ [i0]). split; [exact Hbs|]. split; [exact R|].
  split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C i0 Hl Hp Hi0).
Qed.
Lemma T_P0A_end : forall p C E F bs, p_s1p0 [buf; len; a1; p; C; E; F] M -> input M buf len = Some bs ->
  prim_cont (nthb bs (p + 1)) = true -> len <= p + 2 -> p_s1a [buf; len; a1; p + 2; C + 1; E; F] M.
Proof.
  intros p C E F bs HP Hbs Hx Hl2. destruct (P0_iter p C E F bs 1 HP Hbs (or_intror (conj eq_refl (conj Hx Hl2)))) as (out & i0 & Hl & Hp & Hi0 & R).
  destruct HP as (W & HF & HC & _). unfold wfctx in W. replace (p + 1 + 1) with (p + 2) in R by lia.
  split; [unfold wfctx; lia|]. split; [exact HF|]. exists bs, (out ++ [i0]). split; [exact Hbs|]. split; [exact R|].
  split; [rewrite length_app; cbn; lia|]. exact (prefix_snoc out C i0 Hl Hp Hi0).
Qed.
End Transitions.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive u8path : Type :=
| U8bad                          (* [comment removed for export] *)
| U8short (n : nat) (k : nat)    (* [comment removed for export] *)
| U8ok (n : nat).                (* [comment removed for export] *)
Inductive sstep : Type := SBs | SCh | SU8 (u : u8path).   (* [comment removed for export] *)
Inductive rule : Type :=
| RNone | RHyp (i : nat) | RContra (v : nat) | RInit
| RAW (i : nat) | RWW (i : nat) | RWS (i : nat) | RWP (i : nat) | RWA (i : nat) | RWX (i : nat)
| RSrun (i : nat) | RSstep (i : nat) (st : sstep) | RSA (i : nat) | RSXq (i : nat) | RSXrun (i : nat) | RSXstep (i : nat) (st : sstep)
| RPP (i : nat) | RPA (i : nat) | RPX (i : nat)
  (* [comment removed for export] *)
| RInitW | RWP0 (i : nat) | RP0P0 (i : nat) | RP0A (i : nat) | RAX (i : nat)
| RSAurun (i : nat) | RSAustep (i : nat) (st : sstep) | RWAq (i : nat)
| RSW (i : nat) | RP0W (i : nat) | RP0X (i : nat) | RWAW (i : nat)   (* [comment removed for export] *)
  (* [comment removed for export] *)
| RXok (i : nat)                 (* [comment removed for export] *)
| RXF (i : nat).                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition c_sp (c : Z) : bool := S1M.is_space c.
Definition c_q (c : Z) : bool := c =? S1M.QUOTE.
Definition c_nspq (c : Z) : bool := negb (S1M.is_space c) && negb (c =? S1M.QUOTE).
Definition c_op (c : Z) : bool := S1M.is_op c.
Definition c_nstop (c : Z) : bool := negb (S1M.is_ascii_stop c).
Definition c_bs (c : Z) : bool := S1M.is_ascii_stop c && (c =? S1M.BACKSLASH).
Definition c_ch (c : Z) : bool := S1M.is_ascii_stop c && negb (c =? S1M.QUOTE) && negb (c =? S1M.BACKSLASH) && (Z.land c 128 =? 0).
Definition c_hi (c : Z) : bool := S1M.is_ascii_stop c && negb (c =? S1M.QUOTE) && negb (c =? S1M.BACKSLASH) && negb (Z.land c 128 =? 0).
Definition c_badlead (c : Z) : bool := c_hi c && (Z.land c 64 =? 0).
Definition c_lead (n : nat) (c : Z) : bool :=
  c_hi c && negb (Z.land c 64 =? 0) &&
  match n with
  | 2%nat => Z.land c 32 =? 0
  | 3%nat => negb (Z.land c 32 =? 0) && (Z.land c 16 =? 0)
  | 4%nat => negb (Z.land c 32 =? 0) && negb (Z.land c 16 =? 0)
  | _ => false
  end.
Definition u8cond (n : nat) (c b1 : Z) : bool :=
  match n with
  | 2%nat => c <=? 193
  | 3%nat => ((c =? 224) && (b1 <=? 159)) || ((c =? 237) && (160 <=? b1))
  | _ => ((c =? 240) && (b1 <=? 143)) || ((c =? 244) && (144 <=? b1)) || (245 <=? c)
  end.
Definition c_ncont (c : Z) : bool := negb (S1M.is_cont c).
Definition c_pcont (c : Z) : bool := prim_cont c.
Definition c_npcont (c : Z) : bool := negb (prim_cont c).

Definition hyp_at (c : vc) (i : nat) (id : nat) : option (list expr) :=
  match nth_error (vc_hyps c) i with
  | Some (GA id' args) => if Nat.eqb id' id then Some args else None
  | None => None
  end.
Definition concl_at (c : vc) (id : nat) : option (list expr) :=
  match vc_concl c with
  | VCAtom (GA id' args) => if Nat.eqb id' id then Some args else None
  | _ => None
  end.
Definition ctx3 (hb hl ha gb gl ga : expr) : bool := expr_eqb gb hb && expr_eqb gl hl && expr_eqb ga ha.
Definition lt32 (kn : list kentry) (len : expr) : bool := Z.ltb (S2G.hiZ kn len) (2 ^ 32).
(* [comment removed for export] *)
Definition idx_is (kn : list kentry) (a1 C : expr) (o : Z) (x : expr) : bool :=
  match find_rec kn kn ((a1, o) :: S2G.xN 4 C) 4 with
  | Some v => expr_eqb v x || xeq kn (recval 4 v) 0 x
  | None => false
  end.
Definition sent_ok (kn : list kentry) (a1 len n : expr) : bool :=
  idx_is kn a1 n 0 len && idx_is kn a1 n 4 len && idx_is kn a1 n 8 (ELit 0) && lt32 kn len.
(* [comment removed for export] *)
Definition rc_ok (kn : list kentry) (n E F rc : expr) (forced : bool) : bool :=
  if forced then expr_eqb rc (ELit 15)
  else (expr_eqb rc (ELit 13) && xeq kn n 0 (ELit 0))
       || (xge kn n (-1) (ELit 0) && ((expr_eqb rc (ELit 15) && xeq kn F 0 (ELit 1)) || (expr_eqb rc E && xeq kn F 0 (ELit 0)))).
Definition rc_maybe0 (rc : expr) : bool := match rc with ELit z => Z.eqb (z mod two64) 0 | _ => true end.
(* [comment removed for export] *)
Definition exit_ok (kn : list kentry) (buf len a1 n rc : expr) : bool :=
  if rc_maybe0 rc then
    sent_ok kn a1 len n && match find_zero kn kn [(buf, 0); (len, 0)] with Some m => Z.leb 1 m | None => false end
  else true.

(* [comment removed for export] *)
Definition sstep_check (kn : list kentry) (buf len x hE gE : expr) (chkE : bool) (st : sstep) : option Z :=
  match byte_info kn buf len x 0 with
  | None => None
  | Some b0 =>
    match st with
    | SBs => if ball c_bs kn b0 && (negb chkE || expr_eqb gE hE) then Some 2 else None
    | SCh => if ball c_ch kn b0 && (negb chkE || forallb (fun c => if c <? 32 then expr_eqb gE (ELit 14) else expr_eqb gE hE) (bvals kn b0))
             then Some 1 else None
    | SU8 U8bad => if ball c_badlead kn b0 && (negb chkE || expr_eqb gE (ELit 11)) then Some 1 else None
    | SU8 (U8short n k) =>
        if negb (ball (c_lead n) kn b0 && (negb chkE || expr_eqb gE (ELit 11))) then None
        else if Nat.eqb k 0 then (if xge kn x (Z.of_nat n - 2) len then Some 1 else None)
        else if Nat.ltb k n then
          match byte_info kn buf len x (Z.of_nat k) with
          | Some bk => if ball c_ncont kn bk then Some 1 else None
          | None => None
          end
        else None
    | SU8 (U8ok n) =>
        if negb (ball (c_lead n) kn b0 && xle kn x (Z.of_nat n - 1) len) then None else
        if negb (forallb (fun k => match byte_info kn buf len x (Z.of_nat k) with
                                   | Some bk => ball S1M.is_cont kn bk | None => false end) (seq 1 (n - 1))) then None else
        if negb chkE then Some (Z.of_nat n) else
        match byte_info kn buf len x 1 with
        | Some b1 => if forallb (fun c => forallb (fun d1 => if u8cond n c d1 then expr_eqb gE (ELit 11) else expr_eqb gE hE) (bvals kn b1)) (bvals kn b0)
                     then Some (Z.of_nat n) else None
        | None => None
        end
    end
  end.

(* [comment removed for export] *)
Definition is0 (e : expr) : bool := match e with ELit z => Z.eqb z 0 | _ => false end.
Definition check_init (kn : list kentry) (g : list expr) : bool :=
  match g with
  | [gb; gl; ga; gx; gC; gE; gF] =>
      is0 gx && is0 gC && is0 gE && is0 gF &&
      find_unk kn kn gb gl && match find_zero kn kn [(gb, 0); (gl, 0)] with Some m => Z.leb 64 m | None => false end
      && Z.ltb (S2G.hiZ kn gb + S2G.hiZ kn gl + 64) two64 && Z.ltb (S2G.hiZ kn ga + 4 * S2G.hiZ kn gl + 48) two64
  | _ => false
  end.
Definition check_AW (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 0 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF && xle kn hx 1 hl
  | _, _ => false
  end.
Definition check_WW (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_sp kn b0 | None => false end
  | _, _ => false
  end.
Definition check_WS (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF &&
      xle kn hx 1 hl && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_q kn b0 | None => false end
  | _, _ => false
  end.
Definition check_WP (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 0 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF &&
      xle kn hx 2 hl && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0, byte_info kn hb hl hx 1 with
      | Some b0, Some b1 => ball prim_start kn b0 && ball c_pcont kn b1
      | _, _ => false
      end
  | _, _ => false
  end.
Definition check_WA (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 1 gC && expr_eqb gE hE && expr_eqb gF hF &&
      xle kn hx 1 hl && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0 with
      | Some b0 => ball c_op kn b0
                   || (ball prim_start kn b0 &&
                       (xge kn hx 1 hl || match byte_info kn hb hl hx 1 with Some b1 => ball c_npcont kn b1 | None => false end))
      | None => false
      end
  | _, _ => false
  end.
Definition check_WX (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xge kn hx 1 hl && exit_ok kn gb gl ga gn grc &&
      match byte_info kn hb hl hx 0 with
      | Some b0 =>
          (ball c_sp kn b0 && xeq kn hC 0 gn && rc_ok kn gn hE hF grc false)
          || (xeq kn hC 1 gn && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
              ((ball c_nspq kn b0 && rc_ok kn gn hE hF grc false) || (ball c_q kn b0 && rc_ok kn gn hE hF grc true)))
      | None => false
      end
  | _, _ => false
  end.
Definition check_Srun (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_nstop kn b0 | None => false end
  | _, _ => false
  end.
Definition check_Sstep (kn : list kentry) (st : sstep) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hC 0 gC && expr_eqb gF hF && xle kn hx 1 hl &&
      match sstep_check kn hb hl hx hE gE true st with Some d => xeq kn hx d gx | None => false end
  | _, _ => false
  end.
Definition check_SA (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 1 gC && expr_eqb gE hE && expr_eqb gF hF && xle kn hx 1 hl &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_q kn b0 | None => false end
  | _, _ => false
  end.
Definition check_SXq (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xge kn hx 1 hl && xeq kn hC 1 gn && exit_ok kn gb gl ga gn grc &&
      rc_ok kn gn hE hF grc false &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_q kn b0 | None => false end
  | _, _ => false
  end.
Definition check_SXrun (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xge kn hx 1 hl && xeq kn hC 1 gn && exit_ok kn gb gl ga gn grc &&
      rc_ok kn gn hE hF grc true &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_nstop kn b0 | None => false end
  | _, _ => false
  end.
Definition check_SXstep (kn : list kentry) (st : sstep) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xeq kn hC 1 gn && exit_ok kn gb gl ga gn grc &&
      rc_ok kn gn hE hF grc true &&
      match sstep_check kn hb hl hx hE hE false st with Some d => xge kn hx d hl | None => false end
  | _, _ => false
  end.
Definition check_PP (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 0 gC && expr_eqb gE hE && expr_eqb gF hF && xle kn hx 3 hl &&
      match byte_info kn hb hl hx 2 with Some b2 => ball c_pcont kn b2 | None => false end
  | _, _ => false
  end.
Definition check_PA (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 2 gx && xeq kn hC 1 gC && expr_eqb gE hE && expr_eqb gF hF &&
      (xge kn hx 2 hl || match byte_info kn hb hl hx 2 with Some b2 => ball c_npcont kn b2 | None => false end)
  | _, _ => false
  end.
Definition check_PX (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xge kn hx 2 hl && xeq kn hC 1 gn && exit_ok kn gb gl ga gn grc && rc_ok kn gn hE hF grc false
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition f_same (hF gF : expr) : bool := expr_eqb gF hF || expr_eqb gF (EAlu ALU_OR hF (ELit 0)).
Definition f_one (kn : list kentry) (hF gF : expr) : bool :=
  expr_eqb gF (ELit 1) || expr_eqb gF (EAlu ALU_OR hF (ELit 1)) || xeq kn gF 0 (ELit 1).
Definition check_initW (kn : list kentry) (g : list expr) : bool :=
  check_init kn g && match g with [gb; gl; ga; gx; gC; gE; gF] => Z.ltb 0 (match xlo kn gl with Some lo => lo | None => 0 end) | _ => false end.
Definition check_WP0 (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 0 gx && xeq kn hC 0 gC && expr_eqb gE hE && f_same hF gF &&
      xle kn hx 2 hl && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0 with Some b0 => ball prim_start kn b0 | None => false end
  | _, _ => false
  end.
Definition check_P0P0 (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 0 gC && expr_eqb gE hE && f_same hF gF && xle kn hx 3 hl &&
      match byte_info kn hb hl hx 1 with Some b1 => ball c_pcont kn b1 | None => false end
  | _, _ => false
  end.
Definition check_P0A (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hC 1 gC && expr_eqb gE hE && f_same hF gF &&
      match byte_info kn hb hl hx 1 with
      | Some b1 => (xeq kn hx 1 gx && ball c_npcont kn b1) || (xeq kn hx 2 gx && ball c_pcont kn b1 && xge kn hx 2 hl)
      | None => false
      end
  | _, _ => false
  end.
Definition check_AX (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xge kn hx 0 hl && xeq kn hC 0 gn && exit_ok kn gb gl ga gn grc && rc_ok kn gn hE hF grc false
  | _, _ => false
  end.
Definition check_SAurun (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xge kn hx 1 hl && xeq kn hx 2 gx && xeq kn hC 1 gC && expr_eqb gE hE && f_one kn hF gF &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_nstop kn b0 | None => false end
  | _, _ => false
  end.
Definition check_SAustep (kn : list kentry) (st : sstep) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xeq kn hC 1 gC && f_one kn hF gF &&
      match sstep_check kn hb hl hx hE gE true st with Some d => xge kn hx d hl && xeq kn hx (d + 1) gx | None => false end
  | _, _ => false
  end.
Definition check_WAq (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xle kn hx 1 hl && xge kn hx 1 hl && xeq kn hx 2 gx && xeq kn hC 1 gC && expr_eqb gE hE && f_one kn hF gF &&
      xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_q kn b0 | None => false end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition check_SW (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 1 gC && expr_eqb gE hE && f_same hF gF && xle kn hx 2 hl &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_q kn b0 | None => false end
  | _, _ => false
  end.
Definition check_P0W (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 1 gC && expr_eqb gE hE && f_same hF gF &&
      match byte_info kn hb hl hx 1 with Some b1 => ball c_npcont kn b1 | None => false end
  | _, _ => false
  end.
Definition check_P0X (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gn; grc] =>
      ctx3 hb hl ha gb gl ga && xge kn hx 2 hl && xeq kn hC 1 gn && exit_ok kn gb gl ga gn grc && rc_ok kn gn hE hF grc false &&
      match byte_info kn hb hl hx 1 with Some b1 => ball c_pcont kn b1 | None => false end
  | _, _ => false
  end.
Definition check_WAW (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hx; hC; hE; hF], [gb; gl; ga; gx; gC; gE; gF] =>
      ctx3 hb hl ha gb gl ga && xeq kn hx 1 gx && xeq kn hC 1 gC && expr_eqb gE hE && f_same hF gF &&
      xle kn hx 2 hl && xle kn hC 1 hl && lt32 kn hl && idx_is kn ha hC 0 hx &&
      match byte_info kn hb hl hx 0 with Some b0 => ball c_op kn b0 | None => false end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition check_Xok (kn : list kentry) (h g : list expr) : bool :=
  match h, g with
  | [hb; hl; ha; hn; hrc], [gb; gl; ga; gn] => ctx3 hb hl ha gb gl ga && expr_eqb gn hn && xeq kn hrc 0 (ELit 0)
  | _, _ => false
  end.
Definition check_XF (kn : list kentry) (h : list expr) (K : kentry) : bool :=
  match h, K with
  | [hb; hl; ha; hn; hrc], KRange e lo hi =>
      Z.ltb hi two64 && Z.leb (S2G.hiZ kn hl) hi &&
      ((expr_eqb e hn && (Z.leb lo 0 || (Z.leb lo 1 && xeq kn hrc 0 (ELit 0))))
       || (expr_eqb e (EAlu ALU_SUB hl hn) && Z.leb lo 0))
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition with_atoms (c : vc) (i hid gid : nat) (chk : list kentry -> list expr -> list expr -> bool) : bool :=
  match hyp_at c i hid, concl_at c gid with
  | Some h, Some g => chk (vc_kn c) h g
  | _, _ => false
  end.
Definition vc_check (r : rule) (c : vc) : bool :=
  match r with
  | RNone => false
  | RHyp i => match vc_concl c, nth_error (vc_hyps c) i with VCAtom g, Some g' => gatom_eqb g g' | _, _ => false end
  | RContra v => match bset (vc_kn c) v with [] => true | _ => false end
  | RInit => match concl_at c 71 with Some g => check_init (vc_kn c) g | None => false end
  | RAW i => with_atoms c i 71 72 check_AW
  | RWW i => with_atoms c i 72 72 check_WW
  | RWS i => with_atoms c i 72 73 check_WS
  | RWP i => with_atoms c i 72 74 check_WP
  | RWA i => with_atoms c i 72 71 check_WA
  | RWX i => with_atoms c i 72 76 check_WX
  | RSrun i => with_atoms c i 73 73 check_Srun
  | RSstep i st => with_atoms c i 73 73 (fun kn => check_Sstep kn st)
  | RSA i => with_atoms c i 73 71 check_SA
  | RSXq i => with_atoms c i 73 76 check_SXq
  | RSXrun i => with_atoms c i 73 76 check_SXrun
  | RSXstep i st => with_atoms c i 73 76 (fun kn => check_SXstep kn st)
  | RPP i => with_atoms c i 74 74 check_PP
  | RPA i => with_atoms c i 74 71 check_PA
  | RPX i => with_atoms c i 74 76 check_PX
  | RInitW => match concl_at c 72 with Some g => check_initW (vc_kn c) g | None => false end
  | RWP0 i => with_atoms c i 72 75 check_WP0
  | RP0P0 i => with_atoms c i 75 75 check_P0P0
  | RP0A i => with_atoms c i 75 71 check_P0A
  | RAX i => with_atoms c i 71 76 check_AX
  | RSAurun i => with_atoms c i 73 71 check_SAurun
  | RSAustep i st => with_atoms c i 73 71 (fun kn => check_SAustep kn st)
  | RWAq i => with_atoms c i 72 71 check_WAq
  | RSW i => with_atoms c i 73 72 check_SW
  | RP0W i => with_atoms c i 75 72 check_P0W
  | RP0X i => with_atoms c i 75 76 check_P0X
  | RWAW i => with_atoms c i 72 72 check_WAW
  | RXok i => with_atoms c i 76 60 check_Xok
  | RXF i => match hyp_at c i 76, vc_concl c with Some h, VCFact K => check_XF (vc_kn c) h K | _, _ => false end
  end.
Fixpoint vcs_check (rs : list rule) (cs : list vc) : bool :=
  match rs, cs with
  | [], [] => true
  | r :: rs', c :: cs' => vc_check r c && vcs_check rs' cs'
  | _, _ => false
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CheckSound.
Ltac bsplit H :=
  lazymatch type of H with
  | (?a && ?b)%bool = true => let H2 := fresh H in apply andb_prop in H; destruct H as [H H2]; bsplit H; bsplit H2
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac bsplit_all := repeat match goal with H : (?a && ?b)%bool = true |- _ => apply andb_prop in H; destruct H end.
Ltac zlit := unfold S1M.UNCLOSED_STRING, S1M.EMPTY, S1M.UTF8_ERROR, S1M.UNESCAPED_CHARS, S1M.SUCCESS, S1M.QUOTE, S1M.BACKSLASH, S1M.RS, two64; lia.
Ltac eqx H := apply expr_eqb_eq in H; subst || (apply expr_eqb_eq in H; rewrite H in * || rewrite <- H in *).

Lemma uE_lit : forall E z, 0 <= z < two64 -> uD E (ELit z) = z.
Proof. intros E z Hz. cbn [edenot]. rewrite u_lit64a. apply Z.mod_small. unfold two64 in Hz. lia. Qed.

Lemma hyp_at_sound : forall E M c i id args, Forall (APS.gholds GP1 E M) (vc_hyps c) -> hyp_at c i id = Some args ->
  GP1 id (map (APS.uE E) args) M.
Proof.
  intros E M c i id args Hh H. unfold hyp_at in H. destruct (nth_error (vc_hyps c) i) as [[id' args']|] eqn:Hi; [|discriminate].
  destruct (Nat.eqb_spec id' id); [|discriminate]. injection H as <-. subst id'.
  exact (proj1 (Forall_forall _ _) Hh _ (nth_error_In _ _ Hi)).
Qed.
Lemma concl_at_sound : forall E M c id args, concl_at c id = Some args -> GP1 id (map (APS.uE E) args) M ->
  match vc_concl c with VCAtom g => APS.gholds GP1 E M g | VCFact K => kentry_ok SEGS E M K end.
Proof.
  intros E M c id args H HG. unfold concl_at in H. destruct (vc_concl c) as [[id' args']|K]; [|discriminate].
  destruct (Nat.eqb_spec id' id); [|discriminate]. injection H as <-. subst id'. exact HG.
Qed.

(* [comment removed for export] *)
Lemma idx_is_sound : forall E M kn a1 C o x, know_ok SEGS E M kn -> idx_is kn a1 C o x = true -> uD E x < 2 ^ 32 ->
  u32_at M (uD E a1 + 4 * uD E C + o) = Some (uD E x).
Proof.
  intros E M kn a1 C o x Hkn H Hx. unfold idx_is in H.
  destruct (find_rec kn kn ((a1, o) :: S2G.xN 4 C) 4) as [v|] eqn:Hr; [|discriminate].
  pose proof (S2G.rdZ_of_rec SEGS E M kn kn _ 4 v Hkn Hkn Hr) as R. cbn [xt_den] in R. rewrite S2G.xt_den_xN in R.
  replace (bv_unsigned (edenot E a1) + o + Z.of_nat 4 * bv_unsigned (edenot E C)) with (uD E a1 + 4 * uD E C + o) in R by lia.
  unfold u32_at, S2G.u32_at. rewrite R. replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity. f_equal.
  pose proof (u64_range (edenot E x)) as Rx.
  apply Bool.orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst v. apply Z.mod_small. lia.
  - apply (xeq_sound E M kn) in H; [|exact Hkn]. rewrite <- S2G.recval4. lia.
Qed.
Lemma lt32_sound : forall E M kn len, know_ok SEGS E M kn -> lt32 kn len = true -> uD E len < 2 ^ 32.
Proof. intros E M kn len Hkn H. unfold lt32 in H. apply Z.ltb_lt in H. pose proof (S2G.hiZ_sound SEGS E M kn len Hkn). lia. Qed.

(* [comment removed for export] *)
Lemma rc_ok_sound : forall E M kn n Ee F rc forced, know_ok SEGS E M kn -> rc_ok kn n Ee F rc forced = true ->
  (F = ELit 0 \/ uD E F = 0 \/ uD E F = 1) ->
  uD E rc = (if forced then S1M.UNCLOSED_STRING else code (uD E n) (uD E Ee) (zb (uD E F))).
Proof.
  intros E M kn n Ee F rc forced Hkn H HF. unfold rc_ok in H. pose proof (u64_range (edenot E n)) as Rn.
  destruct forced.
  - apply expr_eqb_eq in H. subst rc. apply uE_lit. zlit.
  - unfold code, zb. apply Bool.orb_prop in H as [H|H].
    + apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. subst rc. apply (xeq_sound E M kn) in H2; [|exact Hkn].
      rewrite uE_lit in H2 by zlit. rewrite uE_lit by zlit.
      destruct (Z.eqb_spec (uD E n) 0); [reflexivity|lia].
    + apply andb_prop in H as [H1 H2]. apply (xge_sound E M kn) in H1; [|exact Hkn]. rewrite uE_lit in H1 by zlit.
      destruct (Z.eqb_spec (uD E n) 0); [lia|].
      apply Bool.orb_prop in H2 as [H2|H2]; apply andb_prop in H2 as [H3 H4]; apply expr_eqb_eq in H3; subst rc;
        apply (xeq_sound E M kn) in H4; try exact Hkn; rewrite uE_lit in H4 by zlit.
      * rewrite uE_lit by zlit. replace (uD E F) with 1 by lia. reflexivity.
      * replace (uD E F) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exit_ok_sound : forall E M kn buf len a1 n rc bs, know_ok SEGS E M kn -> exit_ok kn buf len a1 n rc = true ->
  0 <= uD E len -> uD E buf + uD E len + 64 < two64 -> input M (uD E buf) (uD E len) = Some bs ->
  uD E rc = 0 -> sentinels M (uD E len) (uD E a1) (uD E n) /\ nthb bs (uD E len) = 0.
Proof.
  intros E M kn buf len a1 n rc bs Hkn H Hl Hbl Hin Hrc. unfold exit_ok in H.
  assert (HM : rc_maybe0 rc = true).
  { unfold rc_maybe0. destruct rc as [z| | | | | | |]; try reflexivity. cbn [edenot] in Hrc. rewrite u_lit64a in Hrc. apply Z.eqb_eq. exact Hrc. }
  rewrite HM in H. apply andb_prop in H as [HS HZ]. unfold sent_ok in HS. bsplit HS.
  pose proof (lt32_sound E M kn len Hkn ltac:(assumption)) as L32.
  split.
  - unfold sentinels. pose proof (u64_range (edenot E len)) as RL.
    split; [|split].
    + rewrite <- (Z.add_0_r (uD E a1 + 4 * uD E n)). eapply idx_is_sound; [exact Hkn|assumption|lia].
    + eapply idx_is_sound; [exact Hkn|assumption|lia].
    + replace (Some 0) with (Some (uD E (ELit 0))) by (rewrite uE_lit by zlit; reflexivity). eapply idx_is_sound; [exact Hkn|assumption|]. rewrite uE_lit by zlit. lia.
  - destruct (find_zero kn kn [(buf, 0); (len, 0)]) as [m|] eqn:Hz; [|discriminate]. apply Z.leb_le in HZ.
    pose proof (u64_range (edenot E buf)) as RB.
    eapply (input_zero E M (uD E buf) (uD E len) bs kn _ m (uD E len)); try eassumption; try lia. cbn [xt_den]. lia.
Qed.
(* [comment removed for export] *)
Ltac sem E M kn Hkn :=
  repeat match goal with
  | H : (_ && _)%bool = true |- _ => bsplit H
  | H : ctx3 _ _ _ _ _ _ = true |- _ => unfold ctx3 in H
  | H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H; subst
  | H : xeq kn ?a ?k ?b = true |- _ => apply (xeq_sound E M kn a k b Hkn) in H
  | H : xle kn ?a ?k ?b = true |- _ => apply (xle_sound E M kn a k b Hkn) in H
  | H : xge kn ?a ?k ?b = true |- _ => apply (xge_sound E M kn a k b Hkn) in H
  | H : lt32 kn ?l = true |- _ => apply (lt32_sound E M kn l Hkn) in H
  | H : match byte_info kn ?b ?l ?x ?k with Some _ => _ | None => false end = true |- _ =>
      let bi := fresh "bi" in let Hb := fresh "Hbi" in destruct (byte_info kn b l x k) as [bi|] eqn:Hb; [|discriminate]
  end.
Ltac dest7 h := destruct h as [|? [|? [|? [|? [|? [|? [|? [|? ?]]]]]]]]; try discriminate.
Ltac dest5 g := destruct g as [|? [|? [|? [|? [|? [|? ?]]]]]]; try discriminate.
(* [comment removed for export] *)
Ltac ballfact E M kn Hkn Hin H :=
  lazymatch type of H with
  | ball ?P kn ?bi = true =>
      lazymatch goal with
      | Hb : byte_info kn ?b ?l ?x ?k = Some bi |- _ =>
          apply (byte_info_sound E M kn b l _ x k bi P Hkn ltac:(lia) ltac:(lia) Hin Hb) in H
      end
  end.

(* [comment removed for export] *)
Section VUtf8.
Variable bf : Z -> Z.
Variables len p err : Z.
Ltac leadtac H := unfold c_lead, c_badlead, c_hi in H; bsplit H;
  repeat match goal with
         | G : negb _ = true |- _ => apply Bool.negb_true_iff in G
         end.
Lemma vutf8_bad : c_badlead (bf p) = true -> S1M.vutf8 bf len p err = (p + 1, S1M.UTF8_ERROR).
Proof. intros H. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end. reflexivity. Qed.
Lemma vutf8_2short : c_lead 2 (bf p) = true -> (len < p + 1 \/ S1M.is_cont (bf (p + 1)) = false) ->
  S1M.vutf8 bf len p err = (p + 1, S1M.UTF8_ERROR).
Proof.
  intros H Hs. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 1)); [reflexivity|]. destruct Hs as [Hs|Hs]; [lia|]. rewrite Hs. reflexivity.
Qed.
Lemma vutf8_2ok : c_lead 2 (bf p) = true -> p + 1 <= len -> S1M.is_cont (bf (p + 1)) = true ->
  S1M.vutf8 bf len p err = (p + 2, if u8cond 2 (bf p) (bf (p + 1)) then S1M.UTF8_ERROR else err).
Proof.
  intros H Hl H1. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 1)); [lia|]. rewrite H1. reflexivity.
Qed.
Lemma vutf8_3short : c_lead 3 (bf p) = true -> (len < p + 2 \/ S1M.is_cont (bf (p + 1)) = false \/ S1M.is_cont (bf (p + 2)) = false) ->
  S1M.vutf8 bf len p err = (p + 1, S1M.UTF8_ERROR).
Proof.
  intros H Hs. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 2)); [reflexivity|]. destruct Hs as [Hs|[Hs|Hs]]; [lia|rewrite Hs; reflexivity|rewrite Hs].
  destruct (S1M.is_cont (bf (p + 1))); reflexivity.
Qed.
Lemma vutf8_3ok : c_lead 3 (bf p) = true -> p + 2 <= len -> S1M.is_cont (bf (p + 1)) = true -> S1M.is_cont (bf (p + 2)) = true ->
  S1M.vutf8 bf len p err = (p + 3, if u8cond 3 (bf p) (bf (p + 1)) then S1M.UTF8_ERROR else err).
Proof.
  intros H Hl H1 H2. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 2)); [lia|]. rewrite H1, H2. reflexivity.
Qed.
Lemma vutf8_4short : c_lead 4 (bf p) = true ->
  (len < p + 3 \/ S1M.is_cont (bf (p + 1)) = false \/ S1M.is_cont (bf (p + 2)) = false \/ S1M.is_cont (bf (p + 3)) = false) ->
  S1M.vutf8 bf len p err = (p + 1, S1M.UTF8_ERROR).
Proof.
  intros H Hs. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 3)); [reflexivity|].
  destruct Hs as [Hs|[Hs|[Hs|Hs]]]; [lia|rewrite Hs; reflexivity|rewrite Hs|rewrite Hs].
  - destruct (S1M.is_cont (bf (p + 1))); reflexivity.
  - destruct (S1M.is_cont (bf (p + 1))); destruct (S1M.is_cont (bf (p + 2))); reflexivity.
Qed.
Lemma vutf8_4ok : c_lead 4 (bf p) = true -> p + 3 <= len -> S1M.is_cont (bf (p + 1)) = true -> S1M.is_cont (bf (p + 2)) = true ->
  S1M.is_cont (bf (p + 3)) = true ->
  S1M.vutf8 bf len p err = (p + 4, if u8cond 4 (bf p) (bf (p + 1)) then S1M.UTF8_ERROR else err).
Proof.
  intros H Hl H1 H2 H3. leadtac H. unfold S1M.vutf8. repeat match goal with G : (Z.land (bf p) _ =? 0) = _ |- _ => rewrite G end.
  destruct (Z.ltb_spec len (p + 3)); [lia|]. rewrite H1, H2, H3. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hi_conds : c_hi (bf p) = true ->
  S1M.is_ascii_stop (bf p) = true /\ bf p <> S1M.QUOTE /\ bf p <> S1M.BACKSLASH /\ Z.land (bf p) 128 <> 0.
Proof.
  intros H. unfold c_hi in H. bsplit H.
  repeat match goal with G : negb _ = true |- _ => apply Bool.negb_true_iff in G end.
  split; [assumption|]. split; [apply Z.eqb_neq; assumption|]. split; [apply Z.eqb_neq; assumption|]. apply Z.eqb_neq; assumption.
Qed.
Lemma lead_hi : forall n, c_lead n (bf p) = true -> c_hi (bf p) = true.
Proof. intros n H. unfold c_lead in H. bsplit H. assumption. Qed.
Lemma badlead_hi : c_badlead (bf p) = true -> c_hi (bf p) = true.
Proof. intros H. unfold c_badlead in H. bsplit H. assumption. Qed.
End VUtf8.

Lemma forallb_seq_In : forall (f : nat -> bool) s n k, forallb f (seq s n) = true -> (s <= k < s + n)%nat -> f k = true.
Proof. intros f s n k H Hk. exact (proj1 (forallb_forall _ _) H k ltac:(apply in_seq; lia)). Qed.

Lemma sstep_check_sound : forall E M kn buf len x hE gE chkE st d bs,
  know_ok SEGS E M kn -> 0 <= uD E len -> uD E buf + uD E len + 64 < two64 -> input M (uD E buf) (uD E len) = Some bs ->
  sstep_check kn buf len x hE gE chkE st = Some d ->
  exists Ec', sstep_sem (uD E len) (nthb bs) (uD E x) (uD E hE) d Ec' /\ (chkE = true -> uD E gE = Ec').
Proof.
  intros E M kn buf len x hE gE chkE st d bs Hkn Hl Hbl Hin H. unfold sstep_check in H.
  destruct (byte_info kn buf len x 0) as [b0|] eqn:Hb0; [|discriminate].
  assert (B0 : forall P, ball P kn b0 = true -> P (nthb bs (uD E x)) = true).
  { intros P HP. rewrite <- (Z.add_0_r (uD E x)). exact (byte_info_sound E M kn buf len bs x 0 b0 P Hkn Hl Hbl Hin Hb0 HP). }
  assert (BK : forall k bk P, byte_info kn buf len x k = Some bk -> ball P kn bk = true -> P (nthb bs (uD E x + k)) = true).
  { intros k bk P Hbk HP. exact (byte_info_sound E M kn buf len bs x k bk P Hkn Hl Hbl Hin Hbk HP). }
  unfold sstep_sem.
  destruct st as [| |u].
  - (* [comment removed for export] *)
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
    apply andb_prop in Hc as [H1 H2]. apply B0 in H1. unfold c_bs in H1. apply andb_prop in H1 as [Hst Hbs]. apply Z.eqb_eq in Hbs.
    exists (uD E hE). split; [|intros ->; cbn in H2; apply expr_eqb_eq in H2; subst gE; reflexivity].
    split; [exact Hst|]. left. repeat split; assumption || reflexivity.
  - (* [comment removed for export] *)
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
    apply andb_prop in Hc as [H1 H2]. apply B0 in H1. unfold c_ch in H1. bsplit H1.
    repeat match goal with G : negb _ = true |- _ => apply Bool.negb_true_iff in G end.
    exists (if nthb bs (uD E x) <? 32 then S1M.UNESCAPED_CHARS else uD E hE). split.
    + split; [assumption|]. right; left. repeat split; try (apply Z.eqb_neq; assumption). apply Z.eqb_eq; assumption.
    + intros ->. cbn [negb orb] in H2. apply (B0 (fun c => if c <? 32 then expr_eqb gE (ELit 14) else expr_eqb gE hE)) in H2.
      destruct (nthb bs (uD E x) <? 32); apply expr_eqb_eq in H2; subst gE; [apply uE_lit; zlit|reflexivity].
  - destruct u as [|n k|n].
    + (* [comment removed for export] *)
      match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
      apply andb_prop in Hc as [H1 H2]. apply B0 in H1.
      destruct (hi_conds (nthb bs) (uD E x) (badlead_hi _ _ H1)) as (C1 & C2 & C3 & C4).
      exists S1M.UTF8_ERROR. split; [|intros ->; cbn in H2; apply expr_eqb_eq in H2; subst gE; apply uE_lit; zlit].
      split; [exact C1|]. right; right. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. apply vutf8_bad. exact H1.
    + (* [comment removed for export] *)
      match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [discriminate|] end.
      apply Bool.negb_false_iff in Hc. apply andb_prop in Hc as [H1 H2]. apply B0 in H1.
      destruct (hi_conds (nthb bs) (uD E x) (lead_hi _ _ n H1)) as (C1 & C2 & C3 & C4).
      exists S1M.UTF8_ERROR. split; [|intros ->; cbn in H2; apply expr_eqb_eq in H2; subst gE; apply uE_lit; zlit].
      split; [exact C1|]. right; right. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
      assert (LN : n = 2%nat \/ n = 3%nat \/ n = 4%nat).
      { unfold c_lead in H1. destruct n as [|[|[|[|[|n']]]]]; try lia; exfalso; bsplit H1; discriminate. }
      destruct (Nat.eqb_spec k 0) as [->|Hk0].
      * destruct (xge kn x (Z.of_nat n - 2) len) eqn:Hge; [|discriminate]. injection H as <-. apply (xge_sound E M kn) in Hge; [|exact Hkn].
        destruct LN as [->|[->| ->]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hge.
        -- apply vutf8_2short; [exact H1|left; lia].
        -- apply vutf8_3short; [exact H1|left; lia].
        -- apply vutf8_4short; [exact H1|left; lia].
      * destruct (Nat.ltb_spec k n); [|discriminate].
        destruct (byte_info kn buf len x (Z.of_nat k)) as [bk|] eqn:Hbk; [|discriminate].
        destruct (ball c_ncont kn bk) eqn:Hnc; [|discriminate]. injection H as <-.
        apply (BK _ _ _ Hbk) in Hnc. unfold c_ncont in Hnc. apply Bool.negb_true_iff in Hnc.
        destruct LN as [->|[->| ->]].
        -- assert (k = 1%nat) by lia. subst k. apply vutf8_2short; [exact H1|right; exact Hnc].
        -- assert (Hk : k = 1%nat \/ k = 2%nat) by lia. destruct Hk as [->| ->]; (apply vutf8_3short; [exact H1|]); [right; left; exact Hnc|right; right; exact Hnc].
        -- assert (Hk : k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia. destruct Hk as [->|[->| ->]]; (apply vutf8_4short; [exact H1|]);
             [right; left; exact Hnc | right; right; left; exact Hnc | right; right; right; exact Hnc].
    + (* [comment removed for export] *)
      match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [discriminate|] end.
      apply Bool.negb_false_iff in Hc. apply andb_prop in Hc as [H1 Hle]. apply B0 in H1. apply (xle_sound E M kn) in Hle; [|exact Hkn].
      destruct (hi_conds (nthb bs) (uD E x) (lead_hi _ _ n H1)) as (C1 & C2 & C3 & C4).
      match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcs; [discriminate|] end. apply Bool.negb_false_iff in Hcs.
      assert (CONT : forall k, (1 <= k < n)%nat -> S1M.is_cont (nthb bs (uD E x + Z.of_nat k)) = true).
      { intros k Hk. pose proof (forallb_seq_In _ 1 (n - 1) k Hcs ltac:(lia)) as X. cbv beta in X.
        destruct (byte_info kn buf len x (Z.of_nat k)) as [bk|] eqn:Hbk; [|discriminate]. exact (BK _ _ _ Hbk X). }
      assert (LN : n = 2%nat \/ n = 3%nat \/ n = 4%nat).
      { unfold c_lead in H1. destruct n as [|[|[|[|[|n']]]]]; try lia; exfalso; bsplit H1; discriminate. }
      set (Ec' := if u8cond n (nthb bs (uD E x)) (nthb bs (uD E x + 1)) then S1M.UTF8_ERROR else uD E hE).
      assert (HV : S1M.vutf8 (nthb bs) (uD E len) (uD E x) (uD E hE) = (uD E x + Z.of_nat n, Ec')).
      { subst Ec'. destruct LN as [->|[->| ->]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hle |- *.
        - apply vutf8_2ok; [exact H1|lia|exact (CONT 1%nat ltac:(lia))].
        - apply vutf8_3ok; [exact H1|lia|exact (CONT 1%nat ltac:(lia))|exact (CONT 2%nat ltac:(lia))].
        - apply vutf8_4ok; [exact H1|lia|exact (CONT 1%nat ltac:(lia))|exact (CONT 2%nat ltac:(lia))|exact (CONT 3%nat ltac:(lia))]. }
      destruct chkE.
      * cbn [negb] in H. destruct (byte_info kn buf len x 1) as [b1|] eqn:Hb1; [|discriminate].
        match type of H with (if ?c then _ else _) = _ => destruct c eqn:HE; [|discriminate] end. injection H as <-.
        exists Ec'. split; [split; [exact C1|]; right; right; split; [exact C2|]; split; [exact C3|]; split; [exact C4|]; exact HV|].
        intros _. subst Ec'.
        apply (B0 (fun c => forallb (fun d1 => if u8cond n c d1 then expr_eqb gE (ELit 11) else expr_eqb gE hE) (bvals kn b1))) in HE. cbv beta in HE.
        apply (BK 1 b1 (fun d1 => if u8cond n (nthb bs (uD E x)) d1 then expr_eqb gE (ELit 11) else expr_eqb gE hE) Hb1) in HE. cbv beta in HE.
        destruct (u8cond n (nthb bs (uD E x)) (nthb bs (uD E x + 1))); apply expr_eqb_eq in HE; subst gE; [apply uE_lit; zlit|reflexivity].
      * cbn [negb] in H. injection H as <-.
        exists Ec'. split; [split; [exact C1|]; right; right; split; [exact C2|]; split; [exact C3|]; split; [exact C4|]; exact HV|]. intros X; discriminate X.
Qed.

Lemma check_AW_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 71 (map (APS.uE E) h) M -> check_AW kn h g = true ->
  GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG H. unfold check_AW in H. dest7 h. dest7 g. cbn [GP1 Nat.eqb map] in HG |- *. unfold APS.uE in *.
  sem E M kn Hkn.
  repeat match goal with H : bv_unsigned (edenot E ?a) + _ = bv_unsigned (edenot E ?b) |- _ => rewrite <- H in *; clear H end. rewrite !Z.add_0_r.
  apply T_AW; [exact HG | lia].
Qed.
Lemma check_WW_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WW kn h g = true ->
  GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG H. unfold check_WW in H. dest7 h. dest7 g. cbn [GP1 Nat.eqb map] in HG |- *. unfold APS.uE in *.
  sem E M kn Hkn.
  pose proof HG as HG'. destruct HG' as (W & HF & bs & out & J0 & Hin & _). unfold wfctx in W.
  repeat match goal with H : ball _ kn _ = true |- _ => ballfact E M kn Hkn Hin H end.
  repeat match goal with H : bv_unsigned (edenot E ?a) + _ = bv_unsigned (edenot E ?b) |- _ => rewrite <- H in *; clear H end. rewrite !Z.add_0_r in *.
  eapply T_WW; [exact HG | exact Hin | ]. unfold c_sp in *. assumption.
Qed.

Lemma op_not_space : forall c, S1M.is_op c = true -> S1M.is_space c = false.
Proof.
  intros c H. unfold S1M.is_op, S1M.is_space in *. unfold S1M.char_class in *.
  repeat match goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn in H |- *; congruence.
Qed.
(* [comment removed for export] *)
Lemma s1w_ctx : forall M b l a x C E F, p_s1w [b; l; a; x; C; E; F] M -> wfctx b l a C /\ (F = 0 \/ F = 1) /\ exists bs, input M b l = Some bs.
Proof. intros M b l a x C E F (W & HF & bs & out & J0 & Hin & _). split; [exact W|]. split; [exact HF|]. exists bs; exact Hin. Qed.
Lemma s1s_ctx : forall M b l a x C E F, p_s1s [b; l; a; x; C; E; F] M -> wfctx b l a C /\ (F = 0 \/ F = 1) /\ C < l /\ exists bs, input M b l = Some bs.
Proof. intros M b l a x C E F (W & HF & HC & bs & out & J0 & E0 & q & cur0 & Hin & _). repeat (split; [assumption|]). exists bs; exact Hin. Qed.
Lemma s1p_ctx : forall M b l a x C E F, p_s1p [b; l; a; x; C; E; F] M -> wfctx b l a C /\ (F = 0 \/ F = 1) /\ C < l /\ exists bs, input M b l = Some bs.
Proof. intros M b l a x C E F (W & HF & HC & bs & out & J0 & i0 & Hin & _). repeat (split; [assumption|]). exists bs; exact Hin. Qed.

Ltac prep chk h g HG :=
  unfold chk; intros H;
  destruct h as [|hb [|hl [|ha [|hx [|hC [|hE [|hF [|? ?]]]]]]]]; try discriminate;
  destruct g as [|gb [|gl [|ga [|gx [|gC [|gE [|gF [|? ?]]]]]]]]; try discriminate;
  cbn [GP1 Nat.eqb map] in HG |- *; unfold APS.uE in *.
Ltac prep5 chk h g HG :=
  unfold chk; intros H;
  destruct h as [|hb [|hl [|ha [|hx [|hC [|hE [|hF [|? ?]]]]]]]]; try discriminate;
  destruct g as [|gb [|gl [|ga [|gn [|grc [|? ?]]]]]]; try discriminate;
  cbn [GP1 Nat.eqb map] in HG |- *; unfold APS.uE in *.
Ltac linsubst E :=
  repeat match goal with
         | H : bv_unsigned (edenot E ?a) + _ = bv_unsigned (edenot E ?b) |- _ => rewrite <- H in *; clear H
         | H : bv_unsigned (edenot E ?a) = bv_unsigned (edenot E ?b) |- _ => rewrite <- H in *; clear H
         end;
  rewrite ?Z.add_0_r in *.
Ltac balls E M kn Hkn Hin := repeat match goal with H : ball _ kn _ = true |- _ => ballfact E M kn Hkn Hin H end; rewrite ?Z.add_0_r in *.
Ltac negs := repeat match goal with G : negb _ = true |- _ => apply Bool.negb_true_iff in G end.

Lemma check_WS_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WS kn h g = true ->
  GP1 73 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WS h g HG. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W.
  balls E M kn Hkn Hin. linsubst E. unfold c_q in *.
  eapply T_WS; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia | lia |].
  rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia].
Qed.
Lemma check_WP_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WP kn h g = true ->
  GP1 74 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WP h g HG.
  destruct (byte_info kn hb hl hx 0) as [b0|] eqn:Hb0; destruct (byte_info kn hb hl hx 1) as [b1|] eqn:Hb1;
    [|rewrite andb_false_r in H; discriminate|rewrite andb_false_r in H; discriminate|rewrite andb_false_r in H; discriminate].
  sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W.
  balls E M kn Hkn Hin. linsubst E. unfold c_pcont in *.
  eapply T_WP; [exact HG | exact Hin | assumption | assumption | lia | lia |].
  rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia].
Qed.
Lemma check_WA_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WA kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WA h g HG.
  destruct (byte_info kn hb hl hx 0) as [b0|] eqn:Hb0; [|rewrite andb_false_r in H; discriminate].
  apply andb_prop in H as [H Halt]. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W.
  assert (REC : u32_at M (uD E ha + 4 * uD E hC) = Some (uD E hx)).
  { rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia]. }
  assert (STOP : S1M.is_space (nthb bs (uD E hx)) = false /\ nthb bs (uD E hx) <> S1M.QUOTE /\
                 (S1M.is_op (nthb bs (uD E hx)) = true \/ uD E hl <= uD E hx + 1 \/ prim_cont (nthb bs (uD E hx + 1)) = false)).
  { apply Bool.orb_prop in Halt as [Hop|Hpr].
    - ballfact E M kn Hkn Hin Hop. rewrite Z.add_0_r in Hop. unfold c_op in Hop.
      split; [|split; [|left; exact Hop]].
      + exact (op_not_space _ Hop).
      + intros X. rewrite X in Hop. discriminate Hop.
    - apply andb_prop in Hpr as [Hst Hend]. ballfact E M kn Hkn Hin Hst. rewrite Z.add_0_r in Hst.
      unfold prim_start in Hst. bsplit Hst. negs.
      split; [assumption|]. split; [apply Z.eqb_neq; assumption|]. right.
      apply Bool.orb_prop in Hend as [Hl|Hb].
      + apply (xge_sound E M kn) in Hl; [|exact Hkn]. left. lia.
      + destruct (byte_info kn _ _ _ 1) as [b1|] eqn:Hb1; [|discriminate].
        ballfact E M kn Hkn Hin Hb. unfold c_npcont in Hb. negs. right. exact Hb. }
  destruct STOP as (S1 & S2 & S3). linsubst E.
  eapply T_WA; [exact HG | exact Hin | exact S1 | exact S2 | exact S3 | lia | lia | exact REC].
Qed.

(* [comment removed for export] *)
Lemma X_concl : forall E M kn gb gl ga gn grc C n bs, know_ok SEGS E M kn ->
  wfctx (uD E gb) (uD E gl) (uD E ga) C -> n <= uD E gl -> input M (uD E gb) (uD E gl) = Some bs ->
  exit_ok kn gb gl ga gn grc = true -> uD E gn = n ->
  finished M (uD E gl) (uD E ga) bs n (uD E grc) ->
  p_s1x [uD E gb; uD E gl; uD E ga; uD E gn; uD E grc] M.
Proof.
  intros E M kn gb gl ga gn grc C n bs Hkn W Hn Hin HX Hgn FIN. pose proof W as W'. unfold wfctx in W'. rewrite Hgn.
  eapply T_X; [exact W | exact Hn | exact Hin | exact FIN |].
  intros Hrc. rewrite <- Hgn. eapply exit_ok_sound; try eassumption; lia.
Qed.

Lemma check_WX_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WX kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_WX h g HG.
  destruct (byte_info kn hb hl hx 0) as [b0|] eqn:Hb0; [|rewrite andb_false_r in H; discriminate].
  apply andb_prop in H as [H Halt]. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  apply Bool.orb_prop in Halt as [Hsp|Hns].
  - (* [comment removed for export] *)
    bsplit Hsp. sem E M kn Hkn. balls E M kn Hkn Hin. unfold c_sp in *.
    match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
    eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
    match goal with HR : uD E grc = _ |- _ => rewrite HR end.
    match goal with HR : uD E hC = uD E gn |- _ => rewrite <- HR end.
    eapply T_WX_sp; [exact HG | exact Hin | assumption | lia | lia].
  - bsplit Hns. sem E M kn Hkn.
    assert (REC : u32_at M (uD E ha + 4 * uD E hC) = Some (uD E hx)).
    { rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia]. }
    match goal with HA : (_ || _)%bool = true |- _ => apply Bool.orb_prop in HA as [Hq|Hq]; bsplit Hq end.
    + (* [comment removed for export] *)
      balls E M kn Hkn Hin. unfold c_nspq in *. bsplit_all. negs.
      match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
      eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
      match goal with HR : uD E grc = _ |- _ => rewrite HR end.
      match goal with HR : uD E hC + 1 = uD E gn |- _ => rewrite <- HR end.
      eapply T_WX_ns; [exact HG | exact Hin | assumption | apply Z.eqb_neq; assumption | lia | lia | exact REC].
    + (* [comment removed for export] *)
      balls E M kn Hkn Hin. unfold c_q in *.
      match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
      eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
      match goal with HR : uD E grc = _ |- _ => rewrite HR end. cbn [code].
      eapply T_WX_q; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia | lia | exact REC].
Qed.

Lemma check_Srun_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_Srun kn h g = true ->
  GP1 73 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_Srun h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W.
  balls E M kn Hkn Hin. linsubst E. unfold c_nstop in *. negs.
  eapply T_Srun; [exact HG | exact Hin | assumption].
Qed.
Lemma check_Sstep_sound : forall E M kn st h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_Sstep kn st h g = true ->
  GP1 73 (map (APS.uE E) g) M.
Proof.
  intros E M kn st h g Hkn HG. prep check_Sstep h g HG.
  destruct (sstep_check kn hb hl hx hE gE true st) as [d|] eqn:Hst; [|rewrite andb_false_r in H; discriminate]. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W.
  destruct (sstep_check_sound E M kn hb hl hx hE gE true st d bs Hkn ltac:(lia) ltac:(lia) Hin Hst) as (Ec' & SEM & HE).
  rewrite (HE eq_refl). linsubst E.
  eapply T_SS; [exact HG | exact Hin | lia | exact SEM].
Qed.
Lemma check_SA_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SA kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_SA h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W.
  balls E M kn Hkn Hin. linsubst E. unfold c_q in *.
  eapply T_SA; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia].
Qed.
Lemma check_SXq_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SXq kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_SXq h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  balls E M kn Hkn Hin. unfold c_q in *.
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end.
  match goal with HR : uD E hC + 1 = uD E gn |- _ => rewrite <- HR end.
  eapply T_SX_q; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia | lia].
Qed.
Lemma check_SXrun_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SXrun kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_SXrun h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  balls E M kn Hkn Hin. unfold c_nstop in *. negs.
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end. cbn [code].
  eapply T_SX_run; [exact HG | exact Hin | assumption | lia | lia].
Qed.
Lemma check_SXstep_sound : forall E M kn st h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SXstep kn st h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn st h g Hkn HG. prep5 check_SXstep h g HG.
  destruct (sstep_check kn hb hl hx hE hE false st) as [d|] eqn:Hst; [|rewrite andb_false_r in H; discriminate]. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  destruct (sstep_check_sound E M kn hb hl hx hE hE false st d bs Hkn ltac:(lia) ltac:(lia) Hin Hst) as (Ec' & SEM & _).
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end. cbn [code].
  eapply T_SX_step; [exact HG | exact Hin | lia | exact SEM | lia].
Qed.
Lemma check_PP_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 74 (map (APS.uE E) h) M -> check_PP kn h g = true ->
  GP1 74 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_PP h g HG. sem E M kn Hkn.
  destruct (s1p_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W.
  balls E M kn Hkn Hin. linsubst E. unfold c_pcont in *.
  eapply T_PP; [exact HG | exact Hin | assumption | lia].
Qed.
Lemma check_PA_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 74 (map (APS.uE E) h) M -> check_PA kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_PA h g HG. apply andb_prop in H as [H Hstop]. sem E M kn Hkn.
  destruct (s1p_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W.
  assert (STOP : uD E hl <= uD E hx + 2 \/ prim_cont (nthb bs (uD E hx + 2)) = false).
  { apply Bool.orb_prop in Hstop as [Hl|Hb].
    - apply (xge_sound E M kn) in Hl; [|exact Hkn]. left; lia.
    - destruct (byte_info kn _ _ _ 2) as [b2|] eqn:Hb2; [|discriminate]. ballfact E M kn Hkn Hin Hb. unfold c_npcont in Hb. negs. right; exact Hb. }
  linsubst E. eapply T_PA; [exact HG | exact Hin | exact STOP].
Qed.
Lemma check_PX_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 74 (map (APS.uE E) h) M -> check_PX kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_PX h g HG. sem E M kn Hkn.
  destruct (s1p_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end.
  match goal with HR : uD E hC + 1 = uD E gn |- _ => rewrite <- HR end.
  eapply T_PX; [exact HG | exact Hin | lia].
Qed.
Lemma check_init_sound : forall E M kn g, know_ok SEGS E M kn -> check_init kn g = true -> GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn g Hkn H. unfold check_init in H.
  destruct g as [|gb [|gl [|ga [|gx [|gC [|gE [|gF [|? ?]]]]]]]]; try discriminate.
  cbn [GP1 Nat.eqb map]. unfold APS.uE. bsplit H.
  assert (Z0 : forall e, is0 e = true -> uD E e = 0).
  { intros e He. unfold is0 in He. destruct e as [z| | | | | | |]; try discriminate. apply Z.eqb_eq in He. subst z. apply uE_lit. zlit. }
  repeat match goal with G : is0 ?e = true |- _ => apply Z0 in G; rewrite G; clear G end. destruct (find_zero kn kn [(gb, 0); (gl, 0)]) as [m|] eqn:Hz; [|discriminate].
  repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G end.
  pose proof (S2G.hiZ_sound SEGS E M kn gb Hkn). pose proof (S2G.hiZ_sound SEGS E M kn gl Hkn). pose proof (S2G.hiZ_sound SEGS E M kn ga Hkn).
  pose proof (u64_range (edenot E gl)). pose proof (u64_range (edenot E ga)).
  apply T_init; try lia. eapply input_exists; [exact Hkn | assumption | exists m; split; [exact Hz | lia]].
Qed.

Lemma s1p0_ctx : forall M b l a x C E F, p_s1p0 [b; l; a; x; C; E; F] M -> wfctx b l a C /\ (F = 0 \/ F = 1) /\ C < l /\ exists bs, input M b l = Some bs.
Proof. intros M b l a x C E F (W & HF & HC & bs & out & J0 & i0 & Hin & _). repeat (split; [assumption|]). exists bs; exact Hin. Qed.
Lemma s1a_ctx : forall M b l a x C E F, p_s1a [b; l; a; x; C; E; F] M -> wfctx b l a C /\ (F = 0 \/ F = 1) /\ exists bs, input M b l = Some bs.
Proof. intros M b l a x C E F (W & HF & bs & out & Hin & _). split; [exact W|]. split; [exact HF|]. exists bs; exact Hin. Qed.
Lemma f_same_sound : forall E hF gF, f_same hF gF = true -> (uD E hF = 0 \/ uD E hF = 1) -> uD E gF = uD E hF.
Proof.
  intros E hF gF H HF. unfold f_same in H. apply Bool.orb_prop in H as [H|H]; apply expr_eqb_eq in H; subst gF; [reflexivity|].
  cbn [edenot]. rewrite u_or64, u_lit64a. change (0 mod 2 ^ 64) with 0. rewrite Z.lor_0_r. reflexivity.
Qed.
Lemma f_one_sound : forall E M kn hF gF, know_ok SEGS E M kn -> f_one kn hF gF = true -> (uD E hF = 0 \/ uD E hF = 1) -> uD E gF = 1.
Proof.
  intros E M kn hF gF Hkn H HF. unfold f_one in H. apply Bool.orb_prop in H as [H|H]; [apply Bool.orb_prop in H as [H|H]|].
  - apply expr_eqb_eq in H; subst gF. apply uE_lit. zlit.
  - apply expr_eqb_eq in H; subst gF. cbn [edenot]. rewrite u_or64, u_lit64a. change (1 mod 2 ^ 64) with 1.
    destruct HF as [HF|HF]; rewrite HF; reflexivity.
  - apply (xeq_sound E M kn) in H; [|exact Hkn]. rewrite uE_lit in H by zlit. lia.
Qed.
(* [comment removed for export] *)
Ltac fsub E M kn Hkn HF :=
  repeat match goal with
         | H : f_same ?hF ?gF = true |- _ => apply (f_same_sound E hF gF) in H; [rewrite H in *; clear H|exact HF]
         | H : f_one kn ?hF ?gF = true |- _ => apply (f_one_sound E M kn hF gF Hkn) in H; [rewrite H in *; clear H|exact HF]
         end.

Lemma check_initW_sound : forall E M kn g, know_ok SEGS E M kn -> check_initW kn g = true -> GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn g Hkn H. unfold check_initW in H. apply andb_prop in H as [H0 H1].
  pose proof (check_init_sound E M kn g Hkn H0) as HA.
  destruct g as [|gb [|gl [|ga [|gx [|gC [|gE [|gF [|? ?]]]]]]]]; try discriminate.
  unfold check_init in H0. bsplit H0.
  assert (Z0 : forall e, is0 e = true -> uD E e = 0).
  { intros e He. unfold is0 in He. destruct e as [z| | | | | | |]; try discriminate. apply Z.eqb_eq in He. subst z. apply uE_lit. zlit. }
  cbn [GP1 Nat.eqb map] in HA |- *. unfold APS.uE in *.
  repeat match goal with G : is0 ?e = true |- _ => apply Z0 in G; rewrite G in *; clear G end.
  apply Z.ltb_lt in H1. destruct (xlo kn gl) as [lo|] eqn:Hlo; [|lia].
  pose proof (xlo_sound SEGS E M kn gl lo Hkn Hlo). apply T_AW; [exact HA | lia].
Qed.
Lemma check_WP0_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WP0 kn h g = true ->
  GP1 75 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WP0 h g HG. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E.
  eapply T_WP0; [exact HG | exact Hin | assumption | lia | lia |].
  rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia].
Qed.
Lemma check_P0P0_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 75 (map (APS.uE E) h) M -> check_P0P0 kn h g = true ->
  GP1 75 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_P0P0 h g HG. sem E M kn Hkn.
  destruct (s1p0_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E. unfold c_pcont in *.
  eapply T_P0P0; [exact HG | exact Hin | assumption | lia].
Qed.
Lemma check_P0A_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 75 (map (APS.uE E) h) M -> check_P0A kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_P0A h g HG.
  destruct (byte_info kn hb hl hx 1) as [b1|] eqn:Hb1; [|rewrite andb_false_r in H; discriminate].
  apply andb_prop in H as [H Halt]. sem E M kn Hkn.
  destruct (s1p0_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  apply Bool.orb_prop in Halt as [H1|H1]; bsplit H1; sem E M kn Hkn; balls E M kn Hkn Hin; linsubst E.
  - unfold c_npcont in *. negs. eapply T_P0A_stop; [exact HG | exact Hin | assumption].
  - unfold c_pcont in *. eapply T_P0A_end; [exact HG | exact Hin | assumption | lia].
Qed.
Lemma check_AX_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 71 (map (APS.uE E) h) M -> check_AX kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_AX h g HG. sem E M kn Hkn.
  destruct (s1a_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end.
  match goal with HR : uD E hC + 0 = uD E gn |- _ => rewrite <- HR | HR : uD E hC = uD E gn |- _ => rewrite <- HR end. rewrite ?Z.add_0_r.
  eapply T_AX; [exact HG | exact Hin | lia].
Qed.
Lemma check_SAurun_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SAurun kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_SAurun h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E. unfold c_nstop in *. negs.
  eapply T_SAu_run; [exact HG | exact Hin | assumption | lia | lia].
Qed.
Lemma check_SAustep_sound : forall E M kn st h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SAustep kn st h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn st h g Hkn HG. prep check_SAustep h g HG.
  destruct (sstep_check kn hb hl hx hE gE true st) as [d|] eqn:Hst; [|rewrite andb_false_r in H; discriminate]. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  destruct (sstep_check_sound E M kn hb hl hx hE gE true st d bs Hkn ltac:(lia) ltac:(lia) Hin Hst) as (Ec' & SEM & HE).
  rewrite (HE eq_refl). linsubst E. rewrite (Z.add_assoc (uD E hx) d 1).
  eapply T_SAu_step; [exact HG | exact Hin | lia | exact SEM | lia].
Qed.
Lemma check_WAq_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WAq kn h g = true ->
  GP1 71 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WAq h g HG. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E. unfold c_q in *.
  eapply T_WAq; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia | lia | lia |].
  rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia].
Qed.

Lemma check_SW_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 73 (map (APS.uE E) h) M -> check_SW kn h g = true ->
  GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_SW h g HG. sem E M kn Hkn.
  destruct (s1s_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E. unfold c_q in *.
  apply T_AW; [|lia]. eapply T_SA; [exact HG | exact Hin | apply Z.eqb_eq; assumption | lia].
Qed.
Lemma check_P0W_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 75 (map (APS.uE E) h) M -> check_P0W kn h g = true ->
  GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_P0W h g HG. sem E M kn Hkn.
  destruct (s1p0_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  pose proof HG as HG'. destruct HG' as (_ & _ & _ & bs' & out & J0 & i0 & Hin' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hip & Hp1 & _).
  balls E M kn Hkn Hin. linsubst E. unfold c_npcont in *. negs.
  apply T_AW; [|lia]. eapply T_P0A_stop; [exact HG | exact Hin | assumption].
Qed.
Lemma check_P0X_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 75 (map (APS.uE E) h) M -> check_P0X kn h g = true ->
  GP1 76 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep5 check_P0X h g HG. sem E M kn Hkn.
  destruct (s1p0_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & HC & bs & Hin). pose proof W as W'. unfold wfctx in W'.
  balls E M kn Hkn Hin. unfold c_pcont in *.
  match goal with HR : rc_ok kn _ _ _ _ _ = true |- _ => apply (rc_ok_sound E M kn) in HR; [|exact Hkn|right; exact HF] end.
  eapply (X_concl E M kn hb hl ha gn grc _ (uD E hC + 1) bs Hkn W ltac:(lia) Hin ltac:(assumption) ltac:(lia)).
  match goal with HR : uD E grc = _ |- _ => rewrite HR end.
  match goal with HR : uD E hC + 1 = uD E gn |- _ => rewrite <- HR end.
  pose proof (T_P0A_end M _ _ _ _ _ _ _ bs HG Hin ltac:(assumption) ltac:(lia)) as HA.
  assert (W1 : wfctx (uD E hb) (uD E hl) (uD E ha) (uD E hC + 1)) by (destruct HA as (W1 & _); exact W1).
  eapply T_AX; [exact HA | exact Hin | lia].
Qed.
Lemma check_WAW_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 72 (map (APS.uE E) h) M -> check_WAW kn h g = true ->
  GP1 72 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG. prep check_WAW h g HG. sem E M kn Hkn.
  destruct (s1w_ctx _ _ _ _ _ _ _ _ HG) as (W & HF & bs & Hin). unfold wfctx in W. fsub E M kn Hkn HF.
  balls E M kn Hkn Hin. linsubst E. unfold c_op in *.
  assert (REC : u32_at M (uD E ha + 4 * uD E hC) = Some (uD E hx)).
  { rewrite <- (Z.add_0_r (_ + 4 * _)). eapply idx_is_sound; [exact Hkn | eassumption | lia]. }
  apply T_AW; [|lia].
  match goal with Hop : S1M.is_op _ = true |- _ =>
    eapply T_WA; [exact HG | exact Hin | exact (op_not_space _ Hop) | intros X; rewrite X in Hop; discriminate Hop | left; exact Hop | lia | lia | exact REC] end.
Qed.

Lemma check_Xok_sound : forall E M kn h g, know_ok SEGS E M kn -> GP1 76 (map (APS.uE E) h) M -> check_Xok kn h g = true ->
  GP1 60 (map (APS.uE E) g) M.
Proof.
  intros E M kn h g Hkn HG H. unfold check_Xok in H.
  destruct h as [|hb [|hl [|ha [|hn [|hrc [|? ?]]]]]]; try discriminate. destruct g as [|gb [|gl [|ga [|gn [|? ?]]]]]; try discriminate.
  cbn [GP1 Nat.eqb map S2G.GP2] in HG |- *. unfold APS.uE in *. sem E M kn Hkn.
  destruct HG as (Hl & Hb & Ha & Hn & Hn0 & Hnl & bs & Hin & Hrc & Hok). apply Hok.
  match goal with HR : bv_unsigned (edenot E hrc) + 0 = _ |- _ => rewrite uE_lit in HR by zlit; unfold S1M.SUCCESS; lia end.
Qed.
Lemma check_XF_sound : forall E M kn h K, know_ok SEGS E M kn -> GP1 76 (map (APS.uE E) h) M -> check_XF kn h K = true ->
  kentry_ok SEGS E M K.
Proof.
  intros E M kn h K Hkn HG H. unfold check_XF in H.
  destruct h as [|hb [|hl [|ha [|hn [|hrc [|? ?]]]]]]; try discriminate. destruct K as [| | | | |e lo hi| | | |]; try discriminate.
  cbn [GP1 Nat.eqb map] in HG. unfold APS.uE in *.
  destruct HG as (Hl & Hb & Ha & Hn & Hn0 & Hnl & bs & Hin & Hrc & Hok).
  bsplit H. repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G end.
  pose proof (S2G.hiZ_sound SEGS E M kn hl Hkn) as HL. cbn [kentry_ok].
  match goal with HA : (_ || _)%bool = true |- _ => apply Bool.orb_prop in HA as [HX|HX]; bsplit HX end.
  - match goal with HE : expr_eqb e hn = true |- _ => apply expr_eqb_eq in HE; subst e end.
    match goal with HA : (_ || _)%bool = true |- _ => apply Bool.orb_prop in HA as [HY|HY]; bsplit HY end.
    + apply Z.leb_le in HY. lia.
    + repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G end. sem E M kn Hkn.
      match goal with HR : bv_unsigned (edenot E hrc) + 0 = _ |- _ => rewrite uE_lit in HR by zlit end.
      assert (HS : S2G.p_s1ok SEGS [uD E hb; uD E hl; uD E ha; uD E hn] M) by (apply Hok; unfold S1M.SUCCESS; lia).
      destruct HS as (_ & _ & _ & Hn1 & _). lia.
  - match goal with HE : expr_eqb e _ = true |- _ => apply expr_eqb_eq in HE; subst e end.
    repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G end.
    cbn [edenot]. rewrite u_sub64. pose proof (u64_range (edenot E hn)). rewrite Z.mod_small by (unfold two64 in *; lia). lia.
Qed.

Theorem vc_check_sound : forall r c, vc_check r c = true -> APS.vc_holds SEGS GP1 c.
Proof.
  intros r c H. unfold APS.vc_holds. intros E M Hk Hh.
  assert (WA : forall i hid gid chk (SND : forall E M kn h g, know_ok SEGS E M kn -> GP1 hid (map (APS.uE E) h) M -> chk kn h g = true -> GP1 gid (map (APS.uE E) g) M),
            with_atoms c i hid gid chk = true ->
            match vc_concl c with VCAtom g => APS.gholds GP1 E M g | VCFact K => kentry_ok SEGS E M K end).
  { intros i hid gid chk SND HW. unfold with_atoms in HW.
    destruct (hyp_at c i hid) as [h|] eqn:Hh1; [|discriminate]. destruct (concl_at c gid) as [g|] eqn:Hg1; [|discriminate].
    eapply concl_at_sound; [exact Hg1|]. eapply SND; [exact Hk | eapply hyp_at_sound; [exact Hh | exact Hh1] | exact HW]. }
  destruct r; cbn [vc_check] in H.
  - discriminate.
  - destruct (vc_concl c) as [g|K]; [|discriminate]. destruct (nth_error (vc_hyps c) i) as [g'|] eqn:Hi; [|discriminate].
    apply APS.gatom_eqb_eq in H. subst g'. exact (proj1 (Forall_forall _ _) Hh g (nth_error_In _ _ Hi)).
  - destruct (bset (vc_kn c) v) as [|? ?] eqn:Hb; [|discriminate]. exfalso.
    pose proof (bset_sound E M (vc_kn c) v Hk) as X. rewrite Hb in X. exact X.
  - destruct (concl_at c 71) as [g|] eqn:Hg1; [|discriminate]. eapply concl_at_sound; [exact Hg1|]. eapply check_init_sound; [exact Hk | exact H].
  - exact (WA _ _ _ _ check_AW_sound H).
  - exact (WA _ _ _ _ check_WW_sound H).
  - exact (WA _ _ _ _ check_WS_sound H).
  - exact (WA _ _ _ _ check_WP_sound H).
  - exact (WA _ _ _ _ check_WA_sound H).
  - exact (WA _ _ _ _ check_WX_sound H).
  - exact (WA _ _ _ _ check_Srun_sound H).
  - exact (WA _ _ _ _ (fun E M kn => check_Sstep_sound E M kn st) H).
  - exact (WA _ _ _ _ check_SA_sound H).
  - exact (WA _ _ _ _ check_SXq_sound H).
  - exact (WA _ _ _ _ check_SXrun_sound H).
  - exact (WA _ _ _ _ (fun E M kn => check_SXstep_sound E M kn st) H).
  - exact (WA _ _ _ _ check_PP_sound H).
  - exact (WA _ _ _ _ check_PA_sound H).
  - exact (WA _ _ _ _ check_PX_sound H).
  - destruct (concl_at c 72) as [g|] eqn:Hg1; [|discriminate]. eapply concl_at_sound; [exact Hg1|]. eapply check_initW_sound; [exact Hk | exact H].
  - exact (WA _ _ _ _ check_WP0_sound H).
  - exact (WA _ _ _ _ check_P0P0_sound H).
  - exact (WA _ _ _ _ check_P0A_sound H).
  - exact (WA _ _ _ _ check_AX_sound H).
  - exact (WA _ _ _ _ check_SAurun_sound H).
  - exact (WA _ _ _ _ (fun E M kn => check_SAustep_sound E M kn st) H).
  - exact (WA _ _ _ _ check_WAq_sound H).
  - exact (WA _ _ _ _ check_SW_sound H).
  - exact (WA _ _ _ _ check_P0W_sound H).
  - exact (WA _ _ _ _ check_P0X_sound H).
  - exact (WA _ _ _ _ check_WAW_sound H).
  - exact (WA _ _ _ _ check_Xok_sound H).
  - destruct (hyp_at c i 76) as [h|] eqn:Hh1; [|discriminate]. destruct (vc_concl c) as [g|K]; [discriminate|].
    eapply check_XF_sound; [exact Hk | eapply hyp_at_sound; [exact Hh | exact Hh1] | exact H].
Qed.
Theorem vcs_check_sound : forall rs cs, vcs_check rs cs = true -> Forall (APS.vc_holds SEGS GP1) cs.
Proof.
  intros rs. induction rs as [|r rs IH]; intros [|c cs] H; cbn [vcs_check] in H; try discriminate; [constructor|].
  apply andb_prop in H as [Hc Hr]. constructor; [exact (vc_check_sound r c Hc) | exact (IH cs Hr)].
Qed.
End CheckSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition id_other (id : nat) : bool :=
  negb (Nat.eqb id 71 || Nat.eqb id 72 || Nat.eqb id 73 || Nat.eqb id 74 || Nat.eqb id 75 || Nat.eqb id 76)%bool.
Lemma GP1_other : forall id vs M, id_other id = true -> GP1 id vs M = S2G.GP2 SEGS id vs M.
Proof.
  intros id vs M H. unfold id_other in H. unfold GP1.
  repeat match goal with |- context [if Nat.eqb id ?n then _ else _] => destruct (Nat.eqb id n); [discriminate|cbn [orb] in H] end. reflexivity.
Qed.
Definition vc_other (c : vc) : bool :=
  forallb (fun g => id_other (g_id g)) (vc_hyps c) && match vc_concl c with VCAtom g => id_other (g_id g) | VCFact _ => true end.
Lemma vc_other_transfer : forall c, vc_other c = true -> APS.vc_holds SEGS (S2G.GP2 SEGS) c -> APS.vc_holds SEGS GP1 c.
Proof.
  intros c H HV. unfold vc_other in H. apply andb_prop in H as [Hh Hc]. unfold APS.vc_holds in *. intros E M Hk Hhyps.
  assert (H2 : Forall (APS.gholds (S2G.GP2 SEGS) E M) (vc_hyps c)).
  { apply Forall_forall. intros g Hg. pose proof (proj1 (Forall_forall _ _) Hhyps g Hg) as X.
    unfold APS.gholds in *. rewrite <- GP1_other; [exact X|]. exact (proj1 (forallb_forall _ _) Hh g Hg). }
  pose proof (HV E M Hk H2) as R. destruct (vc_concl c) as [g|K]; [|exact R].
  unfold APS.gholds in *. rewrite GP1_other; [exact R | exact Hc].
Qed.
Theorem gp2_vcs_transfer : forall L, forallb vc_other L = true -> Forall (APS.vc_holds SEGS (S2G.GP2 SEGS)) L -> Forall (APS.vc_holds SEGS GP1) L.
Proof.
  intros L H HL. apply Forall_forall. intros c Hc. apply vc_other_transfer; [exact (proj1 (forallb_forall _ _) H c Hc) | exact (proj1 (Forall_forall _ _) HL c Hc)].
Qed.

End WithSegs.
End S1G.
