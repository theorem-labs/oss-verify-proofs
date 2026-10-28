(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BStoreOk.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition in_rng (a base : word) (len : Z) : Prop :=
  (bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.

Definition in_rngb (a base : word) (len : Z) : bool :=
  (Z.leb (bv_unsigned base) (bv_unsigned a) && Z.ltb (bv_unsigned a) (bv_unsigned base + len))%bool.

Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
  match rs with
  | [] => True
  | (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
  end.

Lemma outside_app : forall a rs1 rs2, outside a (rs1 ++ rs2) <-> outside a rs1 /\ outside a rs2.
Proof.
  intros a rs1 rs2. induction rs1 as [|[b n] rs1 IH]; cbn; tauto.
Qed.

Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
  (forall a, outside a rs -> mem' a = mem a) /\ mem_grows mem mem'.

Lemma frame_mod_refl : forall mem rs, frame_mod mem mem rs.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma frame_mod_weaken : forall mem mem' rs rs',
  (forall a, outside a rs' -> outside a rs) -> frame_mod mem mem' rs -> frame_mod mem mem' rs'.
Proof.
  intros mem mem' rs rs' Hw [He Hg]. split; [|exact Hg]. intros a Ha. apply He, Hw, Ha.
Qed.

Lemma frame_mod_trans : forall m1 m2 m3 rs1 rs2,
  frame_mod m1 m2 rs1 -> frame_mod m2 m3 rs2 -> frame_mod m1 m3 (rs1 ++ rs2).
Proof.
  intros m1 m2 m3 rs1 rs2 [E1 G1] [E2 G2]. split.
  - intros a Ha. apply outside_app in Ha as [H1 H2]. rewrite (E2 a H2). apply E1, H1.
  - eapply mem_grows_trans; eassumption.
Qed.

Lemma frame_mod_trans_same : forall m1 m2 m3 rs,
  frame_mod m1 m2 rs -> frame_mod m2 m3 rs -> frame_mod m1 m3 rs.
Proof.
  intros m1 m2 m3 rs H1 H2. eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
  intros a Ha. apply outside_app. tauto.
Qed.

Lemma wbytes_outside : forall bs m (base a : word),
  ~ in_rng a base (Z.of_nat (length bs)) ->
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbytes m base bs a = m a.
Proof.
  intros bs m base a Hn Hb. unfold in_rng in Hn.
  destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned base)) as [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above. lia.
Qed.

Lemma frame_mod_wbytes : forall m base bs,
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  frame_mod m (wbytes m base bs) [(base, Z.of_nat (length bs))].
Proof.
  intros m base bs Hb. split.
  - intros a [Ha _]. apply wbytes_outside; assumption.
  - apply wbytes_grows.
Qed.

Lemma frame_mod_store_ok : forall segs mem mem' rs a n,
  frame_mod mem mem' rs -> store_ok segs mem a n = true -> store_ok segs mem' a n = true.
Proof. intros segs mem mem' rs a n [_ Hg] H. eapply store_ok_mono; eassumption. Qed.

Lemma frame_mod_byte : forall mem mem' rs a,
  frame_mod mem mem' rs -> outside a rs -> mem' a = mem a.
Proof. intros mem mem' rs a [He _] Ha. apply He, Ha. Qed.

Lemma frame_mod_rdn : forall segs mem mem' rs n (a : word),
  frame_mod mem mem' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs mem' a n = rdn segs mem a n.
Proof.
  intros segs mem mem' rs n. induction n as [|n IH]; intros a Hf Ho Hb; [reflexivity|].
  cbn [rdn]. pose proof (u64_range a).
  assert (Ha : mem' a = mem a).
  { pose proof (Ho 0%Z ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
    eapply frame_mod_byte; eassumption. }
  rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Ha1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1) Hf).
    + reflexivity.
    + intros i Hi. rewrite Ha1. replace (bv_unsigned a + 1 + i)%Z with (bv_unsigned a + (1 + i))%Z by lia.
      apply Ho. lia.
    + rewrite Ha1. lia.
Qed.
