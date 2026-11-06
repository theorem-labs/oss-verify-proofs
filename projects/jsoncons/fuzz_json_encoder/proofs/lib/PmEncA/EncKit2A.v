(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core AxSymExec3 AxSymExec3Sound AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EK2A.
Import PMES.
Abbreviation mem := (word -> option byte).
Abbreviation agree := (L5C.agree_on).

Section K.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.

Lemma stack_at_head : forall (M M' : mem) V c c' r b capb,
  0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> agree M M' (V + O_STACK) 24 ->
  0 <= b -> b + capb <= 2 ^ 64 -> agree M M' b (32 * depth r) -> PMESA.ctx_at L M' (b + 32 * depth r) c' ->
  PMESA.stack_at L M V (c :: r) b capb -> PMESA.stack_at L M' V (c' :: r) b capb.
Proof.
  intros M M' V c c' r b capb HV HV2 Hag Hb Hb2 Hlow Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold PMESA.stack_at, ENC_SIZE, O_STACK in *.
  rewrite EKA.depth_cons in *.
  split; [apply (EKA.u64_agree L M M' _ _); [apply (EKA.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S1]|].
  split; [apply (EKA.u64_agree L M M' _ _); [apply (EKA.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S2]|].
  split; [apply (EKA.u64_agree L M M' _ _); [apply (EKA.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (Datatypes.S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (Datatypes.S (length r) - 1 - i)%nat with (Datatypes.S (length r - 1 - i))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EKA.ctx_at_agree L M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EKA.agree_sub M M' _ _ _ _ Hlow); lia | exact S6].
Qed.

(* [comment removed for export] *)
Lemma enc_invA_head : forall (M M' : mem) V S2 g c c' r,
  g_es g = c :: r ->
  agree M M' V O_COLUMN -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 -> agree M M' S2 24 ->
  (forall b, In b (PML.srep_blocks (g_rep g)) -> agree M M' (fst b) (snd b) /\ EKA.shagree M M' (fst b) (snd b / 8)) ->
  agree M M' (g_sb g) (32 * depth r) -> EKA.shagree M M' (g_sb g) (g_scap g / 8) -> PMESA.ctx_at L M' (g_sb g + 32 * depth r) c' ->
  PMESA.enc_invA L IC EC M V S2 g -> PMESA.enc_invA L IC EC M' V S2 (EG (c' :: r) (g_len g) (g_rep g) (g_sb g) (g_scap g)).
Proof.
  intros M M' V S2 g c c' r Hes A1 A2 Hcol A3 HB Hlow Hsh Hhead (I1 & I2 & I3 & I4 & I5 & I6 & (R1 & R2 & R3 & R4 & RB)).
  assert (HV : 0 <= V) by exact R1. assert (HV2 : V + ENC_SIZE <= 2 ^ 64) by lia. assert (HS : 0 <= S2) by exact R3. assert (HS2 : S2 + 24 <= 2 ^ 64) by lia.
  rewrite Hes in I1, I2, I3, I6. unfold PMESA.enc_invA. cbn [g_es g_len g_rep g_sb g_scap]. rewrite EKA.depth_cons in *.
  assert (STB : g_scap g <> 0 -> In (g_sb g, g_scap g) (g_lbv g)).
  { intros Hne. unfold g_lbv, stack_blocks. apply in_or_app. right. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
  split; [exact (EKA.enc_obj_agree L IC EC M M' V S2 _ HV HV2 A1 A2 Hcol I1)|].
  split; [|split; [|split; [|split; [exact I5 | split; [exact I6 | exact (conj R1 (conj R2 (conj R3 (conj R4 RB))))]]]]].
  - apply (stack_at_head M M' V c c' r _ _ HV HV2); [unfold O_STACK, O_COLUMN in *; apply (EKA.agree_sub _ _ _ _ _ _ A1); lia | | | exact Hlow | exact Hhead | exact I2].
    + destruct I2 as (_ & _ & _ & _ & S5 & _). destruct S5 as [[E0 ->]|(k & Hk & Ek)]; [lia|]. destruct (RB _ (STB ltac:(pose proof (Z.pow_pos_nonneg 2 k); lia))) as (B0 & _). exact B0.
    + destruct I2 as (_ & _ & _ & _ & S5 & _). destruct S5 as [[E0 ->]|(k & Hk & Ek)]; [lia|]. destruct (RB _ (STB ltac:(pose proof (Z.pow_pos_nonneg 2 k); lia))) as (B0 & _ & _ & B3). cbn [fst snd] in B3. lia.
  - (* [comment removed for export] *)
    unfold PMESA.stack_sh in *. rewrite EKA.depth_cons in *. destruct I3 as [E0|SC]; [left; exact E0|].
    destruct (Z.eq_dec (g_scap g) 0) as [E0|Hne]; [left; exact E0|]. right.
    destruct I2 as (_ & _ & _ & S4 & S5 & _). rewrite EKA.depth_cons in S4.
    destruct (RB _ (STB Hne)) as (B0 & B1 & B2 & B3). cbn [fst snd] in *.
    assert (C8 : g_scap g mod 8 = 0) by (destruct S5 as [[E _]|(k & Hk & ->)]; [contradiction | apply EKA.mul32_mod8; lia]).
    assert (B8 : g_sb g mod 8 = 0) by (apply Z.mod_divide in B1; [|lia]; destruct B1 as [q ->]; replace (q * 16) with ((q * 2) * 8) by lia; apply Z_mod_mult).
    apply (CL5A.shadow_cont_same M M' (g_sb g) (g_scap g) (32 * (depth r + 1)) ltac:(pose proof (EKA.depth_nonneg r); lia) B8); [|exact SC].
    intros a Ha. unfold in_shadow_of, HeapIfaceA.S in Ha.
    apply Z.mod_divide in B8; [|lia]. destruct B8 as [q Hq]. apply Z.mod_divide in C8; [|lia]. destruct C8 as [r8 Hr].
    assert (E1 : g_sb g / 8 = q) by (rewrite Hq; apply Z.div_mul; lia).
    assert (E2 : (g_sb g + g_scap g - 1) / 8 = q + r8 - 1) by (rewrite Hq, Hr; replace (q * 8 + r8 * 8 - 1) with (7 + (q + r8 - 1) * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    assert (E3 : g_scap g / 8 = r8) by (rewrite Hr; apply Z.div_mul; lia).
    rewrite E1, E2 in Ha. replace a with (HeapIfaceA.S (g_sb g) + (a - HeapIfaceA.S (g_sb g))) by lia. apply Hsh. unfold HeapIfaceA.S. rewrite E1, E3. lia.
  - apply (EKA.sink_at_agree L M M' S2 _ HS HS2 A3); [|exact I4].
    destruct (g_rep g) as [s|cap p s] eqn:Er; [exact I|].
    assert (Hin : In (p, cap) (g_lbv g)) by (unfold g_lbv; rewrite Er; cbn [PML.srep_blocks]; left; reflexivity).
    destruct (RB _ Hin) as (B0 & _ & _ & B3). cbn [fst snd] in *. destruct (HB (p, cap) ltac:(cbn [PML.srep_blocks]; left; reflexivity)) as [HA HSH]. cbn [fst snd] in HA, HSH.
    split; [lia|]. split; [lia|]. split; [exact HA | exact HSH].
Qed.
End K.

(* [comment removed for export] *)
Lemma u64_of_defined : forall segs (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof.
  intros segs M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn segs M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (PropExec.bytes_le_to_Z_nonneg bs) as N0. pose proof (AX2S.bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
End EK2A.
