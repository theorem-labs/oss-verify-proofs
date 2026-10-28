(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EK2.
Import PMES.
Abbreviation mem := (word -> option byte).

Lemma depth_cons : forall (c : ectx) r, depth (c :: r) = depth r + 1.
Proof. intros. unfold depth. cbn [length]. lia. Qed.

Lemma stack_at_head : forall (M M' : mem) V c c' r b capb,
  0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> L5C.agree_on M M' (V + O_STACK) 24 ->
  0 <= b -> b + capb <= 2 ^ 64 -> L5C.agree_on M M' b (32 * depth r) -> ctx_at M' (b + 32 * depth r) c' ->
  stack_at M V (c :: r) b capb -> stack_at M' V (c' :: r) b capb.
Proof.
  intros M M' V c c' r b capb HV HV2 Hag Hb Hb2 Hlow Hhead (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, ENC_SIZE, O_STACK in *.
  rewrite depth_cons in *.
  split; [apply (EK.u64_agree M M' _ _); [apply (EK.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S1]|].
  split; [apply (EK.u64_agree M M' _ _); [apply (EK.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S2]|].
  split; [apply (EK.u64_agree M M' _ _); [apply (EK.agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|].
  intros i Hi. cbn [length] in Hi |- *. assert (D0 : 0 <= depth r) by (unfold depth; lia).
  destruct (Nat.eq_dec i (length r)) as [->|Hne].
  - replace (S (length r) - 1 - length r)%nat with 0%nat by lia. cbn [nth]. exact Hhead.
  - specialize (S6 i ltac:(cbn [length]; lia)). cbn [length] in S6.
    replace (S (length r) - 1 - i)%nat with (S (length r - 1 - i))%nat in S6 |- * by lia. cbn [nth] in S6 |- *.
    assert (Hd : Z.of_nat i < depth r) by (unfold depth; lia).
    apply (EK.ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (EK.agree_sub M M' _ _ _ _ Hlow); lia | exact S6].
Qed.

Lemma enc_inv_head : forall (M M' : mem) V S2 g c c' r,
  g_es g = c :: r -> 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= S2 -> S2 + 24 <= 2 ^ 64 ->
  L5C.agree_on M M' V O_COLUMN -> L5C.agree_on M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 -> L5C.agree_on M M' S2 24 ->
  (forall b, In b (PML.srep_blocks (g_rep g)) -> 0 <= fst b /\ fst b + snd b <= 2 ^ 64 /\ L5C.agree_on M M' (fst b) (snd b)) ->
  0 <= g_sb g -> g_sb g + g_scap g <= 2 ^ 64 -> L5C.agree_on M M' (g_sb g) (32 * depth r) -> ctx_at M' (g_sb g + 32 * depth r) c' ->
  enc_inv M V S2 g -> enc_inv M' V S2 (EG (c' :: r) (g_len g) (g_rep g) (g_sb g) (g_scap g)).
Proof.
  intros M M' V S2 g c c' r Hes HV HV2 HS HS2 A1 A2 Hcol A3 HB B0 B1 Hlow Hhead (I1 & I2 & I3 & I4 & I5).
  rewrite Hes in I1, I2, I5. unfold enc_inv. cbn [g_es g_len g_rep g_sb g_scap]. rewrite depth_cons in *.
  split; [exact (EK.enc_obj_agree M M' V S2 _ HV HV2 A1 A2 Hcol I1)|].
  split; [|split; [|split; assumption]].
  - apply (stack_at_head M M' V c c' r _ _ HV HV2); [unfold O_STACK, O_COLUMN in *; apply (EK.agree_sub _ _ _ _ _ _ A1); lia | exact B0 | exact B1 | exact Hlow | exact Hhead | exact I2].
  - apply (EK.sink_at_agree M M' S2 _ HS HS2 A3); [|exact I3].
    destruct (g_rep g) as [s|cap p s] eqn:Er; [exact I|]. apply (HB (p, cap)). cbn [PML.srep_blocks]. left. reflexivity.
Qed.
End EK2.
