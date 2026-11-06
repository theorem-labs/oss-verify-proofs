(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AsanPlanSoundSums L5Defs L5Core PmModel PmModelFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCG.
Section G.
Variable segs : list Segment. Context {bmK : BMode}.

Lemma rdn_some (M : word -> option byte) : forall (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn segs M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn D. { exists []. split; reflexivity. }
  cbn [rdn]. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
  destruct (M (Z_to_bv 64 a)) as [b0|] eqn:E0; [|exfalso; apply D0; reflexivity].
  rewrite (L5C.add1_lit a).
  destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & E & Hl).
  { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply D. lia. }
  rewrite E. exists (b0 :: bs). split; [reflexivity| cbn; rewrite Hl; reflexivity].
Qed.

Lemma u64_of_defined (M : word -> option byte) a : 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 ->
  exists w, 0 <= w < 2 ^ 64 /\ L5.u64_at segs M a w.
Proof.
  intros Ha Hn D. destruct (rdn_some M 8%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u64_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.

Lemma u8_of_defined (M : word -> option byte) a : 0 <= a -> a + 1 <= 2 ^ 64 -> L5.defined M a 1 -> exists b, 0 <= b < 256 /\ L5.u8_at segs M a b.
Proof.
  intros Ha Hn D. destruct (rdn_some M 1%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  destruct bs as [|b0 [|]]; cbn in Hl; try discriminate. exists (bv_unsigned b0).
  pose proof (bv_unsigned_in_range 8 b0) as B. change (bv_modulus 8) with 256 in B. split; [exact B|].
  unfold L5.u8_at. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma u8_at_fun (M : word -> option byte) a x y : L5.u8_at segs M a x -> L5.u8_at segs M a y -> x mod 256 = y mod 256.
Proof.
  unfold L5.u8_at. intros Hx Hy. rewrite Hx in Hy.
  assert (Hb : Z_to_bv 8 x = Z_to_bv 8 y) by congruence.
  assert (E : bv_unsigned (Z_to_bv 8 x) = bv_unsigned (Z_to_bv 8 y)) by (rewrite Hb; reflexivity).
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E.
Qed.

Lemma u8_of_u64_eq (M : word -> option byte) a w v : 0 <= w < 2 ^ 64 -> 0 <= v < 256 -> L5.u64_at segs M a w -> L5.u8_at segs M a v ->
  w mod 256 = v.
Proof.
  intros Hw Hv H8 H1. pose proof (PMF.u8_of_u64 segs M a w Hw H8) as H1'. pose proof (u8_at_fun M a _ _ H1' H1) as E.
  rewrite Z.mod_mod in E by lia. rewrite E. apply Z.mod_small. lia.
Qed.

Lemma rdn_zeros (M : word -> option byte) : forall (k : nat) a, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) -> rdn segs M (Z_to_bv 64 a) k = Some (repeat (Z_to_bv 8 0) k).
Proof.
  induction k as [|k IH]; intros a Ha Hk Z0. { reflexivity. }
  cbn [rdn repeat]. pose proof (Z0 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. rewrite E0.
  rewrite (L5C.add1_lit a). rewrite (IH (a + 1)); [reflexivity| lia| lia|].
  intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply Z0. lia.
Qed.

Lemma u64_of_zeros (M : word -> option byte) a : PM.zeros_at M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at segs M a 0.
Proof.
  intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
  apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.
Lemma u32_of_zeros (M : word -> option byte) a : PM.zeros_at M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at segs M a 0.
Proof.
  intros Z8 Ha Hn. unfold L5.u32_at. change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 4).
  apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.
Lemma u8_of_zeros (M : word -> option byte) a : PM.zeros_at M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at segs M a 0.
Proof.
  intros Z8 Ha Hn. unfold L5.u8_at. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0 : byte) 1).
  apply rdn_zeros; [lia| cbn; lia|]. intros i Hi. apply Z8. cbn in Hi. lia.
Qed.

Lemma rdn_img (M : word -> option byte) lo hi a (k : nat) : L5.img_clear M lo hi -> 0 <= a -> lo <= a -> a + Z.of_nat k <= hi -> hi <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 a) k = rdn segs (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros IC Ha Hlo Hk Hhi. apply (L5C.rdn_agree segs (fun _ => None) M k a Ha ltac:(lia)). intros i Hi. apply IC. lia.
Qed.

Lemma lw_run (fx : FPState) R M (pc : Z) (W : bv 32) (rd rs : bv 5) (imm : bv 12) (a0 : Z) (bs : list byte) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rd <> 0%bv -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  getr R rs = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> 0 <= a0 + bv_signed imm < 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (a0 + bv_signed imm)) 4 = Some bs -> length bs = 4%nat ->
  exists v, msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx (regupd R rd v) (Z_to_bv 64 (pc + 4)) M (seg_rom segs)).
Proof.
  intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha RB Hl.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  exists (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))).
  eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_lw segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm bs (Z_to_bv 64 (bytes_le_to_Z bs)) HF HE HD).
  - rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
  - unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
  - rewrite L5.unsigned_lit by lia. reflexivity.
Qed.

Lemma lbu_img_run (fx : FPState) R M (pc : Z) (W : bv 32) (rd rs : bv 5) (imm : bv 12) (a0 : Z) (b : byte) :
  fetch_word segs (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rd <> 0%bv -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  getr R rs = Z_to_bv 64 a0 -> 0 <= a0 < 2 ^ 64 -> 0 <= a0 + bv_signed imm < 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (a0 + bv_signed imm)) 1 = Some [b] ->
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx (regupd R rd (Z_to_bv 64 (bv_unsigned b))) (Z_to_bv 64 (pc + 4)) M (seg_rom segs)).
Proof.
  intros HF HE HD Hrd Hpc Hpc4 Hrs Ha0 Ha RB.
  eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_lbu segs R (Z_to_bv 64 pc) M (seg_rom segs) W rd rs imm b HF HE HD).
  - rewrite (bv_eqb_neq rd 0%bv Hrd). f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
  - unfold v_addi. rewrite Hrs, L5.unsigned_lit by lia. exact RB.
Qed.
Lemma zeros_sub (M : word -> option byte) a n a' n' : PM.zeros_at M a n -> a <= a' -> a' + n' <= a + n -> PM.zeros_at M a' n'.
Proof. intros Z0 H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Z0. lia. Qed.
End G.

Lemma nodup_swap (a b : Z) (l : list Z) : NoDup (a :: b :: l) -> NoDup (b :: a :: l).
Proof.
  intros H. inversion H as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst.
  constructor.
  - intros E. inversion E as [|? ? ? E']; subst; [apply N1; constructor| apply N2; exact E'].
  - constructor; [intros E; apply N1; constructor; exact E| exact ND2].
Qed.
End PMCG.
