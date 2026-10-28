(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BStoreOk BAgentLib BFrame BSymExec2 BSymExec2Sound BSymRun BSymDrive BMemSplit BLibTail BainDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BImage.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BSegs BsPrintfFirst.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import BSymExec2.SX2. Import BSymExec2Sound.SX2S.
Import BPropExec.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation rsegs := asegs (only parsing).

Lemma seg_rom_same : BLPropExec.seg_rom = BPropExec.seg_rom.
Proof. reflexivity. Qed.

Lemma getr_same : BLPropExec.getr = BPropExec.getr.
Proof. reflexivity. Qed.

Lemma wbytes_eq : forall bs m a, wbytes m a bs = write_to_mem m a bs.
Proof. induction bs as [|b bs IH]; intros m a; cbn; [reflexivity | apply IH]. Qed.

Lemma wa_eq : forall z, wa z = Z_to_bv 64 z. Proof. reflexivity. Qed.

Definition ivls (rs : list (word * Z)) : list ivl := map (fun r => (bv_unsigned (fst r), bv_unsigned (fst r) + snd r)) rs.

Lemma outside_ivls : forall rs (x : word), BLFrame.outside (ivls rs) (bv_unsigned x) -> BFrame.outside x rs.
Proof.
  induction rs as [|[b n] rs IH]; intros x H; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [|apply IH; exact H2]. unfold in_rng. lia.
Qed.

Lemma frame_mod_munch : forall m m' rs, frame_mod m m' rs -> munch (ivls rs) m m'.
Proof. intros m m' rs [H _] x Hx. apply H. apply outside_ivls. exact Hx. Qed.

Lemma store_ok_of_wview : forall m (n : nat) (a : word),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64) ->
  (forall i, 0 <= i < Z.of_nat n -> wview RSEGS m (Z_to_bv 64 (bv_unsigned a + i)) <> None) ->
  store_ok RSEGS m a n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hn Hw; [reflexivity|].
  cbn [store_ok]. pose proof (u64_range a) as Ha.
  assert (W0 : wview RSEGS m a <> None).
  { pose proof (Hw 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0. }
  destruct (wview RSEGS m a); [|contradiction].
  apply IH; [rewrite u_add1 by lia; lia|]. intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hw. lia.
Qed.

Lemma wr_at_store_ok : forall m A n (k : Z) (j : nat),
  wr_at rsegs m A n -> 0 <= k -> k + Z.of_nat j <= n -> A + n < 2 ^ 64 ->
  store_ok RSEGS m (Z_to_bv 64 (A + k)) j = true.
Proof.
  intros m A n k j (H1 & H2 & H) Hk Hj HAn. apply store_ok_of_wview; [rewrite u_small by lia; lia|].
  intros i Hi. rewrite u_small by lia. rewrite <- wa_eq. replace (A + k + i) with (A + (k + i)) by lia. apply H. lia.
Qed.

Lemma outside_of_disjoint : forall (x : word) (rs : list (word * Z)),
  (forall r, In r rs -> bv_unsigned x < bv_unsigned (fst r) \/ bv_unsigned (fst r) + snd r <= bv_unsigned x) ->
  BFrame.outside x rs.
Proof.
  intros x rs H. induction rs as [|[r n] rs IH]; [exact I|]. cbn. split.
  - pose proof (H (r, n) (or_introl eq_refl)) as H1. cbn [fst snd] in H1. unfold in_rng. lia.
  - apply IH. intros r' Hr'. apply H. right. exact Hr'.
Qed.

Definition cells_agree (mem mem' : word -> option byte) (cs : list (Z * nat * Z)) : Prop :=
  Forall (fun c => match c with (a, w, _) =>
    forall i, (a <= i < a + Z.of_nat w)%Z -> mem' (Z_to_bv 64 i) = mem (Z_to_bv 64 i) end) cs.

Lemma rdn_wbytes_out : forall m (wad : word) bs (a : word) n v,
  rdn RSEGS m a n = Some v ->
  bv_unsigned wad + Z.of_nat (length bs) <= 2 ^ 64 -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned wad \/ bv_unsigned wad + Z.of_nat (length bs) <= bv_unsigned a) ->
  rdn RSEGS (wbytes m wad bs) a n = Some v.
Proof.
  intros m wad bs a n v Hr H1 H2 Hd. rewrite (rdn_ext RSEGS n (wbytes m wad bs) m a); [exact Hr | exact H2 |].
  intros x Hx. apply wbytes_outside; lia.
Qed.

