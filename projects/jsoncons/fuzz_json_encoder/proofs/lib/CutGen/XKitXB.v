(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module XKA.
Definition VIS : Z := 16384.
Definition VISD : Z := 8.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Definition lits_inside (IC : PMLA.consts) : Prop :=
  let lo := PMLA.LIT_LO IC in let hi := PMLA.LIT_HI IC in
  lo <= PMLA.LIT_NULL_S IC /\ PMLA.LIT_NULL_S IC + 16 <= hi /\ lo <= PMLA.LIT_NULL_G IC /\ PMLA.LIT_NULL_G IC + 2 <= hi /\
  lo <= PMLA.LIT_TRUE_S IC /\ PMLA.LIT_TRUE_S IC + 16 <= hi /\ lo <= PMLA.LIT_TRUE_G IC /\ PMLA.LIT_TRUE_G IC + 2 <= hi /\
  lo <= PMLA.LIT_FALSE_S IC /\ PMLA.LIT_FALSE_S IC + 16 <= hi /\ lo <= PMLA.LIT_FALSE_G IC /\ PMLA.LIT_FALSE_G IC + 2 <= hi /\ 0 <= lo /\ hi <= 2 ^ 64.
Lemma lits_inside_xasan : lits_inside PMLA.C_xasan.
Proof. unfold lits_inside, PMLA.LIT_LO, PMLA.LIT_HI. cbn. repeat split; lia. Qed.
Lemma lits_inside_xboth : lits_inside PMLA.C_xboth.
Proof. unfold lits_inside, PMLA.LIT_LO, PMLA.LIT_HI. cbn. repeat split; lia. Qed.

Lemma lit_ok_agree : forall segs (M M' : mem) S G txt len, 0 <= S -> S + 16 <= 2 ^ 64 -> 0 <= G -> G + 2 <= 2 ^ 64 ->
  (forall i, 0 <= i < 16 -> M' (Z_to_bv 64 (S + i)) = M (Z_to_bv 64 (S + i))) -> (forall i, 0 <= i < 2 -> M' (Z_to_bv 64 (G + i)) = M (Z_to_bv 64 (G + i))) ->
  PMLA.lit_ok segs M S G txt len -> PMLA.lit_ok segs M' S G txt len.
Proof.
  intros segs M M' S G txt len HS HS2 HG HG2 AS AG H. unfold PMLA.lit_ok, PMLA.u8, PMLA.u64 in *.
  assert (X8 : forall a v, 0 <= a - G < 2 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v).
  { intros a v Ha Hu. apply (CL5A.u8_same segs M M' a); [lia | lia | | exact Hu]. replace a with (G + (a - G)) by lia. apply AG. lia. }
  assert (X64 : forall a v, 0 <= a - S /\ a - S + 8 <= 16 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
  { intros a v Ha Hu. apply (CL5A.u64_same segs M M' a); [lia | lia | | exact Hu]. intros y Hy. replace y with (S + (y - S)) by lia. apply AS. lia. }
  destruct H as [(H1 & H2 & H3 & H4)|(H1 & H2 & H3 & H4)]; [left | right]; repeat split;
    first [apply X8; [lia | assumption] | apply X64; [lia | assumption] | replace (G + 1) with (G + 1) by lia; apply X8; [lia | assumption]].
Qed.
Lemma lits_ok_agree : forall segs IC (M M' : mem), lits_inside IC ->
  (forall a, PMLA.LIT_LO IC <= a < PMLA.LIT_HI IC -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMLA.lits_ok segs IC M -> PMLA.lits_ok segs IC M'.
Proof.
  intros segs IC M M' HI AG (H1 & H2 & H3). unfold lits_inside in HI. cbv zeta in HI.
  destruct HI as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
  split; [|split]; (eapply lit_ok_agree; [| | | | | |eassumption]); try (intros i Hi; apply AG; lia); lia.
Qed.

Section X.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Hypothesis ENC_AGREE : PMXA.enc_agreeP enc_invA.
Hypothesis LITS : lits_inside IC.
Variables V S2 : Z.

(* [comment removed for export] *)
Definition xinv (M : mem) (g : PMES.eghost) : Prop := enc_invA M V S2 g /\ PMLA.lits_ok (hl_segs L) IC M.
(* [comment removed for export] *)
Definition xfoot (g : PMES.eghost) (a : Z) : Prop := PMXA.efootA V S2 g a \/ PMLA.LIT_LO IC <= a < PMLA.LIT_HI IC.
Lemma xinv_keep : forall (M M' : mem) g, (forall a, xfoot g a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> xinv M g -> xinv M' g.
Proof.
  intros M M' g AG [H1 H2]. split.
  - apply (ENC_AGREE M M' V S2 g H1). intros a Ha. apply AG. left. exact Ha.
  - apply (lits_ok_agree (hl_segs L) IC M M' LITS); [|exact H2]. intros a Ha. apply AG. right. exact Ha.
Qed.
(* [comment removed for export] *)
Lemma xfoot_cases : forall g a, xfoot g a ->
  (V <= a < V + PMES.ENC_SIZE) \/ (S2 <= a < S2 + 24) \/ (exists b, In b (PMES.g_lbv g) /\ (fst b <= a < fst b + snd b \/ in_shadow_of (fst b) (snd b) a)) \/
  (in_shadow_of V PMES.ENC_SIZE a \/ in_shadow_of S2 24 a) \/ PMLA.LIT_LO IC <= a < PMLA.LIT_HI IC.
Proof.
  intros g a [[H|[H|[H|[H|[H|H]]]]]|H].
  - left. exact H.
  - right; left. exact H.
  - right; right; left. destruct H as (b & Hb & Hr). exists b. split; [exact Hb | left; unfold in_block in Hr; lia].
  - right; right; left. destruct H as (b & Hb & Hr). exists b. split; [exact Hb | right; exact Hr].
  - right; right; right; left. left. exact H.
  - right; right; right; left. right. exact H.
  - do 4 right. exact H.
Qed.
Lemma kenc_nonneg : forall g, 0 <= hl_k_per_malloc L -> 0 <= PMXA.kenc L g.
Proof. intros g Hk. exact (PMXA.kenc_nonneg L g Hk). Qed.
End X.
End XKA.
