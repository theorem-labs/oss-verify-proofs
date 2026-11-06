(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncNtbSpec PeAEncNtb PeAEncKit PeAEncU64P.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ab4d4_ab4d8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENCVU.
#[local] Transparent e_end_value.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.
Definition INT64_MAX : Z := 9223372036854775807.

Definition CSK : list nat := [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition CSI : list nat := [2; 8; 9; 18; 19; 3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.

Definition inregs (R : bvmap 5 word) (sp ov v : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R (reg 8) = Z_to_bv 64 ov /\ getr R (reg 9) = Z_to_bv 64 v /\ getr R (reg 18) = Z_to_bv 64 (ov + 8) /\ getr R (reg 19) = Z_to_bv 64 SBL.
Definition fstat (M : word -> option byte) (sp : Z) : Prop :=
  L5.img_clear M 1253376 1286144 /\ L5.u64_at RSEGS M 1317368 SBL /\ L5.u32_at RSEGS M 1317376 1 /\ 140735332487232 <= sp <= 140737488355328 /\ sp mod 16 = 0
  /\ L5.writable RSEGS M (sp - 64) 64.
Definition fov (M : word -> option byte) (sp ov osk : Z) : Prop :=
  4096 <= ov <= 140737488355272 /\ ov mod 8 = 0 /\ (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) /\ L5KA.zeros_at M (ov / 8 + SBL) 7
  /\ L5.writable RSEGS M ov 56 /\ ((sp - 64) + 64 <= ov \/ ov + 56 <= (sp - 64))
  /\ L5KA.zeros_at M ((ov + 8) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 24) / 8 + SBL) 1 /\ L5KA.zeros_at M ((ov + 32) / 8 + SBL) 1
  /\ L5.u64_at RSEGS M (ov + 8) osk /\ 4096 <= osk <= 140737488355304 /\ osk mod 8 = 0.

Definition fcells (R0 : bvmap 5 word) (r : Z) (M : word -> option byte) (sp : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 8) r /\ L5.u64_at RSEGS M (sp - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (sp - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (sp - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (sp - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (sp - 48) (bv_unsigned (getr R0 (reg 20))).

Definition runA (lo hi byo raA : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk v r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 ov -> getr R (reg 11) = Z_to_bv 64 v -> getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487232 <= sp <= 140737488355328 -> sp mod 16 = 0 ->
    L5.writable RSEGS M (sp - 64) 64 -> fov M sp ov osk -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab378 M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSK -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raA /\ inregs R' sp ov v /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp + byo)
      /\ (lo = 0 -> getr R' (reg 20) = Z_to_bv 64 ((ov + 8) / 8 + SBL))
      /\ fcells R r M' sp.

Definition runB8 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov osk v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
    inregs R sp ov v -> getr R (reg 20) = Z_to_bv 64 ((ov + 8) / 8 + SBL) -> fstat M sp -> fov M sp ov osk -> 0 <= v <= 255 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 52 <= i < sp - 52 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab424 M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 0xab43c /\ getr R' (reg 10) = Z_to_bv 64 osk /\ getr R' (reg 11) = Z_to_bv 64 (sp - 52).

Definition runBW (pcB wr raW lo hi : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
    inregs R sp ov v -> fstat M sp -> lo <= v <= hi ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcB M) (mst fx' R' wr M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 raW /\ getr R' (reg 11) = Z_to_bv 64 (ov + 8).

Definition runJ (pcJ : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp ov v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
    inregs R sp ov v -> fstat M sp ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pcJ M) (mst fx' R' 0xab4b0 M')
      /\ (forall j, In j CSI -> getr R' (reg j) = getr R (reg j)).

Definition runE0 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk v eb r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregs R sp ov v -> fstat M sp -> fov M sp ov osk ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) eb -> 0 <= eb <= 140737488355328 -> fcells R0 r M sp -> L5.ra_ok r ->
    getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab4b0 M) (mst fx' R' r M')
      /\ regs_preserved R0 R'.

Definition runE1 : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (sp ov osk v eb ed cn r : Z),
    0 <= sp < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= osk < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= eb < 2 ^ 64 -> 0 <= ed < 2 ^ 64 -> 0 <= cn < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    inregs R sp ov v -> fstat M sp -> fov M sp ov osk ->
    L5.u64_at RSEGS M (ov + 24) eb -> L5.u64_at RSEGS M (ov + 32) ed -> 4096 <= eb <= 140737488355328 -> 4120 <= ed <= 140737488355328 -> ed mod 8 = 0 ->
    24 <= ed - eb <= 100000 -> L5.writable RSEGS M (ed - 24) 24 -> (2147446784 + 17592186048512 <= ed - 24 \/ (ed - 24) + 24 <= 2147446784) ->
    L5KA.zeros_at M ((ed - 8) / 8 + SBL) 1 ->
    ((ed - 24) + 24 <= (sp - 64) \/ (sp - 64) + 64 <= (ed - 24)) -> ((ed - 24) + 24 <= ov \/ ov + 56 <= (ed - 24)) -> L5.u64_at RSEGS M (ed - 8) cn ->
    fcells R0 r M sp -> L5.ra_ok r -> getr R0 (reg 2) = Z_to_bv 64 sp -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (ed - 8 <= i < ed - 8 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R 0xab4b0 M) (mst fx' R' r M')
      /\ regs_preserved R0 R'
      /\ L5.u64_at RSEGS M' (ed - 8) ((cn + 1) mod 2 ^ 64).

Local Ltac kept_tac KS := intros j Hj; apply KS; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl.
Local Ltac feedP P := L5SAR.feed P ltac:(first [assumption | unfold PEAENCVUP.aligned; assumption | lia]).

Local Ltac runA_pre A_conc :=
  intros fx R M sp ov osk v r H1 H2 H3 H4 G2 G10 G11 G1 RA K0 K1 K2 K3 K4 K5 FOV VR;
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12);
  let HO := fresh "HO" in let HV := fresh "HV" in
  assert (HO : bv_unsigned (getr R (reg 10)) = ov) by (rewrite G10; apply L5.unsigned_lit; exact H2);
  assert (HV : bv_unsigned (getr R (reg 11)) = v) by (rewrite G11; apply L5.unsigned_lit; exact H4);
  let Hr := fresh "Hr" in
  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite G1; apply L5.unsigned_lit; destruct RA as [Hr1 Hr2]; clear - Hr1; lia);
  let P := fresh "P" in
  pose proof (A_conc fx R M (fun j => match j with 2%nat => sp | 41%nat => osk | _ => 0 end)) as P; cbn beta iota in P; rewrite !HO, !HV in P;
  feedP P; rewrite Hr in P.
Local Ltac runA_tac8 A_conc :=
  runA_pre A_conc;
  let P := match goal with H : exists _ _ _, _ |- _ => H end in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & _ & S48 & S40 & S32 & S24 & S16 & S8);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|]; split; [kept_tac KS1|];
  split; [exact T1|]; split; [split; [exact T2|]; split; [rewrite T8; assumption|]; split; [rewrite T9; assumption|]; split; [exact T18| exact T19]|];
  split; [exact T10|]; split; [exact T11|]; split; [intros _; exact T20|];
  split; [exact S8|]; split; [exact S16|]; split; [exact S24|]; split; [exact S32|]; split; [exact S40| exact S48].
Local Ltac runA_tacW A_conc :=
  runA_pre A_conc;
  let P := match goal with H : exists _ _ _, _ |- _ => H end in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & _ & S48 & S40 & S32 & S24 & S16 & S8);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|]; split; [kept_tac KS1|];
  split; [exact T1|]; split; [split; [exact T2|]; split; [rewrite T8; assumption|]; split; [rewrite T9; assumption|]; split; [exact T18| exact T19]|];
  split; [exact T10|]; split; [exact T11|]; split; [intros X0; exfalso; clear - X0; lia|];
  split; [exact S8|]; split; [exact S16|]; split; [exact S24|]; split; [exact S32|]; split; [exact S40| exact S48].

Lemma u_runA8 : runA 0 255 (-53) 0xab424. Proof. unfold runA. runA_tac8 PEAENCVUP.avuA8_conc. Qed.
Lemma u_runA16 : runA 256 32767 (-51) 0xab468. Proof. unfold runA. runA_tacW PEAENCVUP.avuA16_conc. Qed.
Lemma u_runA32 : runA 32768 2147483647 (-50) 0xab4a4. Proof. unfold runA. runA_tacW PEAENCVUP.avuA32_conc. Qed.
Lemma u_runA64 : runA 2147483648 INT64_MAX (-49) 0xab3ec. Proof. unfold runA, INT64_MAX. runA_tacW PEAENCVUP.avuA64_conc. Qed.

Lemma u_runB8 : runB8.
Proof.
  unfold runB8. intros fx R M sp ov osk v H1 H2 H3 H4 (G2 & G8 & G9 & G18 & G19) G20 (K0 & K1 & K2 & K3 & K4 & K5) FOV VR.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as B12.
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12.
  assert (G10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply PMPK.word_id).
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply PMPK.word_id).
  assert (G12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply PMPK.word_id).
  pose proof (PEAENCVUP.avuB8_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v | 41%nat => osk
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P. cbn beta iota in P.
  feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T10 & T11 & _).
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [exact MS1|]. split; [kept_tac KS1|]. split; [exact T1|]. split; [exact T10| exact T11].
Qed.

Local Ltac runBW_tac B_conc :=
  intros fx R M sp ov v H1 H2 H4 (G2 & G8 & G9 & G18 & G19) (K0 & K1 & K2 & K3 & K4 & K5) VR;
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10; pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as B11; pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as B12;
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12;
  assert (G10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply PMPK.word_id);
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply PMPK.word_id);
  assert (G12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply PMPK.word_id);
  let P := fresh "P" in
  pose proof (B_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P; cbn beta iota in P;
  feedP P;
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T11);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|]; split; [kept_tac KS1|]; split; [exact T1| exact T11].

Lemma u_runB16 : runBW 0xab468 0xb0a00 0xab478 256 32767. Proof. unfold runBW. runBW_tac PEAENCVUP.avuB16_conc. Qed.
Lemma u_runB32 : runBW 0xab4a4 0xb0a98 0xab4b0 32768 2147483647. Proof. unfold runBW. runBW_tac PEAENCVUP.avuB32_conc. Qed.
Lemma u_runB64 : runBW 0xab3ec 0xb0b4c 0xab3f8 2147483648 INT64_MAX. Proof. unfold runBW, INT64_MAX. runBW_tac PEAENCVUP.avuB64_conc. Qed.

Local Ltac runJ_tac J_conc :=
  intros fx R M sp ov v H1 H2 H4 (G2 & G8 & G9 & G18 & G19) (K0 & K1 & K2 & K3 & K4 & K5);
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10; pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as B11; pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as B12;
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12;
  assert (G10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply PMPK.word_id);
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply PMPK.word_id);
  assert (G12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply PMPK.word_id);
  let P := fresh "P" in
  pose proof (J_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v
      | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P; cbn beta iota in P;
  feedP P;
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1| kept_tac KS1].

Lemma u_runJ8 : runJ 0xab43c. Proof. unfold runJ. runJ_tac PEAENCVUP.avuJ8_conc. Qed.
Lemma u_runJ16 : runJ 0xab478. Proof. unfold runJ. runJ_tac PEAENCVUP.avuJ16_conc. Qed.
Lemma u_runJ64 : runJ 0xab3f8. Proof. unfold runJ. runJ_tac PEAENCVUP.avuJ64_conc. Qed.

Lemma regs_end (R R0 R3 : bvmap 5 word) (sp : Z) (KS : list nat) :
  (forall j, In j CSK -> In j KS) -> (forall x, In x KS -> getr R3 (reg x) = getr R (reg x)) -> (forall j, In j CSK -> getr R (reg j) = getr R0 (reg j)) ->
  getr R0 (reg 2) = Z_to_bv 64 sp -> getr R3 (reg 2) = Z_to_bv 64 sp ->
  getr R3 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R3 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R3 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R3 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R3 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> regs_preserved R0 R3.
Proof.
  intros SUB KS3 QCS Rsp T2 T8 T9 T18 T19 T20. apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
  repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply PMPK.word_id | rewrite T9; apply PMPK.word_id | rewrite T18; apply PMPK.word_id
                                          | rewrite T19; apply PMPK.word_id | rewrite T20; apply PMPK.word_id | rewrite (KS3 _) by (apply SUB; inl); apply QCS; inl ] |]). destruct Hj.
Qed.

Lemma u_runE0 : runE0.
Proof.
  unfold runE0. intros fx R R0 M sp ov osk v eb r H1 H2 H3 H4 H5 H6 (G2 & G8 & G9 & G18 & G19) (K0 & K1 & K2 & K3 & K4 & K5) FOV U24 U32 EB (C8 & C16 & C24 & C32 & C40 & C48) RA R0sp QCS.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as B12.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as C8r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as C9r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as C18r.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as C19r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as C20r.
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12, C8r, C9r, C18r, C19r, C20r.
  assert (G10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply PMPK.word_id).
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply PMPK.word_id).
  assert (G12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply PMPK.word_id).
  pose proof (PEAENCVUP.avuE0_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v | 38%nat => eb | 44%nat => r
      | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
      | 49%nat => bv_unsigned (getr R0 (reg 20)) | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
  cbn beta iota in P. feedP P.
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20).
  pose proof RA as (Hr1 & Hr2).
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xab524 W_ab4d4 r F_ab4d4 eq_refl D_ab4d4 T1 ltac:(lia) Hr2) as MSR.
  exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
  apply (regs_end R R0 R1 sp PEAENCVUP.KS_avuE0); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS1| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20].
Qed.

Lemma u_runE1 : runE1.
Proof.
  unfold runE1. intros fx R R0 M sp ov osk v eb ed cn r H1 H2 H3 H4 H5 H6 H7 H8 (G2 & G8 & G9 & G18 & G19) (K0 & K1 & K2 & K3 & K4 & K5) FOV U24 U32 EB ED AL8 LEN WR24 NSH ZC DJS DJO UC
    (C8 & C16 & C24 & C32 & C40 & C48) RA R0sp QCS.
  destruct FOV as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr R (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr R (reg 12))) as B12.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as C8r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as C9r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as C18r.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 19))) as C19r. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 20))) as C20r.
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12, C8r, C9r, C18r, C19r, C20r.
  assert (G10 : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 10)))) by (symmetry; apply PMPK.word_id).
  assert (G11 : getr R (reg 11) = Z_to_bv 64 (bv_unsigned (getr R (reg 11)))) by (symmetry; apply PMPK.word_id).
  assert (G12 : getr R (reg 12) = Z_to_bv 64 (bv_unsigned (getr R (reg 12)))) by (symmetry; apply PMPK.word_id).
  pose proof RA as (Hr1 & Hr2).
  destruct (Z.eq_dec cn 18446744073709551615) as [CW|CNW].
  - rewrite CW in UC.
    pose proof (PEAENCVUP.avuE1w_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v | 38%nat => eb | 39%nat => ed | 44%nat => r
        | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
        | 49%nat => bv_unsigned (getr R0 (reg 20)) | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
    cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xab524 W_ab4d4 r F_ab4d4 eq_refl D_ab4d4 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [apply (regs_end R R0 R1 sp PEAENCVUP.KS_avuE1w); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS1| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20]|].
    rewrite CW. change ((18446744073709551615 + 1) mod 2 ^ 64) with 0. exact CC.
  - pose proof (PEAENCVUP.avuE1_conc fx R M (fun j => match j with 2%nat => sp | 10%nat => ov | 11%nat => v | 38%nat => eb | 39%nat => ed | 42%nat => cn | 44%nat => r
        | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9)) | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19))
        | 49%nat => bv_unsigned (getr R0 (reg 20)) | 55%nat => bv_unsigned (getr R (reg 10)) | 56%nat => bv_unsigned (getr R (reg 11)) | 57%nat => bv_unsigned (getr R (reg 12)) | _ => 0 end)) as P.
    cbn beta iota in P. feedP P.
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & CC).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1 0xab524 W_ab4d4 r F_ab4d4 eq_refl D_ab4d4 T1 ltac:(lia) Hr2) as MSR.
    exists fx1, R1, M1. split; [exact MG1|]. split; [exact FRZ1|]. split; [eapply msteps_trans; [exact MS1| exact MSR]|].
    split; [apply (regs_end R R0 R1 sp PEAENCVUP.KS_avuE1); [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl| exact KS1| exact QCS| exact R0sp| exact T2| exact T8| exact T9| exact T18| exact T19| exact T20]|].
    rewrite Z.mod_small by lia. exact CC.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.
Let NTB16 := PEAENTB.ntb_i16_ok L ar C HI P LY HIok PO PB.
Let NTB32 := PEAENTB.ntb_i32_ok L ar C HI P LY HIok PO PB.
Let NTB64 := PEAENTB.ntb_i64_ok L ar C HI P LY HIok PO PB.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (v : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (p : list Z).
Variables (xstk : list pstate) (xpos : Z) (xmore xdone xhalt : bool) (xdepth : Z) (xec : bool) (xestk : list eitem) (xedepth xlo xhi : Z) (xbad : bool).
Variables (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Let X : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad.
Let XS (a : Z) : st := ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + a) (xhi + a) xbad.
Let W : Z := PECSPA.uint64_width v.
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 4.
Hypothesis FRM : PMSPA.ffroomA 4 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_v AD fb).
Hypothesis VR : 0 <= v <= INT64_MAX.
Hypothesis A11 : getr R (reg 11) = Z_to_bv 64 v.
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis MP : PECSPA.mp_enc p X.
Hypothesis HBN : PESKA.spa_hb P (xhi + W).
Hypothesis CRED : PMSP.credit_le (PECA.pot_encA L ar P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (en' : PEC.enc) (k' : PESK.sink) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (e_end_value (XS W)) s str sm en' k' e' cat -> (e = true -> e' = true) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PEC.W_enc AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_encA L ar P en k) (PECA.pot_encA L ar P en' k') ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.owned s en' k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Definition FC (Mx : word -> option byte) : Prop := fcells R r Mx sp.
Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 4) with 20480 in ASTK, STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp.

Lemma FC_frame M1 M2 : (forall a, sp - 64 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros AG (C8 & C16 & C24 & C32 & C40 & C48). entry_facts.
  assert (SV : forall a0 w, sp - 64 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; clear - Hi H1 H2; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.

Lemma FC_but M1 M2 lo hi : hi <= sp - 48 -> (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> FC M1 -> FC M2.
Proof.
  intros Hhi AG (C8 & C16 & C24 & C32 & C40 & C48). entry_facts.
  assert (SV : forall a0 w, sp - 48 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 w -> L5.u64_at RSEGS M2 a0 w).
  { intros a0 w H1 H2 U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply AG; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  unfold FC, fcells. repeat (split; [apply SV; [clear; lia| clear; lia| assumption]|]). apply SV; [clear; lia| clear; lia| assumption].
Qed.
Lemma HFR : 64 = 32 \/ 64 = 64. Proof. right; reflexivity. Qed.
Lemma CSK3 : In 3%nat CSK. Proof. inl. Qed.
Lemma CSK4 : In 4%nat CSK. Proof. inl. Qed.
Lemma CSKall j : In j CSK -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma CSIall j : In j CSI -> In j L5SAR.cs_all. Proof. intros Hj. cbn in Hj. decompose [or] Hj; try contradiction; subst; inl. Qed.
Lemma W1 : 2 <= W <= 9. Proof. unfold W, PECSPA.uint64_width. repeat destruct (_ <=? _); lia. Qed.

Abbreviation INV := (PEAEK.inv L ar HI P M model LBX FF LK Aw cr sp fb xlo xhi s en k FC).
Abbreviation csk := (PEAEK.csk CSK R).

Lemma inregs_after R1 R2 ov : inregs R1 sp ov v -> csk R1 -> regs_preserved R1 R2 -> inregs R2 sp ov v /\ csk R2.
Proof.
  intros (G2 & G8 & G9 & G18 & G19) QCS RP. split.
  - split; [rewrite (L5SAR.cs_of_preserved R1 R2 2 RP) by inl; exact G2|]. split; [rewrite (L5SAR.cs_of_preserved R1 R2 8 RP) by inl; exact G8|].
    split; [rewrite (L5SAR.cs_of_preserved R1 R2 9 RP) by inl; exact G9|]. split; [rewrite (L5SAR.cs_of_preserved R1 R2 18 RP) by inl; exact G18|].
    rewrite (L5SAR.cs_of_preserved R1 R2 19 RP) by inl; exact G19.
  - intros j Hj. rewrite (L5SAR.cs_of_preserved R1 R2 j RP (CSKall j Hj)). exact (QCS j Hj).
Qed.
Lemma inregs_kept R1 R2 ov : inregs R1 sp ov v -> csk R1 -> (forall j, In j CSI -> getr R2 (reg j) = getr R1 (reg j)) -> inregs R2 sp ov v /\ csk R2.
Proof.
  intros (G2 & G8 & G9 & G18 & G19) QCS KS. split.
  - split; [rewrite (KS 2%nat) by inl; exact G2|]. split; [rewrite (KS 8%nat) by inl; exact G8|]. split; [rewrite (KS 9%nat) by inl; exact G9|].
    split; [rewrite (KS 18%nat) by inl; exact G18|]. rewrite (KS 19%nat) by inl; exact G19.
  - intros j Hj. rewrite (KS j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). exact (QCS j Hj).
Qed.

Lemma tailE a (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  INV Mq mdq LKq Awq crq kq a -> a = W -> inregs Rq sp (PMSPA.o_v AD fb) v -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xab4b0 Mq mdq) K.
Proof.
  intros INVq Ha IRq QCS. entry_facts.
  pose proof (PEAEK.vis_facts L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq a INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & SVV & FCq).
  cbv beta in SVV. set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  pose proof CPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL & _). destruct CL as (_ & _ & _ & _ & _ & Lestk & _). cbn [s_estk X] in Lestk.
  destruct FCq as (C8 & C16 & C24 & C32 & C40 & C48).
  assert (FCv : fcells R r MV sp) by (split; [| split; [| split; [| split; [| split]]]]; (apply SVV; [clear; lia| clear; lia| assumption])).
  pose proof (bv_unsigned_in_range 64 (getr Rq (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
  assert (OVR : 0 <= ov < 2 ^ 64) by (clear - OR; lia). assert (OKR : 0 <= osk < 2 ^ 64) by (clear - KR; lia). assert (VRR : 0 <= v < 2 ^ 64) by (unfold INT64_MAX in VR; clear - VR; lia).
  assert (SP0 : 0 <= sp < 2 ^ 64) by (clear - SPR; lia).
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOVq : fov MV sp ov osk).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|].
    split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|]. split; [exact U8|]. split; [exact KR| exact K8]. }
  destruct xestk as [|e1 rr] eqn:HXS.
  - rewrite Lestk in U32. cbn [rev length Z.of_nat Z.mul] in U32. rewrite Z.add_0_r in U32.
    destruct (u_runE0 fxq Rq R MV sp ov osk v (PEC.en_b en) r SP0 OVR OKR VRR ltac:(clear - EB; lia) ltac:(clear - Hr1; lia) IRq FS FOVq U24 U32 ltac:(clear - EB; lia) FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3).
    exact (PEAEK.finish_ro L ar C HI P LY HIok 64 W HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec [] xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS KONT a 0xab4b0 fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v INVq eq_refl Ha MS3 MG3 FRZ3 RP3).
  - pose proof (PEAEK.vis_facts_top L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
                  HH ENT FOK FC CPRE MP Mq mdq LKq Awq crq kq a e1 rr INVq eq_refl)
      as (HLEN & EKP & EB1 & ED2 & ALend & ED3 & WR24 & EB6 & ZC & EDS & OVA & TCv & E1C & E1OK & BINe & EDC & EBC & _).
    cbv beta in HLEN, ED2, ALend, ED3, WR24, EB6, ZC, EDS, OVA, TCv, EDC. fold H MV ov in WR24, ZC, TCv, OVA, EDS. fold H in ZC. fold MV in ZC.
    rewrite HLEN in U32. set (ed := PEC.en_b en + 24 * (Z.of_nat (length rr) + 1)) in *.
    destruct (u_runE1 fxq Rq R MV sp ov osk v (PEC.en_b en) ed (ei_cnt e1) r SP0 OVR OKR VRR ltac:(clear - EB; lia) ltac:(clear - EB1 ED2; lia) E1C ltac:(clear - Hr1; lia) IRq FS FOVq U24 U32
              ltac:(clear - EB EB1; lia) ltac:(clear - EB1 ED2 ED3; lia) ALend ED3 WR24 EB6 ZC EDS OVA TCv FCv RAok Rsp QCS)
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & RP3 & CC).
    exact (PEAEK.finish_bump L ar C HI P LY HIok 64 W HFR R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec (e1 :: rr) xedepth xlo xhi xbad s str sm en k e
             HH ENT FOK FC CPRE INCS MP CRED KONT a 0xab4b0 fxq Rq Mq mdq LKq Awq crq kq fx3 R3 M3v e1 rr INVq eq_refl Ha MS3 MG3 FRZ3 CC RP3).
Qed.

Lemma step_ro a (fxq : FPState) Rq Mq mdq LKq Awq crq kq (pcq pc' : Z) (fx3 : FPState) R3 M3v
      (KX : FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) :
  INV Mq mdq LKq Awq crq kq a ->
  msteps RSEGS (mst fxq Rq pcq (mrestrict (ahid Awq mdq) Mq)) (mst fx3 R3 pc' M3v) -> mem_grows (mrestrict (ahid Awq mdq) Mq) M3v ->
  (forall i, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = mrestrict (ahid Awq mdq) Mq (Z_to_bv 64 i)) ->
  (forall md3, INV Mq md3 LKq Awq crq kq a -> srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx3) R3 pc' Mq md3) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcq Mq mdq) K.
Proof.
  intros INVq MS3 MG3 FRZ3 KX3. pose proof INVq as (FCq & _ & _ & _ & AMq & _ & _ & HHq & _).
  unfold PMSPA.cfg. apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq pcq R3 pc' M3v K HHq AMq MS3 MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
  apply KX3. apply (PEAEK.inv_frame L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq Mq mdq md3 LKq Awq crq kq a sp sp INVq);
    [clear; lia| clear; lia| intros w D; exact D| intros i _ _; reflexivity| exact FCq| exact HH3| exact AM3| exact MRT3].
Qed.

Lemma stepJ pcJ a (fxq : FPState) Rq Mq mdq LKq Awq crq kq : runJ pcJ ->
  INV Mq mdq LKq Awq crq kq a -> a = W -> inregs Rq sp (PMSPA.o_v AD fb) v -> csk Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcJ Mq mdq) K.
Proof.
  intros RJ INVq Ha IRq QCS.
  pose proof (PEAEK.vis_facts L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq a INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & _).
  assert (FS : fstat (mrestrict (ahid Awq mdq) Mq) sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  destruct (RJ fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(unfold INT64_MAX in VR; clear - VR; lia) IRq FS)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3).
  apply (step_ro a fxq Rq Mq mdq LKq Awq crq kq pcJ 0xab4b0 fx3 R3 M3v (fun _ _ _ _ => True) INVq MS3 MG3 FRZ3).
  intros md3 INV3. destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. exact (tailE a fx3 R3 Mq md3 LKq Awq crq kq INV3 Ha IR3 QCS3).
Qed.

Lemma stepBW pcB wr raW lo hi kb a (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  runBW pcB wr raW lo hi -> PENTBA.ntb_specA RSEGS AD L ar HI wr kb P -> lo <= v <= hi -> 0 <= kb -> L5.ra_ok raW ->
  INV Mq mdq LKq Awq crq kq a -> xhi + a + kb <= xhi + W -> inregs Rq sp (PMSPA.o_v AD fb) v -> csk Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 (a + kb) -> inregs R2 sp (PMSPA.o_v AD fb) v -> csk R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raW M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq pcB Mq mdq) K.
Proof.
  intros RB NTB HV KB0 RAW INVq Hh IRq QCS KX.
  pose proof (PEAEK.vis_facts L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq a INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & _).
  assert (FS : fstat (mrestrict (ahid Awq mdq) Mq) sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  destruct (RB fxq Rq (mrestrict (ahid Awq mdq) Mq) sp (PMSPA.o_v AD fb) v ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(unfold INT64_MAX in VR; clear - VR; lia) IRq FS HV)
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T11).
  apply (step_ro a fxq Rq Mq mdq LKq Awq crq kq pcB wr fx3 R3 M3v (fun _ _ _ _ => True) INVq MS3 MG3 FRZ3).
  intros md3 INV3. destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. pose proof IR3 as (G2 & _).
  apply (PEAEK.wr_call L ar C HI P LY HIok 64 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           a kb wr (xhi + W) raW fx3 R3 Mq md3 LKq Awq crq kq NTB INV3 HBN Hh KB0 RAW T1 G2 T11 QCS3).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. destruct (inregs_after R3 R2 _ IR3 QCS3 RP2) as [IR2 QCS2]. exact (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2).
Qed.

Lemma stepA lo hi byo raA : runA lo hi byo raA -> lo <= v <= hi -> -64 <= byo <= -49 -> L5.ra_ok raA ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 1 -> inregs R2 sp (PMSPA.o_v AD fb) v -> csk R2 ->
      (lo = 0 -> getr R2 (reg 20) = Z_to_bv 64 ((PMSPA.o_v AD fb + 8) / 8 + SBL)) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 raA M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xab378 M model) K.
Proof.
  intros RA HV BYO RAA KX. entry_facts. pose proof AM as (Mh & MI).
  pose proof (PEAEK.vis_entry L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 A10 CPRE)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & G2 & G10 & G1 & RAr & RB).
  cbv beta in RB. set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (FOV0 : fov MV sp ov osk).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|].
    split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|]. split; [exact U8|]. split; [exact KR| exact K8]. }
  destruct (RA fx R MV sp ov osk v r ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(clear - KR; lia) ltac:(unfold INT64_MAX in VR; clear - VR; lia) G2 G10 A11 G1 RAr
             IC0 CSBv CUARv ltac:(clear - SPR; lia) A16' SWR FOV0 HV) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & IR1 & T10 & T11 & T20 & FC1).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xab378 R1 0xaf02c M1v (fun a0 => sp - 64 <= a0 < sp - 64 + 64) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (FCM1 : FC M1).
  { destruct FC1 as (C8 & C16 & C24 & C32 & C40 & C48). rewrite <- VIS1 in C8, C16, C24, C32, C40, C48.
    unfold FC, fcells. repeat (split; [apply RB; [clear; lia| clear; lia| assumption]|]). apply RB; [clear; lia| clear; lia| assumption]. }
  pose proof (PEAEK.inv_start L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e HH ENT FOK SP32 FC CPRE
                M1 md1 MGM1 FR1 FCM1 HH1 AM1 MRT1) as INV1.
  pose proof IR1 as (G2' & _). pose proof W1 as HW.
  apply (PEAEK.pb_call L ar C HI P LY HIok PO PB 64 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           0 (sp + byo) (xhi + W) raA fx1 R1 M1 md1 LK Aw cr k INV1 HBN ltac:(clear - HW; lia) ltac:(clear - BYO; lia) ltac:(clear - BYO; lia) RAA T1 G2' T10 T11 KS1).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. destruct (inregs_after R1 R2 _ IR1 KS1 RP2) as [IR2 QCS2].
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2). intros Hlo. rewrite (L5SAR.cs_of_preserved R1 R2 20 RP2) by inl. exact (T20 Hlo).
Qed.

Lemma stepB8 (fxq : FPState) Rq Mq mdq LKq Awq crq kq : v <= 255 ->
  INV Mq mdq LKq Awq crq kq 1 -> inregs Rq sp (PMSPA.o_v AD fb) v -> csk Rq -> getr Rq (reg 20) = Z_to_bv 64 ((PMSPA.o_v AD fb + 8) / 8 + SBL) ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, INV M2 md2 LK2 Aw2 cr2 k2 2 -> inregs R2 sp (PMSPA.o_v AD fb) v -> csk R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx2) R2 0xab43c M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fxq) Rq 0xab424 Mq mdq) K.
Proof.
  intros HV INVq IRq QCS G20 KX. entry_facts.
  pose proof (PEAEK.vis_facts L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq mdq LKq Awq crq kq 1 INVq)
    as (IC0 & CSBv & CUARv & SPR & A16' & SWR & OR & O8 & OBIG & Zov & OWR & ODJ & Z8 & Z24 & Z32 & U8 & KR & K8 & KO & U24 & U32 & EB & SVV & FCq).
  pose proof INVq as (_ & _ & _ & _ & AMq & _ & _ & HHq & _).
  set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *. set (ov := PMSPA.o_v AD fb) in *. set (osk := PESK.o_sink EE fb) in *.
  assert (FS : fstat MV sp) by (split; [exact IC0|]; split; [exact CSBv|]; split; [exact CUARv|]; split; [clear - SPR; lia|]; split; [exact A16'| exact SWR]).
  assert (FOVq : fov MV sp ov osk).
  { split; [exact OR|]. split; [exact O8|]. split; [exact OBIG|]. split; [exact Zov|]. split; [exact OWR|]. split; [exact ODJ|].
    split; [exact Z8|]. split; [exact Z24|]. split; [exact Z32|]. split; [exact U8|]. split; [exact KR| exact K8]. }
  destruct (u_runB8 fxq Rq MV sp ov osk v ltac:(clear - SPR; lia) ltac:(clear - OR; lia) ltac:(clear - KR; lia) ltac:(unfold INT64_MAX in VR; clear - VR; lia) IRq G20 FS FOVq ltac:(clear - VR HV; lia))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T10 & T11).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq fxq fx3 Rq 0xab424 R3 0xaf02c M3v (fun a0 => sp - 52 <= a0 < sp - 52 + 1) K HHq AMq MS3 MG3).
  { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (INV3 : INV M3 md3 LKq Awq crq kq 1).
  { apply (PEAEK.inv_frame L ar C HI P LY HIok 64 HFR R M model LBX FF LK Aw cr sp r fb xlo xhi s en k HH ENT FOK SP32 FC Mq M3 mdq md3 LKq Awq crq kq 1 (sp - 52) (sp - 52 + 1) INVq);
      [clear; lia| clear; lia| exact MGM3| exact FR3| exact (FC_but Mq M3 (sp - 52) (sp - 52 + 1) ltac:(clear; lia) FR3 FCq)| exact HH3| exact AM3| exact MRT3]. }
  destruct (inregs_kept Rq R3 _ IRq QCS KS3) as [IR3 QCS3]. pose proof IR3 as (G2 & _). pose proof W1 as HW.
  assert (HW2 : W = 2) by (unfold W, PECSPA.uint64_width; replace (v <=? 255) with true by (symmetry; apply Z.leb_le; exact HV); reflexivity).
  apply (PEAEK.pb_call L ar C HI P LY HIok PO PB 64 CSK HFR CSK3 CSK4 PMODE R M model K LBX FF LK Aw cr sp r fb xlo xhi s en k HH K0 ENT FRM FRS FOK SP32 FC FC_frame CRED
           1 (sp - 52) (xhi + W) 0xab43c fx3 R3 M3 md3 LKq Awq crq kq INV3 HBN ltac:(clear - HW2; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(split; [clear; lia| reflexivity]) T1 G2 T10 T11 QCS3).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2. destruct (inregs_after R3 R2 _ IR3 QCS3 RP2) as [IR2 QCS2].
  exact (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2).
Qed.

Lemma main : srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R 0xab378 M model) K.
Proof.
  pose proof W1 as HW.
  destruct (Z.le_gt_cases v 255) as [V8|V8'].
  { assert (HW2 : W = 2) by (unfold W, PECSPA.uint64_width; replace (v <=? 255) with true by (symmetry; apply Z.leb_le; exact V8); reflexivity).
    apply (stepA 0 255 (-53) 0xab424 u_runA8); [clear - VR V8; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2 G20.
    apply (stepB8 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 V8 INV2 IR2 QCS2 (G20 eq_refl)).
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
    exact (stepJ 0xab43c 2 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ8 INV4 (eq_sym HW2) IR4 QCS4). }
  destruct (Z.le_gt_cases v 32767) as [V16|V16'].
  { assert (HW3 : W = 3).
    { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with true by (symmetry; apply Z.leb_le; exact V16). reflexivity. }
    apply (stepA 256 32767 (-51) 0xab468 u_runA16); [clear - V8' V16; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2 _.
    apply (stepBW 0xab468 0xb0a00 0xab478 256 32767 2 1 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 u_runB16 NTB16); [clear - V8' V16; lia| clear; lia| split; [clear; lia| reflexivity]| exact INV2| clear - HW3; lia| exact IR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
    exact (stepJ 0xab478 3 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ16 INV4 (eq_sym HW3) IR4 QCS4). }
  destruct (Z.le_gt_cases v 2147483647) as [V32|V32'].
  { assert (HW5 : W = 5).
    { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
      replace (v <=? 2147483647) with true by (symmetry; apply Z.leb_le; exact V32). reflexivity. }
    apply (stepA 32768 2147483647 (-50) 0xab4a4 u_runA32); [clear - V16' V32; lia| clear; lia| split; [clear; lia| reflexivity]|].
    intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2 _.
    apply (stepBW 0xab4a4 0xb0a98 0xab4b0 32768 2147483647 4 1 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 u_runB32 NTB32); [clear - V16' V32; lia| clear; lia| split; [clear; lia| reflexivity]| exact INV2| clear - HW5; lia| exact IR2| exact QCS2|].
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
    exact (tailE 5 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 (eq_sym HW5) IR4 QCS4). }
  assert (HW9 : W = 9).
  { unfold W, PECSPA.uint64_width. replace (v <=? 255) with false by (symmetry; apply Z.leb_gt; exact V8'). replace (v <=? 32767) with false by (symmetry; apply Z.leb_gt; exact V16').
    replace (v <=? 2147483647) with false by (symmetry; apply Z.leb_gt; exact V32'). reflexivity. }
  apply (stepA 2147483648 INT64_MAX (-49) 0xab3ec u_runA64); [clear - V32' VR; lia| clear; lia| split; [clear; lia| reflexivity]|].
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 IR2 QCS2 _.
  apply (stepBW 0xab3ec 0xb0b4c 0xab3f8 2147483648 INT64_MAX 8 1 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 u_runB64 NTB64); [clear - V32' VR; lia| clear; lia| split; [clear; lia| reflexivity]| exact INV2| clear - HW9; lia| exact IR2| exact QCS2|].
  intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 IR4 QCS4.
  exact (stepJ 0xab3f8 9 fx4 R4 M4 md4 LK4 Aw4 cr4 k4 u_runJ64 INV4 (eq_sym HW9) IR4 QCS4).
Qed.
End Call.

Theorem v_uint64_ok : PECSA.v_uint64_spec L ar HI P.
Proof.
  unfold PECSA.v_uint64_spec, PECSPA.v_uint64_spec, PECSPA.eslot_spec. cbn [pe_uint64 EE PeCLayoutA.EADDR_A].
  intros PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 AV CPRE INCS POK MP NB HB CRED KONT.
  destruct AV as (VR & A11 & _). rewrite L5K.rl11 in A11. unfold INT64_MAX in VR |- *.
  destruct X as [xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad].
  assert (ESC : forall w, e_scalar w w (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad)
          = e_end_value (ST xstk xpos xmore xdone xhalt xdepth xec xestk xedepth (xlo + w) (xhi + w) xbad)) by reflexivity.
  rewrite ESC in HB, KONT. rewrite eev_hi in HB. cbn [s_hi] in HB.
  exact (main PMODE v fx R M model K LBX FF LK Aw cr sp r fb cat p xstk xpos xmore xdone xhalt xdepth xec xestk xedepth xlo xhi xbad s str sm en k e
           HH AM K0 ENT FRM FRS FOK SP32 A10 VR A11 CPRE INCS MP HB CRED KONT).
Qed.
End WithHeap.
End PEAENCVU.
